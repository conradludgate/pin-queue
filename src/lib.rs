//! This crate provides [`PinQueue`], a safe `Pin`-based intrusive linked list for a FIFO queue.
//!
/*! ```
use std::sync::Arc;
use std::pin::Pin;

// define your node type (using pin-projection to project the intrusive node)
pin_project_lite::pin_project!(
    struct Node<V: ?Sized> {
        #[pin]
        intrusive: pin_queue::Intrusive<QueueTypes>,
        value: V,
    }
);

impl<V> Node<V> {
    pub fn new(value: V) -> Self {
        Self {
            intrusive: pin_queue::Intrusive::new(),
            value,
        }
    }
}

// Define how to acquire the intrusive values from the node
struct Key;
impl pin_queue::GetIntrusive<QueueTypes> for Key {
    fn get_intrusive(
        p: Pin<&Node<dyn std::fmt::Display>>
    ) -> Pin<&pin_queue::Intrusive<QueueTypes>> {
        p.project_ref().intrusive
    }
}

// alias of all the relevant types
type QueueTypes = dyn pin_queue::Types<
    // with checked IDs
    Id = pin_queue::id::Checked,
    // with this intrusive key
    Key = Key,
    // storing this pointer
    Pointer = Arc<Node<dyn std::fmt::Display>>
>;

let mut queue = pin_queue::PinQueue::<QueueTypes>::new(pin_queue::id::Checked::new());

// can push to the back
queue.push_back(Arc::pin(Node::new(1))).unwrap();
// can push many types
queue.push_back(Arc::pin(Node::new("hello"))).unwrap();

// can pop from the front
assert_eq!(queue.pop_front().unwrap().value.to_string(), "1");
assert_eq!(queue.pop_front().unwrap().value.to_string(), "hello");

assert!(queue.pop_front().is_none());
``` */
#![warn(
    clippy::pedantic,
    missing_debug_implementations,
    missing_docs,
    noop_method_call,
    trivial_casts,
    trivial_numeric_casts,
    unsafe_op_in_unsafe_fn,
    unused_lifetimes,
    unused_qualifications
)]
#![allow(
    // Repetition is used in `Send`+`Sync` bounds so each one can be individually commented.
    clippy::type_repetition_in_bounds,

    // I export all the types at the crate root, so this lint is pointless.
    clippy::module_name_repetitions,
)]

pub mod id;
use core::{cell::UnsafeCell, fmt, ops::Deref, pin::Pin};
use std::{mem::ManuallyDrop, sync::Arc};

use crate::id::Id;

/// Types used in a [`PinQueue`]. This trait is used to avoid an excessive number of generic
/// parameters on [`PinQueue`] and related types.
pub trait Types: 'static {
    /// The ID type this list uses to ensure that different [`PinQueue`]s are not mixed up.
    ///
    /// This crate provides a couple built-in ID types, but you can also define your own:
    /// - [`id::Checked`]:
    ///     IDs are allocated with a single global atomic `u64` counter.
    /// - [`id::Unchecked`]:
    ///     The responsibility is left up to the user to ensure that different [`PinQueue`]s are not
    ///     incorrectly mixed up. Using this is `unsafe`.
    /// - [`id::DebugChecked`]:
    ///     Equivalent to [`id::Checked`] when `debug_assertions` are enabled, but
    ///     [`id::Unchecked`] in release.
    type Id: Id;

    /// How to extract the intrusive data from the pointer
    type Key;

    /// The pointer type that will be stored in the queue
    type Pointer: SharedPointer;
}

/// Gets the intrusive component out of a node
pub trait GetIntrusive<T: ?Sized + Types> {
    /// From the pinned node, get the intrusive component
    fn get_intrusive(p: Pin<&<T::Pointer as Deref>::Target>) -> Pin<&Intrusive<T>>;
}

/// An intrusive linked-list based FIFO queue
pub struct PinQueue<T: Types + ?Sized>
where
    T::Key: GetIntrusive<T>,
{
    id: T::Id,
    pointers: Option<ListPointers<T>>,
}

struct ListPointers<T: Types + ?Sized> {
    head: Pin<T::Pointer>,
    tail: ManuallyDrop<Pin<T::Pointer>>,
}

impl<T: ?Sized + Types> fmt::Debug for PinQueue<T>
where
    T::Key: GetIntrusive<T>,
{
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PinQueue").field("id", &self.id).finish()
    }
}

/// `Pointer` trait represents an aliasable read-only shared-ownership pointer.
///
/// # Safety
/// Type must be an aliasable pointer
pub unsafe trait SharedPointer: Deref + 'static + Sized {}

// Safety: Arc is aliasable
unsafe impl<T: ?Sized + 'static> SharedPointer for Arc<T> {}

/// The error returned by [`PinQueue::push_back`] when the node is already in a [`PinQueue`]
pub struct AlreadyInsertedError<P>(pub Pin<P>);

impl<P> fmt::Debug for AlreadyInsertedError<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("AlreadyInsertedError")
    }
}
impl<P> fmt::Display for AlreadyInsertedError<P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("node was already inserted into a PinQueue")
    }
}

impl<P> std::error::Error for AlreadyInsertedError<P> {}

impl<T: ?Sized + Types> PinQueue<T>
where
    T::Key: GetIntrusive<T>,
{
    /// Create a new empty `PinQueue` from a unique ID.
    pub fn new(id: id::Unique<T::Id>) -> Self {
        PinQueue {
            id: id.into_inner(),
            pointers: None,
        }
    }

    /// Insert the node into the back of the queue.
    ///
    /// # Errors
    /// This will fail if the node is already inserted into another queue
    pub fn push_back(
        &mut self,
        node: Pin<T::Pointer>,
    ) -> Result<(), AlreadyInsertedError<T::Pointer>> {
        if !self
            .id
            .acquire(&<T::Key as GetIntrusive<T>>::get_intrusive(node.as_ref()).lock)
        {
            return Err(AlreadyInsertedError(node));
        };
        // initiate a copy of the pointer. This is fine because `T::Pointer` guarantees this is
        // an aliasable type, and we will never drop this copy
        let tail = unsafe { ManuallyDrop::new(std::ptr::read(&node)) };

        let pointers = match self.pointers.take() {
            Some(mut pointers) => {
                let intrusive = <T::Key as GetIntrusive<T>>::get_intrusive(pointers.tail.as_ref());
                let old = unsafe { (*intrusive.next.get()).replace(node) };
                debug_assert!(old.is_none());
                pointers.tail = tail;
                pointers
            }
            None => ListPointers { head: node, tail },
        };
        self.pointers = Some(pointers);
        Ok(())
    }

    /// Take the first node from the queue
    pub fn pop_front(&mut self) -> Option<Pin<T::Pointer>> {
        let mut pointers = self.pointers.take()?;
        let node = pointers.head;
        let intrusive = <T::Key as GetIntrusive<T>>::get_intrusive(node.as_ref());
        if let Some(next) = unsafe { (*intrusive.next.get()).take() } {
            pointers.head = next;
            self.pointers = Some(pointers);
        };
        let released = self.id.release(&intrusive.lock);
        debug_assert!(released);
        Some(node)
    }
}

// unsafe impl<T: ?Sized + Types> Send for Intrusive<T> where <T::Id as id::Id>::Atomic: Send {}

// Same bounds as Mutex
unsafe impl<T: ?Sized + Types> Sync for Intrusive<T> where T::Pointer: Send {}

/// The intrusive type that you stuff into your node
pub struct Intrusive<T: Types + ?Sized> {
    pub(crate) lock: <T::Id as Id>::Atomic,
    // locked by the `lock` field
    pub(crate) next: UnsafeCell<Option<Pin<T::Pointer>>>,
}

impl<T: ?Sized + Types> fmt::Debug for Intrusive<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Intrusive")
            .field("id", &T::Id::read_relaxed(&self.lock))
            .finish()
    }
}

impl<T: Types + ?Sized> Intrusive<T> {
    /// Create a new node
    #[must_use]
    pub fn new() -> Self {
        Self {
            lock: T::Id::unset(),
            next: UnsafeCell::new(None),
        }
    }
}

impl<T: Types + ?Sized> Default for Intrusive<T> {
    fn default() -> Self {
        Self::new()
    }
}
impl<T: Types + ?Sized> Drop for PinQueue<T>
where
    T::Key: GetIntrusive<T>,
{
    fn drop(&mut self) {
        while self.pop_front().is_some() {}
    }
}

#[cfg(test)]
mod tests {
    use crate::{id, PinQueue};
    use core::fmt::Display;
    use core::pin::Pin;
    use std::sync::Arc;

    type MyTypes = dyn crate::Types<
        Id = id::Checked,
        Key = Key,
        Pointer = Arc<ThisIsAReallyLongTypeName<dyn Display>>,
    >;
    pin_project_lite::pin_project!(
        struct ThisIsAReallyLongTypeName<V: ?Sized> {
            #[pin]
            intrusive: crate::Intrusive<MyTypes>,
            value: V,
        }
    );
    impl<V> ThisIsAReallyLongTypeName<V> {
        pub fn new(value: V) -> Self {
            Self {
                intrusive: crate::Intrusive::new(),
                value,
            }
        }
    }
    struct Key;
    impl crate::GetIntrusive<MyTypes> for Key {
        fn get_intrusive(
            p: Pin<&ThisIsAReallyLongTypeName<dyn Display>>,
        ) -> Pin<&crate::Intrusive<MyTypes>> {
            p.project_ref().intrusive
        }
    }

    #[test]
    fn my_list() {
        let mut list = PinQueue::<MyTypes>::new(id::Checked::new());
        list.push_back(Arc::pin(ThisIsAReallyLongTypeName::new(1)))
            .unwrap();
        list.push_back(Arc::pin(ThisIsAReallyLongTypeName::new("hello")))
            .unwrap();

        let task1 = list.pop_front().unwrap();
        assert_eq!(task1.value.to_string(), "1");
        list.push_back(task1).unwrap();
        assert_eq!(list.pop_front().unwrap().value.to_string(), "hello");
        assert_eq!(list.pop_front().unwrap().value.to_string(), "1");
        assert!(list.pop_front().is_none());
    }

    #[test]
    fn my_list_push_back_error() {
        let mut list1 = PinQueue::<MyTypes>::new(id::Checked::new());
        let mut list2 = PinQueue::<MyTypes>::new(id::Checked::new());

        let val = Arc::pin(ThisIsAReallyLongTypeName::new(1));
        list1.push_back(val.clone()).unwrap();
        list2.push_back(val).unwrap_err();
    }

    #[test]
    fn my_list_push_back_same_error() {
        let mut list = PinQueue::<MyTypes>::new(id::Checked::new());

        let val = Arc::pin(ThisIsAReallyLongTypeName::new(1));
        list.push_back(val.clone()).unwrap();
        list.push_back(val).unwrap_err();
    }
}
