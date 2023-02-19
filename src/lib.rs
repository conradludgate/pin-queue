//! This crate provides [`PinQueue`], a safe `Pin`-based intrusive linked list for a FIFO queue.
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
use core::{cell::UnsafeCell, fmt, marker::PhantomData, ops::Deref, pin::Pin, ptr::NonNull};
use std::sync::Arc;

// use arc_dyn::{Core, ThinArc};
pub use id::Id;

mod util;

/// Types used in a [`PinQueue`]. This trait is used to avoid an excessive number of generic
/// parameters on [`PinQueue`] and related types.
pub trait Types: 'static {
    /// The ID type this list uses to ensure that different [`PinList`]s are not mixed up.
    ///
    /// This crate provides a couple built-in ID types, but you can also define your own:
    /// - [`id::Checked`]:
    ///     IDs are allocated with a single global atomic `u64` counter.
    /// - [`id::Unchecked`]:
    ///     The responsibility is left up to the user to ensure that different [`PinList`]s are not
    ///     incorrectly mixed up. Using this is `unsafe`.
    /// - [`id::DebugChecked`]:
    ///     Equivalent to [`id::Checked`] when `debug_assertions` are enabled, but
    ///     [`id::Unchecked`] in release.
    type Id: Id;

    /// The node stored in the [`PinQueue`]
    type Node: ?Sized;
}

/// Gets the intrusive component out of a node
pub trait GetIntrusive<T: ?Sized + Types> {
    /// From the pinned node, get the intrusive component
    fn get_intrusive(p: Pin<&T::Node>) -> Pin<&Intrusive<T>>;
}

/// An intrusive linked-list based FIFO queue
pub struct PinQueue<T: Types + ?Sized, P: Pointer<T>, K: GetIntrusive<T>> {
    id: T::Id,

    /// The head of the list.
    ///
    /// If this is `None`, the list is empty.
    head: Option<NonNull<T::Node>>,

    /// The tail of the list.
    ///
    /// Whether this is `None` must remain in sync with whether `head` is `None`.
    tail: Option<NonNull<T::Node>>,

    _pointer: PhantomData<P>,
    _key: PhantomData<K>,
}

impl<T: ?Sized + Types, P: Pointer<T>, K: GetIntrusive<T>> fmt::Debug for PinQueue<T, P, K> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PinQueue").field("id", &self.id).finish()
    }
}

/// `Pointer` trait represents types that act like owned pointers.
/// Eg [`Box`] or [`Arc`]
pub trait Pointer<T: ?Sized + Types>: Deref<Target = T::Node> + 'static {
    /// Turn this pointer into a raw pointer
    fn into_raw(self) -> *const T::Node;
    /// # Safety
    /// Must only be called **once** with the output of from [`into_raw`](Pointer::into_raw)
    unsafe fn from_raw(p: *const T::Node) -> Self;
}

impl<T: ?Sized + Types> Pointer<T> for Box<T::Node> {
    fn into_raw(self) -> *const T::Node {
        Box::into_raw(self)
    }

    unsafe fn from_raw(p: *const T::Node) -> Self {
        // SAFETY: guaranteed by caller
        unsafe { Box::from_raw(p as _) }
    }
}

impl<T: ?Sized + Types> Pointer<T> for Arc<T::Node> {
    fn into_raw(self) -> *const T::Node {
        Arc::into_raw(self)
    }

    unsafe fn from_raw(p: *const T::Node) -> Self {
        // SAFETY: guaranteed by caller
        unsafe { Arc::from_raw(p) }
    }
}

/// The error returned by [`PinQueue::push_back`] when the [`Node`] is already in a [`PinQueue`]
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
#[cfg(feature = "std")]
impl<P> std::error::Error for AlreadyInsertedError<P> {}

impl<T: ?Sized + Types, P, K> PinQueue<T, P, K>
where
    P: Pointer<T>,
    K: GetIntrusive<T>,
{
    /// Create a new empty `PinQueue` from a unique ID.
    pub fn new(id: id::Unique<T::Id>) -> Self {
        PinQueue {
            id: id.into_inner(),
            head: None,
            tail: None,
            _pointer: PhantomData,
            _key: PhantomData,
        }
    }

    /// Insert the node into the back of the queue.
    ///
    /// # Errors
    /// This will fail if the node is already inserted into another queue
    pub fn push_back(&mut self, node: Pin<P>) -> Result<(), AlreadyInsertedError<P>> {
        if !self.id.acquire(&K::get_intrusive(node.as_ref()).lock) {
            return Err(AlreadyInsertedError(node));
        };
        let node = unsafe { Pin::into_inner_unchecked(node) };
        let node = unsafe { NonNull::new_unchecked(node.into_raw() as *mut _) };
        if let Some(tail) = self.tail {
            unsafe {
                (*K::get_intrusive(Pin::new_unchecked(tail.as_ref()))
                    .pointers
                    .get())
                .next = Some(node);
            }
        }
        self.head = Some(self.head.unwrap_or(node));
        self.tail = Some(node);
        Ok(())
    }

    /// Take the first node from the queue
    pub fn pop_front(&mut self) -> Option<Pin<P>> {
        let node = self.head?;
        let node = unsafe { Pin::new_unchecked(P::from_raw(node.as_ptr())) };
        let intrusive = K::get_intrusive(node.as_ref());
        self.head = unsafe { (*intrusive.pointers.get()).next };
        debug_assert!(self.id.release(&intrusive.lock));
        Some(node)
    }
}

unsafe impl<T: ?Sized + Types> Send for Intrusive<T> where <T::Id as id::Id>::Atomic: Send {}

unsafe impl<T: ?Sized + Types> Sync for Intrusive<T> where
    // Required because it is owned by this type and will be dropped by it.
    <T::Id as id::Id>::Atomic: Sync
{
}

unsafe impl<T: ?Sized + Types, P: Pointer<T>, K: GetIntrusive<T>> Send for PinQueue<T, P, K>
where
    T::Id: Send,
    T::Node: Send + Sync,
    P: Send,
{
}

unsafe impl<T: ?Sized + Types, P: Pointer<T>, K: GetIntrusive<T>> Sync for PinQueue<T, P, K>
where
    T::Id: Sync,
    T::Node: Send + Sync,
    P: Sync,
{
}

/// The intrusive type that you stuff into your node
pub struct Intrusive<T: Types + ?Sized> {
    pub(crate) lock: <T::Id as id::Id>::Atomic,
    // locked by the `lock` field
    pub(crate) pointers: UnsafeCell<Pointers<T>>,
}

impl<T: ?Sized + Types> fmt::Debug for Intrusive<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Intrusive")
            .field("id", &<T::Id as id::Id>::read_relaxed(&self.lock))
            .finish()
    }
}

struct Pointers<T: Types + ?Sized> {
    /// The next node in the linked list.
    pub(crate) next: Option<NonNull<T::Node>>,
}

impl<T: Types + ?Sized> Intrusive<T> {
    /// Create a new node
    #[must_use]
    pub fn new() -> Self {
        Self {
            lock: <T::Id as id::Id>::unset(),
            pointers: UnsafeCell::new(Pointers { next: None }),
        }
    }
}

impl<T: Types + ?Sized> Default for Intrusive<T> {
    fn default() -> Self {
        Self::new()
    }
}

#[cfg(test)]
mod tests {
    use crate::{id, PinQueue};
    use core::fmt::Display;
    use core::pin::Pin;
    use std::sync::Arc;

    type MyTypes = dyn crate::Types<Id = id::Checked, Node = Node<dyn Display>>;
    pin_project_lite::pin_project!(
        struct Node<V: ?Sized> {
            #[pin]
            intrusive: crate::Intrusive<MyTypes>,
            value: V,
        }
    );
    impl<V> Node<V> {
        pub fn new(value: V) -> Self {
            Self {
                intrusive: crate::Intrusive::new(),
                value,
            }
        }
    }
    struct Key;
    impl crate::GetIntrusive<MyTypes> for Key {
        fn get_intrusive(p: Pin<&Node<dyn Display>>) -> Pin<&crate::Intrusive<MyTypes>> {
            p.project_ref().intrusive
        }
    }

    #[test]
    fn my_list() {
        let mut list = PinQueue::<MyTypes, Arc<_>, Key>::new(id::Checked::new());
        list.push_back(Arc::pin(Node::new(1))).unwrap();
        list.push_back(Arc::pin(Node::new("hello"))).unwrap();

        assert_eq!(list.pop_front().unwrap().value.to_string(), "1");
        assert_eq!(list.pop_front().unwrap().value.to_string(), "hello");
        assert!(list.pop_front().is_none());
    }

    #[test]
    fn my_list_push_back_error() {
        let mut list1 = PinQueue::<MyTypes, Arc<_>, Key>::new(id::Checked::new());
        let mut list2 = PinQueue::<MyTypes, Arc<_>, Key>::new(id::Checked::new());

        let val = Arc::pin(Node::new(1));
        list1.push_back(val.clone()).unwrap();
        list2.push_back(val).unwrap_err();
    }
}
