//! This crate provides [`PinQueue`], a safe `Pin`-based intrusive linked list for a FIFO queue.
//!
//! # Example
//!
//! A thread-safe future queue.
//!
//! ```
//! use std::cell::UnsafeCell;
//! use std::future::Future;
//! use std::ops::Deref;
//! use std::ops::DerefMut;
//! use std::pin::Pin;
//! use std::task;
//! use std::task::Poll;
//! use std::sync::{Mutex, Arc};
//! use once_cell::sync::Lazy;
//!
//! // aliases
//! type PinQueueTypes = dyn pin_queue::Types<
//!     Id = pin_queue::id::Checked,
//!     Value = Mutex<dyn Future<Output = usize>>,
//! >;
//! type PinQueue = pin_queue::PinQueue<PinQueueTypes, Arc<_>>;
//! type Node<V = PinQueueTypes::Value> = pin_queue::Node<PinQueueTypes, V>;
//!
//! // global queue
//! static QUEUE: Lazy<Mutex<PinQueue>> = Lazy::new(|| {
//!     Mutex::new(PinQueue::new(pin_queue::id::Checked::new()))
//! });
//!
//! // spawn()
//! let task1 = Arc::new(Node::new(Mutex::new(async { 1 })));
//! QUEUE.lock().unwrap().push_back(task1);
//!
//! let task2 = Arc::new(Node::new(Mutex::new(async { 2 })));
//! QUEUE.lock().unwrap().push_back(task2);
//!
//! // worker
//! while let Some(task) = QUEUE.lock().unwrap().pop_front() {
//!     let waker = TaskWaker(task.clone());
//! }
//!
//! // waker
//! pub struct TaskWaker(Arc<Node>)
//!
//! pub struct Mutex<T> {
//!     data: UnsafeCell<T>,
//!     inner: std::sync::Mutex<Inner>,
//! }
//!
//! struct Inner {
//!     locked: bool,
//!     waiters: PinList<PinListTypes>,
//! }
//!
//! unsafe impl<T> Sync for Mutex<T> {}
//!
//! impl<T> Mutex<T> {
//!     pub fn new(data: T) -> Self {
//!         Self {
//!             data: UnsafeCell::new(data),
//!             inner: std::sync::Mutex::new(Inner {
//!                 locked: false,
//!                 waiters: PinList::new(unsized_pin_list::id::Checked::new()),
//!             }),
//!         }
//!     }
//!     pub fn lock(&self) -> Lock<'_, T> {
//!         Lock {
//!             mutex: self,
//!             node: unsized_pin_list::Node::new(),
//!         }
//!     }
//! }
//!
//! pin_project! {
//!     pub struct Lock<'mutex, T> {
//!         mutex: &'mutex Mutex<T>,
//!         #[pin]
//!         node: unsized_pin_list::Node<PinListTypes, [(); 0]>,
//!     }
//!
//!     impl<T> PinnedDrop for Lock<'_, T> {
//!         fn drop(this: Pin<&mut Self>) {
//!             let this = this.project();
//!             let node = match this.node.initialized_mut() {
//!                 // The future was cancelled before it could complete.
//!                 Some(initialized) => initialized,
//!                 // The future has completed already (or hasn't started); we don't have to do
//!                 // anything.
//!                 None => return,
//!             };
//!
//!             let mut inner = this.mutex.inner.lock().unwrap();
//!
//!             match node.reset(&mut inner.waiters) {
//!                 // If we've cancelled the future like usual, just do that.
//!                 (unsized_pin_list::NodeData::Linked(_waker), []) => {}
//!
//!                 // Otherwise, we have been woken but aren't around to take the lock. To
//!                 // prevent deadlocks, pass the notification on to someone else.
//!                 (unsized_pin_list::NodeData::Removed(()), []) => {
//!                     if let Ok(waker) = inner.waiters.cursor_front_mut().remove_current(()) {
//!                         drop(inner);
//!                         waker.wake();
//!                     }
//!                 }
//!             }
//!         }
//!     }
//! }
//!
//! impl<'mutex, T> Future for Lock<'mutex, T> {
//!     type Output = Guard<'mutex, T>;
//!     fn poll(self: Pin<&mut Self>, cx: &mut task::Context<'_>) -> Poll<Self::Output> {
//!         let mut this = self.project();
//!
//!         let mut inner = this.mutex.inner.lock().unwrap();
//!
//!         if let Some(mut node) = this.node.as_mut().initialized_mut() {
//!             // Check whether we've been woken up, only continuing if so.
//!             if let Err(node) = node.take_removed(&inner.waiters) {
//!                 // If we haven't been woken, re-register our waker and pend.
//!                 *node.protected_mut(&mut inner.waiters).unwrap() = cx.waker().clone();
//!                 return Poll::Pending;
//!             }
//!         }
//!
//!         // If the mutex is unlocked, mark it as locked and return the guard
//!         if !inner.locked {
//!             inner.locked = true;
//!             return Poll::Ready(Guard { mutex: this.mutex });
//!         }
//!
//!         // Otherwise, re-register ourselves to be woken when the mutex is unlocked again
//!         inner.waiters.push_back(this.node, cx.waker().clone(), []);
//!
//!         Poll::Pending
//!     }
//! }
//!
//! pub struct Guard<'mutex, T> {
//!     mutex: &'mutex Mutex<T>,
//! }
//!
//! impl<T> Deref for Guard<'_, T> {
//!     type Target = T;
//!     fn deref(&self) -> &Self::Target {
//!         unsafe { &*self.mutex.data.get() }
//!     }
//! }
//! impl<T> DerefMut for Guard<'_, T> {
//!     fn deref_mut(&mut self) -> &mut Self::Target {
//!         unsafe { &mut *self.mutex.data.get() }
//!     }
//! }
//!
//! impl<T> Drop for Guard<'_, T> {
//!     fn drop(&mut self) {
//!         let mut inner = self.mutex.inner.lock().unwrap();
//!         inner.locked = false;
//!
//!         if let Ok(waker) = inner.waiters.cursor_front_mut().remove_current(()) {
//!             drop(inner);
//!             waker.wake();
//!         }
//!     }
//! }
//! #
//! # fn assert_send<T: Send>(_: T) {}
//! # let mutex = Mutex::new(());
//! # assert_send(mutex.lock());
//! ```
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
#![no_std]

#[cfg(feature = "alloc")]
extern crate alloc;

#[cfg(feature = "std")]
extern crate std;

pub mod id;
use core::{
    cell::UnsafeCell,
    fmt,
    marker::PhantomData,
    ops::{Deref, DerefMut},
    pin::Pin,
    ptr::NonNull,
};

pub use id::Id;

mod util;

/// Types used in a [`PinQueue`]. This trait is used to avoid an excessive number of generic
/// parameters on [`PinQueue`] and related types.
///
/// Generally you won't want to implement this trait directly — instead you can create ad-hoc
/// implementations by using `dyn Trait` syntax, for example:
///
/// ```
/// use std::sync::Arc;
/// type PinQueueTypes = dyn pin_queue::Types<
///     Id = pin_queue::id::Checked,
///     Value = (),
/// >;
/// type PinList = unsized_pin_list::PinList<PinQueueTypes, Arc<_>>;
/// ```
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

    /// The value stored in the [`PinQueue`]. Can be a dynamically sized type (eg `dyn Future<Output = ()>`)
    type Value: ?Sized + 'static;
}

/// An intrusive linked-list based FIFO queue
pub struct PinQueue<T: Types + ?Sized, P: Pointer<T>> {
    id: T::Id,

    /// The head of the list.
    ///
    /// If this is `None`, the list is empty.
    head: Option<NonNull<Node<T>>>,

    /// The tail of the list.
    ///
    /// Whether this is `None` must remain in sync with whether `head` is `None`.
    tail: Option<NonNull<Node<T>>>,

    _pointer: PhantomData<P>,
}

impl<T: ?Sized + Types, P: Pointer<T>> fmt::Debug for PinQueue<T, P> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("PinQueue").field("id", &self.id).finish()
    }
}

/// `Pointer` trait represents types that act like owned pointers.
/// Eg [`Box`](alloc::boxed::Box) or [`Arc`](alloc::sync::Arc).
pub trait Pointer<T: ?Sized + Types>: Deref<Target = Node<T>> + 'static {
    /// Turn this pointer into a raw pointer
    fn into_raw(self) -> *const Node<T>;
    /// # Safety
    /// Must only be called **once** with the output of from [`into_raw`](Pointer::into_raw)
    unsafe fn from_raw(p: *const Node<T>) -> Self;
}

#[cfg(feature = "alloc")]
impl<T: ?Sized + Types> Pointer<T> for alloc::boxed::Box<Node<T>> {
    fn into_raw(self) -> *const Node<T> {
        alloc::boxed::Box::into_raw(self)
    }

    unsafe fn from_raw(p: *const Node<T>) -> Self {
        // SAFETY: guaranteed by caller
        unsafe { alloc::boxed::Box::from_raw(p as _) }
    }
}

#[cfg(feature = "alloc")]
impl<T: ?Sized + Types> Pointer<T> for alloc::sync::Arc<Node<T>> {
    fn into_raw(self) -> *const Node<T> {
        alloc::sync::Arc::into_raw(self)
    }

    unsafe fn from_raw(p: *const Node<T>) -> Self {
        // SAFETY: guaranteed by caller
        unsafe { alloc::sync::Arc::from_raw(p) }
    }
}

#[derive(Debug)]
/// The error returned by [`PinQueue::push_back`] when the [`Node`] is already in a [`PinQueue`]
pub struct AlreadyInsertedError<P>(pub Pin<P>);

impl<T: ?Sized + Types, P> PinQueue<T, P>
where
    P: Pointer<T>,
{
    /// Create a new empty `PinQueue` from a unique ID.
    pub fn new(id: id::Unique<T::Id>) -> Self {
        PinQueue {
            id: id.into_inner(),
            head: None,
            tail: None,
            _pointer: PhantomData,
        }
    }

    /// Insert the node into the back of the queue.
    ///
    /// # Errors
    /// This will fail if the node is already inserted into another queue
    pub fn push_back(&mut self, node: Pin<P>) -> Result<(), AlreadyInsertedError<P>> {
        if !self.id.acquire(&node.intrusive.lock) {
            return Err(AlreadyInsertedError(node));
        };
        let node = unsafe { Pin::into_inner_unchecked(node) };
        let node = unsafe { NonNull::new_unchecked(node.into_raw() as *mut _) };
        if let Some(tail) = self.tail {
            unsafe { (*tail.as_ref().intrusive.pointers.get()).next = Some(node) }
        }
        self.head = Some(self.head.unwrap_or(node));
        self.tail = Some(node);
        Ok(())
    }

    /// Take the first node from the queue
    pub fn pop_front(&mut self) -> Option<Pin<P>> {
        let node = self.head?;
        self.head = unsafe { (*node.as_ref().intrusive.pointers.get()).next };
        debug_assert!(self.id.release(unsafe { &node.as_ref().intrusive.lock }));
        unsafe { Some(Pin::new_unchecked(P::from_raw(node.as_ptr()))) }
    }
}

/// A node that can be inserted into a [`PinQueue`]
pub struct Node<T: Types + ?Sized, V: ?Sized = <T as Types>::Value> {
    pub(crate) intrusive: Intrusive<T>,
    pub(crate) value: V,
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
    // /// The previous node in the linked list.
    // pub(crate) prev: Option<NonNull<MyNode<T>>>,
    /// The next node in the linked list.
    pub(crate) next: Option<NonNull<Node<T>>>,
}

impl<T: Types + ?Sized, V: ?Sized> Deref for Node<T, V> {
    type Target = V;

    fn deref(&self) -> &Self::Target {
        &self.value
    }
}

impl<T: Types + ?Sized, V: ?Sized> DerefMut for Node<T, V> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.value
    }
}

impl<T: Types + ?Sized, V> Node<T, V> {
    /// Create a new node
    pub fn new(value: V) -> Self {
        Self {
            lock: <T::Id as id::Id>::unset(),
            pointers: UnsafeCell::new(Pointers {
                // prev: None,
                next: None,
            }),
            value,
        }
    }
    /// Take the value from this node
    pub fn into_inner(self) -> V {
        self.value
    }
}

#[cfg(all(test, feature = "std"))]
mod tests {
    use crate::{id, Node, PinQueue};
    use alloc::string::ToString;
    use alloc::sync::Arc;
    use core::fmt::Display;

    type MyTypes = dyn crate::Types<Id = id::Checked, Value = dyn Display>;

    #[test]
    fn my_list() {
        let mut list = PinQueue::<MyTypes, Arc<_>>::new(id::Checked::new());
        list.push_back(Arc::pin(Node::new(1))).unwrap();
        list.push_back(Arc::pin(Node::new("hello"))).unwrap();

        assert_eq!(list.pop_front().unwrap().to_string(), "1");
        assert_eq!(list.pop_front().unwrap().to_string(), "hello");
        assert!(list.pop_front().is_none());
    }

    #[test]
    fn my_list_push_back_error() {
        let mut list1 = PinQueue::<MyTypes, Arc<_>>::new(id::Checked::new());
        let mut list2 = PinQueue::<MyTypes, Arc<_>>::new(id::Checked::new());

        let val = Arc::pin(Node::new(1));
        list1.push_back(val.clone()).unwrap();
        list2.push_back(val).unwrap_err();
    }
}
