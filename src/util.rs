//! Shared internal utilities.

use core::mem::ManuallyDrop;

pub(crate) fn run_on_drop<F: FnOnce()>(f: F) -> impl Drop {
    RunOnDrop(ManuallyDrop::new(f))
}

struct RunOnDrop<F: FnOnce()>(ManuallyDrop<F>);
impl<F: FnOnce()> Drop for RunOnDrop<F> {
    fn drop(&mut self) {
        (unsafe { ManuallyDrop::take(&mut self.0) })();
    }
}

#[cold]
pub(crate) fn abort() -> ! {
    // When `std` is not available, a double-panic will turn into an abort. Don’t use it always
    // though because it has worse codegen than a plain abort.
    #[cfg(not(feature = "std"))]
    {
        let _guard = run_on_drop(|| panic!());
        panic!();
    }
    #[cfg(feature = "std")]
    std::process::abort();
}

/// A public but not exposed helper trait used to work around the lack of trait bounds in `const
/// fn`s on this crate's MSRV. Instead of writing `T: Bound` which doesn't work, one can write
/// `<T as ConstFnBounds>::Type: Bound` which does work (it was originally an oversight that this
/// was allowed, but in later versions it was stabilized so it's fine to rely on it now).
pub trait ConstFnBounds {
    type Type: ?Sized;
}
impl<T: ?Sized> ConstFnBounds for T {
    type Type = T;
}
