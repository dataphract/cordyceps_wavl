use core::ptr::{self, NonNull};

use sptr::Strict;

pub(crate) struct RankPtr<T> {
    ptr: *mut T,
}

impl<T> RankPtr<T> {
    pub(crate) fn new(ptr: Option<NonNull<T>>, parity: bool) -> RankPtr<T> {
        let ptr = opt_nonnull_to_raw(ptr);

        assert!(ptr.addr() % 2 == 0);

        RankPtr {
            ptr: ptr.map_addr(|addr| addr | parity as usize),
        }
    }

    pub(crate) fn ptr(&self) -> Option<NonNull<T>> {
        NonNull::new(self.ptr.map_addr(|tagged_addr| tagged_addr & !1_usize))
    }

    pub(crate) fn parity(&self) -> bool {
        self.ptr.addr() & 1 != 0
    }

    pub(crate) fn set_ptr(&mut self, ptr: Option<NonNull<T>>) {
        *self = RankPtr::new(ptr, self.parity());
    }

    pub(crate) fn set_parity(&mut self, parity: bool) {
        *self = RankPtr::new(self.ptr(), parity);
    }

    #[inline]
    pub(crate) fn promote(&mut self) {
        self.ptr = self.ptr.map_addr(|tagged_addr| tagged_addr ^ 1);
    }

    #[inline]
    pub(crate) fn promote_twice(&mut self) {}

    #[inline]
    pub(crate) fn demote(&mut self) {
        self.ptr = self.ptr.map_addr(|tagged_addr| tagged_addr ^ 1);
    }

    #[inline]
    pub(crate) fn demote_twice(&mut self) {}
}

fn opt_nonnull_to_raw<T>(ptr: Option<NonNull<T>>) -> *mut T {
    match ptr {
        Some(p) => p.as_ptr(),
        None => ptr::null_mut(),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rank_ptr() {
        let ptr: NonNull<u32> = NonNull::dangling();

        let tagged_0 = RankPtr::new(Some(ptr), false);
        assert!(!tagged_0.parity());

        let tagged_1 = RankPtr::new(Some(ptr), true);
        assert!(tagged_1.parity());

        assert_eq!(tagged_0.ptr(), Some(ptr));
        assert_eq!(tagged_0.ptr(), tagged_1.ptr());
    }
}
