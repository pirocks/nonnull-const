use std::ptr::NonNull;

use crate::NonNullConst;

impl<T: ?Sized> From<NonNull<T>> for NonNullConst<T> {
    fn from(nonnull: NonNull<T>) -> Self {
        Self {
            inner: nonnull
        }
    }
}
