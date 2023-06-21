#![feature(negative_impls)]
#![feature(unsize)]
#![feature(const_trait_impl)]
#![feature(dispatch_from_dyn)]
#![feature(coerce_unsized)]
#![feature(slice_ptr_get)]
#![feature(ptr_as_uninit)]
#![feature(strict_provenance)]
#![feature(ptr_metadata)]
#![feature(const_mut_refs)]
#![feature(const_ptr_as_ref)]
#![feature(const_ptr_is_null)]
#![feature(const_try)]
#![feature(const_nonnull_new)]
#![feature(const_slice_from_raw_parts_mut)]

use std::{fmt, hash};
use std::cmp::Ordering;
use std::marker::Unsize;
use std::mem::MaybeUninit;
use std::num::NonZeroUsize;
use std::ops::{CoerceUnsized, DispatchFromDyn};
use std::ptr::NonNull;

pub mod additional;

pub type NonNullMut<T> = NonNull<T>;

#[repr(transparent)]
pub struct NonNullConst<T: ?Sized> {
    inner: NonNull<T>,
}
// from std:

// N.B., this impl is unnecessary, but should provide better error messages.
impl<T: ?Sized> ! Send for NonNullConst<T> {}

/// `NonNull` pointers are not `Sync` because the data they reference may be aliased.
// N.B., this impl is unnecessary, but should provide better error messages.
impl<T: ?Sized> ! Sync for NonNullConst<T> {}


impl<T: Sized> NonNullConst<T> {
    /// Creates a new `NonNullConst` that is dangling, but well-aligned.
    ///
    /// This is useful for initializing types which lazily allocate, like
    /// `Vec::new` does.
    ///
    /// Note that the pointer value may potentially represent a valid pointer to
    /// a `T`, which means this must not be used as a "not yet initialized"
    /// sentinel value. Types that lazily allocate must track initialization by
    /// some other means.
    ///
    /// # Examples
    ///
    /// ```
    /// use nonnull_const::NonNullConst;
    ///
    /// let ptr = NonNullConst::<u32>::dangling();
    /// // Important: don't try to access the value of `ptr` without
    /// // initializing it first! The pointer is not null but isn't valid either!
    /// ```
    #[must_use]
    #[inline]
    pub const fn dangling() -> Self {
        Self { inner: NonNull::dangling() }
    }

    /// Returns a shared references to the value. In contrast to [`as_ref`], this does not require
    /// that the value has to be initialized.
    ///
    /// For the mutable counterpart see [`as_uninit_mut`].
    ///
    /// [`as_ref`]: NonNullConst::as_ref
    /// [`as_uninit_mut`]: NonNullConst::as_uninit_mut
    ///
    /// # Safety
    ///
    /// When calling this method, you have to ensure that all of the following is true:
    ///
    /// * The pointer must be properly aligned.
    ///
    /// * It must be "dereferenceable" in the sense defined in [the module documentation].
    ///
    /// * You must enforce Rust's aliasing rules, since the returned lifetime `'a` is
    ///   arbitrarily chosen and does not necessarily reflect the actual lifetime of the data.
    ///   In particular, while this reference exists, the memory the pointer points to must
    ///   not get mutated (except inside `UnsafeCell`).
    ///
    /// This applies even if the result of this method is unused!
    ///
    /// [the module documentation]: crate::ptr#safety
    #[inline]
    #[must_use]
    pub const unsafe fn as_uninit_ref<'a>(self) -> &'a MaybeUninit<T> {
        self.inner.as_uninit_ref()
    }
}

impl<T: ?Sized> NonNullConst<T> {
    /// Creates a new `NonNullConst`.
    ///
    /// # Safety
    ///
    /// `ptr` must be non-null.
    ///
    /// # Examples
    ///
    /// ```
    /// use nonnull_const::NonNullConst;
    ///
    /// let mut x = 0u32;
    /// let ptr = unsafe { NonNullConst::new_unchecked(&mut x as *const _) };
    /// ```
    ///
    /// *Incorrect* usage of this function:
    ///
    /// ```rust,no_run
    /// use nonnull_const::NonNullConst;
    ///
    /// // NEVER DO THAT!!! This is undefined behavior. ⚠️
    /// let ptr = unsafe { NonNullConst::<u32>::new_unchecked(std::ptr::null()) };
    /// ```
    #[inline]
    pub const unsafe fn new_unchecked(ptr: *const T) -> Self {
        Self { inner: NonNull::new_unchecked(ptr as *mut T) }
    }

    /// Creates a new `NonNullConst` if `ptr` is non-null.
    ///
    /// # Examples
    ///
    /// ```
    /// use nonnull_const::NonNullConst;
    ///
    /// let mut x = 0u32;
    /// let ptr = NonNullConst::<u32>::new(&mut x as *mut _).expect("ptr is null!");
    ///
    /// if let Some(ptr) = NonNullConst::<u32>::new(std::ptr::null_mut()) {
    ///     unreachable!();
    /// }
    /// ```
    #[inline]
    pub fn new(ptr: *const T) -> Option<Self> {
        Some(NonNullConst { inner: NonNull::new(ptr as *mut T)? })
    }

    /// Performs the same functionality as [`std::ptr::from_raw_parts`], except that a
    /// `NonNullConst` pointer is returned, as opposed to a raw `*const` pointer.
    ///
    /// See the documentation of [`std::ptr::from_raw_parts`] for more details.
    ///
    /// [`std::ptr::from_raw_parts`]: crate::ptr::from_raw_parts
    #[inline]
    pub const fn from_raw_parts(
        data_address: NonNullConst<()>,
        metadata: <T as std::ptr::Pointee>::Metadata,
    ) -> NonNullConst<T> {
        NonNullConst { inner: NonNull::from_raw_parts(data_address.inner, metadata) }
    }

    /// Decompose a (possibly wide) pointer into its address and metadata components.
    ///
    /// The pointer can be later reconstructed with [`NonNullConst::from_raw_parts`].
    #[must_use = "this returns the result of the operation, \
                  without modifying the original"]
    #[inline]
    pub const fn to_raw_parts(self) -> (NonNullConst<()>, <T as std::ptr::Pointee>::Metadata) {
        let (nonnull, meta) = self.inner.to_raw_parts();
        (NonNullConst { inner: nonnull }, meta)
    }

    /// Gets the "address" portion of the pointer.
    ///
    /// For more details see the equivalent method on a raw pointer, [`pointer::addr`].
    ///
    /// This API and its claimed semantics are part of the Strict Provenance experiment,
    /// see the [`ptr` module documentation][crate::ptr].
    #[must_use]
    #[inline]
    pub fn addr(self) -> NonZeroUsize
        where
            T: Sized,
    {
        self.inner.addr()
    }

    /// Creates a new pointer with the given address.
    ///
    /// For more details see the equivalent method on a raw pointer, [`pointer::with_addr`].
    ///
    /// This API and its claimed semantics are part of the Strict Provenance experiment,
    /// see the [`ptr` module documentation][crate::ptr].
    #[must_use]
    #[inline]
    pub fn with_addr(self, addr: NonZeroUsize) -> Self
        where
            T: Sized,
    {
        Self { inner: NonNull::with_addr(self.inner, addr) }
    }

    /// Creates a new pointer by mapping `self`'s address to a new one.
    ///
    /// For more details see the equivalent method on a raw pointer, [`pointer::map_addr`].
    ///
    /// This API and its claimed semantics are part of the Strict Provenance experiment,
    /// see the [`ptr` module documentation][crate::ptr].
    #[must_use]
    #[inline]
    pub fn map_addr(self, f: impl FnOnce(NonZeroUsize) -> NonZeroUsize) -> Self
        where
            T: Sized,
    {
        self.with_addr(f(self.addr()))
    }

    /// Acquires the underlying `*const` pointer.
    ///
    /// # Examples
    ///
    /// ```
    /// use nonnull_const::NonNullConst;
    ///
    /// let mut x = 2u32;
    /// let ptr = NonNullConst::new(&mut x).expect("ptr is null!");
    ///
    /// let x_value = unsafe { *ptr.as_ptr() };
    /// assert_eq!(x_value, 2);
    /// ```
    #[must_use]
    #[inline]
    pub const fn as_ptr(self) -> *const T {
        self.inner.as_ptr() as *const T
    }

    /// Returns a shared reference to the value. If the value may be uninitialized, [`as_uninit_ref`]
    /// must be used instead.
    ///
    /// For the mutable counterpart see [`as_mut`].
    ///
    /// [`as_uninit_ref`]: NonNullConst::as_uninit_ref
    /// [`as_mut`]: NonNullConst::as_mut
    ///
    /// # Safety
    ///
    /// When calling this method, you have to ensure that all of the following is true:
    ///
    /// * The pointer must be properly aligned.
    ///
    /// * It must be "dereferenceable" in the sense defined in [the module documentation].
    ///
    /// * The pointer must point to an initialized instance of `T`.
    ///
    /// * You must enforce Rust's aliasing rules, since the returned lifetime `'a` is
    ///   arbitrarily chosen and does not necessarily reflect the actual lifetime of the data.
    ///   In particular, while this reference exists, the memory the pointer points to must
    ///   not get mutated (except inside `UnsafeCell`).
    ///
    /// This applies even if the result of this method is unused!
    /// (The part about being initialized is not yet fully decided, but until
    /// it is, the only safe approach is to ensure that they are indeed initialized.)
    ///
    /// # Examples
    ///
    /// ```
    /// use nonnull_const::NonNullConst;
    ///
    /// let mut x = 0u32;
    /// let ptr = NonNullConst::new(&mut x as *mut _).expect("ptr is null!");
    ///
    /// let ref_x = unsafe { ptr.as_ref() };
    /// println!("{ref_x}");
    /// ```
    ///
    /// [the module documentation]: crate::ptr#safety
    #[must_use]
    #[inline]
    pub const unsafe fn as_ref<'a>(&self) -> &'a T {
        self.inner.as_ref()
    }

    /// Casts to a pointer of another type.
    ///
    /// # Examples
    ///
    /// ```
    /// use nonnull_const::NonNullConst;
    ///
    /// let mut x = 0u32;
    /// let ptr = NonNullConst::new(&mut x as *mut _).expect("null pointer");
    ///
    /// let casted_ptr = ptr.cast::<i8>();
    /// let raw_ptr: *const i8 = casted_ptr.as_ptr();
    /// ```
    #[must_use = "this returns the result of the operation, \
                  without modifying the original"]
    #[inline]
    pub const fn cast<U>(self) -> NonNullConst<U> {
        NonNullConst { inner: self.inner.cast() }
    }
}

impl<T> NonNullConst<[T]> {
    /// Creates a non-null raw slice from a thin pointer and a length.
    ///
    /// The `len` argument is the number of **elements**, not the number of bytes.
    ///
    /// This function is safe, but dereferencing the return value is unsafe.
    /// See the documentation of [`slice::from_raw_parts`] for slice safety requirements.
    ///
    /// # Examples
    ///
    /// ```rust
    /// #![feature(nonnull_slice_from_raw_parts)]
    ///
    /// use nonnull_const::NonNullConst;
    ///
    /// // create a slice pointer when starting out with a pointer to the first element
    /// let mut x = [5, 6, 7];
    /// let nonnull_pointer = NonNullConst::new(x.as_mut_ptr()).unwrap();
    /// let slice = NonNullConst::slice_from_raw_parts(nonnull_pointer, 3);
    /// assert_eq!(unsafe { slice.as_ref()[2] }, 7);
    /// ```
    ///
    /// (Note that this example artificially demonstrates a use of this method,
    /// but `let slice = NonNullConst::from(&x[..]);` would be a better way to write code like this.)
    #[must_use]
    #[inline]
    pub const fn slice_from_raw_parts(data: NonNullConst<T>, len: usize) -> Self {
        NonNullConst { inner: NonNull::slice_from_raw_parts(data.inner, len) }
    }

    /// Returns the length of a non-null raw slice.
    ///
    /// The returned value is the number of **elements**, not the number of bytes.
    ///
    /// This function is safe, even when the non-null raw slice cannot be dereferenced to a slice
    /// because the pointer does not have a valid address.
    ///
    /// # Examples
    ///
    /// ```rust
    /// #![feature(nonnull_slice_from_raw_parts)]
    /// use nonnull_const::NonNullConst;
    ///
    /// let slice: NonNullConst<[i8]> = NonNullConst::slice_from_raw_parts(NonNullConst::dangling(), 3);
    /// assert_eq!(slice.len(), 3);
    /// ```
    #[must_use]
    #[inline]
    pub const fn len(self) -> usize {
        self.inner.len()
    }

    /// Returns a non-null pointer to the slice's buffer.
    ///
    /// # Examples
    ///
    /// ```rust
    /// #![feature(slice_ptr_get, nonnull_slice_from_raw_parts)]
    /// use nonnull_const::NonNullConst;
    ///
    /// let slice: NonNullConst<[i8]> = NonNullConst::slice_from_raw_parts(NonNullConst::dangling(), 3);
    /// assert_eq!(slice.as_non_null_ptr(), NonNullConst::<i8>::dangling());
    /// ```
    #[inline]
    #[must_use]
    pub const fn as_non_null_ptr(self) -> NonNullConst<T> {
        NonNullConst { inner: self.inner.as_non_null_ptr() }
    }

    /// Returns a shared reference to a slice of possibly uninitialized values. In contrast to
    /// [`as_ref`], this does not require that the value has to be initialized.
    ///
    /// For the mutable counterpart see [`as_uninit_slice_mut`].
    ///
    /// [`as_ref`]: NonNullConst::as_ref
    /// [`as_uninit_slice_mut`]: NonNullConst::as_uninit_slice_mut
    ///
    /// # Safety
    ///
    /// When calling this method, you have to ensure that all of the following is true:
    ///
    /// * The pointer must be [valid] for reads for `ptr.len() * mem::size_of::<T>()` many bytes,
    ///   and it must be properly aligned. This means in particular:
    ///
    ///     * The entire memory range of this slice must be contained within a single allocated object!
    ///       Slices can never span across multiple allocated objects.
    ///
    ///     * The pointer must be aligned even for zero-length slices. One
    ///       reason for this is that enum layout optimizations may rely on references
    ///       (including slices of any length) being aligned and non-null to distinguish
    ///       them from other data. You can obtain a pointer that is usable as `data`
    ///       for zero-length slices using [`NonNullConst::dangling()`].
    ///
    /// * The total size `ptr.len() * mem::size_of::<T>()` of the slice must be no larger than `isize::MAX`.
    ///   See the safety documentation of [`pointer::offset`].
    ///
    /// * You must enforce Rust's aliasing rules, since the returned lifetime `'a` is
    ///   arbitrarily chosen and does not necessarily reflect the actual lifetime of the data.
    ///   In particular, while this reference exists, the memory the pointer points to must
    ///   not get mutated (except inside `UnsafeCell`).
    ///
    /// This applies even if the result of this method is unused!
    ///
    /// See also [`slice::from_raw_parts`].
    ///
    /// [valid]: crate::ptr#safety
    #[inline]
    #[must_use]
    pub const unsafe fn as_uninit_slice<'a>(self) -> &'a [MaybeUninit<T>] {
        // SAFETY: the caller must uphold the safety contract for `as_uninit_slice`.
        self.inner.as_uninit_slice()
    }
}

impl<T: ?Sized> Clone for NonNullConst<T> {
    #[inline]
    fn clone(&self) -> Self {
        NonNullConst { inner: self.inner.clone() }
    }
}

impl<T: ?Sized> Copy for NonNullConst<T> {}

impl<T: ?Sized, U: ?Sized> CoerceUnsized<NonNullConst<U>> for NonNullConst<T> where T: Unsize<U> {}

impl<T: ?Sized, U: ?Sized> DispatchFromDyn<NonNullConst<U>> for NonNullConst<T> where T: Unsize<U> {}

impl<T: ?Sized> fmt::Debug for NonNullConst<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.inner.as_ptr(), f)
    }
}

impl<T: ?Sized> fmt::Pointer for NonNullConst<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.inner.as_ptr(), f)
    }
}

impl<T: ?Sized> Eq for NonNullConst<T> {}

impl<T: ?Sized> PartialEq for NonNullConst<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.inner.as_ptr() == other.inner.as_ptr()
    }
}

impl<T: ?Sized> Ord for NonNullConst<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.inner.as_ptr().cmp(&other.inner.as_ptr())
    }
}

impl<T: ?Sized> PartialOrd for NonNullConst<T> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.inner.as_ptr().partial_cmp(&other.inner.as_ptr())
    }
}

impl<T: ?Sized> hash::Hash for NonNullConst<T> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.inner.as_ptr().hash(state)
    }
}

impl<T: ?Sized> From<&mut T> for NonNullConst<T> {
    /// Converts a `&mut T` to a `NonNullConst<T>`.
    ///
    /// This conversion is safe and infallible since references cannot be null.
    #[inline]
    fn from(reference: &mut T) -> Self {
        NonNullConst { inner: NonNull::from(reference) }
    }
}

impl<T: ?Sized> From<&T> for NonNullConst<T> {
    /// Converts a `&T` to a `NonNullConst<T>`.
    ///
    /// This conversion is safe and infallible since references cannot be null.
    #[inline]
    fn from(reference: &T) -> Self {
        NonNullConst { inner: NonNull::from(reference) }
    }
}
