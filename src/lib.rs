#![feature(negative_impls)]
#![feature(unsize)]
#![feature(const_trait_impl)]
#![feature(dispatch_from_dyn)]
#![feature(coerce_unsized)]

use std::cmp::Ordering;
use std::{fmt, hash};
use std::marker::Unsize;
use std::mem::MaybeUninit;
use std::num::NonZeroUsize;
use std::ops::{CoerceUnsized, DispatchFromDyn};
use std::ptr::{NonNull};
use std::slice::SliceIndex;

pub type NonNullMut<T> = NonNull<T>;

#[repr(transparent)]
pub struct NonNullConst<T> {
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
    /// use std::ptr::NonNullConst;
    ///
    /// let ptr = NonNullConst::<u32>::dangling();
    /// // Important: don't try to access the value of `ptr` without
    /// // initializing it first! The pointer is not null but isn't valid either!
    /// ```
    #[must_use]
    #[inline]
    pub const fn dangling() -> Self {
        // SAFETY: mem::align_of() returns a non-zero usize which is then casted
        // to a *mut T. Therefore, `ptr` is not null and the conditions for
        // calling new_unchecked() are respected.
        unsafe {
            let ptr = crate::ptr::invalid_mut::<T>(mem::align_of::<T>());
            NonNullConst::new_unchecked(ptr)
        }
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
        // SAFETY: the caller must guarantee that `self` meets all the
        // requirements for a reference.
        unsafe { &*self.cast().as_ptr() }
    }

    /// Returns a unique references to the value. In contrast to [`as_mut`], this does not require
    /// that the value has to be initialized.
    ///
    /// For the shared counterpart see [`as_uninit_ref`].
    ///
    /// [`as_mut`]: NonNullConst::as_mut
    /// [`as_uninit_ref`]: NonNullConst::as_uninit_ref
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
    ///   not get accessed (read or written) through any other pointer.
    ///
    /// This applies even if the result of this method is unused!
    ///
    /// [the module documentation]: crate::ptr#safety
    #[inline]
    #[must_use]
    pub const unsafe fn as_uninit_mut<'a>(self) -> &'a mut MaybeUninit<T> {
        // SAFETY: the caller must guarantee that `self` meets all the
        // requirements for a reference.
        unsafe { &mut *self.cast().as_ptr() }
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
    /// use std::ptr::NonNullConst;
    ///
    /// let mut x = 0u32;
    /// let ptr = unsafe { NonNullConst::new_unchecked(&mut x as *mut _) };
    /// ```
    ///
    /// *Incorrect* usage of this function:
    ///
    /// ```rust,no_run
    /// use std::ptr::NonNullConst;
    ///
    /// // NEVER DO THAT!!! This is undefined behavior. ⚠️
    /// let ptr = unsafe { NonNullConst::<u32>::new_unchecked(std::ptr::null_mut()) };
    /// ```
    #[inline]
    pub const unsafe fn new_unchecked(ptr: *mut T) -> Self {
        // SAFETY: the caller must guarantee that `ptr` is non-null.
        unsafe { NonNullConst { pointer: ptr as _ } }
    }

    /// Creates a new `NonNullConst` if `ptr` is non-null.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::ptr::NonNullConst;
    ///
    /// let mut x = 0u32;
    /// let ptr = NonNullConst::<u32>::new(&mut x as *mut _).expect("ptr is null!");
    ///
    /// if let Some(ptr) = NonNullConst::<u32>::new(std::ptr::null_mut()) {
    ///     unreachable!();
    /// }
    /// ```
    #[inline]
    pub const fn new(ptr: *mut T) -> Option<Self> {
        if !ptr.is_null() {
            // SAFETY: The pointer is already checked and is not null
            Some(unsafe { Self::new_unchecked(ptr) })
        } else {
            None
        }
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
        metadata: <T as super::Pointee>::Metadata,
    ) -> NonNullConst<T> {
        // SAFETY: The result of `ptr::from::raw_parts_mut` is non-null because `data_address` is.
        unsafe {
            NonNullConst::new_unchecked(super::from_raw_parts_mut(data_address.as_ptr(), metadata))
        }
    }

    /// Decompose a (possibly wide) pointer into its address and metadata components.
    ///
    /// The pointer can be later reconstructed with [`NonNullConst::from_raw_parts`].
    #[must_use = "this returns the result of the operation, \
                  without modifying the original"]
    #[inline]
    pub const fn to_raw_parts(self) -> (NonNullConst<()>, <T as super::Pointee>::Metadata) {
        (self.cast(), super::metadata(self.as_ptr()))
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
        // SAFETY: The pointer is guaranteed by the type to be non-null,
        // meaning that the address will be non-zero.
        unsafe { NonZeroUsize::new_unchecked(self.pointer.addr()) }
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
        // SAFETY: The result of `ptr::from::with_addr` is non-null because `addr` is guaranteed to be non-zero.
        unsafe { NonNullConst::new_unchecked(self.pointer.with_addr(addr.get()) as *mut _) }
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

    /// Acquires the underlying `*mut` pointer.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::ptr::NonNullConst;
    ///
    /// let mut x = 0u32;
    /// let ptr = NonNullConst::new(&mut x).expect("ptr is null!");
    ///
    /// let x_value = unsafe { *ptr.as_ptr() };
    /// assert_eq!(x_value, 0);
    ///
    /// unsafe { *ptr.as_ptr() += 2; }
    /// let x_value = unsafe { *ptr.as_ptr() };
    /// assert_eq!(x_value, 2);
    /// ```
    #[must_use]
    #[inline]
    pub const fn as_ptr(self) -> *mut T {
        self.pointer as *mut T
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
    /// use std::ptr::NonNullConst;
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
        // SAFETY: the caller must guarantee that `self` meets all the
        // requirements for a reference.
        unsafe { &*self.as_ptr() }
    }

    /// Returns a unique reference to the value. If the value may be uninitialized, [`as_uninit_mut`]
    /// must be used instead.
    ///
    /// For the shared counterpart see [`as_ref`].
    ///
    /// [`as_uninit_mut`]: NonNullConst::as_uninit_mut
    /// [`as_ref`]: NonNullConst::as_ref
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
    ///   not get accessed (read or written) through any other pointer.
    ///
    /// This applies even if the result of this method is unused!
    /// (The part about being initialized is not yet fully decided, but until
    /// it is, the only safe approach is to ensure that they are indeed initialized.)
    /// # Examples
    ///
    /// ```
    /// use std::ptr::NonNullConst;
    ///
    /// let mut x = 0u32;
    /// let mut ptr = NonNullConst::new(&mut x).expect("null pointer");
    ///
    /// let x_ref = unsafe { ptr.as_mut() };
    /// assert_eq!(*x_ref, 0);
    /// *x_ref += 2;
    /// assert_eq!(*x_ref, 2);
    /// ```
    ///
    /// [the module documentation]: crate::ptr#safety
    #[must_use]
    #[inline]
    pub const unsafe fn as_mut<'a>(&mut self) -> &'a mut T {
        // SAFETY: the caller must guarantee that `self` meets all the
        // requirements for a mutable reference.
        unsafe { &mut *self.as_ptr() }
    }

    /// Casts to a pointer of another type.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::ptr::NonNullConst;
    ///
    /// let mut x = 0u32;
    /// let ptr = NonNullConst::new(&mut x as *mut _).expect("null pointer");
    ///
    /// let casted_ptr = ptr.cast::<i8>();
    /// let raw_ptr: *mut i8 = casted_ptr.as_ptr();
    /// ```
    #[must_use = "this returns the result of the operation, \
                  without modifying the original"]
    #[inline]
    pub const fn cast<U>(self) -> NonNullConst<U> {
        // SAFETY: `self` is a `NonNullConst` pointer which is necessarily non-null
        unsafe { NonNullConst::new_unchecked(self.as_ptr() as *mut U) }
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
    /// use std::ptr::NonNullConst;
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
        // SAFETY: `data` is a `NonNullConst` pointer which is necessarily non-null
        unsafe { Self::new_unchecked(super::slice_from_raw_parts_mut(data.as_ptr(), len)) }
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
    /// use std::ptr::NonNullConst;
    ///
    /// let slice: NonNullConst<[i8]> = NonNullConst::slice_from_raw_parts(NonNullConst::dangling(), 3);
    /// assert_eq!(slice.len(), 3);
    /// ```
    #[must_use]
    #[inline]
    pub const fn len(self) -> usize {
        self.as_ptr().len()
    }

    /// Returns a non-null pointer to the slice's buffer.
    ///
    /// # Examples
    ///
    /// ```rust
    /// #![feature(slice_ptr_get, nonnull_slice_from_raw_parts)]
    /// use std::ptr::NonNullConst;
    ///
    /// let slice: NonNullConst<[i8]> = NonNullConst::slice_from_raw_parts(NonNullConst::dangling(), 3);
    /// assert_eq!(slice.as_non_null_ptr(), NonNullConst::<i8>::dangling());
    /// ```
    #[inline]
    #[must_use]
    pub const fn as_non_null_ptr(self) -> NonNullConst<T> {
        // SAFETY: We know `self` is non-null.
        unsafe { NonNullConst::new_unchecked(self.as_ptr().as_mut_ptr()) }
    }

    /// Returns a raw pointer to the slice's buffer.
    ///
    /// # Examples
    ///
    /// ```rust
    /// #![feature(slice_ptr_get, nonnull_slice_from_raw_parts)]
    /// use std::ptr::NonNullConst;
    ///
    /// let slice: NonNullConst<[i8]> = NonNullConst::slice_from_raw_parts(NonNullConst::dangling(), 3);
    /// assert_eq!(slice.as_mut_ptr(), NonNullConst::<i8>::dangling().as_ptr());
    /// ```
    #[inline]
    #[must_use]
    pub const fn as_mut_ptr(self) -> *mut T {
        self.as_non_null_ptr().as_ptr()
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
        unsafe { slice::from_raw_parts(self.cast().as_ptr(), self.len()) }
    }

    /// Returns a unique reference to a slice of possibly uninitialized values. In contrast to
    /// [`as_mut`], this does not require that the value has to be initialized.
    ///
    /// For the shared counterpart see [`as_uninit_slice`].
    ///
    /// [`as_mut`]: NonNullConst::as_mut
    /// [`as_uninit_slice`]: NonNullConst::as_uninit_slice
    ///
    /// # Safety
    ///
    /// When calling this method, you have to ensure that all of the following is true:
    ///
    /// * The pointer must be [valid] for reads and writes for `ptr.len() * mem::size_of::<T>()`
    ///   many bytes, and it must be properly aligned. This means in particular:
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
    ///   not get accessed (read or written) through any other pointer.
    ///
    /// This applies even if the result of this method is unused!
    ///
    /// See also [`slice::from_raw_parts_mut`].
    ///
    /// [valid]: crate::ptr#safety
    ///
    /// # Examples
    ///
    /// ```rust
    /// #![feature(allocator_api, ptr_as_uninit)]
    ///
    /// use std::alloc::{Allocator, Layout, Global};
    /// use std::mem::MaybeUninit;
    /// use std::ptr::NonNullConst;
    ///
    /// let memory: NonNullConst<[u8]> = Global.allocate(Layout::new::<[u8; 32]>())?;
    /// // This is safe as `memory` is valid for reads and writes for `memory.len()` many bytes.
    /// // Note that calling `memory.as_mut()` is not allowed here as the content may be uninitialized.
    /// # #[allow(unused_variables)]
    /// let slice: &mut [MaybeUninit<u8>] = unsafe { memory.as_uninit_slice_mut() };
    /// # Ok::<_, std::alloc::AllocError>(())
    /// ```
    #[inline]
    #[must_use]
    pub const unsafe fn as_uninit_slice_mut<'a>(self) -> &'a mut [MaybeUninit<T>] {
        // SAFETY: the caller must uphold the safety contract for `as_uninit_slice_mut`.
        unsafe { slice::from_raw_parts_mut(self.cast().as_ptr(), self.len()) }
    }

    /// Returns a raw pointer to an element or subslice, without doing bounds
    /// checking.
    ///
    /// Calling this method with an out-of-bounds index or when `self` is not dereferenceable
    /// is *[undefined behavior]* even if the resulting pointer is not used.
    ///
    /// [undefined behavior]: https://doc.rust-lang.org/reference/behavior-considered-undefined.html
    ///
    /// # Examples
    ///
    /// ```
    /// #![feature(slice_ptr_get, nonnull_slice_from_raw_parts)]
    /// use std::ptr::NonNullConst;
    ///
    /// let x = &mut [1, 2, 4];
    /// let x = NonNullConst::slice_from_raw_parts(NonNullConst::new(x.as_mut_ptr()).unwrap(), x.len());
    ///
    /// unsafe {
    ///     assert_eq!(x.get_unchecked_mut(1).as_ptr(), x.as_non_null_ptr().as_ptr().add(1));
    /// }
    /// ```
    #[inline]
    pub const unsafe fn get_unchecked_mut<I>(self, index: I) -> NonNullConst<I::Output>
        where
            I: ~const SliceIndex<[T]>,
    {
        // SAFETY: the caller ensures that `self` is dereferenceable and `index` in-bounds.
        // As a consequence, the resulting pointer cannot be null.
        unsafe { NonNullConst::new_unchecked(self.as_ptr().get_unchecked_mut(index)) }
    }
}

impl<T: ?Sized> const Clone for NonNullConst<T> {
    #[inline]
    fn clone(&self) -> Self {
        *self
    }
}

impl<T: ?Sized> Copy for NonNullConst<T> {}

impl<T: ?Sized, U: ?Sized> CoerceUnsized<NonNullConst<U>> for NonNullConst<T> where T: Unsize<U> {}

impl<T: ?Sized, U: ?Sized> DispatchFromDyn<NonNullConst<U>> for NonNullConst<T> where T: Unsize<U> {}

impl<T: ?Sized> fmt::Debug for NonNullConst<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.as_ptr(), f)
    }
}

impl<T: ?Sized> fmt::Pointer for NonNullConst<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Pointer::fmt(&self.as_ptr(), f)
    }
}

impl<T: ?Sized> Eq for NonNullConst<T> {}

impl<T: ?Sized> PartialEq for NonNullConst<T> {
    #[inline]
    fn eq(&self, other: &Self) -> bool {
        self.as_ptr() == other.as_ptr()
    }
}

impl<T: ?Sized> Ord for NonNullConst<T> {
    #[inline]
    fn cmp(&self, other: &Self) -> Ordering {
        self.as_ptr().cmp(&other.as_ptr())
    }
}

impl<T: ?Sized> PartialOrd for NonNullConst<T> {
    #[inline]
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        self.as_ptr().partial_cmp(&other.as_ptr())
    }
}

impl<T: ?Sized> hash::Hash for NonNullConst<T> {
    #[inline]
    fn hash<H: hash::Hasher>(&self, state: &mut H) {
        self.as_ptr().hash(state)
    }
}

impl<T: ?Sized> const From<&mut T> for NonNullConst<T> {
    /// Converts a `&mut T` to a `NonNullConst<T>`.
    ///
    /// This conversion is safe and infallible since references cannot be null.
    #[inline]
    fn from(reference: &mut T) -> Self {
        // SAFETY: A mutable reference cannot be null.
        unsafe { NonNullConst { pointer: reference as *mut T } }
    }
}

impl<T: ?Sized> const From<&T> for NonNullConst<T> {
    /// Converts a `&T` to a `NonNullConst<T>`.
    ///
    /// This conversion is safe and infallible since references cannot be null.
    #[inline]
    fn from(reference: &T) -> Self {
        // SAFETY: A reference cannot be null, so the conditions for
        // new_unchecked() are respected.
        unsafe { NonNullConst { pointer: reference as *const T } }
    }
}
