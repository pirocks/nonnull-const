# nonnull-const

I've frequently wanted an equivalent of the rust standard library's `Nonnull` for const pointers. That's what this is.

Implements `NonNullConst` as a wrapper around `NonNull` with the same traits/impls/functions, except when the const nature of `NonNullConst` prevents it. 
