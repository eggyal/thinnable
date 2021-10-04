# Thinnable

Standard Rust [DST] references comprise not only a pointer to the underlying
object, but also some associated metadata by which the DST can be resolved
at runtime. Both the pointer and the metadata reside together in a so-called
"fat" or "wide" reference, which is typically what one wants: the referent
can thus be reached with only direct memory accesses, and each reference can
refer to a *different* DST (for example, slices or traits) of a single
underlying object.

However, in order to store multiple copies of the *same* DST reference, one
typically suffers either metadata duplication across each such reference or
else some costly indirection; furthermore, in some situations Rust's
metadata may be known to be excessive: some other (smaller) type may suffice
instead (for example, with particular slices, we may know that their lengths
will always fit in a `u8` and hence using a `usize` for their metadata would
be unnecessary; or, with particular trait objects, we may know that the
underlying type will always be from some `enum` and hence using a vtable
pointer for their metadata would be unnecessary). Addressing these concerns
can save valuable memory, especially when there are a great many such
references in simultaneous use.

A [`Thinnable`] stores the metadata together with the *referent* rather than
the *reference*, and thereby enables one to obtain "thin" DST references to
the (now metadata-decorated) object: namely, [`ThinRef`] and [`ThinMut`] for
shared and exclusive references respectively. But this comes at the cost of
an additional indirect memory access in order to fetch the metadata, rather
than it being directly available on the stack; hence, as is so often the
case, we are trading off between time and space.  Furthermore, for any given
[`Thinnable`], its "thin" references can only refer to the one DST with
which that [`Thinnable`] was instantiated (although regular "fat" references
can still be obtained to any of its DSTs, if required).

One can specify a non-standard metadata type, e.g. to use a smaller integer
such as `u8` in place of the default `usize` when a slice fits within its
bounds: a [`MetadataCreationFailure`] will arise if the metadata cannot be
converted into the proposed type.  Using such a non-standard metadata type
may save some bytes of storage, but obviously adds additional conversion
overhead on every dereference.

The [`ThinnableSlice<T>`] type alias is provided for more convenient use
with `[T]` slices; and the [`ThinnableSliceU8<T>`], [`ThinnableSliceU16<T>`]
and [`ThinnableSliceU32<T>`] aliases provide the same convenient use with
`[T]` slices but encoding the length metadata in a `u8`, `u16` or `u32`
respectively.

This crate presently depends on Rust's unstable [`ptr_metadata`] and
[`unsize`] features and, accordingly, requires a nightly toolchain.

## Example
```rust
use core::{alloc::Layout, convert::TryFrom, fmt, mem};
use thinnable::*;

const THIN_SIZE: usize = mem::size_of::<&()>();

// Creating a thinnable slice for an array is straightforward.
let thinnable_slice = ThinnableSlice::new([1, 2, 3]);

// Given a thinnable, we can obtain a shared reference...
let r = thinnable_slice.as_thin_ref(); // ThinRef<[u16]>
// ...which is "thin"....
assert_eq!(mem::size_of_val(&r), THIN_SIZE);
// ...but which otherwise behaves just like a regular "fat" DST reference
assert_eq!(&r[..2], &[1, 2]);

// For types `M` where the metadata type implements `TryInto<M>`, we can use
// `Thinnable::try_new` to try creating a thinnable using `M` as its stored
// metadata type (dereferencing requires that `M: TryInto<R>` where `R` is
// the original metadata type).
//
// For slices, there's a slightly more ergonomic interface:
let size_default = mem::size_of_val(&thinnable_slice);
let mut thinnable_slice = ThinnableSliceU8::try_slice([1, 2, 3]).unwrap();
let size_u8 = mem::size_of_val(&thinnable_slice);
assert!(size_u8 < size_default);

// We can also obtain a mutable reference...
let mut m = thinnable_slice.as_thin_mut(); // ThinMut<[u16], u8>
// ...which is also "thin"....
assert_eq!(mem::size_of_val(&m), THIN_SIZE);
// ...but which otherwise behaves just like a regular "fat" DST reference.
m[1] = 5;
assert_eq!(&m[1..], &[5, 3]);

// We can also have thinnable trait objects:
let thinnable_trait_object = Thinnable::<_, dyn fmt::Display>::new(123);
let o = thinnable_trait_object.as_thin_ref(); // ThinRef<dyn Display>
assert_eq!(mem::size_of_val(&o), THIN_SIZE);
assert_eq!(o.to_string(), "123");
```

[DST]: https://doc.rust-lang.org/book/ch19-04-advanced-types.html#dynamically-sized-types-and-the-sized-trait
[`ptr_metadata`]: https://doc.rust-lang.org/nightly/unstable-book/library-features/ptr-metadata.html
[`unsize`]: https://doc.rust-lang.org/nightly/unstable-book/library-features/unsize.html

[`Thinnable`]: https://docs.rs/thinnable/latest/thinnable/struct.Thinnable.html
[`ThinRef`]: https://docs.rs/thinnable/latest/thinnable/struct.ThinRef.html
[`ThinMut`]: https://docs.rs/thinnable/latest/thinnable/struct.ThinMut.html
[`MetadataCreationFailure`]: https://docs.rs/thinnable/latest/thinnable/type.MetadataCreationFailure.html
[`ThinnableSlice<T>`]: https://docs.rs/thinnable/latest/thinnable/type.ThinnableSlice.html
[`ThinnableSliceU8<T>`]: https://docs.rs/thinnable/latest/thinnable/type.ThinnableSliceU8.html
[`ThinnableSliceU16<T>`]: https://docs.rs/thinnable/latest/thinnable/type.ThinnableSliceU16.html
[`ThinnableSliceU32<T>`]: https://docs.rs/thinnable/latest/thinnable/type.ThinnableSliceU32.html