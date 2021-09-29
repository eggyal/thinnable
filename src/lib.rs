#![cfg_attr(not(feature = "std"), no_std)]
#![cfg_attr(feature = "fn-refs", feature(fn_traits, unboxed_closures))]
#![feature(ptr_metadata, unsize)]
#![deny(unsafe_code)]

//! Standard Rust [DST] references comprise not only a pointer to the underlying
//! object, but also some associated metadata by which the DST can be resolved
//! at runtime. Both the pointer and the metadata reside together in a so-called
//! "fat" or "wide" reference, which is typically what one wants: the referent
//! can thus be reached with only direct memory accesses, and each reference can
//! refer to a *different* DST (for example, slices or traits) of a single
//! underlying object.
//!
//! However, in order to store multiple copies of the *same* DST reference, one
//! typically suffers either metadata duplication across each such reference or
//! else some costly indirection; furthermore, in some situations Rust's
//! metadata may be known to be excessive: some other (smaller) type may suffice
//! instead (for example, with particular slices, we may know that their lengths
//! will always fit in a `u8` and hence using a `usize` for their metadata would
//! be unnecessary; or, with particular trait objects, we may know that the
//! underlying type will always be from some `enum` and hence using a vtable
//! pointer for their metadata would be unnecessary). Addressing these concerns
//! can save valuable memory, especially when there are a great many such
//! references in simultaneous use.
//!
//! A [`Thinnable`] stores the metadata together with the *referent* rather than
//! the *reference*, and thereby enables one to obtain "thin" DST references to
//! the (now metadata-decorated) object: namely, [`ThinRef`] and [`ThinMut`] for
//! shared and exclusive references respectively. But this comes at the cost of
//! an additional indirect memory access in order to fetch the metadata, rather
//! than it being directly available on the stack; hence, as is so often the
//! case, we are trading off between time and space.  Furthermore, for any given
//! [`Thinnable`], its "thin" references can only refer to the one DST with
//! which that [`Thinnable`] was instantiated (although regular "fat" references
//! can still be obtained to any of its DSTs, if required).
//!
//! One can specify a non-standard metadata type, e.g. to use a smaller integer
//! such as `u8` in place of the default `usize` when a slice fits within its
//! bounds: a [`MetadataConversionFailure`] will arise if the metadata cannot be
//! converted into the proposed type.  Using such a non-standard metadata type
//! may save some bytes of storage, but obviously adds additional conversion
//! overhead on every dereference.
//!
//! The [`ThinnableSlice<T>`] type alias is provided for more convenient use
//! with `[T]` slices.
//!
//! This crate presently depends on Rust's unstable [`ptr_metadata`] and
//! [`unsize`] features and, accordingly, requires a nightly toolchain.
//!
//! # Example
//! ```rust
//! use std::{alloc::Layout, convert::TryFrom, fmt, mem::size_of_val};
//! use thinnable::*;
//!
//! const ARRAY: [u16; 3] = [1, 2, 3];
//!
//! const LAYOUT_ARRAY: Layout = Layout::new::<[u16; 3]>();
//! const LAYOUT_USIZE: Layout = Layout::new::<usize>();
//! const LAYOUT_U8   : Layout = Layout::new::<u8>();
//!
//! // Creating a thinnable slice for an array is straightforward.
//! let thinnable_slice = ThinnableSlice::new(ARRAY);
//!
//! // A thinnable comprises its metadata (for a slice, it's the number of
//! // elements), followed by its content.
//! let (layout, _) = LAYOUT_USIZE.extend(LAYOUT_ARRAY).unwrap();
//! assert_eq!(size_of_val(&thinnable_slice), layout.pad_to_align().size());
//!
//! // Given a thinnable, we can obtain a shared reference...
//! let r = thinnable_slice.as_thin_ref(); // ThinRef<[u16]>
//! // ...which is "thin"....
//! assert_eq!(size_of_val(&r), size_of_val(&&()));
//! // ...but which otherwise behaves just like a regular "fat" DST reference
//! // (dereferencing requires that `M: TryInto<R>` where `R` is the true
//! // metadata type).
//! assert_eq!(&r[..2], &[1, 2]);
//!
//! // For types `M` where the metadata type implements `TryInto<M>`, we can use
//! // `Thinnable::try_new` to try creating a thinnable using `M` as its stored
//! // metadata type:
//! let mut thinnable_slice = Thinnable::<_, [_], u8>::try_new(ARRAY).unwrap();
//! let (layout, _) = LAYOUT_U8.extend(LAYOUT_ARRAY).unwrap();
//! assert_eq!(size_of_val(&thinnable_slice), layout.pad_to_align().size());
//!
//! // We can also obtain a mutable reference...
//! let mut m = thinnable_slice.as_thin_mut(); // ThinMut<[u16], u8>
//! // ...which is also "thin"....
//! assert_eq!(size_of_val(&m), size_of_val(&&()));
//! // ...but which otherwise behaves just like a regular "fat" DST reference.
//! m[1] = 5;
//! assert_eq!(&m[1..], &[5, 3]);
//!
//! // We can also have thinnable trait objects:
//! let thinnable_trait_object = Thinnable::<_, dyn fmt::Display>::new(123);
//! let o = thinnable_trait_object.as_thin_ref(); // ThinRef<dyn Display>
//! assert_eq!(size_of_val(&o), size_of_val(&&()));
//! assert_eq!(o.to_string(), "123");
//! ```
//!
//! [DST]: https://doc.rust-lang.org/book/ch19-04-advanced-types.html#dynamically-sized-types-and-the-sized-trait
//! [`ptr_metadata`]: https://doc.rust-lang.org/beta/unstable-book/library-features/ptr-metadata.html
//! [`unsize`]: https://doc.rust-lang.org/beta/unstable-book/library-features/unsize.html

#[allow(unsafe_code)]
mod inner;
mod thin_refs;

use core::{convert::TryInto, marker::{PhantomData, Unsize}, ptr};
use inner::{Fake, Real};
pub use thin_refs::{ThinMut, ThinRef};

type Metadata<U> = <U as ptr::Pointee>::Metadata;

/// Convenient alias for slices.
pub type ThinnableSlice<T, M, const N: usize> = Thinnable<[T; N], [T], M>;

/// A failure on conversion of DST `U`'s metadata to type `M`.
pub type MetadataConversionFailure<U, M> = <Metadata<U> as TryInto<M>>::Error;

/// An owned value of type `T`, for which `U` is a DST to/from which it
/// can be "unsized"/"sized" using metadata of type `M`.
#[repr(C)]
pub struct Thinnable<T, U: ?Sized, M = Metadata<U>>(Real<T, M>, PhantomData<U>);

impl<T, U> Thinnable<T, U>
where
    U: ?Sized,
{
    #[inline(always)]
    pub fn new(data: T) -> Self
    where
        T: Unsize<U>,
    {
        Self::try_new(data).unwrap()
    }

    #[inline(always)]
    pub fn cast<V>(self) -> Thinnable<T, V>
    where
        T: Unsize<V>,
        V: ?Sized + ptr::Pointee<Metadata = Metadata<U>>,
    {
        self.try_cast().unwrap()
    }
}

impl<T, U, M> Thinnable<T, U, M>
where
    U: ?Sized,
{
    #[inline(always)]
    pub fn try_new(data: T) -> Result<Self, MetadataConversionFailure<U, M>>
    where
        T: Unsize<U>,
        Metadata<U>: TryInto<M>,
    {
        let metadata = ptr::metadata(&data as &U).try_into()?;
        Ok(Self(Real { metadata, data }, PhantomData))
    }

    #[inline(always)]
    pub fn try_cast<V>(self) -> Result<Thinnable<T, V, M>, MetadataConversionFailure<V, M>>
    where
        T: Unsize<V>,
        V: ?Sized,
        Metadata<V>: TryInto<M>,
    {
        Thinnable::try_new(self.into_inner())
    }
}

impl<T, U, M> Thinnable<T, U, M>
where
    U: ?Sized,
{
    #[inline(always)]
    pub fn as_thin_ref(&self) -> ThinRef<U, M> {
        ThinRef(self.0.as_ref())
    }

    #[inline(always)]
    pub fn as_thin_mut(&mut self) -> ThinMut<U, M> {
        ThinMut(self.0.as_mut())
    }

    #[inline(always)]
    pub fn into_inner(self) -> T {
        self.0.data
    }
}

impl<T, U, M> AsRef<T> for Thinnable<T, U, M>
where
    U: ?Sized,
{
    #[inline(always)]
    fn as_ref(&self) -> &T {
        &self.0.data
    }
}

impl<T, U, M> AsMut<T> for Thinnable<T, U, M>
where
    U: ?Sized,
{
    #[inline(always)]
    fn as_mut(&mut self) -> &mut T {
        &mut self.0.data
    }
}
