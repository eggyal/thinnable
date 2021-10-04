#![cfg_attr(not(any(feature = "std", doc)), no_std)]
#![cfg_attr(any(feature = "fn-refs", doc), feature(fn_traits, unboxed_closures))]
#![feature(doc_cfg, ptr_metadata, unsize)]
#![deny(missing_docs)]

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
//! bounds: a [`MetadataCreationFailure`] will arise if the metadata cannot be
//! converted into the proposed type.  Using such a non-standard metadata type
//! may save some bytes of storage, but obviously adds additional conversion
//! overhead on every dereference.
//!
//! The [`ThinnableSlice<T>`] type alias is provided for more convenient use
//! with `[T]` slices; and the [`ThinnableSliceU8<T>`], [`ThinnableSliceU16<T>`]
//! and [`ThinnableSliceU32<T>`] aliases provide the same convenient use with
//! `[T]` slices but encoding the length metadata in a `u8`, `u16` or `u32`
//! respectively.
//!
//! This crate presently depends on Rust's unstable [`ptr_metadata`] and
//! [`unsize`] features and, accordingly, requires a nightly toolchain.
//!
//! # Example
//! ```rust
//! use core::{alloc::Layout, convert::TryFrom, fmt, mem};
//! use thinnable::*;
//!
//! const THIN_SIZE: usize = mem::size_of::<&()>();
//!
//! // Creating a thinnable slice for an array is straightforward.
//! let thinnable_slice = ThinnableSlice::new([1, 2, 3]);
//!
//! // Given a thinnable, we can obtain a shared reference...
//! let r = thinnable_slice.as_thin_ref(); // ThinRef<[u16]>
//! // ...which is "thin"....
//! assert_eq!(mem::size_of_val(&r), THIN_SIZE);
//! // ...but which otherwise behaves just like a regular "fat" DST
//! // reference
//! assert_eq!(&r[..2], &[1, 2]);
//!
//! // For types `M` where the metadata type implements `TryInto<M>`, we
//! // can use `Thinnable::try_new` to try creating a thinnable using
//! // `M` as its stored metadata type (dereferencing requires that
//! // `M: TryInto<R>` where `R` is the original metadata type).
//! //
//! // For slices, there's a slightly more ergonomic interface:
//! let size_default = mem::size_of_val(&thinnable_slice);
//! let mut thinnable_slice;
//! thinnable_slice = ThinnableSliceU8::try_slice([1, 2, 3]).unwrap();
//! let size_u8 = mem::size_of_val(&thinnable_slice);
//! assert!(size_u8 < size_default);
//!
//! // We can also obtain a mutable reference...
//! let mut m = thinnable_slice.as_thin_mut(); // ThinMut<[u16], u8>
//! // ...which is also "thin"....
//! assert_eq!(mem::size_of_val(&m), THIN_SIZE);
//! // ...but which otherwise behaves just like a regular "fat" DST
//! // reference.
//! m[1] = 5;
//! assert_eq!(&m[1..], &[5, 3]);
//!
//! // We can also have thinnable trait objects:
//! let thinnable_trait_object;
//! thinnable_trait_object = Thinnable::<_, dyn fmt::Display>::new(123);
//! let o = thinnable_trait_object.as_thin_ref();// ThinRef<dyn Display>
//! assert_eq!(mem::size_of_val(&o), THIN_SIZE);
//! assert_eq!(o.to_string(), "123");
//! ```
//!
//! [DST]: https://doc.rust-lang.org/book/ch19-04-advanced-types.html#dynamically-sized-types-and-the-sized-trait
//! [`ptr_metadata`]: https://doc.rust-lang.org/nightly/unstable-book/library-features/ptr-metadata.html
//! [`unsize`]: https://doc.rust-lang.org/nightly/unstable-book/library-features/unsize.html

mod inner;
mod metadata;
mod slice;
mod thin_refs;

use core::{convert::TryInto, marker::Unsize};
use inner::{Fake, Real};
use metadata::Metadata;

pub use metadata::MetadataCreationFailure;
pub use slice::{
    SliceLength, ThinnableSlice, ThinnableSliceU16, ThinnableSliceU32, ThinnableSliceU8,
};
pub use thin_refs::{ThinMut, ThinRef};

/// Create convenient aliases for trait objects.
#[macro_export]
macro_rules! thinnable_trait {
    ($vis:vis $alias:ident for dyn $trait:path) => {
        $vis type $alias<T, M> = $crate::Thinnable<T, dyn $trait, M>;
    };
}

/// An owned value of type `T`, for which `U` is a DST to/from which it
/// can be "unsized"/"sized" using metadata of type `M`.
pub struct Thinnable<T, U: ?Sized, M = Metadata<U>>(Real<T, U, M>);

impl<T, U> Thinnable<T, U>
where
    U: ?Sized,
{
    /// Create a new `Thinnable` for the given `data`, embedding the metadata
    /// for `U` without conversion.
    ///
    /// For a similar function that also converts the metadata to some desired
    /// type, see [`try_new`][Self::try_new].
    ///
    /// # Example
    /// ```rust
    /// use core::mem::size_of_val;
    ///
    /// // For convenience, we might define a type alias for Thinnables of our desired DST
    /// thinnable::thinnable_trait!(ThinnableDisplay for dyn core::fmt::Display);
    ///
    /// // We can then create an array of thin references to such thinnables, even if the
    /// // underlying type differs.
    /// let int = ThinnableDisplay::new(123);
    /// let float = ThinnableDisplay::new(4.56);
    /// let string = ThinnableDisplay::new("xyz");
    ///
    /// let collection = [
    ///     int.as_thin_ref(),
    ///     float.as_thin_ref(),
    ///     string.as_thin_ref(),
    /// ];
    ///
    /// assert_eq!(size_of_val(&collection), 3 * size_of_val(&&()));
    /// assert_eq!(collection[0].to_string(), "123");
    /// assert_eq!(collection[1].to_string(), "4.56");
    /// assert_eq!(collection[2].to_string(), "xyz");
    /// ```
    #[inline(always)]
    pub fn new(data: T) -> Self
    where
        T: Unsize<U>,
    {
        unsafe { Self::try_new(data) }.unwrap()
    }

    /// Cast this `Thinnable` into one embedding metadata for `V` without
    /// conversion.  This is particularly useful if one wants thin
    /// references to a different trait object for the existing underlying data.
    ///
    /// For a similar method that also converts the metadata to some desired
    /// type, see [`try_cast`][Self::try_cast].
    ///
    /// # Example
    /// ```rust
    /// use core::{fmt, mem::size_of_val};
    /// use thinnable::thinnable_trait;
    ///
    /// thinnable_trait!(ThinnableLowerExp for dyn fmt::LowerExp);
    /// let int = ThinnableLowerExp::new(123);
    /// let float = ThinnableLowerExp::new(4.56);
    ///
    /// let hexes = [
    ///     int.as_thin_ref(),
    ///     float.as_thin_ref(),
    /// ];
    ///
    /// assert_eq!(size_of_val(&hexes), 2 * size_of_val(&&()));
    /// assert_eq!(format!("{:e}", hexes[0]), "1.23e2");
    /// assert_eq!(format!("{:e}", hexes[1]), "4.56e0");
    ///
    /// // cast these existing ThinnableLowerExps to ThinnableDisplays
    /// thinnable_trait!(ThinnableDisplay for dyn fmt::Display);
    /// let int = int.cast();
    /// let float = float.cast();
    /// let string = ThinnableDisplay::new("xyz");
    ///
    /// let displays = [
    ///     int.as_thin_ref(),
    ///     float.as_thin_ref(),
    ///     string.as_thin_ref(),
    /// ];
    ///
    /// assert_eq!(size_of_val(&displays), 3 * size_of_val(&&()));
    /// assert_eq!(displays[0].to_string(), "123");
    /// assert_eq!(displays[1].to_string(), "4.56");
    /// assert_eq!(displays[2].to_string(), "xyz");
    /// ```
    #[inline(always)]
    pub fn cast<V>(self) -> Thinnable<T, V>
    where
        T: Unsize<V>,
        V: ?Sized,
    {
        unsafe { self.try_cast() }.unwrap()
    }
}

impl<T, U, M> Thinnable<T, U, M>
where
    T: Unsize<U>,
    U: ?Sized,
{
    /// Rebuild this `Thinnable`, embedding metadata for the existing DST `U`
    /// without conversion.  This is particularly useful to restore a
    /// `Thinnable` to its default metadata encoding after previous conversions.
    ///
    /// For a similar method that also converts the metadata to some desired
    /// type, see [`try_convert`][Self::try_convert].
    ///
    /// # Example
    /// ```rust
    /// use core::mem::size_of_val;
    /// use thinnable::ThinnableSliceU8;
    ///
    /// let slice = ThinnableSliceU8::try_slice([1, 2, 3]).unwrap();
    ///
    /// let size_u8 = size_of_val(&slice);
    /// let slice = slice.normalize();
    /// let size_default = size_of_val(&slice);
    ///
    /// assert!(size_default > size_u8);
    /// ```
    #[inline(always)]
    pub fn normalize(self) -> Thinnable<T, U> {
        unsafe { self.try_convert() }.unwrap()
    }

    /// Attempt to create a new `Thinnable` for the given `data`, embedding the
    /// metadata for `U` converted to `M`.
    ///
    /// For a similar, infallible, safe function that does not convert the
    /// metadata, see [`new`][Self::new].
    ///
    /// # Safety
    /// If `<<U as Pointee>::Metadata as TryInto<M>>::try_into(in)` returns
    /// `Ok(m)` and `<M as TryInto<<U as Pointee>::Metadata>>::try_into(m)`
    /// returns `Ok(out)`, then dereferencing a [`ThinRef`] or [`ThinMut`]
    /// of the returned `Thinnable` is undefined behavior unless `in` and
    /// `out` are bitwise identical.
    ///
    /// That is to say, callers are responsible for ensuring that metadata
    /// conversion to `M` either fails, or produces reversible results.
    #[inline(always)]
    pub unsafe fn try_new(data: T) -> Result<Self, MetadataCreationFailure<U, M>>
    where
        Metadata<U>: TryInto<M>,
    {
        Real::try_new(data).map(Self)
    }

    /// Attempt to rebuild this `Thinnable`, converting metadata for the
    /// existing DST `U` into `N`.  This is particularly useful if one wants
    /// the metadata embedded in this `Thinnable` to use a more/less compressed
    /// representation.
    ///
    /// For a similar, infallible, safe method that embeds `U`'s unconverted
    /// metadata, see [`normalize`][Self::normalize].
    ///
    /// # Safety
    /// If `<<U as Pointee>::Metadata as TryInto<N>>::try_into(in)` returns
    /// `Ok(n)` and `<N as TryInto<<U as Pointee>::Metadata>>::try_into(n)`
    /// returns `Ok(out)`, then dereferencing a [`ThinRef`] or [`ThinMut`]
    /// of the returned `Thinnable` is undefined behavior unless `in` and
    /// `out` are bitwise identical.
    ///
    /// That is to say, callers are responsible for ensuring that metadata
    /// conversion to `N` either fails, or produces reversible results.
    ///
    /// # Example
    /// ```rust
    /// use core::mem::size_of_val;
    ///
    /// let slice = thinnable::ThinnableSlice::new([1, 2, 3]);
    ///
    /// let size_default = size_of_val(&slice);
    /// let slice = unsafe { slice.try_convert::<u8>() };
    /// let size_u8 = size_of_val(&slice);
    ///
    /// assert!(size_u8 < size_default);
    /// ```
    #[inline(always)]
    pub unsafe fn try_convert<N>(self) -> Result<Thinnable<T, U, N>, MetadataCreationFailure<U, N>>
    where
        Metadata<U>: TryInto<N>,
    {
        self.try_cast()
    }
}

impl<T, U, M> Thinnable<T, U, M>
where
    U: ?Sized,
{
    /// Attempt to cast this `Thinnable` into one embedding metadata for `V`
    /// converted to `N`.  This is particularly useful if one wants thin
    /// references to a different trait object for the existing underlying data.
    ///
    /// For a similar, infallible, safe method that does not convert the
    /// metadata, see [`cast`][Self::cast].
    ///
    /// # Safety
    /// If `<<V as Pointee>::Metadata as TryInto<N>>::try_into(in)` returns
    /// `Ok(n)` and `<N as TryInto<<V as Pointee>::Metadata>>::try_into(n)`
    /// returns `Ok(out)`, then dereferencing a [`ThinRef`] or [`ThinMut`]
    /// of the returned `Thinnable` is undefined behavior unless `in` and
    /// `out` are bitwise identical.
    ///
    /// That is to say, callers are responsible for ensuring that metadata
    /// conversion to `N` either fails, or produces reversible results.
    #[inline(always)]
    pub unsafe fn try_cast<V, N>(self) -> Result<Thinnable<T, V, N>, MetadataCreationFailure<V, N>>
    where
        T: Unsize<V>,
        V: ?Sized,
        Metadata<V>: TryInto<N>,
    {
        Thinnable::try_new(self.into_inner())
    }

    /// Obtain a [`ThinRef`] to this `Thinnable`'s DST, analogous to `&U`, but
    /// only a single pointer-width in size.
    ///
    /// `ThinRef` provides shared access, and therefore does not permit direct
    /// mutation of the underlying data.  For exclusive access, see
    /// [`as_thin_mut`][Self::as_thin_mut].
    #[inline(always)]
    pub fn as_thin_ref(&self) -> ThinRef<U, M> {
        ThinRef::new(self.0.as_ref())
    }

    /// Obtain a [`ThinMut`] to this `Thinnable`'s DST, analogous to `&mut U`,
    /// but only a single pointer-width in size.
    ///
    /// `ThinMut` provides exclusive access, and therefore permits direct
    /// mutation of the underlying data.  For shared access, see
    /// [`as_thin_ref`][Self::as_thin_ref].
    #[inline(always)]
    pub fn as_thin_mut(&mut self) -> ThinMut<U, M> {
        ThinMut::new(self.0.as_mut())
    }

    /// Extract the embedded data from this `Thinnable`.
    #[inline(always)]
    pub fn into_inner(self) -> T {
        self.0.into_inner()
    }
}

impl<T, U, M> AsRef<T> for Thinnable<T, U, M>
where
    U: ?Sized,
{
    #[inline(always)]
    fn as_ref(&self) -> &T {
        &self.0
    }
}

impl<T, U, M> AsMut<T> for Thinnable<T, U, M>
where
    U: ?Sized,
{
    #[inline(always)]
    fn as_mut(&mut self) -> &mut T {
        &mut self.0
    }
}
