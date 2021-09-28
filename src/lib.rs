#![cfg_attr(not(feature = "std"), no_std)]
#![feature(fn_traits, ptr_metadata, unboxed_closures, unsize)]

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
//! instead (for example, we may know that the length of an array will always
//! fit in a `u8` and hence using a `usize` for the metadata is unnecessary; or
//! we may know that the trait is always one from an enumerated list and hence
//! could be represented with an `enum` rather than a vtable pointer).
//! Addressing these concerns can save valuable memory, especially when there
//! are a great many such references in simultaneous use.
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
//! converted into the proposed type.
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

use core::{
    borrow::{Borrow, BorrowMut},
    cmp,
    convert::TryInto,
    fmt,
    hash::{Hash, Hasher},
    marker::{PhantomData, Unsize},
    mem,
    ops::{Deref, DerefMut},
    ptr,
};

type Metadata<U> = <U as ptr::Pointee>::Metadata;

#[derive(Debug)]
#[repr(C)]
struct Real<T, M>
where
    T: ?Sized,
{
    metadata: M,
    data: T,
}

#[repr(C)]
struct Fake<U, M = Metadata<U>>
where
    U: ?Sized,
{
    metadata: M,
    data: PhantomData<U>,
}

/// An owned value of type `T`, for which `U` is a DST to/from which it
/// can be "unsized"/"sized" using metadata of type `M`.
#[repr(C)]
pub union Thinnable<T, U, M = Metadata<U>>
where
    U: ?Sized,
{
    real: mem::ManuallyDrop<Real<T, M>>,
    fake: mem::ManuallyDrop<Fake<U, M>>,
}

impl<T, U, M> fmt::Debug for Thinnable<T, U, M>
where
    T: fmt::Debug,
    U: ?Sized,
    M: fmt::Debug,
{
    #[inline(always)]
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(unsafe { &self.real }, f)
    }
}

impl<T, U, M> Drop for Thinnable<T, U, M>
where
    U: ?Sized,
{
    #[inline(always)]
    fn drop(&mut self) {
        unsafe { mem::ManuallyDrop::drop(&mut self.real) };
    }
}

/// Convenient alias for slices.
pub type ThinnableSlice<T, M, const N: usize> = Thinnable<[T; N], [T], M>;

impl<U, M> Fake<U, M>
where
    U: ?Sized,
    M: Copy + TryInto<Metadata<U>>,
{
    /// ### Panics
    /// This method will panic if `self.metadata` contains an invalid value
    /// that cannot be converted to a `Metadata<U>`.
    #[inline(always)]
    fn metadata(&self) -> Metadata<Real<U, M>> {
        let t_metadata = self
            .metadata
            .try_into()
            .ok()
            .expect("not a valid metadata value");

        // The metadata of `Unsized<U, _>` is that of its last field, `data`,
        // which has type `U`.
        //
        // `Metadata<U>` and `Metadata<Unsized<U, _>>` are therefore the same,
        // but we cannot inform the compiler of this without publicly exposing
        // `Unsized`; likewise for adding constraints that would enable safe
        // conversion (such as `Metadata<U>: Into<Metadata<Unsized<U, M>>>`).
        //
        // Instead, we simply dereference a casted raw pointer, which is
        // perfectly safe because the types are necessarily identical.
        unsafe { *(&t_metadata as *const _ as *const _) }
    }
}

/// A "thin" shared DST reference, analogue of `&U`.
#[repr(transparent)]
pub struct ThinRef<'a, U, M = Metadata<U>>(&'a Fake<U, M>)
where
    U: ?Sized;

impl<U, M> Clone for ThinRef<'_, U, M>
where
    U: ?Sized,
{
    fn clone(&self) -> Self {
        Self(self.0)
    }
}
impl<U, M> Copy for ThinRef<'_, U, M> where U: ?Sized {}

/// A "thin" exclusive DST reference, analogue of `&mut U`.
#[repr(transparent)]
pub struct ThinMut<'a, U, M = Metadata<U>>(&'a mut Fake<U, M>)
where
    U: ?Sized;

/// A failure on conversion of DST `U`'s metadata to type `M`.
pub type MetadataConversionFailure<U, M> = <Metadata<U> as TryInto<M>>::Error;

impl<T, M> Deref for Real<T, M>
where
    T: ?Sized,
{
    type Target = T;
    #[inline(always)]
    fn deref(&self) -> &T {
        &self.data
    }
}

impl<T, M> DerefMut for Real<T, M>
where
    T: ?Sized,
{
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut T {
        &mut self.data
    }
}

impl<U, M> AsRef<Real<U, M>> for Fake<U, M>
where
    U: ?Sized,
    M: Copy + TryInto<Metadata<U>>,
{
    #[inline(always)]
    fn as_ref(&self) -> &Real<U, M> {
        let data_address = self as *const _ as _;
        let metadata = self.metadata();
        let ptr = ptr::from_raw_parts(data_address, metadata);
        unsafe { &*ptr }
    }
}

impl<U, M> AsMut<Real<U, M>> for Fake<U, M>
where
    U: ?Sized,
    M: Copy + TryInto<Metadata<U>>,
{
    #[inline(always)]
    fn as_mut(&mut self) -> &mut Real<U, M> {
        let data_address = self as *mut _ as _;
        let metadata = self.metadata();
        let ptr = ptr::from_raw_parts_mut(data_address, metadata);
        unsafe { &mut *ptr }
    }
}

impl<U, M> Deref for Fake<U, M>
where
    U: ?Sized,
    M: Copy + TryInto<Metadata<U>>,
{
    type Target = U;
    #[inline(always)]
    fn deref(&self) -> &U {
        self.as_ref()
    }
}

impl<U, M> DerefMut for Fake<U, M>
where
    U: ?Sized,
    M: Copy + TryInto<Metadata<U>>,
{
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut U {
        self.as_mut()
    }
}

macro_rules! refs {
    (common $ref:ident) => {
        impl<U, M> Borrow<U> for $ref<'_, U, M>
        where
            U: ?Sized,
            M: Copy + TryInto<Metadata<U>>,
        {
            #[inline(always)]
            fn borrow(&self) -> &U {
                self.0.as_ref()
            }
        }

        impl<U, M> Deref for $ref<'_, U, M>
        where
            U: ?Sized,
            M: Copy + TryInto<Metadata<U>>,
        {
            type Target = U;
            #[inline(always)]
            fn deref(&self) -> &U {
                self.borrow()
            }
        }

        impl<U, M> fmt::Pointer for $ref<'_, U, M>
        where
            U: ?Sized,
            M: Copy + TryInto<Metadata<U>>,
        {
            #[inline(always)]
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Pointer::fmt(&(&**self as *const U), f)
            }
        }

        refs! {
            fmt for $ref: Binary, Debug, Display, LowerExp, LowerHex, Octal, UpperExp, UpperHex;
        }

        impl<Rhs, U, M, N> PartialOrd<$ref<'_, Rhs, N>> for $ref<'_, U, M>
        where
            Rhs: ?Sized,
            U: ?Sized + PartialOrd<Rhs>,
            M: Copy + TryInto<Metadata<U>>,
            N: Copy + TryInto<Metadata<Rhs>>,
        {
            #[inline(always)]
            fn partial_cmp(&self, other: &$ref<'_, Rhs, N>) -> Option<cmp::Ordering> {
                (**self).partial_cmp(&**other)
            }

            #[inline(always)]
            fn lt(&self, other: &$ref<'_, Rhs, N>) -> bool {
                (**self).lt(&**other)
            }

            #[inline(always)]
            fn le(&self, other: &$ref<'_, Rhs, N>) -> bool {
                (**self).le(&**other)
            }

            #[inline(always)]
            fn gt(&self, other: &$ref<'_, Rhs, N>) -> bool {
                (**self).gt(&**other)
            }

            #[inline(always)]
            fn ge(&self, other: &$ref<'_, Rhs, N>) -> bool {
                (**self).ge(&**other)
            }
        }

        impl<Rhs, U, M, N> PartialEq<$ref<'_, Rhs, N>> for $ref<'_, U, M>
        where
            Rhs: ?Sized,
            U: ?Sized + PartialEq<Rhs>,
            M: Copy + TryInto<Metadata<U>>,
            N: Copy + TryInto<Metadata<Rhs>>,
        {
            #[inline(always)]
            fn eq(&self, other: &$ref<'_, Rhs, N>) -> bool {
                (**self).eq(&**other)
            }

            #[inline(always)]
            fn ne(&self, other: &$ref<'_, Rhs, N>) -> bool {
                (**self).ne(&**other)
            }
        }

        delegate! {
            for $ref {
                Ord {
                    fn cmp(&self, other: &Self) -> cmp::Ordering;
                }
                Eq {}
                AsRef<T> {
                    fn as_ref(&self) -> &T;
                }
                Hash {
                    fn hash<H>(&self, hasher: &mut H) where H: Hasher;
                }
            }
        }
    };

    (const $const:ident) => {
        refs!(common $const);

        impl<Args, U, M> FnMut<Args> for $const<'_, U, M>
        where
            U: ?Sized + Fn<Args>,
            M: Copy + TryInto<Metadata<U>>,
        {
            #[inline(always)]
            extern "rust-call" fn call_mut(&mut self, args: Args) -> U::Output {
                (**self).call(args)
            }
        }

        impl<Args, U, M> FnOnce<Args> for $const<'_, U, M>
        where
            U: ?Sized + Fn<Args>,
            M: Copy + TryInto<Metadata<U>>,
        {
            type Output = U::Output;
            #[inline(always)]
            extern "rust-call" fn call_once(self, args: Args) -> U::Output {
                (&*self).call(args)
            }
        }

        delegate! {
            for $const {
                Fn<Args> {
                    extern "rust-call" fn call(&self, args: Args) -> U::Output;
                }

                #[cfg(feature = "std")]
                std::net::ToSocketAddrs {
                    type Iter;
                    fn to_socket_addrs(&self) -> std::io::Result<U::Iter>;
                }
            }
        }

        unsafe impl<U, M> Send for $const<'_, U, M>
        where
            U: ?Sized + Sync,
        {}
    };

    (mut $mut:ident) => {
        refs!(common $mut);

        impl<U, M> BorrowMut<U> for $mut<'_, U, M>
        where
            U: ?Sized,
            M: Copy + TryInto<Metadata<U>>,
        {
            #[inline(always)]
            fn borrow_mut(&mut self) -> &mut U {
                self.0.as_mut()
            }
        }

        impl<U, M> DerefMut for $mut<'_, U, M>
        where
            U: ?Sized,
            M: Copy + TryInto<Metadata<U>>,
        {
            #[inline(always)]
            fn deref_mut(&mut self) -> &mut U {
                self.borrow_mut()
            }
        }

        delegate! {
            for $mut {
                FnMut<Args> {
                    extern "rust-call" fn call_mut(&mut self, args: Args) -> U::Output;
                }

                fmt::Write {
                    fn write_str(&mut self, s: &str) -> fmt::Result;
                    fn write_char(&mut self, c: char) -> fmt::Result;
                    fn write_fmt(&mut self, args: fmt::Arguments<'_>) -> fmt::Result;
                }

                Iterator {
                    type Item;
                    fn next(&mut self) -> Option<U::Item>;
                    fn size_hint(&self) -> (usize, Option<usize>);
                    fn nth(&mut self, n: usize) -> Option<Self::Item>;
                }
                DoubleEndedIterator {
                    fn next_back(&mut self) -> Option<U::Item>;
                    fn nth_back(&mut self, n: usize) -> Option<U::Item>;
                }
                ExactSizeIterator {}
                core::iter::FusedIterator {}

                #[cfg(feature = "std")]
                std::io::Write {
                    fn write(&mut self, buf: &[u8]) -> std::io::Result<usize>;
                    fn write_vectored(&mut self, bufs: &[std::io::IoSlice<'_>]) -> std::io::Result<usize>;
                    fn flush(&mut self) -> std::io::Result<()>;
                    fn write_all(&mut self, buf: &[u8]) -> std::io::Result<()>;
                    fn write_fmt(&mut self, fmt: fmt::Arguments<'_>) -> std::io::Result<()>;
                }

                #[cfg(feature = "std")]
                std::io::Read {
                    fn read(&mut self, buf: &mut [u8]) -> std::io::Result<usize>;
                    fn read_vectored(&mut self, bufs: &mut [std::io::IoSliceMut<'_>]) -> std::io::Result<usize>;
                    fn read_to_end(&mut self, buf: &mut Vec<u8>) -> std::io::Result<usize>;
                    fn read_to_string(&mut self, buf: &mut String) -> std::io::Result<usize>;
                    fn read_exact(&mut self, buf: &mut [u8]) -> std::io::Result<()>;
                }

                #[cfg(feature = "std")]
                std::io::Seek {
                    fn seek(&mut self, pos: std::io::SeekFrom) -> std::io::Result<u64>;
                    fn rewind(&mut self) -> std::io::Result<()>;
                    fn stream_position(&mut self) -> std::io::Result<u64>;
                }

                #[cfg(feature = "std")]
                std::io::BufRead {
                    fn fill_buf(&mut self) -> std::io::Result<&[u8]>;
                    fn consume(&mut self, amt: usize);
                    fn read_until(&mut self, byte: u8, buf: &mut Vec<u8>) -> std::io::Result<usize>;
                    fn read_line(&mut self, buf: &mut String) -> std::io::Result<usize>;
                }
            }
        }

        impl<T, U, M> AsMut<T> for $mut<'_, U, M>
        where
            T: ?Sized,
            U: ?Sized + AsMut<T>,
            M: Copy + TryInto<Metadata<U>>,
        {
            #[inline(always)]
            fn as_mut(&mut self) -> &mut T {
                (**self).as_mut()
            }
        }

        impl<Args, U, M> FnOnce<Args> for $mut<'_, U, M>
        where
            U: ?Sized + FnMut<Args>,
            M: Copy + TryInto<Metadata<U>>,
        {
            type Output = U::Output;
            #[inline(always)]
            extern "rust-call" fn call_once(mut self, args: Args) -> U::Output {
                (&mut *self).call_mut(args)
            }
        }

        unsafe impl<U, M> Send for $mut<'_, U, M>
        where
            U: ?Sized + Send,
        {}
    };

    (fmt for $ref:ident: $($trait:ident),+;) => {
        delegate! {
            for $ref {$(
                fmt::$trait {
                    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result;
                }
            )+}
        }
    };

    ($($mut:tt $name:ident;)+) => { $(refs!($mut $name);)+ };
}

macro_rules! delegate {
    (for $ref:ident {$(
        $(#[$attr:meta])*
        $($($unsafet:literal)? unsafe)? $trait:ident $(::$trait2:ident)*$(<$($tlt:lifetime,)* $($tg:ident),*>)? $(where $($tcl:ty: $tcr:path,)+)? {$(
            type $td:ident;
        )*$(
            $($($unsafe:literal)? unsafe)? $(extern $abi:literal)? fn $fn:ident$(<$($lt:lifetime,)* $($g:ident),*>)?(&$($($mut:literal)? mut)? self$(, $arg:ident: $ty:ty)*) $(-> $ret:ty)? $(where $($fcl:ty: $fcr:path),+)?;
        )*}
    )+}) => {$(
        $(#[$attr])*
        $($($unsafet)? unsafe)? impl<$($($tlt,)*)? U, M $($(, $tg)*)?> $trait$(::$trait2)*$(<$($tlt,)* $($tg),*>)? for $ref<'_, U, M>
        where
            U: ?Sized + $trait$(::$trait2)*$(<$($tlt,)* $($tg),*>)?,
            M: Copy + TryInto<Metadata<U>>,
            $($($tcl: $tcr,)+)?
        {$(
            type $td = U::$td;
        )*$(
            #[inline(always)]
            $($($unsafe)? unsafe)? $(extern $abi)? fn $fn$(<$($lt,)* $($g),*>)?(&$($($mut)? mut)? self$(, $arg: $ty)*) $(-> $ret)?
            $(where $(
                $fcl: $fcr,
            )+)? {
                (**self).$fn($($arg),*)
            }
        )*}
    )+};
}

refs! {
    const ThinRef;
    mut ThinMut;
}

impl<T, U> Thinnable<T, U>
where
    T: Unsize<U>,
    U: ?Sized,
{
    #[inline(always)]
    pub fn new(data: T) -> Self {
        Self::try_new(data).unwrap()
    }
}

impl<T, U, M> Thinnable<T, U, M>
where
    T: Unsize<U>,
    U: ?Sized,
    Metadata<U>: TryInto<M>,
{
    #[inline(always)]
    pub fn try_new(data: T) -> Result<Self, MetadataConversionFailure<U, M>> {
        let metadata = ptr::metadata(&data as &U).try_into()?;
        Ok(Self {
            real: mem::ManuallyDrop::new(Real { metadata, data }),
        })
    }
}

impl<T, U, M> Thinnable<T, U, M>
where
    U: ?Sized,
{
    #[inline(always)]
    pub fn as_thin_ref(&self) -> ThinRef<U, M> {
        ThinRef(unsafe { &*self.fake })
    }

    #[inline(always)]
    pub fn as_thin_mut(&mut self) -> ThinMut<U, M> {
        ThinMut(unsafe { &mut *self.fake })
    }

    #[inline(always)]
    pub fn into_inner(mut self) -> T {
        unsafe { mem::ManuallyDrop::take(&mut self.real) }.data
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

impl<T, U> Thinnable<T, U>
where
    U: ?Sized,
{
    #[inline(always)]
    pub fn cast<V>(self) -> Thinnable<T, V>
    where
        T: Unsize<V>,
        V: ?Sized + ptr::Pointee<Metadata = Metadata<U>>,
    {
        self.try_cast().unwrap()
    }
}

impl<T, U, M> AsRef<T> for Thinnable<T, U, M>
where
    U: ?Sized,
{
    fn as_ref(&self) -> &T {
        unsafe { &self.real.data }
    }
}

impl<T, U, M> AsMut<T> for Thinnable<T, U, M>
where
    U: ?Sized,
{
    fn as_mut(&mut self) -> &mut T {
        unsafe { &mut self.real.data }
    }
}
