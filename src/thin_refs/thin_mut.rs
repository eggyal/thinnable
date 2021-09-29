use core::{
    borrow::{Borrow, BorrowMut},
    cmp,
    convert::TryInto,
    fmt,
    hash::{Hash, Hasher},
    ops::{Deref, DerefMut},
};

use crate::{Fake, Metadata};

/// A "thin" exclusive DST reference, analogue of `&mut U`.
pub struct ThinMut<'a, U: ?Sized, M = Metadata<U>>(&'a mut Fake<U, M>);

impl<'a, U, M> ThinMut<'a, U, M>
where
    U: ?Sized,
{
    pub(crate) fn new(r: &'a mut Fake<U, M>) -> Self {
        Self(r)
    }
}

impl<U, M> BorrowMut<U> for ThinMut<'_, U, M>
where
    U: ?Sized,
    M: Copy + TryInto<Metadata<U>>,
{
    #[inline(always)]
    fn borrow_mut(&mut self) -> &mut U {
        self.0
    }
}

impl<U, M> DerefMut for ThinMut<'_, U, M>
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
    for ThinMut {
        #[cfg(feature = "fn-refs")]
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

impl<T, U, M> AsMut<T> for ThinMut<'_, U, M>
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

#[cfg(feature = "fn-refs")]
impl<Args, U, M> FnOnce<Args> for ThinMut<'_, U, M>
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

impl_common_ref_traits_for!(ThinMut);
