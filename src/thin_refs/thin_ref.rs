use core::{
    borrow::Borrow,
    cmp,
    convert::TryInto,
    fmt,
    hash::{Hash, Hasher},
    ops::Deref,
};

use crate::{Fake, Metadata};

/// A "thin" shared DST reference, analogue of `&U` (but only one pointer-width
/// in size).
pub struct ThinRef<'a, U: ?Sized, M = Metadata<U>>(&'a Fake<U, M>);

impl<'a, U, M> ThinRef<'a, U, M>
where
    U: ?Sized,
{
    pub(crate) fn new(r: &'a Fake<U, M>) -> Self {
        Self(r)
    }
}

impl<U, M> Clone for ThinRef<'_, U, M>
where
    U: ?Sized,
{
    fn clone(&self) -> Self {
        Self(self.0)
    }
}

impl<U, M> Copy for ThinRef<'_, U, M> where U: ?Sized {}

#[cfg(feature = "fn-refs")]
impl<Args, U, M> FnMut<Args> for ThinRef<'_, U, M>
where
    U: ?Sized + Fn<Args>,
    M: Copy + TryInto<Metadata<U>>,
{
    #[inline(always)]
    extern "rust-call" fn call_mut(&mut self, args: Args) -> U::Output {
        (**self).call(args)
    }
}

#[cfg(feature = "fn-refs")]
impl<Args, U, M> FnOnce<Args> for ThinRef<'_, U, M>
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
    for ThinRef {
        #[cfg(feature = "fn-refs")]
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

impl_common_ref_traits_for!(ThinRef);
