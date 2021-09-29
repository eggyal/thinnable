macro_rules! delegate {
    (for $ref:ident {$(
        $(#[$attr:meta])*
        $trait:ident $(::$trait2:ident)*$(<$($tlt:lifetime,)* $($tg:ident),*>)? $(where $($tcl:ty: $tcr:path,)+)? {$(
            type $td:ident;
        )*$(
            $(extern $abi:literal)? fn $fn:ident$(<$($lt:lifetime,)* $($g:ident),*>)?(&$($($mut:literal)? mut)? self$(, $arg:ident: $ty:ty)*) $(-> $ret:ty)? $(where $($fcl:ty: $fcr:path),+)?;
        )*}
    )+}) => {$(
        $(#[$attr])*
        impl<$($($tlt,)*)? U, M $($(, $tg)*)?> $trait$(::$trait2)*$(<$($tlt,)* $($tg),*>)? for $ref<'_, U, M>
        where
            U: ?Sized + $trait$(::$trait2)*$(<$($tlt,)* $($tg),*>)?,
            M: Copy + TryInto<Metadata<U>>,
            $($($tcl: $tcr,)+)?
        {$(
            type $td = U::$td;
        )*$(
            #[inline(always)]
            $(extern $abi)? fn $fn$(<$($lt,)* $($g),*>)?(&$($($mut)? mut)? self$(, $arg: $ty)*) $(-> $ret)?
            $(where $(
                $fcl: $fcr,
            )+)? {
                (**self).$fn($($arg),*)
            }
        )*}
    )+};
}

macro_rules! impl_common_ref_traits_for {
    ($ref:ident) => {
        impl<U, M> Borrow<U> for $ref<'_, U, M>
        where
            U: ?Sized,
            M: Copy + TryInto<Metadata<U>>,
        {
            #[inline(always)]
            fn borrow(&self) -> &U {
                self.0
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

        impl_common_ref_traits_for! {
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

    (fmt for $ref:ident: $($trait:ident),+;) => {
        delegate! {
            for $ref {$(
                fmt::$trait {
                    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result;
                }
            )+}
        }
    };
}

mod thin_mut;
mod thin_ref;

pub use thin_mut::ThinMut;
pub use thin_ref::ThinRef;
