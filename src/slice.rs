use crate::{MetadataCreationFailure, Thinnable};
use core::convert::{TryFrom, TryInto};

/// Marker trait for types that can safely be converted from/to slice metadata.
///
/// This trait really only exists as a means of defining the metadata types for
/// which [`ThinnableSlice::try_slice`] is available.
///
/// # Safety
/// If `<M as SliceLength>::try_from(in).and_then(TryInto::try_into)` returns
/// `Ok(out)`, then dereferencing a [`ThinRef`][crate::ThinRef] or
/// [`ThinMut`][crate::ThinMut] of a [`ThinnableSlice`] using `M` metadata is
/// undefined behavior unless `in` and `out` are bitwise identical.
///
/// That is to say, implementations are responsible for ensuring that metadata
/// conversion between `Self` and `usize` either fails, or produces reversible
/// results.
pub unsafe trait SliceLength: Sized + TryFrom<usize> + TryInto<usize> {}

/// Convenient alias for slices.
pub type ThinnableSlice<T, M, const N: usize> = Thinnable<[T; N], [T], M>;

impl<T, M: SliceLength, const N: usize> ThinnableSlice<T, M, N> {
    /// Create a new `ThinnableSlice` for the given `data`, embedding the
    /// metadata for `[T]` (that is to say, its length `N`) converted to `M`.
    ///
    /// This is a specialized version of [`try_new`][`Self::try_new`] that
    /// defers responsibility for upholding its safety guarantees to
    /// implementations of the [`SliceLength`] marker trait.
    #[inline(always)]
    pub fn try_slice(data: [T; N]) -> Result<Self, MetadataCreationFailure<[T], M>> {
        unsafe { Self::try_new(data) }
    }
}

macro_rules! thinnable_slices {
    ($($alias:ident($ty:ty))+) => {$(
        #[doc = concat!("Convenient alias for slices with length stored in a `", stringify!($ty), "`.")]
        pub type $alias<T, const N: usize> = ThinnableSlice<T, $ty, N>;
        unsafe impl SliceLength for $ty {}
    )+};
}

thinnable_slices! {
    ThinnableSliceU8(u8)
    ThinnableSliceU16(u16)
    ThinnableSliceU32(u32)
}
