use core::{
    convert::TryInto,
    marker::PhantomData,
    ops::{Deref, DerefMut},
    ptr,
};

use crate::Metadata;

#[repr(C)]
pub(crate) struct Real<T, M>
where
    T: ?Sized,
{
    pub metadata: M,
    pub data: T,
}

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

#[repr(transparent)]
pub(crate) struct Fake<U: ?Sized, M>(Real<PhantomData<U>, M>);

/// Obtain the metadata for the DST wrapper.
///
/// ### Panics
/// This method will panic if `fake.0.metadata` contains a value
/// that cannot be converted to a `Metadata<U>`.
#[inline(always)]
fn metadata<U, M>(fake: &Fake<U, M>) -> Metadata<Real<U, M>>
where
    U: ?Sized,
    M: Copy + TryInto<Metadata<U>>,
{
    let metadata = fake
        .0
        .metadata
        .try_into()
        .ok()
        .expect("not a valid metadata value");

    // The metadata of `Real<U, _>` is that of its last field, `data`,
    // which has type `U`.
    //
    // `Metadata<U>` and `Metadata<Real<U, _>>` are therefore the same,
    // but we cannot inform the compiler of this without publicly exposing
    // `Unsized`; likewise for adding constraints that would enable safe
    // conversion (such as `Metadata<U>: Into<Metadata<Real<U, M>>>`).
    //
    // Instead, we simply dereference a casted raw pointer, which is
    // perfectly safe because the types are necessarily identical.
    unsafe { *ptr::addr_of!(metadata).cast() }
}

impl<U, M> Deref for Fake<U, M>
where
    U: ?Sized,
    M: Copy + TryInto<Metadata<U>>,
{
    type Target = Real<U, M>;
    #[inline(always)]
    fn deref(&self) -> &Real<U, M> {
        let data_address = ptr::addr_of!(self.0).cast();
        let metadata = metadata(self);
        let ptr = ptr::from_raw_parts(data_address, metadata);
        unsafe { &*ptr }
    }
}

impl<U, M> DerefMut for Fake<U, M>
where
    U: ?Sized,
    M: Copy + TryInto<Metadata<U>>,
{
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut Real<U, M> {
        let data_address = ptr::addr_of_mut!(self.0).cast();
        let metadata = metadata(self);
        let ptr = ptr::from_raw_parts_mut(data_address, metadata);
        unsafe { &mut *ptr }
    }
}

impl<T, U: ?Sized, M> AsRef<Fake<U, M>> for Real<T, M> {
    #[inline(always)]
    fn as_ref(&self) -> &Fake<U, M> {
        unsafe { &*(self as *const Self).cast() }
    }
}

impl<T, U: ?Sized, M> AsMut<Fake<U, M>> for Real<T, M> {
    #[inline(always)]
    fn as_mut(&mut self) -> &mut Fake<U, M> {
        unsafe { &mut *(self as *mut Self).cast() }
    }
}
