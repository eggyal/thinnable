use core::{
    convert::TryInto,
    marker::Unsize,
    ops::{Deref, DerefMut},
};

use crate::metadata::{Metadata, MetadataCreationFailure, MetadataFor};

#[repr(C)]
pub(crate) struct Real<T, U, M>
where
    T: ?Sized,
    U: ?Sized,
{
    metadata: MetadataFor<U, M>,
    data: T,
}

impl<T, U, M> Real<T, U, M>
where
    U: ?Sized,
{
    #[inline(always)]
    pub fn try_new(data: T) -> Result<Self, MetadataCreationFailure<U, M>>
    where
        T: Unsize<U>,
        Metadata<U>: TryInto<M>,
    {
        MetadataFor::try_new(&data).map(|metadata| Self { metadata, data })
    }

    /// Obtain the metadata for the DST wrapper.
    ///
    /// ### Panics
    /// This method will panic if `metadata` contains a value that cannot be
    /// converted to a `Metadata<U>`.
    #[inline(always)]
    pub fn metadata(&self) -> Metadata<U>
    where
        M: Copy + TryInto<Metadata<U>>,
    {
        self.metadata.try_get().ok().unwrap()
    }

    #[inline(always)]
    pub fn into_inner(self) -> T {
        self.data
    }
}

impl<T, U, M> Deref for Real<T, U, M>
where
    T: ?Sized,
    U: ?Sized,
{
    type Target = T;
    #[inline(always)]
    fn deref(&self) -> &T {
        &self.data
    }
}

impl<T, U, M> DerefMut for Real<T, U, M>
where
    T: ?Sized,
    U: ?Sized,
{
    #[inline(always)]
    fn deref_mut(&mut self) -> &mut T {
        &mut self.data
    }
}

#[allow(unsafe_code)]
mod fake {
    use super::{Deref, DerefMut, Metadata, Real, TryInto};
    use core::{marker::PhantomData, ptr};

    #[repr(transparent)]
    pub(crate) struct Fake<U: ?Sized, M>(Real<PhantomData<U>, U, M>);

    /// Obtain the metadata for the DST wrapper.
    ///
    /// ### Panics
    /// This method will panic if `fake.0` contains metadata that cannot be
    /// converted to a `Metadata<U>`.
    #[inline(always)]
    fn metadata<U, M>(fake: &Fake<U, M>) -> Metadata<Real<U, U, M>>
    where
        U: ?Sized,
        M: Copy + TryInto<Metadata<U>>,
    {
        let metadata = fake.0.metadata();

        // The metadata of `Real<U, _, _>` is that of its last field, `data`,
        // which has type `U`.
        //
        // `Metadata<U>` and `Metadata<Real<U, _, _>>` are therefore the same,
        // but we cannot inform the compiler of this without publicly exposing
        // `Real`; likewise for adding constraints that would enable safe
        // conversion (such as `Metadata<U>: Into<Metadata<Real<U, M>>>`).
        //
        // Instead, we simply dereference a casted raw pointer, which is
        // perfectly safe because the types are necessarily identical.
        let ptr = ptr::addr_of!(metadata).cast();
        unsafe { *ptr }
    }

    impl<U, M> Deref for Fake<U, M>
    where
        U: ?Sized,
        M: Copy + TryInto<Metadata<U>>,
    {
        type Target = Real<U, U, M>;
        #[inline(always)]
        fn deref(&self) -> &Real<U, U, M> {
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
        fn deref_mut(&mut self) -> &mut Real<U, U, M> {
            let data_address = ptr::addr_of_mut!(self.0).cast();
            let metadata = metadata(self);
            let ptr = ptr::from_raw_parts_mut(data_address, metadata);
            unsafe { &mut *ptr }
        }
    }

    impl<T, U: ?Sized, M> AsRef<Fake<U, M>> for Real<T, U, M> {
        #[inline(always)]
        fn as_ref(&self) -> &Fake<U, M> {
            let ptr = (self as *const Self).cast();
            unsafe { &*ptr }
        }
    }

    impl<T, U: ?Sized, M> AsMut<Fake<U, M>> for Real<T, U, M> {
        #[inline(always)]
        fn as_mut(&mut self) -> &mut Fake<U, M> {
            let ptr = (self as *mut Self).cast();
            unsafe { &mut *ptr }
        }
    }
}

pub(crate) use fake::Fake;
