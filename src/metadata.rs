use core::{
    convert::TryInto,
    marker::{PhantomData, Unsize},
    ptr,
};

pub type Metadata<U> = <U as ptr::Pointee>::Metadata;

/// A failure on conversion of DST `U`'s metadata to type `M`.
pub type MetadataCreationFailure<U, M> = <Metadata<U> as TryInto<M>>::Error;
pub type MetadataConversionFailure<M, N> = <M as TryInto<N>>::Error;
pub type MetadataRecoveryFailure<U, M> = <M as TryInto<Metadata<U>>>::Error;

pub(crate) struct MetadataFor<U: ?Sized, M> {
    for_type: PhantomData<U>,
    metadata: M,
}

impl<U, M> MetadataFor<U, M>
where
    U: ?Sized,
{
    #[inline(always)]
    pub fn try_new<T: Unsize<U>>(data: &T) -> Result<Self, MetadataCreationFailure<U, M>>
    where
        Metadata<U>: TryInto<M>,
    {
        Ok(Self {
            for_type: PhantomData,
            metadata: ptr::metadata(data as &U).try_into()?,
        })
    }

    #[inline(always)]
    pub fn try_get(&self) -> Result<Metadata<U>, MetadataRecoveryFailure<U, M>>
    where
        M: Copy + TryInto<Metadata<U>>,
    {
        self.metadata.try_into()
    }

    #[inline(always)]
    pub fn try_convert<N>(self) -> Result<MetadataFor<U, N>, MetadataConversionFailure<M, N>>
    where
        M: TryInto<N>,
    {
        let Self { for_type, metadata } = self;
        metadata
            .try_into()
            .map(|metadata| MetadataFor { for_type, metadata })
    }
}
