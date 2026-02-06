use crate::traits::MetaData;
use std::fmt::{Debug, Display, Formatter};

/// A struct that associate a piece of meta-data with a piece of data
#[derive(Clone, PartialEq, Eq, Hash)]
pub(crate) struct WithMeta<A, B> {
    pub(crate) data: A,
    pub(crate) meta: B,
}

impl<A, B> WithMeta<A, B> {
    pub(crate) fn new(data: A, meta: B) -> Self {
        Self { data, meta }
    }
}

impl<A> WithMeta<A, String> {
    pub(crate) fn empty_meta(data: A) -> Self {
        Self::new(data, "".into())
    }
}

impl<A, B> MetaData for WithMeta<A, B>
where
    B: Display,
{
    type T = B;

    fn meta_data(&self) -> &Self::T {
        &self.meta
    }

    fn display_meta_data(&self) -> String {
        self.meta_data().to_string()
    }
}

impl<A, B> Display for WithMeta<A, B>
where
    A: Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(&self.data, f)
    }
}

impl<A, B> Debug for WithMeta<A, B>
where
    A: Debug,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Debug::fmt(&self.data, f)
    }
}
