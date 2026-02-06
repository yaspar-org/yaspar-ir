use crate::allocator::StrAllocator;
use crate::ast::{HasArenaAlt, Str};

/// A unifying trait to pull content from a wrapper type
///
/// This trait is an interface to accommodate different libraries.
pub trait Contains {
    type T: ?Sized;
    fn inner(&self) -> &Self::T;
}

impl<T> Contains for &T {
    type T = T;

    #[inline]
    fn inner(&self) -> &Self::T {
        self
    }
}

/// implement this trait if there exists some meta-data for `Self`
pub trait MetaData {
    type T: ?Sized;
    /// the meta-data itself
    fn meta_data(&self) -> &Self::T;

    /// display the meta-data
    fn display_meta_data(&self) -> String;
}

/// a unifying trait to obtain the representation of a wrapped enum
pub trait Repr {
    type T;
    fn repr(&self) -> &Self::T;
}

/// a trait that represents an object that can be allocated as `Out` using some environment
pub trait Allocatable<Env> {
    type Out;

    fn allocate(&self, env: &mut Env) -> Self::Out;
}

impl Contains for str {
    type T = str;

    #[inline]
    fn inner(&self) -> &Self::T {
        self
    }
}

impl MetaData for &str {
    type T = &'static str;

    #[inline]
    fn meta_data(&self) -> &Self::T {
        &""
    }

    fn display_meta_data(&self) -> String {
        "".into()
    }
}

impl<Env: HasArenaAlt> Allocatable<Env> for &str {
    type Out = Str;

    #[inline]
    fn allocate(&self, env: &mut Env) -> Self::Out {
        env.arena_alt().allocate_symbol(self)
    }
}

impl Contains for String {
    type T = str;

    #[inline]
    fn inner(&self) -> &Self::T {
        self
    }
}

impl MetaData for String {
    type T = &'static str;

    #[inline]
    fn meta_data(&self) -> &Self::T {
        &""
    }

    fn display_meta_data(&self) -> String {
        "".into()
    }
}

impl<Env: HasArenaAlt> Allocatable<Env> for String {
    type Out = Str;

    #[inline]
    fn allocate(&self, env: &mut Env) -> Self::Out {
        env.arena_alt().allocate_symbol(self)
    }
}

impl<T> MetaData for &T
where
    T: MetaData,
{
    type T = T::T;

    fn meta_data(&self) -> &Self::T {
        (*self).meta_data()
    }

    fn display_meta_data(&self) -> String {
        (*self).display_meta_data()
    }
}

impl<Env, T> Allocatable<Env> for &T
where
    T: Allocatable<Env>,
{
    type Out = T::Out;

    fn allocate(&self, env: &mut Env) -> Self::Out {
        (*self).allocate(env)
    }
}

/// This is the trait that captures a string with meta-data so that we can feed in
/// different representations of strings to APIs.
///
/// It can be used to allocate a symbol in some environment (usually a [crate::ast::Arena]).
///
/// It has the following impls:
/// * &str
/// * String
/// * Str
/// * u::Str (this one incldues non-trivial location information from the inputs)
pub trait AllocatableString<Env>: Allocatable<Env, Out = Str> + MetaData {}

impl<Env, T> AllocatableString<Env> for T where T: Allocatable<Env, Out = Str> + MetaData {}
