#[macro_export]
macro_rules! wrapper_type {
    ($N:ident, $T:ty) => {
        #[derive(Clone, PartialEq, Eq, Hash)]
        pub struct $N(pub $T);

        impl std::ops::Deref for $N {
            type Target = $T;

            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }

        impl $crate::traits::Repr for $N {
            type T = $T;

            fn repr(&self) -> &$T {
                &self.0
            }
        }

        impl From<$T> for $N {
            fn from(x: $T) -> Self {
                Self(x)
            }
        }

        impl std::fmt::Display for $N {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                std::fmt::Display::fmt(&self.0, f)
            }
        }

        impl std::fmt::Debug for $N {
            fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
                std::fmt::Debug::fmt(&self.0, f)
            }
        }
    };
}
