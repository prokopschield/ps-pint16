#[repr(transparent)]
#[derive(Clone, Copy, Debug, Default, Hash, PartialEq, Eq, PartialOrd, Ord)]
pub struct PackedInt {
    inner: u16,
}

macro_rules! impl_from_type {
    ($type:ty, $name:ident) => {
        pub fn $name(mut value: $type) -> Self {
            let mut prefix = 0u16;

            while value > 0x1ff {
                prefix += 1;
                value += 1;
                value >>= 1;
            }

            return Self {
                inner: (prefix << 8) + (value as u16),
            };
        }
    };
}

macro_rules! impl_into_type {
    ($type:ty, $name:ident) => {
        pub fn $name(&self) -> $type {
            let prefix = (self.inner >> 8) as $type;
            let suffix = (self.inner & 0xff) as $type;

            if prefix == 0 {
                suffix
            } else {
                (1 << (7 + prefix)) | (suffix << (prefix - 1))
            }
        }
    };
}

macro_rules! impl_traits {
    ($type:ty, $from:ident, $into:ident) => {
        impl From<$type> for PackedInt {
            fn from(value: $type) -> Self {
                Self::$from(value)
            }
        }

        impl From<PackedInt> for $type {
            fn from(packed: PackedInt) -> $type {
                packed.$into()
            }
        }
    };
}

impl PackedInt {
    pub fn from_12_bits(bits: &[u8; 2]) -> Self {
        Self {
            inner: ((bits[1] as u16) << 4) | (bits[0] as u16),
        }
    }

    pub fn to_12_bits(&self) -> [u8; 2] {
        [self.inner as u8, 0xF0 & (self.inner >> 4) as u8]
    }

    pub fn from_16_bits(bits: &[u8; 2]) -> Self {
        Self {
            inner: u16::from_le_bytes(*bits),
        }
    }

    pub fn to_16_bits(&self) -> [u8; 2] {
        self.inner.to_le_bytes()
    }

    pub fn from_inner_u16(inner: u16) -> Self {
        Self { inner }
    }

    pub fn to_inner_u16(&self) -> u16 {
        self.inner
    }

    impl_from_type!(usize, from_usize);
    impl_from_type!(u128, from_u128);
    impl_from_type!(u64, from_u64);
    impl_from_type!(u32, from_u32);
    impl_from_type!(u16, from_u16);

    impl_into_type!(usize, to_usize);
    impl_into_type!(u128, to_u128);
    impl_into_type!(u64, to_u64);
    impl_into_type!(u32, to_u32);
    impl_into_type!(u16, to_u16);
}

impl_traits!(usize, from_usize, to_usize);
impl_traits!(u128, from_u128, to_u128);
impl_traits!(u64, from_u64, to_u64);
impl_traits!(u32, from_u32, to_u32);

#[cfg(test)]
mod tests {
    use crate::*;

    #[test]
    pub fn test_int_packing() {
        let check = |value| {
            let packed = PackedInt::from_u64(value);
            let unpacked = packed.to_u64();
            assert_eq!(value, unpacked);
        };

        for value in 0..512 {
            for shift in 0..64 {
                check(value << shift)
            }
        }

        for inner in 0..0x3900 {
            check((PackedInt { inner }).to_u64())
        }
    }
}
