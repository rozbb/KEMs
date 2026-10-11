use array::{
    Array, Flatten, Unflatten,
    typenum::{Gcd, Gcf, Prod, Quot, U0, U8, U32, U256, Unsigned},
};
use core::fmt::Debug;
use core::ops::{Div, Mul, Rem};
use num_traits::One;

use super::algebra::{Elem, Field, NttPolynomial, NttVector, Polynomial, Vector};
use super::truncate::Truncate;

/// An array length with other useful properties
pub trait ArraySize: array::ArraySize + PartialEq + Debug {}

impl<T> ArraySize for T where T: array::ArraySize + PartialEq + Debug {}

/// An integer that can describe encoded polynomials.
pub trait EncodingSize: ArraySize {
    /// Size of an encoded polynomial.
    type EncodedPolynomialSize: ArraySize;
    /// Value step.
    type ValueStep: ArraySize;
    /// Byte step.
    type ByteStep: ArraySize;
}

type EncodingUnit<D> = Quot<Prod<D, U8>, Gcf<D, U8>>;

/// Size of an encoded polynomial.
pub type EncodedPolynomialSize<D> = <D as EncodingSize>::EncodedPolynomialSize;
/// Encoded polynomial.
pub type EncodedPolynomial<D> = Array<u8, EncodedPolynomialSize<D>>;

impl<D> EncodingSize for D
where
    D: ArraySize + Mul<U8> + Gcd<U8> + Mul<U32>,
    Prod<D, U32>: ArraySize,
    Prod<D, U8>: Div<Gcf<D, U8>>,
    EncodingUnit<D>: Div<D> + Div<U8>,
    Quot<EncodingUnit<D>, D>: ArraySize,
    Quot<EncodingUnit<D>, U8>: ArraySize,
{
    type EncodedPolynomialSize = Prod<D, U32>;
    type ValueStep = Quot<EncodingUnit<D>, D>;
    type ByteStep = Quot<EncodingUnit<D>, U8>;
}

/// Decoded value.
pub type DecodedValue<F> = Array<Elem<F>, U256>;

/// An integer that can describe encoded vectors.
pub trait VectorEncodingSize<K>: EncodingSize
where
    K: ArraySize,
{
    /// Size of an encoded vector.
    type EncodedVectorSize: ArraySize;

    /// Flatten encoded polynomial array into encoded vector.
    fn flatten(polys: Array<EncodedPolynomial<Self>, K>) -> EncodedVector<Self, K>;
    /// Unflatten encoded vector into encoded polynomial array.
    fn unflatten(vec: &EncodedVector<Self, K>) -> Array<&EncodedPolynomial<Self>, K>;
}

/// Size of an encoded vector.
pub type EncodedVectorSize<D, K> = <D as VectorEncodingSize<K>>::EncodedVectorSize;
/// Encoded vector.
pub type EncodedVector<D, K> = Array<u8, EncodedVectorSize<D, K>>;

impl<D, K> VectorEncodingSize<K> for D
where
    D: EncodingSize,
    K: ArraySize,
    D::EncodedPolynomialSize: Mul<K>,
    Prod<D::EncodedPolynomialSize, K>:
        ArraySize + Div<K, Output = D::EncodedPolynomialSize> + Rem<K, Output = U0>,
{
    type EncodedVectorSize = Prod<D::EncodedPolynomialSize, K>;

    fn flatten(polys: Array<EncodedPolynomial<Self>, K>) -> EncodedVector<Self, K> {
        polys.flatten()
    }

    fn unflatten(vec: &EncodedVector<Self, K>) -> Array<&EncodedPolynomial<Self>, K> {
        vec.unflatten()
    }
}

/// Packs the `D::ValueStep` values starting at `start` into a little-endian integer.
fn pack_chunk<F: Field, D: EncodingSize>(vals: &DecodedValue<F>, start: usize) -> u128 {
    let mut x = 0u128;
    for j in 0..D::ValueStep::USIZE {
        let vj: u128 = vals[start + j].0.into();
        x |= vj << (D::USIZE * j);
    }
    x
}

/// Reads the `D::ByteStep` bytes starting at `start` as a little-endian integer.
fn unpack_chunk<D: EncodingSize>(bytes: &EncodedPolynomial<D>, start: usize) -> u128 {
    let mut xb = [0u8; 16];
    for k in 0..D::ByteStep::USIZE {
        xb[k] = bytes[start + k];
    }
    u128::from_le_bytes(xb)
}

/// FIPS 203: Algorithm 4 `ByteEncode_d`.
/// FIPS 204: Algorithm 16 `SimpleBitPack`.
#[allow(clippy::integer_division_remainder_used, reason = "public values")]
pub fn byte_encode<F: Field, D: EncodingSize>(vals: &DecodedValue<F>) -> EncodedPolynomial<D> {
    let val_step = D::ValueStep::USIZE;
    let byte_step = D::ByteStep::USIZE;

    let mut bytes = EncodedPolynomial::<D>::default();
    for c in 0..256 / val_step {
        let xb = pack_chunk::<F, D>(vals, c * val_step).to_le_bytes();
        for k in 0..byte_step {
            bytes[c * byte_step + k] = xb[k];
        }
    }
    bytes
}

/// FIPS 203: Algorithm 5 `ByteDecode_d(F)`
/// FIPS 204: Algorithm 18 `SimpleBitUnpack`
#[allow(clippy::integer_division_remainder_used, reason = "public values")]
pub fn byte_decode<F: Field, D: EncodingSize>(bytes: &EncodedPolynomial<D>) -> DecodedValue<F> {
    let val_step = D::ValueStep::USIZE;
    let byte_step = D::ByteStep::USIZE;
    let mask = (F::Int::one() << D::USIZE) - F::Int::one();

    let mut vals = DecodedValue::default();
    for c in 0..256 / val_step {
        let x = unpack_chunk::<D>(bytes, c * byte_step);
        for j in 0..val_step {
            let val = F::Int::truncate(x >> (D::USIZE * j));
            let mut v = val & mask;
            if D::USIZE == 12 {
                v = F::small_reduce(v);
            }
            vals[c * val_step + j].0 = v;
        }
    }
    vals
}

/// Encoding trait.
pub trait Encode<D: EncodingSize> {
    /// Size of the encoded object.
    type EncodedSize: ArraySize;
    /// Encode object.
    fn encode(&self) -> Array<u8, Self::EncodedSize>;
    /// Decode object.
    fn decode(enc: &Array<u8, Self::EncodedSize>) -> Self;
}

impl<F: Field, D: EncodingSize> Encode<D> for Polynomial<F> {
    type EncodedSize = D::EncodedPolynomialSize;

    fn encode(&self) -> Array<u8, Self::EncodedSize> {
        byte_encode::<F, D>(&self.0)
    }

    fn decode(enc: &Array<u8, Self::EncodedSize>) -> Self {
        Self(byte_decode::<F, D>(enc))
    }
}

impl<F, D, K> Encode<D> for Vector<F, K>
where
    F: Field,
    K: ArraySize,
    D: VectorEncodingSize<K>,
{
    type EncodedSize = D::EncodedVectorSize;

    fn encode(&self) -> Array<u8, Self::EncodedSize> {
        let mut polys = Array::<EncodedPolynomial<D>, K>::default();
        for i in 0..polys.len() {
            polys[i] = Encode::<D>::encode(&self.0[i]);
        }
        <D as VectorEncodingSize<K>>::flatten(polys)
    }

    fn decode(enc: &Array<u8, Self::EncodedSize>) -> Self {
        let n = D::EncodedPolynomialSize::USIZE;
        let mut out = Self(Array::default());
        for i in 0..out.0.len() {
            #[allow(deprecated, reason = "the `TryFrom` replacement is fallible")]
            let x = EncodedPolynomial::<D>::from_slice(&enc[i * n..(i + 1) * n]);
            out.0[i] = <Polynomial<F> as Encode<D>>::decode(x);
        }
        out
    }
}

impl<F: Field, D: EncodingSize> Encode<D> for NttPolynomial<F> {
    type EncodedSize = D::EncodedPolynomialSize;

    fn encode(&self) -> Array<u8, Self::EncodedSize> {
        byte_encode::<F, D>(&self.0)
    }

    fn decode(enc: &Array<u8, Self::EncodedSize>) -> Self {
        Self(byte_decode::<F, D>(enc))
    }
}

impl<F, D, K> Encode<D> for NttVector<F, K>
where
    F: Field,
    D: VectorEncodingSize<K>,
    K: ArraySize,
{
    type EncodedSize = D::EncodedVectorSize;

    fn encode(&self) -> Array<u8, Self::EncodedSize> {
        let mut polys = Array::<EncodedPolynomial<D>, K>::default();
        for i in 0..polys.len() {
            polys[i] = Encode::<D>::encode(&self.0[i]);
        }
        <D as VectorEncodingSize<K>>::flatten(polys)
    }

    fn decode(enc: &Array<u8, Self::EncodedSize>) -> Self {
        let n = D::EncodedPolynomialSize::USIZE;
        let mut out = Self(Array::default());
        for i in 0..out.0.len() {
            #[allow(deprecated, reason = "the `TryFrom` replacement is fallible")]
            let x = EncodedPolynomial::<D>::from_slice(&enc[i * n..(i + 1) * n]);
            out.0[i] = <NttPolynomial<F> as Encode<D>>::decode(x);
        }
        out
    }
}
