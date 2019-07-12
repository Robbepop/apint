// A note about the insane amount of cloning here: a lot of this is just unrelated one time
// assertions and we do not want potential invariant bugs to propagate down a long sequence.
// The insane amount of unwrapping is done here instead of returning `Result<(), Error>` from all
// the functions, because it removes the ability to see what line an error came from.

#[cfg(test)]
mod tests {
    use crate::data::ApInt;
    use crate::info::BitWidth;

    mod general_regressions {
        use super::*;
        use std::u64;

        #[test]
        fn pull_request_35_regression() {
            let width = BitWidth::new(65).unwrap();
            //arithmetic shift right shift
            assert_eq!(
                ApInt::from([1u64, u64::MAX - (1 << 6)]).into_truncate(width).unwrap(),
                ApInt::from([1u64, u64::MAX - (1 << 10)]).into_truncate(width).unwrap()
                    .into_wrapping_ashr(4).unwrap()
            );
            //multiplication related
            let v1 = ApInt::from((1u128 << 64) | (7u128)).into_zero_resize(width);
            let v2 = ApInt::one(BitWidth::w1()).into_zero_extend(width).unwrap().into_wrapping_shl(64).unwrap();
            let v3 = v1.clone().into_wrapping_mul(&v2).unwrap();
            assert_eq!(v1, ApInt::from([1u64,7]).into_zero_resize(width));
            assert_eq!(v2, ApInt::from([1u64,0]).into_zero_resize(width));
            assert_eq!(v3, ApInt::from([1u64,0]).into_zero_resize(width));
            let width = BitWidth::new(193).unwrap();
            let v3 = ApInt::from([0u64, 0, 17179852800, 1073676288]).into_zero_resize(width).into_wrapping_mul(&ApInt::from(1u128 << 115).into_zero_resize(width)).unwrap();
            assert_eq!(v3, ApInt::from([0u64, 0, 17179852800, 1073676288]).into_wrapping_shl(115).unwrap().into_zero_resize(width));
        }
    }
    
    mod megafuzz {
        use super::*;
        use std::u64;
        use rand::random;

        //throws all the functions together for an identities party. If one function is incorrect,
        //the whole thing should break.
        fn identities_unary(size: usize, width: BitWidth, lhs: ApInt) {
            let shift = random::<usize>() % size;
            // basic addition and subtraction tests
            // subtracts one below and one above `lhs`
            let mut temp = lhs.clone().into_wrapping_inc();
            assert_eq!(temp, lhs.clone().into_wrapping_add(&ApInt::one(width)).unwrap());
            assert_eq!(temp, lhs.clone().into_wrapping_sub(&ApInt::all_set(width)).unwrap());
            temp.wrapping_dec();
            assert_eq!(temp, lhs);
            temp.wrapping_dec();
            assert_eq!(temp, lhs.clone().into_wrapping_sub(&ApInt::one(width)).unwrap());
            assert_eq!(temp, lhs.clone().into_wrapping_add(&ApInt::all_set(width)).unwrap());
            temp.wrapping_inc();
            assert_eq!(temp, lhs);
            
            // rotation tests
            let rotated_left = if shift == 0 {
                lhs.clone()
            } else {
                lhs.clone().into_wrapping_shl(shift).unwrap() | (&lhs.clone().into_wrapping_lshr(size - shift).unwrap())
            };
            assert_eq!(rotated_left, lhs.clone().into_rotate_left(shift).unwrap());
            let rotated_right = if shift == 0 {
                lhs.clone()
            } else {
                lhs.clone().into_wrapping_lshr(shift).unwrap() | (&lhs.clone().into_wrapping_shl(size - shift).unwrap())
            };
            assert_eq!(rotated_right, lhs.clone().into_rotate_right(shift).unwrap());

            // unsigned power of two multiplication shifting
            let mut tmp1 = ApInt::one(BitWidth::w1()).into_zero_extend(width).unwrap().into_wrapping_shl(shift).unwrap();
            assert_eq!(
                lhs.clone().into_wrapping_shl(shift).unwrap(),
                lhs.clone().into_wrapping_mul(&tmp1).unwrap()
            );

            // signed power of two multiplication shifting
            assert_eq!(
                lhs.clone().into_wrapping_neg().into_wrapping_shl(shift).unwrap(),
                lhs.clone().into_wrapping_mul(
                    &ApInt::one(BitWidth::w1()).into_sign_extend(width).unwrap().into_wrapping_shl(shift).unwrap()
                ).unwrap()
            );

            // unsigned power of two division shifting
            assert_eq!(
                lhs.clone().into_wrapping_lshr(shift).unwrap(),
                lhs.clone().into_wrapping_udiv(&tmp1).unwrap()
            );
            
            // signed power of two division shifting
            if (tmp1 == ApInt::signed_min_value(width)) && (lhs == ApInt::signed_min_value(width)) {
                // numerical corner case where the result of the shift is -1 but the division ends
                // up as +1
                assert_eq!(
                    lhs.clone().into_wrapping_ashr(shift).unwrap(),
                    ApInt::all_set(width)
                );
                assert_eq!(
                    lhs.clone().into_wrapping_sdiv(&tmp1).unwrap(),
                    ApInt::one(width)
                );
            } else {
                let mut tmp0 = lhs.clone();
                // make it a floored division, and note that `b` is set to `tmp0.is_negative()`
                // instead of `tmp0.is_negative() != tmp1.is_negative()` because of how the `tmp1`
                // division behaves at shift = width - 1
                let b = tmp0.is_negative();
                ApInt::wrapping_sdivrem_assign(&mut tmp0, &mut tmp1).unwrap();
                if b && !tmp1.is_zero() {
                    tmp0.wrapping_dec();
                }
                
                assert_eq!(tmp0, lhs.clone().into_wrapping_ashr(shift).unwrap());
            }
        }

        fn identities_binary(size: usize, width: BitWidth, zero: &ApInt, lhs: ApInt, rhs: ApInt, third: ApInt) {
            let rand_width = BitWidth::new((random::<usize>() % size) + 1).unwrap();
            let wrapping_add = lhs.clone().into_wrapping_add(&rhs).unwrap();

            //overflowing addition test
            let mut overflowing_uadd = lhs.clone();
            let uoverflow = overflowing_uadd.overflowing_uadd_assign(&rhs).unwrap();
            assert_eq!(wrapping_add, overflowing_uadd);
            if lhs.checked_uge(&rhs).unwrap() {
                assert_eq!(wrapping_add.checked_ult(&lhs).unwrap(), uoverflow);
            } else {
                assert_eq!(wrapping_add.checked_ult(&rhs).unwrap(), uoverflow);
            }

            let mut overflowing_sadd = lhs.clone();
            let soverflow = overflowing_sadd.overflowing_sadd_assign(&rhs).unwrap();
            assert_eq!(wrapping_add, overflowing_sadd);
            if lhs.is_negative() == rhs.is_negative() {
                assert!((overflowing_sadd.is_negative() != lhs.is_negative()) == soverflow);
            } else {
                assert!(!soverflow);
            }

            //wrapping multiplication test
            assert_eq!(
                lhs.clone().into_zero_extend(BitWidth::new(size * 2).unwrap()).unwrap()
                    .into_wrapping_mul(
                        &rhs.clone().into_zero_extend(BitWidth::new(size * 2).unwrap()).unwrap()
                    ).unwrap().into_zero_resize(rand_width),
                lhs.clone().into_wrapping_mul(&rhs).unwrap().into_zero_resize(rand_width)
            );
            //multiplication and division tests
            //the following tests that `((lhs * rhs) + (third % rhs)) / rhs == lhs` and
            //`((lhs * rhs) + (third % rhs)) % rhs == (third % rhs)`
            let tot_leading_zeros = lhs.leading_zeros() + rhs.leading_zeros();
            //this trims down `lhs` until overflow will not happen
            let anti_overflow_mask = if tot_leading_zeros < size {
                if rhs.leading_zeros() == 0 {
                    ApInt::zero(width)
                } else {
                    ApInt::one(BitWidth::w1()).into_sign_extend(rhs.leading_zeros()).unwrap().into_zero_extend(width).unwrap()
                }
            } else {
                ApInt::one(BitWidth::w1()).into_sign_extend(width).unwrap()
            };
            let mul = (lhs.clone() & &anti_overflow_mask).into_wrapping_mul(&rhs).unwrap();
            if rhs != *zero {
                let rem = third.clone().into_wrapping_urem(&rhs).unwrap();
                let mut temp0 = mul.clone();
                if !temp0.overflowing_uadd_assign(&rem).unwrap() {
                    let mut temp1 = rhs.clone();
                    let mul_plus_rem = temp0.clone();
                    ApInt::wrapping_udivrem_assign(&mut temp0, &mut temp1).unwrap();
                    if temp0 != (lhs.clone() & &anti_overflow_mask) {panic!("wrong div\nlhs:{:?}\nrhs:{:?}\nthird:{:?}\nrem:{:?}\nmul:{:?}\nmul_plus_rem:{:?}\ntemp0:{:?}\ntemp1:{:?}",(lhs.clone() & &anti_overflow_mask),rhs,third,rem,mul,mul_plus_rem,temp0,temp1)}
                    if temp1 != rem {panic!("wrong rem\nlhs:{:?}\nrhs:{:?}\nthird:{:?}\nrem:{:?}\nmul:{:?}\nmul_plus_rem:{:?}\ntemp0:{:?}\ntemp1:{:?}",(lhs.clone() & &anti_overflow_mask),rhs,third,rem,mul,mul_plus_rem,temp0,temp1)}
                }
            }
        }

        //random length AND, XOR, and OR fuzzer;
        fn fuzz_random(size: usize, iterations: usize) {
            let width = BitWidth::new(size).unwrap();
            let mut lhs = ApInt::from(0u64).into_zero_resize(width);
            let mut rhs = ApInt::from(0u64).into_zero_resize(width);
            let mut third = ApInt::from(0u64).into_zero_resize(width);
            let zero = ApInt::from(0u64).into_zero_resize(width);
            for _ in 0..iterations {
                //the `identities_` functions are very expensive so it makes sense to run this
                //multiple times to cover a larger space
                for _ in 0..12 {
                    let r0 =  random::<usize>() % size;
                    let r1 = random::<usize>() % size;
                    let mask = if r0 == 0 {
                        ApInt::zero(BitWidth::new(size).unwrap())
                    } else {
                        ApInt::one(BitWidth::new(1).unwrap())
                            .into_sign_extend(r0).unwrap()
                            .into_zero_extend(width).unwrap()
                            .into_rotate_left(r1).unwrap()
                    };
                    match random::<u8>() % 16 {
                        0 => lhs |= &mask,
                        1 => lhs &= &mask,
                        2 => lhs ^= &mask,
                        3 => lhs ^= &mask,
                        4 => rhs |= &mask,
                        5 => rhs &= &mask,
                        6 => rhs ^= &mask,
                        7 => rhs ^= &mask,
                        8 => third |= &mask,
                        9 => third &= &mask,
                        10 => third ^= &mask,
                        11 => third ^= &mask,
                        12 => rhs |= &mask,
                        13 => rhs &= &mask,
                        14 => rhs ^= &mask,
                        15 => rhs ^= &mask,
                        _ => unreachable!()
                    }
                }
                identities_unary(size, width, lhs.clone());
                identities_unary(size, width, rhs.clone());
                identities_unary(size, width, third.clone());
                identities_binary(size, width, &zero, lhs.clone(), rhs.clone(), third.clone());
                identities_binary(size, width, &zero, rhs.clone(), lhs.clone(), third.clone());
                identities_binary(size, width, &zero, lhs.clone(), lhs.clone(), rhs.clone());
            }
        }

        //named so because nesting this causes an explosion in testing time
        macro_rules! explode {
            ($cd:ident, $temp:ident, $i_zero:ident, $i_one:ident, $inner:tt) => {{
                for $i_zero in 0..(2usize.pow(($cd * 2) as u32)) {
                    let mut $temp: Vec<u64> = Vec::with_capacity($cd);
                    for $i_one in 0..$cd {
                        match ($i_zero >> ($i_one * 2)) & 0b11 {
                            0b0 => $temp.push(0),
                            0b1 => $temp.push(1),
                            0b10 => $temp.push(u64::MAX - 1),
                            0b11 => $temp.push(u64::MAX),
                            _ => unreachable!()
                        }
                    }
                    $inner
                }
            }}
        }

        //catch edge and corner cases involving 0, 1, Digit::MAX - 1, and Digit::MAX
        fn fuzz_edge_unary(size: usize) {
            let width = BitWidth::new(size).unwrap();
            let cd = 
                if (size % 64) == 0 {size / 64}
                else {(size / 64) + 1};
            explode!(cd,temp0,i0,i1,{
                identities_unary(size, width,
                    ApInt::from_vec_u64(temp0.clone()).unwrap().into_truncate(size).unwrap());
            })
        }

        fn fuzz_edge_binary(size: usize) {
            let width = BitWidth::new(size).unwrap();
            let zero = ApInt::from(0u64).into_zero_resize(width);
            let cd = 
                if (size % 64) == 0 {size / 64}
                else {(size / 64) + 1};
            explode!(cd,temp0,i0,i1,
                {explode!(cd,temp1,i1,i2,
                    {explode!(cd,temp2,i2,i3,
                        {identities_binary(size, width, &zero,
                            ApInt::from_vec_u64(temp0.clone()).unwrap().into_truncate(size).unwrap(),
                            ApInt::from_vec_u64(temp1.clone()).unwrap().into_truncate(size).unwrap(),
                            ApInt::from_vec_u64(temp2.clone()).unwrap().into_truncate(size).unwrap());}
                    )}
                )}
            )
        }

        #[test]
        fn fuzz_test_random() {
            assert_eq!(ApInt::from_vec_u64(vec![32u64,234,23]).unwrap(),ApInt::from([32u64,234,23]));
            let a = 10000;
            fuzz_random(1, a);
            fuzz_random(2, a);
            fuzz_random(3, a);
            fuzz_random(8, a);
            //trying to catch edge cases by going one bit below and over
            fuzz_random(31, a);
            fuzz_random(32, a);
            fuzz_random(33, a);
            fuzz_random(63, a);
            fuzz_random(64, a);
            fuzz_random(65, a);
            fuzz_random(100, a);
            fuzz_random(127, a);
            fuzz_random(128, a);
            fuzz_random(129, a);
            fuzz_random(150, a);
            fuzz_random(191, a);
            fuzz_random(192, a);
            fuzz_random(193, a);
            fuzz_random(200, a);
            fuzz_random(255, a);
            fuzz_random(256, a);
            //this is for functions like `rotate_left_assign` which like to fail on many digits
            fuzz_random(33*64, a);
        }

        #[test]
        fn fuzz_test_edge() {
            fuzz_edge_unary(63);
            fuzz_edge_unary(64);
            fuzz_edge_unary(65);
            fuzz_edge_unary(100);
            fuzz_edge_unary(127);
            fuzz_edge_unary(128);
            fuzz_edge_unary(129);
            fuzz_edge_unary(150);
            fuzz_edge_unary(191);
            fuzz_edge_unary(192);
            fuzz_edge_unary(193);
            fuzz_edge_unary(200);
            fuzz_edge_unary(255);
            fuzz_edge_unary(256);
            fuzz_edge_binary(63);
            fuzz_edge_binary(64);
            fuzz_edge_binary(65);
            fuzz_edge_binary(100);
            fuzz_edge_binary(127);
            fuzz_edge_binary(128);
            fuzz_edge_binary(129);
            fuzz_edge_binary(150);
            fuzz_edge_binary(191);
            fuzz_edge_binary(192);
        }

        // TODO: use `rayon` to automatically split up this work among several threads

        //takes a long time to run, so this was split up into 4 tests for 4 threads
        #[test]
        #[ignore]
        fn expensive_0() {
            let a = 10000;
            fuzz_random(301, a);
            fuzz_random(512, a);
            fuzz_random(777, a);
            fuzz_random(64*5, a);
            fuzz_random(16*64, a);
            for _ in 0..1000 {
                fuzz_random((random::<usize>() % (16 * 64)) + 1, 100);
            }
            for _ in 0..100 {
                fuzz_edge_unary(random::<usize>() % (9 * 64) + 1)
            }
        }
    
        #[test]
        #[ignore]
        fn expensive_1() {
            fuzz_edge_binary(193);
        }

        #[test]
        #[ignore]
        fn expensive_2() {
            fuzz_edge_binary(255);
        }

        #[test]
        #[ignore]
        fn expensive_3() {
            fuzz_edge_binary(256);
        }
    }
}