
#[cfg(test)]
mod tests {
    use crate::data::ApInt;
    use crate::info::BitWidth;
    
    mod megafuzz {
        use super::*;
        use std::u64;
        use rand::random;

        //throws all the functions together for an identities party. If one function breaks, the
        //whole thing should break.
        fn identities(size: usize, width: BitWidth, zero: &ApInt, lhs: ApInt, rhs: ApInt, third: ApInt) {
            //basic addition and subtraction tests
            let shift = random::<usize>() % size;
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
            
            //shifting tests
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

            //multiplication and division tests
            //the following tests that `((lhs * rhs) + (third % rhs)) / rhs == lhs` and
            //`((lhs * rhs) + (third % rhs)) % rhs == (third % rhs)`
            let tot_leading_zeros = lhs.leading_zeros() + rhs.leading_zeros();
            let anti_overflow_mask = if tot_leading_zeros < size {
                if rhs.leading_zeros() == 0 {
                    ApInt::zero(width)
                } else {
                    ApInt::one(BitWidth::new(1).unwrap()).into_sign_extend(rhs.leading_zeros()).unwrap().into_zero_extend(width).unwrap()
                }
            } else {
                ApInt::one(BitWidth::new(1).unwrap()).into_sign_extend(width).unwrap()
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
            let mut lhs = ApInt::from(0u8).into_zero_resize(width);
            let mut rhs = ApInt::from(0u8).into_zero_resize(width);
            let mut third = ApInt::from(0u8).into_zero_resize(width);
            let zero = ApInt::from(0u8).into_zero_resize(width);
            for _ in 0..iterations {
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
                identities(size, width, &zero, lhs.clone(), lhs.clone(), rhs.clone());
                identities(size, width, &zero, lhs.clone(), rhs.clone(), third.clone());
                identities(size, width, &zero, rhs.clone(), lhs.clone(), third.clone());
                identities(size, width, &zero, third.clone(), lhs.clone(), rhs.clone());
                identities(size, width, &zero, lhs.clone(), third.clone(), rhs.clone());
                identities(size, width, &zero, third.clone(), rhs.clone(), lhs.clone());
                identities(size, width, &zero, rhs.clone(), third.clone(), lhs.clone());
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
        fn fuzz_edge(size: usize) {
            let width = BitWidth::new(size).unwrap();
            let zero = ApInt::from(0u8).into_zero_resize(width);
            let cd = 
                if (size % 64) == 0 {size / 64}
                else {(size / 64) + 1};
            explode!(cd,temp0,i0,i1,
                {explode!(cd,temp1,i1,i2,
                    {explode!(cd,temp2,i2,i3,
                        {identities(size, width, &zero,
                            ApInt::from_vec_u64(temp0.clone()).unwrap().into_truncate(size).unwrap(),
                            ApInt::from_vec_u64(temp1.clone()).unwrap().into_truncate(size).unwrap(),
                            ApInt::from_vec_u64(temp2.clone()).unwrap().into_truncate(size).unwrap());}
                    )}
                )}
            )
        }

        #[test]
        fn fuzz_test() {
            assert_eq!(ApInt::from_vec_u64(vec![32u64,234,23]).unwrap(),ApInt::from([32u64,234,23]));
            let a = 10000;
            fuzz_random(1, a);
            fuzz_random(2, a);
            fuzz_random(3, a);
            //trying to catch edge cases by going one bit below and over
            fuzz_random(31, a);
            fuzz_random(32, a);
            fuzz_random(33, a);
            fuzz_random(63, a);
            fuzz_random(64, a);
            fuzz_random(65, a);
            fuzz_random(127, a);
            fuzz_random(128, a);
            fuzz_random(129, a);
            fuzz_random(191, a);
            fuzz_random(192, a);
            fuzz_random(193, a);
            fuzz_random(255, a);
            fuzz_random(256, a);
            fuzz_edge(63);
            fuzz_edge(64);
            fuzz_edge(65);
            fuzz_edge(127);
            fuzz_edge(128);
            fuzz_edge(129);
            fuzz_edge(191);
            fuzz_edge(192);
        }

        //takes about an hour on one computer
        #[test]
        #[ignore]
        fn expensive() {
            let a = 10000;
            fuzz_random(301, a);
            fuzz_random(512, a);
            fuzz_random(777, a);
            fuzz_random(64*5, a);
            fuzz_random(16*64, a);
            //this is for functions like `rotate_left_assign` which like to fail on many digits
            fuzz_random(33*64, a);
            for _ in 0..1000 {
                fuzz_random((random::<usize>() % (16 * 64)) + 1, 100);
            }
            fuzz_edge(193);
            fuzz_edge(255);
            fuzz_edge(256);
        }
    }
}