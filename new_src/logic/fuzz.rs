    mod megafuzz {
        use super::*;
        use bitwidth::BitWidth;
        use std::u64;
        use rand::random;

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

            //power of two multiplication and division shifting tests
            let mut tmp1 = ApInt::one(BitWidth::w1()).into_zero_extend(width).unwrap().into_wrapping_shl(shift).unwrap();
            assert_eq!(
                lhs.clone().into_wrapping_shl(shift).unwrap(),
                lhs.clone().into_wrapping_mul(&tmp1).unwrap()
            );
            //negation test also
            assert_eq!(
                lhs.clone().into_wrapping_neg().into_wrapping_shl(shift).unwrap(),
                lhs.clone().into_wrapping_mul(
                    &ApInt::one(BitWidth::w1()).into_sign_extend(width).unwrap().into_wrapping_shl(shift).unwrap()
                ).unwrap()
            );
            assert_eq!(
                lhs.clone().into_wrapping_lshr(shift).unwrap(),
                lhs.clone().into_wrapping_udiv(&tmp1).unwrap()
            );
            if (shift == (size - 1)) && (lhs == tmp1) {
                //unfortunate numerical corner case where the result of the shift is -1 but the
                //division ends up as +1
                assert_eq!(
                    lhs.clone().into_wrapping_sdiv(&tmp1).unwrap(),
                    ApInt::one(width)
                );
            } else {
                let mut tmp0 = lhs.clone();
                ApInt::wrapping_sdivrem_assign(&mut tmp0, &mut tmp1).unwrap();
                //make it a floored division
                if lhs.is_negative() && !tmp1.is_zero() {
                    tmp0.wrapping_dec();
                }
                assert_eq!(tmp0, lhs.clone().into_wrapping_ashr(shift).unwrap());
            }
            let rand_width = BitWidth::new((random::<usize>() % size) + 1).unwrap();
            //wrapping multiplication test
            assert_eq!(
                lhs.clone().into_zero_extend(BitWidth::new(size * 2).unwrap()).unwrap()
                    .into_wrapping_mul(
                        &rhs.clone().into_zero_extend(BitWidth::new(size * 2).unwrap()).unwrap()
                    ).unwrap().into_zero_resize(rand_width),
                lhs.clone().into_wrapping_mul(&rhs).unwrap().into_zero_resize(rand_width)
            );
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
                    if temp0 != (lhs.clone() & &anti_overflow_mask) {panic!("wrong div\nlhs:{:?}\nactual:{:?}\nrhs:{:?}\nthird:{:?}\nrem:{:?}\nmul:{:?}\nmul_plus_rem:{:?}\ntemp0:{:?}\ntemp1:{:?}",lhs,(lhs.clone() & &anti_overflow_mask),rhs,third,rem,mul,mul_plus_rem,temp0,temp1)}
                    if temp1 != rem {panic!("wrong rem\nlhs:{:?}\nactual:{:?}\nrhs:{:?}\nthird:{:?}\nrem:{:?}\nmul:{:?}\nmul_plus_rem:{:?}\ntemp0:{:?}\ntemp1:{:?}",lhs,(lhs.clone() & &anti_overflow_mask),rhs,third,rem,mul,mul_plus_rem,temp0,temp1)}
                }
            }
        }

        //random length AND, XOR, and OR fuzzer;
        fn fuzz_random(size: usize, iterations: usize) {
            let width = BitWidth::new(size).unwrap();
            use rand::random;
            let mut lhs = ApInt::from(0u8).into_zero_resize(width);
            let mut rhs = ApInt::from(0u8).into_zero_resize(width);
            let mut third = ApInt::from(0u8).into_zero_resize(width);
            let zero = ApInt::from(0u8).into_zero_resize(width);
            for _ in 0..iterations {
                let mut r0 =  (random::<u32>() % (size as u32)) as usize;
                if r0 == 0 {r0 = 1;}
                let ones = ApInt::one(BitWidth::new(1).unwrap()).into_sign_extend(r0).unwrap().into_zero_extend(width).unwrap();
                let r1 = (random::<u32>() % (size as u32)) as usize;
                //circular shift
                let mask = if r1 == 0 {
                    ones.clone()
                } else {
                    ones.clone().into_wrapping_shl(r1).unwrap() | (&ones.clone().into_wrapping_lshr((size - r1) as usize).unwrap())
                };
                //assert_eq!(mask,ones.into_rotate_left(r1 as usize).unwrap());
                match (random(),random(),random(),random()) {
                    (false,false,false,false) => lhs |= &mask,
                    (false,false,false,true) => lhs &= &mask,
                    (false,false,true,false) => lhs ^= &mask,
                    (false,false,true,true) => lhs ^= &mask,
                    (false,true,false,false) => rhs |= &mask,
                    (false,true,false,true) => rhs &= &mask,
                    (false,true,true,false) => rhs ^= &mask,
                    (false,true,true,true) => rhs ^= &mask,
                    (true,false,false,false) => third |= &mask,
                    (true,false,false,true) => third &= &mask,
                    (true,false,true,false) => third ^= &mask,
                    (true,false,true,true) => third ^= &mask,
                    (true,true,false,false) => rhs |= &mask,
                    (true,true,false,true) => rhs &= &mask,
                    (true,true,true,false) => rhs ^= &mask,
                    (true,true,true,true) => rhs ^= &mask,
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

        //edge and corner case fuzzer
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
            //very expensive
            //fuzz_random(512, a);
            //fuzz_random(777, a);
            //fuzz_random(16*64, a);
            //fuzz_edge(193);
            //fuzz_edge(255);
            //fuzz_edge(256);
        }
    }
}