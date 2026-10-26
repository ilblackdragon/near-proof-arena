# CurveCallbacks: nearcore outcomes per step (8 runs)

| step | nearcore (first receipt; later failures) × runs |
|---|---|
| `000.alt_bn128_g1_multiexp.then-args.pos.5g+7(2g)` | ret0 ×8 |
| `001.alt_bn128_g1_multiexp.then-result-memory.pos.5g+7(2g)` | ret0 ×8 |
| `002.alt_bn128_g1_multiexp.then-result-register.pos.5g+7(2g)` | ret0 ×8 |
| `003.alt_bn128_g1_multiexp.chain3-result-memory.pos.5g+7(2g)` | ret0 ×8 |
| `004.alt_bn128_g1_multiexp.yield-args.pos.5g+7(2g)` | ret0 ×8 |
| `005.alt_bn128_g1_multiexp.yield-payload-memory.pos.5g+7(2g)` | ret0 ×8 |
| `006.alt_bn128_g1_multiexp.yield-payload-register.pos.5g+7(2g)` | ret0 ×8 |
| `007.alt_bn128_g1_multiexp.then-after-cross-shard-promise.pos.5g+7(2g)` | ret0 ×8 |
| `008.alt_bn128_g1_multiexp.then-args.neg.scalar_r` | fail:AltBn128 invalid input: invalid fr: [1, 0, 0, F0, 93, F5, E1 ×8 |
| `009.alt_bn128_g1_multiexp.then-result-memory.neg.scalar_r` | fail:AltBn128 invalid input: invalid fr: [1, 0, 0, F0, 93, F5, E1 ×8 |
| `010.alt_bn128_g1_multiexp.then-result-register.neg.scalar_r` | fail:AltBn128 invalid input: invalid fr: [1, 0, 0, F0, 93, F5, E1 ×8 |
| `011.alt_bn128_g1_multiexp.chain3-result-memory.neg.scalar_r` | fail:AltBn128 invalid input: invalid fr: [1, 0, 0, F0, 93, F5, E1 ×8 |
| `012.alt_bn128_g1_multiexp.yield-args.neg.scalar_r` | fail:AltBn128 invalid input: invalid fr: [1, 0, 0, F0, 93, F5, E1 ×8 |
| `013.alt_bn128_g1_multiexp.yield-payload-memory.neg.scalar_r` | fail:AltBn128 invalid input: invalid fr: [1, 0, 0, F0, 93, F5, E1 ×8 |
| `014.alt_bn128_g1_multiexp.yield-payload-register.neg.scalar_r` | fail:AltBn128 invalid input: invalid fr: [1, 0, 0, F0, 93, F5, E1 ×8 |
| `015.alt_bn128_g1_multiexp.then-after-cross-shard-promise.neg.scalar_r` | fail:AltBn128 invalid input: invalid fr: [1, 0, 0, F0, 93, F5, E1 ×8 |
| `016.alt_bn128_g1_multiexp.then-args.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `017.alt_bn128_g1_multiexp.then-result-memory.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `018.alt_bn128_g1_multiexp.then-result-register.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `019.alt_bn128_g1_multiexp.chain3-result-memory.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `020.alt_bn128_g1_multiexp.yield-args.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `021.alt_bn128_g1_multiexp.yield-payload-memory.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `022.alt_bn128_g1_multiexp.yield-payload-register.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `023.alt_bn128_g1_multiexp.then-after-cross-shard-promise.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `024.alt_bn128_g1_sum.then-args.pos.g+2g-g` | ret0 ×8 |
| `025.alt_bn128_g1_sum.then-result-memory.pos.g+2g-g` | ret0 ×8 |
| `026.alt_bn128_g1_sum.then-result-register.pos.g+2g-g` | ret0 ×8 |
| `027.alt_bn128_g1_sum.chain3-result-memory.pos.g+2g-g` | ret0 ×8 |
| `028.alt_bn128_g1_sum.yield-args.pos.g+2g-g` | ret0 ×8 |
| `029.alt_bn128_g1_sum.yield-payload-memory.pos.g+2g-g` | ret0 ×8 |
| `030.alt_bn128_g1_sum.yield-payload-register.pos.g+2g-g` | ret0 ×8 |
| `031.alt_bn128_g1_sum.then-after-cross-shard-promise.pos.g+2g-g` | ret0 ×8 |
| `032.alt_bn128_g1_sum.then-args.neg.len64` | fail:AltBn128 invalid input: slice of size 64 cannot be precisely ×8 |
| `033.alt_bn128_g1_sum.then-result-memory.neg.len64` | fail:AltBn128 invalid input: slice of size 64 cannot be precisely ×8 |
| `034.alt_bn128_g1_sum.then-result-register.neg.len64` | fail:AltBn128 invalid input: slice of size 64 cannot be precisely ×8 |
| `035.alt_bn128_g1_sum.chain3-result-memory.neg.len64` | fail:AltBn128 invalid input: slice of size 64 cannot be precisely ×8 |
| `036.alt_bn128_g1_sum.yield-args.neg.len64` | fail:AltBn128 invalid input: slice of size 64 cannot be precisely ×8 |
| `037.alt_bn128_g1_sum.yield-payload-memory.neg.len64` | fail:AltBn128 invalid input: slice of size 64 cannot be precisely ×8 |
| `038.alt_bn128_g1_sum.yield-payload-register.neg.len64` | fail:AltBn128 invalid input: slice of size 64 cannot be precisely ×8 |
| `039.alt_bn128_g1_sum.then-after-cross-shard-promise.neg.len64` | fail:AltBn128 invalid input: slice of size 64 cannot be precisely ×8 |
| `040.alt_bn128_pairing_check.then-args.pos.e(5g,q)e(-g,5q)` | ret1 ×8 |
| `041.alt_bn128_pairing_check.then-result-memory.pos.e(5g,q)e(-g,5q)` | ret1 ×8 |
| `042.alt_bn128_pairing_check.then-result-register.pos.e(5g,q)e(-g,5q)` | ret1 ×8 |
| `043.alt_bn128_pairing_check.chain3-result-memory.pos.e(5g,q)e(-g,5q)` | ret1 ×8 |
| `044.alt_bn128_pairing_check.yield-args.pos.e(5g,q)e(-g,5q)` | ret1 ×8 |
| `045.alt_bn128_pairing_check.yield-payload-memory.pos.e(5g,q)e(-g,5q)` | ret1 ×8 |
| `046.alt_bn128_pairing_check.yield-payload-register.pos.e(5g,q)e(-g,5q)` | ret1 ×8 |
| `047.alt_bn128_pairing_check.then-after-cross-shard-promise.pos.e(5g,q)e(-g,5q)` | ret1 ×8 |
| `048.alt_bn128_pairing_check.then-args.neg.g2_not_in_subgroup` | fail:AltBn128 invalid input: invalid g2: [2, 0, 0, 0, 0, 0, 0, 0, ×8 |
| `049.alt_bn128_pairing_check.then-result-memory.neg.g2_not_in_subgroup` | fail:AltBn128 invalid input: invalid g2: [2, 0, 0, 0, 0, 0, 0, 0, ×8 |
| `050.alt_bn128_pairing_check.then-result-register.neg.g2_not_in_subgroup` | fail:AltBn128 invalid input: invalid g2: [2, 0, 0, 0, 0, 0, 0, 0, ×8 |
| `051.alt_bn128_pairing_check.chain3-result-memory.neg.g2_not_in_subgroup` | fail:AltBn128 invalid input: invalid g2: [2, 0, 0, 0, 0, 0, 0, 0, ×8 |
| `052.alt_bn128_pairing_check.yield-args.neg.g2_not_in_subgroup` | fail:AltBn128 invalid input: invalid g2: [2, 0, 0, 0, 0, 0, 0, 0, ×8 |
| `053.alt_bn128_pairing_check.yield-payload-memory.neg.g2_not_in_subgroup` | fail:AltBn128 invalid input: invalid g2: [2, 0, 0, 0, 0, 0, 0, 0, ×8 |
| `054.alt_bn128_pairing_check.yield-payload-register.neg.g2_not_in_subgroup` | fail:AltBn128 invalid input: invalid g2: [2, 0, 0, 0, 0, 0, 0, 0, ×8 |
| `055.alt_bn128_pairing_check.then-after-cross-shard-promise.neg.g2_not_in_subgroup` | fail:AltBn128 invalid input: invalid g2: [2, 0, 0, 0, 0, 0, 0, 0, ×8 |
| `056.alt_bn128_pairing_check.then-args.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `057.alt_bn128_pairing_check.then-result-memory.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `058.alt_bn128_pairing_check.then-result-register.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `059.alt_bn128_pairing_check.chain3-result-memory.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `060.alt_bn128_pairing_check.yield-args.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `061.alt_bn128_pairing_check.yield-payload-memory.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `062.alt_bn128_pairing_check.yield-payload-register.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `063.alt_bn128_pairing_check.then-after-cross-shard-promise.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `064.bls12381_p1_sum.then-args.pos.a+2a-a` | ret0 ×8 |
| `065.bls12381_p1_sum.then-result-memory.pos.a+2a-a` | ret0 ×8 |
| `066.bls12381_p1_sum.then-result-register.pos.a+2a-a` | fail:Integer overflow ×8 |
| `067.bls12381_p1_sum.chain3-result-memory.pos.a+2a-a` | ret0 ×8 |
| `068.bls12381_p1_sum.yield-args.pos.a+2a-a` | ret0 ×8 |
| `069.bls12381_p1_sum.yield-payload-memory.pos.a+2a-a` | ret0 ×8 |
| `070.bls12381_p1_sum.yield-payload-register.pos.a+2a-a` | fail:Integer overflow ×8 |
| `071.bls12381_p1_sum.then-after-cross-shard-promise.pos.a+2a-a` | ret0 ×8 |
| `072.bls12381_p1_sum.then-args.neg.sign2` | ret1 ×8 |
| `073.bls12381_p1_sum.then-result-memory.neg.sign2` | ret1 ×8 |
| `074.bls12381_p1_sum.then-result-register.neg.sign2` | fail:Integer overflow ×8 |
| `075.bls12381_p1_sum.chain3-result-memory.neg.sign2` | ret1 ×8 |
| `076.bls12381_p1_sum.yield-args.neg.sign2` | ret1 ×8 |
| `077.bls12381_p1_sum.yield-payload-memory.neg.sign2` | ret1 ×8 |
| `078.bls12381_p1_sum.yield-payload-register.neg.sign2` | fail:Integer overflow ×8 |
| `079.bls12381_p1_sum.then-after-cross-shard-promise.neg.sign2` | ret1 ×8 |
| `080.bls12381_p1_sum.then-args.edge.not_in_subgroup` | ret0 ×8 |
| `081.bls12381_p1_sum.then-result-memory.edge.not_in_subgroup` | ret0 ×8 |
| `082.bls12381_p1_sum.then-result-register.edge.not_in_subgroup` | fail:Integer overflow ×8 |
| `083.bls12381_p1_sum.chain3-result-memory.edge.not_in_subgroup` | ret0 ×8 |
| `084.bls12381_p1_sum.yield-args.edge.not_in_subgroup` | ret0 ×8 |
| `085.bls12381_p1_sum.yield-payload-memory.edge.not_in_subgroup` | ret0 ×8 |
| `086.bls12381_p1_sum.yield-payload-register.edge.not_in_subgroup` | fail:Integer overflow ×8 |
| `087.bls12381_p1_sum.then-after-cross-shard-promise.edge.not_in_subgroup` | ret0 ×8 |
| `088.bls12381_p2_sum.then-args.pos.b+2b-b` | ret0 ×8 |
| `089.bls12381_p2_sum.then-result-memory.pos.b+2b-b` | ret0 ×8 |
| `090.bls12381_p2_sum.then-result-register.pos.b+2b-b` | fail:Integer overflow ×8 |
| `091.bls12381_p2_sum.chain3-result-memory.pos.b+2b-b` | ret0 ×8 |
| `092.bls12381_p2_sum.yield-args.pos.b+2b-b` | ret0 ×8 |
| `093.bls12381_p2_sum.yield-payload-memory.pos.b+2b-b` | ret0 ×8 |
| `094.bls12381_p2_sum.yield-payload-register.pos.b+2b-b` | fail:Integer overflow ×8 |
| `095.bls12381_p2_sum.then-after-cross-shard-promise.pos.b+2b-b` | ret0 ×8 |
| `096.bls12381_p2_sum.then-args.neg.sign255` | ret1 ×8 |
| `097.bls12381_p2_sum.then-result-memory.neg.sign255` | ret1 ×8 |
| `098.bls12381_p2_sum.then-result-register.neg.sign255` | fail:Integer overflow ×8 |
| `099.bls12381_p2_sum.chain3-result-memory.neg.sign255` | ret1 ×8 |
| `100.bls12381_p2_sum.yield-args.neg.sign255` | ret1 ×8 |
| `101.bls12381_p2_sum.yield-payload-memory.neg.sign255` | ret1 ×8 |
| `102.bls12381_p2_sum.yield-payload-register.neg.sign255` | fail:Integer overflow ×8 |
| `103.bls12381_p2_sum.then-after-cross-shard-promise.neg.sign255` | ret1 ×8 |
| `104.bls12381_p2_sum.then-args.edge.not_in_subgroup` | ret0 ×8 |
| `105.bls12381_p2_sum.then-result-memory.edge.not_in_subgroup` | ret0 ×8 |
| `106.bls12381_p2_sum.then-result-register.edge.not_in_subgroup` | fail:Integer overflow ×8 |
| `107.bls12381_p2_sum.chain3-result-memory.edge.not_in_subgroup` | ret0 ×8 |
| `108.bls12381_p2_sum.yield-args.edge.not_in_subgroup` | ret0 ×8 |
| `109.bls12381_p2_sum.yield-payload-memory.edge.not_in_subgroup` | ret0 ×8 |
| `110.bls12381_p2_sum.yield-payload-register.edge.not_in_subgroup` | fail:Integer overflow ×8 |
| `111.bls12381_p2_sum.then-after-cross-shard-promise.edge.not_in_subgroup` | ret0 ×8 |
| `112.bls12381_g1_multiexp.then-args.pos.5a+7(2a)` | ret0 ×8 |
| `113.bls12381_g1_multiexp.then-result-memory.pos.5a+7(2a)` | ret0 ×8 |
| `114.bls12381_g1_multiexp.then-result-register.pos.5a+7(2a)` | fail:Integer overflow ×8 |
| `115.bls12381_g1_multiexp.chain3-result-memory.pos.5a+7(2a)` | ret0 ×8 |
| `116.bls12381_g1_multiexp.yield-args.pos.5a+7(2a)` | ret0 ×8 |
| `117.bls12381_g1_multiexp.yield-payload-memory.pos.5a+7(2a)` | ret0 ×8 |
| `118.bls12381_g1_multiexp.yield-payload-register.pos.5a+7(2a)` | fail:Integer overflow ×8 |
| `119.bls12381_g1_multiexp.then-after-cross-shard-promise.pos.5a+7(2a)` | ret0 ×8 |
| `120.bls12381_g1_multiexp.then-args.neg.not_in_subgroup` | ret1 ×8 |
| `121.bls12381_g1_multiexp.then-result-memory.neg.not_in_subgroup` | ret1 ×8 |
| `122.bls12381_g1_multiexp.then-result-register.neg.not_in_subgroup` | fail:Integer overflow ×8 |
| `123.bls12381_g1_multiexp.chain3-result-memory.neg.not_in_subgroup` | ret1 ×8 |
| `124.bls12381_g1_multiexp.yield-args.neg.not_in_subgroup` | ret1 ×8 |
| `125.bls12381_g1_multiexp.yield-payload-memory.neg.not_in_subgroup` | ret1 ×8 |
| `126.bls12381_g1_multiexp.yield-payload-register.neg.not_in_subgroup` | fail:Integer overflow ×8 |
| `127.bls12381_g1_multiexp.then-after-cross-shard-promise.neg.not_in_subgroup` | ret1 ×8 |
| `128.bls12381_g1_multiexp.then-args.edge.scalar_r` | ret0 ×8 |
| `129.bls12381_g1_multiexp.then-result-memory.edge.scalar_r` | ret0 ×8 |
| `130.bls12381_g1_multiexp.then-result-register.edge.scalar_r` | fail:Integer overflow ×8 |
| `131.bls12381_g1_multiexp.chain3-result-memory.edge.scalar_r` | ret0 ×8 |
| `132.bls12381_g1_multiexp.yield-args.edge.scalar_r` | ret0 ×8 |
| `133.bls12381_g1_multiexp.yield-payload-memory.edge.scalar_r` | ret0 ×8 |
| `134.bls12381_g1_multiexp.yield-payload-register.edge.scalar_r` | fail:Integer overflow ×8 |
| `135.bls12381_g1_multiexp.then-after-cross-shard-promise.edge.scalar_r` | ret0 ×8 |
| `136.bls12381_g1_multiexp.then-args.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `137.bls12381_g1_multiexp.then-result-memory.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `138.bls12381_g1_multiexp.then-result-register.neg.gas_at_element_charge` | fail:Integer overflow ×8 |
| `139.bls12381_g1_multiexp.chain3-result-memory.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `140.bls12381_g1_multiexp.yield-args.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `141.bls12381_g1_multiexp.yield-payload-memory.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `142.bls12381_g1_multiexp.yield-payload-register.neg.gas_at_element_charge` | fail:Integer overflow ×8 |
| `143.bls12381_g1_multiexp.then-after-cross-shard-promise.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `144.bls12381_g2_multiexp.then-args.pos.5b+7(2b)` | ret0 ×8 |
| `145.bls12381_g2_multiexp.then-result-memory.pos.5b+7(2b)` | ret0 ×8 |
| `146.bls12381_g2_multiexp.then-result-register.pos.5b+7(2b)` | fail:Integer overflow ×8 |
| `147.bls12381_g2_multiexp.chain3-result-memory.pos.5b+7(2b)` | ret0 ×8 |
| `148.bls12381_g2_multiexp.yield-args.pos.5b+7(2b)` | ret0 ×8 |
| `149.bls12381_g2_multiexp.yield-payload-memory.pos.5b+7(2b)` | ret0 ×8 |
| `150.bls12381_g2_multiexp.yield-payload-register.pos.5b+7(2b)` | fail:Integer overflow ×8 |
| `151.bls12381_g2_multiexp.then-after-cross-shard-promise.pos.5b+7(2b)` | ret0 ×8 |
| `152.bls12381_g2_multiexp.then-args.neg.not_in_subgroup` | ret1 ×8 |
| `153.bls12381_g2_multiexp.then-result-memory.neg.not_in_subgroup` | ret1 ×8 |
| `154.bls12381_g2_multiexp.then-result-register.neg.not_in_subgroup` | fail:Integer overflow ×8 |
| `155.bls12381_g2_multiexp.chain3-result-memory.neg.not_in_subgroup` | ret1 ×8 |
| `156.bls12381_g2_multiexp.yield-args.neg.not_in_subgroup` | ret1 ×8 |
| `157.bls12381_g2_multiexp.yield-payload-memory.neg.not_in_subgroup` | ret1 ×8 |
| `158.bls12381_g2_multiexp.yield-payload-register.neg.not_in_subgroup` | fail:Integer overflow ×8 |
| `159.bls12381_g2_multiexp.then-after-cross-shard-promise.neg.not_in_subgroup` | ret1 ×8 |
| `160.bls12381_g2_multiexp.then-args.edge.scalar_r` | ret0 ×8 |
| `161.bls12381_g2_multiexp.then-result-memory.edge.scalar_r` | ret0 ×8 |
| `162.bls12381_g2_multiexp.then-result-register.edge.scalar_r` | fail:Integer overflow ×8 |
| `163.bls12381_g2_multiexp.chain3-result-memory.edge.scalar_r` | ret0 ×8 |
| `164.bls12381_g2_multiexp.yield-args.edge.scalar_r` | ret0 ×8 |
| `165.bls12381_g2_multiexp.yield-payload-memory.edge.scalar_r` | ret0 ×8 |
| `166.bls12381_g2_multiexp.yield-payload-register.edge.scalar_r` | fail:Integer overflow ×8 |
| `167.bls12381_g2_multiexp.then-after-cross-shard-promise.edge.scalar_r` | ret0 ×8 |
| `168.bls12381_g2_multiexp.then-args.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `169.bls12381_g2_multiexp.then-result-memory.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `170.bls12381_g2_multiexp.then-result-register.neg.gas_at_element_charge` | fail:Integer overflow ×8 |
| `171.bls12381_g2_multiexp.chain3-result-memory.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `172.bls12381_g2_multiexp.yield-args.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `173.bls12381_g2_multiexp.yield-payload-memory.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `174.bls12381_g2_multiexp.yield-payload-register.neg.gas_at_element_charge` | fail:Integer overflow ×8 |
| `175.bls12381_g2_multiexp.then-after-cross-shard-promise.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `176.bls12381_map_fp_to_g1.then-args.pos.one` | ret0 ×8 |
| `177.bls12381_map_fp_to_g1.then-result-memory.pos.one` | ret0 ×8 |
| `178.bls12381_map_fp_to_g1.then-result-register.pos.one` | fail:Integer overflow ×8 |
| `179.bls12381_map_fp_to_g1.chain3-result-memory.pos.one` | ret0 ×8 |
| `180.bls12381_map_fp_to_g1.yield-args.pos.one` | ret0 ×8 |
| `181.bls12381_map_fp_to_g1.yield-payload-memory.pos.one` | ret0 ×8 |
| `182.bls12381_map_fp_to_g1.yield-payload-register.pos.one` | fail:Integer overflow ×8 |
| `183.bls12381_map_fp_to_g1.then-after-cross-shard-promise.pos.one` | ret0 ×8 |
| `184.bls12381_map_fp_to_g1.then-args.neg.fp_is_p` | ret1 ×8 |
| `185.bls12381_map_fp_to_g1.then-result-memory.neg.fp_is_p` | ret1 ×8 |
| `186.bls12381_map_fp_to_g1.then-result-register.neg.fp_is_p` | fail:Integer overflow ×8 |
| `187.bls12381_map_fp_to_g1.chain3-result-memory.neg.fp_is_p` | ret1 ×8 |
| `188.bls12381_map_fp_to_g1.yield-args.neg.fp_is_p` | ret1 ×8 |
| `189.bls12381_map_fp_to_g1.yield-payload-memory.neg.fp_is_p` | ret1 ×8 |
| `190.bls12381_map_fp_to_g1.yield-payload-register.neg.fp_is_p` | fail:Integer overflow ×8 |
| `191.bls12381_map_fp_to_g1.then-after-cross-shard-promise.neg.fp_is_p` | ret1 ×8 |
| `192.bls12381_map_fp2_to_g2.then-args.pos.one` | ret0 ×8 |
| `193.bls12381_map_fp2_to_g2.then-result-memory.pos.one` | ret0 ×8 |
| `194.bls12381_map_fp2_to_g2.then-result-register.pos.one` | fail:Integer overflow ×8 |
| `195.bls12381_map_fp2_to_g2.chain3-result-memory.pos.one` | ret0 ×8 |
| `196.bls12381_map_fp2_to_g2.yield-args.pos.one` | ret0 ×8 |
| `197.bls12381_map_fp2_to_g2.yield-payload-memory.pos.one` | ret0 ×8 |
| `198.bls12381_map_fp2_to_g2.yield-payload-register.pos.one` | fail:Integer overflow ×8 |
| `199.bls12381_map_fp2_to_g2.then-after-cross-shard-promise.pos.one` | ret0 ×8 |
| `200.bls12381_map_fp2_to_g2.then-args.neg.c1_is_p` | ret1 ×8 |
| `201.bls12381_map_fp2_to_g2.then-result-memory.neg.c1_is_p` | ret1 ×8 |
| `202.bls12381_map_fp2_to_g2.then-result-register.neg.c1_is_p` | fail:Integer overflow ×8 |
| `203.bls12381_map_fp2_to_g2.chain3-result-memory.neg.c1_is_p` | ret1 ×8 |
| `204.bls12381_map_fp2_to_g2.yield-args.neg.c1_is_p` | ret1 ×8 |
| `205.bls12381_map_fp2_to_g2.yield-payload-memory.neg.c1_is_p` | ret1 ×8 |
| `206.bls12381_map_fp2_to_g2.yield-payload-register.neg.c1_is_p` | fail:Integer overflow ×8 |
| `207.bls12381_map_fp2_to_g2.then-after-cross-shard-promise.neg.c1_is_p` | ret1 ×8 |
| `208.bls12381_pairing_check.then-args.pos.e(5a,b)e(-a,5b)` | ret0 ×8 |
| `209.bls12381_pairing_check.then-result-memory.pos.e(5a,b)e(-a,5b)` | ret0 ×8 |
| `210.bls12381_pairing_check.then-result-register.pos.e(5a,b)e(-a,5b)` | ret0 ×8 |
| `211.bls12381_pairing_check.chain3-result-memory.pos.e(5a,b)e(-a,5b)` | ret0 ×8 |
| `212.bls12381_pairing_check.yield-args.pos.e(5a,b)e(-a,5b)` | ret0 ×8 |
| `213.bls12381_pairing_check.yield-payload-memory.pos.e(5a,b)e(-a,5b)` | ret0 ×8 |
| `214.bls12381_pairing_check.yield-payload-register.pos.e(5a,b)e(-a,5b)` | ret0 ×8 |
| `215.bls12381_pairing_check.then-after-cross-shard-promise.pos.e(5a,b)e(-a,5b)` | ret0 ×8 |
| `216.bls12381_pairing_check.then-args.neg.g1_not_in_subgroup` | ret1 ×8 |
| `217.bls12381_pairing_check.then-result-memory.neg.g1_not_in_subgroup` | ret1 ×8 |
| `218.bls12381_pairing_check.then-result-register.neg.g1_not_in_subgroup` | ret1 ×8 |
| `219.bls12381_pairing_check.chain3-result-memory.neg.g1_not_in_subgroup` | ret1 ×8 |
| `220.bls12381_pairing_check.yield-args.neg.g1_not_in_subgroup` | ret1 ×8 |
| `221.bls12381_pairing_check.yield-payload-memory.neg.g1_not_in_subgroup` | ret1 ×8 |
| `222.bls12381_pairing_check.yield-payload-register.neg.g1_not_in_subgroup` | ret1 ×8 |
| `223.bls12381_pairing_check.then-after-cross-shard-promise.neg.g1_not_in_subgroup` | ret1 ×8 |
| `224.bls12381_pairing_check.then-args.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `225.bls12381_pairing_check.then-result-memory.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `226.bls12381_pairing_check.then-result-register.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `227.bls12381_pairing_check.chain3-result-memory.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `228.bls12381_pairing_check.yield-args.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `229.bls12381_pairing_check.yield-payload-memory.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `230.bls12381_pairing_check.yield-payload-register.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `231.bls12381_pairing_check.then-after-cross-shard-promise.neg.gas_at_element_charge` | fail:Exceeded the prepaid gas ×8 |
| `232.bls12381_p1_decompress.then-args.pos.a` | ret0 ×8 |
| `233.bls12381_p1_decompress.then-result-memory.pos.a` | ret0 ×8 |
| `234.bls12381_p1_decompress.then-result-register.pos.a` | fail:Integer overflow ×8 |
| `235.bls12381_p1_decompress.chain3-result-memory.pos.a` | ret0 ×8 |
| `236.bls12381_p1_decompress.yield-args.pos.a` | ret0 ×8 |
| `237.bls12381_p1_decompress.yield-payload-memory.pos.a` | ret0 ×8 |
| `238.bls12381_p1_decompress.yield-payload-register.pos.a` | fail:Integer overflow ×8 |
| `239.bls12381_p1_decompress.then-after-cross-shard-promise.pos.a` | ret0 ×8 |
| `240.bls12381_p1_decompress.then-args.neg.no_compression_flag` | ret1 ×8 |
| `241.bls12381_p1_decompress.then-result-memory.neg.no_compression_flag` | ret1 ×8 |
| `242.bls12381_p1_decompress.then-result-register.neg.no_compression_flag` | fail:Integer overflow ×8 |
| `243.bls12381_p1_decompress.chain3-result-memory.neg.no_compression_flag` | ret1 ×8 |
| `244.bls12381_p1_decompress.yield-args.neg.no_compression_flag` | ret1 ×8 |
| `245.bls12381_p1_decompress.yield-payload-memory.neg.no_compression_flag` | ret1 ×8 |
| `246.bls12381_p1_decompress.yield-payload-register.neg.no_compression_flag` | fail:Integer overflow ×8 |
| `247.bls12381_p1_decompress.then-after-cross-shard-promise.neg.no_compression_flag` | ret1 ×8 |
| `248.bls12381_p1_decompress.then-args.edge.not_in_subgroup` | ret0 ×8 |
| `249.bls12381_p1_decompress.then-result-memory.edge.not_in_subgroup` | ret0 ×8 |
| `250.bls12381_p1_decompress.then-result-register.edge.not_in_subgroup` | fail:Integer overflow ×8 |
| `251.bls12381_p1_decompress.chain3-result-memory.edge.not_in_subgroup` | ret0 ×8 |
| `252.bls12381_p1_decompress.yield-args.edge.not_in_subgroup` | ret0 ×8 |
| `253.bls12381_p1_decompress.yield-payload-memory.edge.not_in_subgroup` | ret0 ×8 |
| `254.bls12381_p1_decompress.yield-payload-register.edge.not_in_subgroup` | fail:Integer overflow ×8 |
| `255.bls12381_p1_decompress.then-after-cross-shard-promise.edge.not_in_subgroup` | ret0 ×8 |
| `256.bls12381_p2_decompress.then-args.pos.b` | ret0 ×8 |
| `257.bls12381_p2_decompress.then-result-memory.pos.b` | ret0 ×8 |
| `258.bls12381_p2_decompress.then-result-register.pos.b` | fail:Integer overflow ×8 |
| `259.bls12381_p2_decompress.chain3-result-memory.pos.b` | ret0 ×8 |
| `260.bls12381_p2_decompress.yield-args.pos.b` | ret0 ×8 |
| `261.bls12381_p2_decompress.yield-payload-memory.pos.b` | ret0 ×8 |
| `262.bls12381_p2_decompress.yield-payload-register.pos.b` | fail:Integer overflow ×8 |
| `263.bls12381_p2_decompress.then-after-cross-shard-promise.pos.b` | ret0 ×8 |
| `264.bls12381_p2_decompress.then-args.neg.no_compression_flag` | ret1 ×8 |
| `265.bls12381_p2_decompress.then-result-memory.neg.no_compression_flag` | ret1 ×8 |
| `266.bls12381_p2_decompress.then-result-register.neg.no_compression_flag` | fail:Integer overflow ×8 |
| `267.bls12381_p2_decompress.chain3-result-memory.neg.no_compression_flag` | ret1 ×8 |
| `268.bls12381_p2_decompress.yield-args.neg.no_compression_flag` | ret1 ×8 |
| `269.bls12381_p2_decompress.yield-payload-memory.neg.no_compression_flag` | ret1 ×8 |
| `270.bls12381_p2_decompress.yield-payload-register.neg.no_compression_flag` | fail:Integer overflow ×8 |
| `271.bls12381_p2_decompress.then-after-cross-shard-promise.neg.no_compression_flag` | ret1 ×8 |
| `272.bls12381_p2_decompress.then-args.edge.not_in_subgroup` | ret0 ×8 |
| `273.bls12381_p2_decompress.then-result-memory.edge.not_in_subgroup` | ret0 ×8 |
| `274.bls12381_p2_decompress.then-result-register.edge.not_in_subgroup` | fail:Integer overflow ×8 |
| `275.bls12381_p2_decompress.chain3-result-memory.edge.not_in_subgroup` | ret0 ×8 |
| `276.bls12381_p2_decompress.yield-args.edge.not_in_subgroup` | ret0 ×8 |
| `277.bls12381_p2_decompress.yield-payload-memory.edge.not_in_subgroup` | ret0 ×8 |
| `278.bls12381_p2_decompress.yield-payload-register.edge.not_in_subgroup` | fail:Integer overflow ×8 |
| `279.bls12381_p2_decompress.then-after-cross-shard-promise.edge.not_in_subgroup` | ret0 ×8 |
| `280.p256_verify.then-args.pos.valid` | ret1 ×8 |
| `281.p256_verify.then-result-memory.pos.valid` | ret1 ×8 |
| `282.p256_verify.chain3-result-memory.pos.valid` | ret1 ×8 |
| `283.p256_verify.yield-args.pos.valid` | ret1 ×8 |
| `284.p256_verify.yield-payload-memory.pos.valid` | ret1 ×8 |
| `285.p256_verify.then-after-cross-shard-promise.pos.valid` | ret1 ×8 |
| `286.p256_verify.then-args.neg.wrong_message` | ret0 ×8 |
| `287.p256_verify.then-result-memory.neg.wrong_message` | ret0 ×8 |
| `288.p256_verify.chain3-result-memory.neg.wrong_message` | ret0 ×8 |
| `289.p256_verify.yield-args.neg.wrong_message` | ret0 ×8 |
| `290.p256_verify.yield-payload-memory.neg.wrong_message` | ret0 ×8 |
| `291.p256_verify.then-after-cross-shard-promise.neg.wrong_message` | ret0 ×8 |
| `292.p256_verify.then-args.edge.empty_message` | ret0 ×8 |
| `293.p256_verify.then-result-memory.edge.empty_message` | ret0 ×8 |
| `294.p256_verify.chain3-result-memory.edge.empty_message` | ret0 ×8 |
| `295.p256_verify.yield-args.edge.empty_message` | ret0 ×8 |
| `296.p256_verify.yield-payload-memory.edge.empty_message` | ret0 ×8 |
| `297.p256_verify.then-after-cross-shard-promise.edge.empty_message` | ret0 ×8 |
| `298.ecrecover.then-args.pos.valid` | ret1 ×8 |
| `299.ecrecover.then-result-memory.pos.valid` | ret1 ×8 |
| `300.ecrecover.chain3-result-memory.pos.valid` | ret1 ×8 |
| `301.ecrecover.yield-args.pos.valid` | ret1 ×8 |
| `302.ecrecover.yield-payload-memory.pos.valid` | ret1 ×8 |
| `303.ecrecover.then-after-cross-shard-promise.pos.valid` | ret1 ×8 |
| `304.ecrecover.then-args.neg.wrong_v` | ret1 ×8 |
| `305.ecrecover.then-result-memory.neg.wrong_v` | ret1 ×8 |
| `306.ecrecover.chain3-result-memory.neg.wrong_v` | ret1 ×8 |
| `307.ecrecover.yield-args.neg.wrong_v` | ret1 ×8 |
| `308.ecrecover.yield-payload-memory.neg.wrong_v` | ret1 ×8 |
| `309.ecrecover.then-after-cross-shard-promise.neg.wrong_v` | ret1 ×8 |
| `310.bls12381_p2_sum.register-input.pos.b+2b-b` | fail:Integer overflow ×8 |
| `311.bls12381_p2_sum.register-input.neg.sign255` | fail:Integer overflow ×8 |
| `312.bls12381_p2_sum.register-input.edge.not_in_subgroup` | fail:Integer overflow ×8 |
| `313.bls12381_p2_sum.memory-oob.neg.memory_oob` | fail:Accessed memory outside the bounds ×8 |
| `314.bls12381_p2_sum.direct-register-without-promise.neg.no_promise_result` | fail:Accessed invalid promise result index: 0 ×8 |
| `315.bls12381_g1_multiexp.register-input.pos.5a+7(2a)` | fail:Integer overflow ×8 |
| `316.bls12381_g1_multiexp.register-input.neg.not_in_subgroup` | fail:Integer overflow ×8 |
| `317.bls12381_g1_multiexp.register-input.edge.scalar_r` | fail:Integer overflow ×8 |
| `318.bls12381_g1_multiexp.memory-oob.neg.memory_oob` | fail:Accessed memory outside the bounds ×8 |
| `319.bls12381_g1_multiexp.direct-register-without-promise.neg.no_promise_result` | fail:Accessed invalid promise result index: 0 ×8 |
| `320.bls12381_g2_multiexp.register-input.pos.5b+7(2b)` | fail:Integer overflow ×8 |
| `321.bls12381_g2_multiexp.register-input.neg.not_in_subgroup` | fail:Integer overflow ×8 |
| `322.bls12381_g2_multiexp.register-input.edge.scalar_r` | fail:Integer overflow ×8 |
| `323.bls12381_g2_multiexp.memory-oob.neg.memory_oob` | fail:Accessed memory outside the bounds ×8 |
| `324.bls12381_g2_multiexp.direct-register-without-promise.neg.no_promise_result` | fail:Accessed invalid promise result index: 0 ×8 |
| `325.bls12381_map_fp_to_g1.register-input.pos.one` | fail:Integer overflow ×8 |
| `326.bls12381_map_fp_to_g1.register-input.neg.fp_is_p` | fail:Integer overflow ×8 |
| `327.bls12381_map_fp_to_g1.memory-oob.neg.memory_oob` | fail:Accessed memory outside the bounds ×8 |
| `328.bls12381_map_fp_to_g1.direct-register-without-promise.neg.no_promise_result` | fail:Accessed invalid promise result index: 0 ×8 |
| `329.bls12381_map_fp2_to_g2.register-input.pos.one` | fail:Integer overflow ×8 |
| `330.bls12381_map_fp2_to_g2.register-input.neg.c1_is_p` | fail:Integer overflow ×8 |
| `331.bls12381_map_fp2_to_g2.memory-oob.neg.memory_oob` | fail:Accessed memory outside the bounds ×8 |
| `332.bls12381_map_fp2_to_g2.direct-register-without-promise.neg.no_promise_result` | fail:Accessed invalid promise result index: 0 ×8 |
| `333.bls12381_p1_decompress.register-input.pos.a` | fail:Integer overflow ×8 |
| `334.bls12381_p1_decompress.register-input.neg.no_compression_flag` | fail:Integer overflow ×8 |
| `335.bls12381_p1_decompress.register-input.edge.not_in_subgroup` | fail:Integer overflow ×8 |
| `336.bls12381_p1_decompress.memory-oob.neg.memory_oob` | fail:Accessed memory outside the bounds ×8 |
| `337.bls12381_p1_decompress.direct-register-without-promise.neg.no_promise_result` | fail:Accessed invalid promise result index: 0 ×8 |
| `338.bls12381_p2_decompress.register-input.pos.b` | fail:Integer overflow ×8 |
| `339.bls12381_p2_decompress.register-input.neg.no_compression_flag` | fail:Integer overflow ×8 |
| `340.bls12381_p2_decompress.register-input.edge.not_in_subgroup` | fail:Integer overflow ×8 |
| `341.bls12381_p2_decompress.memory-oob.neg.memory_oob` | fail:Accessed memory outside the bounds ×8 |
| `342.bls12381_p2_decompress.direct-register-without-promise.neg.no_promise_result` | fail:Accessed invalid promise result index: 0 ×8 |
| `343.alt_bn128_g1_multiexp.yield-resumed-later.pos.5g+7(2g)` | ret0 ×5; no host outcome (pending or resumed later) ×3 |
| `344.alt_bn128_g1_multiexp.yield-resumed-later.neg.scalar_r` | fail:AltBn128 invalid input: invalid fr: [1, 0, 0, F0, 93, F5, E1 ×6; no host outcome (pending or resumed later) ×2 |
| `345.alt_bn128_g1_sum.yield-resumed-later.pos.g+2g-g` | ret0 ×5; no host outcome (pending or resumed later) ×3 |
| `346.alt_bn128_g1_sum.yield-resumed-later.neg.len64` | no host outcome (pending or resumed later) ×4; fail:AltBn128 invalid input: slice of size 64 cannot be precisely ×4 |
| `347.alt_bn128_pairing_check.yield-resumed-later.pos.e(5g,q)e(-g,5q)` | ret1 ×4; no host outcome (pending or resumed later) ×3; receipts pending at run end ×1 |
| `348.alt_bn128_pairing_check.yield-resumed-later.neg.g2_not_in_subgroup` | no host outcome (pending or resumed later) ×4; fail:AltBn128 invalid input: invalid g2: [2, 0, 0, 0, 0, 0, 0, 0, ×4 |
| `349.bls12381_p1_sum.yield-resumed-later.pos.a+2a-a` | no host outcome (pending or resumed later) ×4; ret0 ×4 |
| `350.bls12381_p1_sum.yield-resumed-later.neg.sign2` | ret1 ×4; no host outcome (pending or resumed later) ×3; receipts pending at run end ×1 |
| `351.bls12381_p2_sum.yield-resumed-later.pos.b+2b-b` | no host outcome (pending or resumed later) ×4; ret0 ×4 |
| `352.bls12381_p2_sum.yield-resumed-later.neg.sign255` | no host outcome (pending or resumed later) ×4; ret1 ×4 |
| `353.alt_bn128_g1_multiexp.resume-later-cross-shard.pos.5g+7(2g)` | resume:01 ×6; receipts pending at run end ×2 |
| `354.alt_bn128_g1_multiexp.resume-later-cross-shard.neg.scalar_r` | resume:01 ×6; receipts pending at run end ×2 |
| `355.alt_bn128_g1_sum.resume-later-cross-shard.pos.g+2g-g` | resume:01 ×6; receipts pending at run end ×2 |
| `356.alt_bn128_g1_sum.resume-later-cross-shard.neg.len64` | resume:01 ×6; receipts pending at run end ×2 |
| `357.alt_bn128_pairing_check.resume-later-cross-shard.pos.e(5g,q)e(-g,5q)` | resume:01 ×5; receipts pending at run end ×3 |
| `358.alt_bn128_pairing_check.resume-later-cross-shard.neg.g2_not_in_subgroup` | resume:01 ×6; receipts pending at run end ×2 |
| `359.bls12381_p1_sum.resume-later-cross-shard.pos.a+2a-a` | resume:01 ×5; receipts pending at run end ×3 |
| `360.bls12381_p1_sum.resume-later-cross-shard.neg.sign2` | receipts pending at run end ×4; resume:01 ×4 |
| `361.bls12381_p2_sum.resume-later-cross-shard.pos.b+2b-b` | receipts pending at run end ×4; resume:01 ×4 |
| `362.bls12381_p2_sum.resume-later-cross-shard.neg.sign255` | receipts pending at run end ×4; resume:01 ×4 |
