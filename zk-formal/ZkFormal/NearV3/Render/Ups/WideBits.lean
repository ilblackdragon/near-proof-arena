import ZkFormal.NearV3.Render.Ups.MemArith

namespace ZkFormal.NearV3.Render.UpsGen
set_option maxHeartbeats 3000000

theorem carry_bits17 (x : Int) (h0 : 0≤x) (h1 : x<131072) :
    ((List.range 17).map (fun i => (2^i : Int)*(x/2^i%2))).sum=x := by
  simp only [List.range_succ,List.range_zero,List.map_append,List.map_cons,List.map_nil,
    List.sum_append,List.sum_cons,List.sum_nil,Int.reducePow,Int.ediv_one,Int.one_mul,
    Int.zero_add,Int.add_zero]
  omega

theorem carry_bits16 (x : Int) (h0 : 0≤x) (h1 : x<65536) :
    ((List.range 16).map (fun i => (2^i : Int)*(x/2^i%2))).sum=x := by
  simp only [List.range_succ,List.range_zero,List.map_append,List.map_cons,List.map_nil,
    List.sum_append,List.sum_cons,List.sum_nil,Int.reducePow,Int.ediv_one,Int.one_mul,
    Int.zero_add,Int.add_zero]
  omega
end ZkFormal.NearV3.Render.UpsGen
