import ZkFormal.NearV3.Render.Ups.CompactNativeBytes
import ZkFormal.NearV3.Sched.View.CodecState
namespace ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.NearV3.Sched

private theorem flatMap_congr_mem {α β : Type} (xs : List α) (f g : α→List β)
    (h : ∀x∈xs,f x=g x) : xs.flatMap f=xs.flatMap g := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons,h x (by simp)]
    rw [ih (fun y hy=>h y (by simp [hy]))]

def codecRelayBlock (tr : Trace Fp) (t f n : Nat) (pub : List Fp) : List (List Fp) :=
  (List.range n).flatMap fun p=>List.replicate (relay.multNat tr t (f+p) pub)
    (relay.msgVal tr t (f+p) pub)

/-- Every encoding row contributes exactly one byte to the scheduler SHA job. -/
theorem codecRelayBlock_exact {tr : Trace Fp} {t f : Nat} {pub : List Fp}
    (hL : Codec.CLocal tr t pub) (hH : tr.height t≤2^22)
    (hf : f<tr.height t) (hF : cv tr t f Codec.kF=1) :
    codecRelayBlock tr t f (37+24*cv tr t f Codec.NN) pub=
      (List.range (37+24*cv tr t f Codec.NN)).map fun p=>
        [Assembly.upsertJobId (cv tr t f Codec.tau) 0,p,cv tr t (f+p) Codec.bpost].map Fp.ofNat := by
  have hh:=(Codec.codec_post hL hH hf hF).1
  unfold codecRelayBlock
  rw [List.map_eq_flatMap]
  apply flatMap_congr_mem
  intro p hp
  have hx:=hh p (by change p<5+24*cv tr t f Codec.NN+32; have := List.mem_range.mp hp; omega)
  rw [relay_gate,hx.1,relay_native_message tr t (f+p) pub hx.2]
  rfl

private theorem rowBytes_range (tr : Trace Fp) (t col n r : Nat) :
    Codec.rowBytes tr t col r n=(List.range n).map fun p=>UInt8.ofNat (cv tr t (r+p) col) := by
  induction n generalizing r with
  | zero => rfl
  | succ n ih =>
    rw [Codec.rowBytes,List.range_succ_eq_map,List.map_cons,List.map_map]
    simp only [Nat.add_zero,Function.comp_def]
    rw [ih]
    congr 1
    apply List.map_congr_left
    intro p hp
    congr 2
    omega

/-- The relay payload is the ordinary serialized codec post-state, not an
unconstrained new byte witness. The unchanged codec local proof authenticates it. -/
theorem codecRelayBlock_state {tr : Trace Fp} {t f : Nat} {pub : List Fp}
    (hL : Codec.CLocal tr t pub) (hH : tr.height t≤2^22)
    (hf : f<tr.height t) (hF : cv tr t f Codec.kF=1) :
    (List.range (37+24*cv tr t f Codec.NN)).map
      (fun p=>UInt8.ofNat (cv tr t (f+p) Codec.bpost))=
    NearSpec.Bandwidth.State.encode ⟨Codec.postLinks tr t f (cv tr t f Codec.NN),
      (List.range 32).map fun j=>UInt8.ofNat (cv tr t (f+5+24*cv tr t f Codec.NN) (Codec.reg j))⟩ := by
  rw [←rowBytes_range]
  exact Codec.codec_post_encode hL hH hf hF
end ZkFormal.NearV3.Render.UpsRelay
