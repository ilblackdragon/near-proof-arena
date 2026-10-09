import ZkFormal.NearV3.Render.Ups.CodecRelayCover
namespace ZkFormal.NearV3.Render.UpsRelay
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near Sched

def relayAt (tr : Trace Fp) (t r : Nat) (pub : List Fp) : List (List Fp) :=
  List.replicate (relay.multNat tr t r pub) (relay.msgVal tr t r pub)

private theorem row_spost (tr : Trace Fp) (t r : Nat) (pub : List Fp) :
    (rowTraffic Codec.interactions tr t r pub B_SPOST true).map relayMsg =
      relayAt tr t r pub := by
  simp [rowTraffic,Codec.interactions,B_SPOST,Sched.B_SPOST,B_BYTES,B_VBYTES,B_DIGEST,
    B_S0F,B_SPLEN,Sched.B_SPLEN,B_SPAR,B_SDL,B_SPUBB,B_SOP,B_SFIN,B_SDG,B_SA0,B_SCMP]
  change _ = List.replicate (relay.multNat tr t r pub) (relay.msgVal tr t r pub)
  rw [relay_gate,relay_message]
  rfl

theorem codecRelayMsgs_rows (tr : Trace Fp) (t : Nat) (pub : List Fp) :
    codecRelayMsgs tr t pub = (List.range (tr.height t)).flatMap (fun r=>relayAt tr t r pub) := by
  unfold codecRelayMsgs
  rw [List.map_flatMap]
  apply UpsRows.flatMap_congr'
  intro r _
  exact row_spost tr t r pub

private theorem quiet_relay {tr : Trace Fp} {t r : Nat} {pub : List Fp}
    (hl : Codec.CLocal tr t pub) (hr : r<tr.height t)
    (he : ZkFormal.Chacha.cv tr t r Codec.kH+ZkFormal.Chacha.cv tr t r Codec.kR+
      ZkFormal.Chacha.cv tr t r Codec.kZ≠1) : relayAt tr t r pub=[] := by
  have hg : relay.multNat tr t r pub=0 := by
    apply Nat.eq_zero_of_not_pos
    intro hp
    rw [relay_gate] at hp
    exact he (Codec.encG_eval r (mult1_enc (by omega)) hl hr)
  simp [relayAt,hg]

private theorem filter_flatMap {α β : Type} (p : α→Bool) (f : α→List β) :
    ∀xs : List α,(∀x∈xs,p x=false → f x=[]) → xs.flatMap f=(xs.filter p).flatMap f
  | [],_ => rfl
  | x::xs,h => by
    have ih:=filter_flatMap p f xs (fun y hy=>h y (by simp [hy]))
    cases hp : p x with
    | true => simp [List.filter_cons,hp,ih]
    | false => simp [List.filter_cons,hp,h x (by simp) hp,ih]

/-- Full physical relay inventory partitions into all real encoding blocks.
Coverage and disjointness are proved from codec constraints, not supplied. -/
theorem codecRelayMsgs_blocks {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hl : Codec.CLocal tr t pub) (hh : tr.height t≤2^22) :
    (codecRelayMsgs tr t pub).Perm
      ((codecFirstRows tr t).flatMap fun f=>
        codecRelayBlock tr t f (37+24*ZkFormal.Chacha.cv tr t f Codec.NN) pub) := by
  rw [codecRelayMsgs_rows]
  have he : (List.range (tr.height t)).flatMap (fun r=>relayAt tr t r pub)=
      (codecEncodingRows tr t).flatMap (fun r=>relayAt tr t r pub) := by
    apply filter_flatMap
    intro r hr hp
    apply quiet_relay hl (List.mem_range.mp hr)
    simpa using hp
  rw [he]
  have hp:=List.Perm.flatMap_right (fun r=>relayAt tr t r pub) (codecEncodingRows_perm hl hh)
  simpa only [List.flatMap_assoc,codecBlockRows,List.flatMap_map,Function.comp_def,
    codecRelayBlock,relayAt] using hp
end ZkFormal.NearV3.Render.UpsRelay
