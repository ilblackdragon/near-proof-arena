import ZkFormal.NearV3.Assembly.SchedulerCodecPlacement
import ZkFormal.NearV3.Assembly.SchedulerCodecNativeSanity

namespace ZkFormal.NearV3.Assembly.CodecDigest
open Candidates Sched Sched.Gen Sched.Codec
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near

def rowTrace (row : Array Nat) : Trace Fp := ⟨fun _=>0,fun _ _ c=>Fp.ofNat row[c]!⟩
def rowDigests (row : Array Nat) : List (List Fp) :=
  Near.rowTraffic Codec.interactions (rowTrace row) 0 0 [] B_DIGEST false

theorem rowDigests_installed (tr : Trace Fp) (t r : Nat) (pub : List Fp) (row : Array Nat)
    (h : ∀c,tr.cell t r c=Fp.ofNat row[c]!) :
    Near.rowTraffic Codec.interactions tr t r pub B_DIGEST false=rowDigests row := by
  have hc:∀c,Chacha.cv tr t r c=Chacha.cv (rowTrace row) 0 0 c:=by
    intro c
    unfold Chacha.cv
    rw [h]
    rfl
  unfold rowDigests
  rw [codec_digest_row,codec_digest_row,Codec.i3_def]
  simp only [Interaction.multNat,Interaction.multNat.go,Interaction.msgVal,
    List.map_append,List.map_cons,List.map_nil,Codec.ev_c,Codec.ev_k,Codec.ev_shaId,List.map_map]
  simp only [Function.comp_def,Codec.ev_c,hc]

theorem quiet_digests (rows : List (Array Nat)) (hq:Quiet rows) :
    rows.flatMap rowDigests=[] := by
  apply List.flatMap_eq_nil_iff.mpr
  intro row hr
  apply zero_digest_row
  change Fp.ofNat row[dgg]! =0
  rw [hq row hr]
  rfl

/-- Every successful corrected Codec block emits exactly one native digest
request, including all record rows and both hash suffixes. -/
theorem generated_digests (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gbA : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut) (htau:R.tau<P)
    (h : ProcPriorCodecGen.codecRows I R present vidV gbA fwd=.ok out) :
    out.rows.toList.flatMap rowDigests=
      [(digMsg (11+16*R.tau) 64 ((NearSpec.sha256 (codecSanityInput I present)).map UInt8.toNat)).toFp] := by
  obtain ⟨lead,hq,_,he⟩:=generated_placement I R present vidV gbA fwd out h
  rw [he,List.flatMap_append,List.flatMap_append,quiet_digests lead hq,List.nil_append]
  have hash : (hashRows I R present vidV).flatMap rowDigests=
      [(digMsg (11+16*R.tau) 64 ((NearSpec.sha256 (codecSanityInput I present)).map UInt8.toNat)).toFp] := by
    unfold hashRows
    rw [List.flatMap_map]
    have he : (List.range 32).flatMap (fun j=>rowDigests
        (ProcPriorCodecAssignments.hashRow (ProcPriorCodecNativeHash.instanceCells I R present vidV)
          ((NearSpec.sha256 (codecSanityInput I present)).map UInt8.toNat)
          (if present then I.prev.sanityHash.map UInt8.toNat else List.replicate 32 0)
          present (5+24*(R.n*R.n)) j))=
        (List.range 32).flatMap (fun j=>if j=0 then
          [(digMsg (11+16*R.tau) 64 ((NearSpec.sha256 (codecSanityInput I present)).map UInt8.toNat)).toFp] else []) := by
      apply UpsRows.flatMap_congr'
      intro j hj
      exact installed_hash_digest I R present vidV _ _ _ j (by simp) htau _ 0 0 [] (fun _=>rfl)
    dsimp only [codecSanityInput] at he
    rw [he]
    change (List.range (31+1)).flatMap _=_
    rw [List.range_succ_eq_map]
    simp [codecSanityInput]
  have ash : (ashRows I R present vidV).flatMap rowDigests=[]:=by
    apply quiet_digests
    intro row hm
    obtain ⟨j,hj,rfl⟩:=List.mem_map.mp hm
    exact ash_digest_gate I R present vidV _ j
  rw [hash,ash,List.append_nil]

/-- Successful corrected output is charged by its exact native block size. -/
theorem generated_length (I : Input) (R : Run) (present : Bool) (vidV : Nat)
    (gbA : Array Nat) (fwd : List (Nat×Nat)) (out : CodecOut)
    (h : ProcPriorCodecGen.codecRows I R present vidV gbA fwd=.ok out) :
    out.rows.size=69+24*(R.n*R.n) := by
  obtain ⟨lead,_,hl,he⟩:=generated_placement I R present vidV gbA fwd out h
  have hn:=congrArg List.length he
  simp only [Array.length_toList,List.length_append,hashRows,ashRows,List.length_map,List.length_range,hl] at hn
  omega

end ZkFormal.NearV3.Assembly.CodecDigest
