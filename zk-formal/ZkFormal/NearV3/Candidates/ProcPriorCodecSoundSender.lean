import ZkFormal.NearV3.Candidates.ProcPriorCodecSoundRows
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecSoundSender
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec ProcPriorCodecSoundRows

theorem post_bit_member (i : Nat) (hi:i<8) :
    ZkFormal.Chacha.Table.boolC (pbit i)∈ProcPriorCodecActual.constraints := by
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_filter.mpr
  constructor
  · unfold cKind
    repeat first | apply List.mem_append_left
    exact List.mem_map.mpr ⟨pbit i,mem_bool_pbit hi,rfl⟩
  · have hh:i=0∨i=1∨i=2∨i=3∨i=4∨i=5∨i=6∨i=7 := by omega
    rcases hh with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals decide +kernel

theorem post_bytes {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL:ProcPriorCodecSoundRows.CLocal tr t pub) {r : Nat} (hr:r<tr.height t)
    (he:cv tr t r kH+cv tr t r kR+cv tr t r kZ=1) :
    cv tr t r bpost=numv tr t r pbit 8 ∧ cv tr t r bpost<256 := by
  have hb:numv tr t r pbit 8<2^8 := nbits_le_of (fun i hi=>hL.bool hr (post_bit_member i hi))
  have hn:zev (tenv tr t r pub) (ZkFormal.Chacha.Rng.Table.num pbit 8)=(numv tr t r pbit 8:Int) := by
    unfold ZkFormal.Chacha.Rng.Table.num numv
    exact zev_sum_pow _ (fun b=>.col (pbit b) false) (fun b=>cv tr t r (pbit b)) 8 (fun _ _=>rfl)
  have hm:.mul encG (sub (c bpost) pbitsE)∈ProcPriorCodecActual.constraints := by
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_append_left
    apply List.mem_filter.mpr
    constructor
    · simp [cKind]
    · decide +kernel
  obtain ⟨q,hq⟩:=Mem.zdvd hL hr hm
  zs hq [pbitsE,hn]
  have hh:(cv tr t r kH:Int)+(cv tr t r kR+cv tr t r kZ)=1 := by omega
  rw [hh] at hq
  have := Codec.lt (tr:=tr) (t:=t) r bpost
  constructor <;> omega

/-- A run of nonterminal sender rows transports every live sender register
back to the corresponding register at its first row. No generator is assumed. -/
theorem sender_path {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL:ProcPriorCodecSoundRows.CLocal tr t pub) (r j i : Nat) (hij:i+j<8)
    (hr:r+j<tr.height t)
    (hS:∀x,x<j→cv tr t (r+x) fS=1)
    (h7:∀x,x<j→cv tr t (r+x) e7=0) :
    cv tr t (r+j) (prbit i)=cv tr t r (prbit (i+j)) := by
  induction j generalizing i with
  | zero=>simp
  | succ j ih=>
    have hs:=sender_shift hL (r:=r+j) (by omega) (by omega) (hS j (by omega)) (h7 j (by omega)) i (by omega)
    rw [show r+(j+1)=r+j+1 by omega,hs]
    have hh:=ih (i+1) (by omega) (by omega) (fun x hx=>hS x (by omega)) (fun x hx=>h7 x (by omega))
    simpa only [show i+1+j=i+(j+1) by omega] using hh

theorem sender_register_byte {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL:ProcPriorCodecSoundRows.CLocal tr t pub) (r i : Nat) (hi:i<8)
    (hr:r+i<tr.height t)
    (hS:∀x,x≤i→cv tr t (r+x) fS=1)
    (h7:∀x,x<i→cv tr t (r+x) e7=0)
    (he:cv tr t (r+i) kH+cv tr t (r+i) kR+cv tr t (r+i) kZ=1) :
    cv tr t r (prbit i)=cv tr t (r+i) bpost ∧ cv tr t r (prbit i)<256 := by
  have hp:=sender_path hL r i 0 (by omega) hr (fun x hx=>hS x (by omega)) h7
  simp only [Nat.zero_add] at hp
  have hbyte:=sender_byte hL hr (hS i (by omega))
  have hbound:=(post_bytes hL hr he).2
  constructor <;> omega
/-- The public sender ID uses two 24-bit limbs and one 16-bit limb. Their
ranges are recovered from actual post-byte constraints plus the seven shifts. -/
theorem sender_limb_ranges {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL:ProcPriorCodecSoundRows.CLocal tr t pub) (r : Nat)
    (hr:r+7<tr.height t)
    (hS:∀x,x<8→cv tr t (r+x) fS=1)
    (h7:∀x,x<7→cv tr t (r+x) e7=0)
    (he:∀x,x<8→cv tr t (r+x) kH+cv tr t (r+x) kR+cv tr t (r+x) kZ=1) :
    (∀i,i<8→cv tr t r (prbit i)=cv tr t (r+i) bpost ∧ cv tr t r (prbit i)<256) ∧
    cv tr t r (prbit 0)+256*cv tr t r (prbit 1)+65536*cv tr t r (prbit 2)<2^24 ∧
    cv tr t r (prbit 3)+256*cv tr t r (prbit 4)+65536*cv tr t r (prbit 5)<2^24 ∧
    cv tr t r (prbit 6)+256*cv tr t r (prbit 7)<2^16 := by
  have hb:∀i,i<8→cv tr t r (prbit i)=cv tr t (r+i) bpost ∧ cv tr t r (prbit i)<256 := by
    intro i hi
    exact sender_register_byte hL r i hi (by omega) (fun x hx=>hS x (by omega))
      (fun x hx=>h7 x (by omega)) (he i hi)
  refine ⟨hb,?_,?_,?_⟩
  · have := (hb 0 (by decide)).2
    have := (hb 1 (by decide)).2
    have := (hb 2 (by decide)).2
    omega
  · have := (hb 3 (by decide)).2
    have := (hb 4 (by decide)).2
    have := (hb 5 (by decide)).2
    omega
  · have := (hb 6 (by decide)).2
    have := (hb 7 (by decide)).2
    omega
end ZkFormal.NearV3.Candidates.ProcPriorCodecSoundSender
