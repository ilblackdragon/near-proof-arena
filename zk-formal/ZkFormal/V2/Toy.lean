import ZkFormal.V2.Admission
import ZkFormal.V2.SizeSched
import ZkFormal.Assembly.Params

/-!
# ZkFormal.V2.Toy — M-v3-1: a toy np-udr-stark-v2 candidate with a hint ("sorted permutation")

Relation: the claim is a byte string `c` (`|c| ≤ 64` in the domain), a witness is a
sorted (by `toNat`, nondecreasing) permutation `w` of `c`.

* hint = the witness; proof bytes `join h π = [|h|] ++ h ++ π`;
* native preprocessing `prep c h` checks `h` sorted, `|h| = |c| ≤ 64` and produces the
  statement `enc c h = [n,0,0,0, n,0,0,0] ++ pad c ++ pad h` (`n = |c|`, `pad` to 64);
* the AIR `toyAirP` has one dummy table and two public segments on bus 0: the claim
  bytes are sent and the hint bytes received.  So `HoldsP` says exactly that the two
  byte multisets agree, i.e. `h` is a permutation of `c` (`toy_soundP`).

Proved here: semantic soundness and completeness through `prep`, the hint codec, the
numerics (`NpOkP`, `NVu`, a size bound via `SizeSched.sizeBound_le_sched`), and the
closed admission statement `toyP_admission` (via `V2.admission_v2`).
-/

namespace ZkFormal.V2.Toy

open ArenaCore ArenaCore.Security Lean.Grind ZkFormal ZkFormal.Stark ZkFormal.Air ZkFormal.Algebra
  ZkFormal.Prover ZkFormal.V2 ZkFormal.Assembly

/-! ## The challenge -/

/-- Adjacent bytes nondecreasing (by `toNat`). -/
def sortedB : Bytes → Bool
  | a :: b :: r => decide (a.toNat ≤ b.toNat) && sortedB (b :: r)
  | _ => true

def toySpec : ChallengeSpec where
  Claim := Bytes
  Witness := Bytes
  Rel := fun c w => w.Perm c ∧ sortedB w = true
  Domain := fun c => c.length ≤ 64
  decodeClaim := some
  encodeClaim := id
  decode_encode := fun _ => rfl

/-! ## Hint codec and native preprocessing -/

def hintOf (_c w : Bytes) : Bytes := w

def join (h π : Bytes) : Bytes := [h.length.toUInt8] ++ h ++ π

def split (pb : Bytes) : Option (Bytes × Bytes) :=
  match pb with
  | n :: r => if n.toNat ≤ r.length then some (r.take n.toNat, r.drop n.toNat) else none
  | [] => none

def pad (l : Bytes) : Bytes := l ++ List.replicate (64 - l.length) 0

def enc (cb h : Bytes) : Bytes :=
  let n := cb.length.toUInt8
  [n, 0, 0, 0, n, 0, 0, 0] ++ pad cb ++ pad h

def prep (cb h : Bytes) : Option Bytes :=
  if sortedB h && h.length == cb.length && decide (cb.length ≤ 64) then some (enc cb h) else none

theorem toNat_len {l : Bytes} (h : l.length ≤ 64) : l.length.toUInt8.toNat = l.length := by
  simp [Nat.toUInt8_eq]; omega

theorem split_join (h π : Bytes) (hh : h.length ≤ 64) : split (join h π) = some (h, π) := by
  simp [join, split, toNat_len hh]

/-! ## The AIR -/

def toyTableP : Air.Table := ⟨1, [], [], 4⟩

/-- One dummy table (height `2^4`, so the query domain is `2^8`), claim bytes sent and
hint bytes received on bus 0 as public messages. -/
def toyAirP : AirP where
  tables := [toyTableP]
  numBuses := 1
  numPub := 0
  pubSegs := [⟨0, true, 1, 0, 8⟩, ⟨0, false, 1, 4, 72⟩]
  maxPub := 136

theorem toyAirP_tables : toyAirP.tables ≠ [] := by simp [toyAirP]

/-! ## Public messages of a prepared statement -/

attribute [local instance] Semiring.natCast

abbrev g (b : UInt8) : Fp := ofNatF b.toNat

theorem toNat_g (b : UInt8) : (g b).toNat = b.toNat := by
  show (Fp.ofNat b.toNat).toNat = b.toNat
  rw [Fp.toNat_ofNat, Nat.mod_eq_of_lt (by have := b.toNat_lt; unfold Algebra.P; omega)]

theorem g_inj {a b : UInt8} (h : g a = g b) : a = b := by
  have := congrArg Fp.toNat h
  rw [toNat_g, toNat_g] at this
  exact UInt8.toNat_inj.mp this

theorem pubOf_enc_length (c h : Bytes) (hc : c.length ≤ 64) (hh : h.length ≤ 64) :
    (Udr.pubOf Fp (enc c h)).length = 136 := by
  simp [Udr.pubOf, enc, pad]; omega

theorem pub_getD (c h : Bytes) (i : Nat) :
    (Udr.pubOf Fp (enc c h)).getD i 0 =
      g (([c.length.toUInt8, 0, 0, 0, c.length.toUInt8, 0, 0, 0] ++ pad c ++ pad h).getD i 0) := by
  simp only [Udr.pubOf, enc, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases (([c.length.toUInt8, 0, 0, 0, c.length.toUInt8, 0, 0, 0] ++ pad c ++ pad h))[i]? <;> rfl

theorem g_zero : g 0 = 0 := rfl

theorem seg_count (c h : Bytes) (hc : c.length ≤ 64) (s : PubSeg) (hs : s.countAt = 0 ∨ s.countAt = 4) :
    s.count (Udr.pubOf Fp (enc c h)) = c.length := by
  unfold PubSeg.count
  simp only [List.range, List.range.loop, List.map_cons, List.map_nil, pub_getD c h]
  rcases hs with hs | hs <;> rw [hs] <;>
    simp [leNat, PubVal.val, List.getD_eq_getElem?_getD, toNat_g, toNat_len hc]

theorem enc_c (c h : Bytes) (j : Nat) (hj : j < c.length) :
    ([c.length.toUInt8, 0, 0, 0, c.length.toUInt8, 0, 0, 0] ++ pad c ++ pad h).getD (8 + j) 0 = c[j] := by
  rw [List.getD_eq_getElem?_getD, List.append_assoc, List.getElem?_append_right (by simp)]
  simp only [List.length_cons, List.length_nil]
  rw [show 8 + j - (0 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1) = j by omega, pad, List.append_assoc,
    List.getElem?_append_left hj, List.getElem?_eq_getElem hj]
  rfl

theorem enc_h (c h : Bytes) (j : Nat) (hc : c.length ≤ 64) (hj : j < h.length) :
    ([c.length.toUInt8, 0, 0, 0, c.length.toUInt8, 0, 0, 0] ++ pad c ++ pad h).getD (72 + j) 0 = h[j] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by simp [pad]; omega)]
  have : (([c.length.toUInt8, 0, 0, 0, c.length.toUInt8, 0, 0, 0] ++ pad c)).length = 72 := by
    simp [pad]; omega
  rw [this, show 72 + j - 72 = j by omega, pad, List.getElem?_append_left hj,
    List.getElem?_eq_getElem hj]
  rfl

theorem seg_msgs (l : Bytes) (n st : Nat) (pub : List Fp) (hn : n = l.length)
    (he : ∀ j (hj : j < l.length), pub.getD (st + j) 0 = g l[j]) (s : PubSeg)
    (hw : s.width = 1) (hs : s.start = st) (hcnt : s.count pub = n) :
    s.msgs pub = l.map fun b => [g b] := by
  unfold PubSeg.msgs PubSeg.record
  rw [hcnt, hw, hs]
  apply List.ext_getElem (by simp [hn])
  intro j h1 h2
  simp only [List.getElem_map, List.getElem_range, List.range_succ, List.range_zero,
    List.nil_append, List.map_cons, List.map_nil, Nat.mul_one, Nat.add_zero]
  rw [he j (by simp at h2; exact h2)]

/-- The public messages of a prepared statement: the claim bytes (sent) and the hint
bytes (received) on bus 0. -/
theorem pubMsgs_enc (c h : Bytes) (hc : c.length ≤ 64) (hh : h.length = c.length) :
    pubMsgs toyAirP (Udr.pubOf Fp (enc c h)) =
      c.map (fun b => (0, true, [g b])) ++ h.map (fun b => (0, false, [g b])) := by
  have m1 := seg_msgs c c.length 8 (Udr.pubOf Fp (enc c h)) rfl
    (fun j hj => by rw [pub_getD c h, enc_c c h j hj]) ⟨0, true, 1, 0, 8⟩ rfl rfl
    (seg_count c h hc _ (Or.inl rfl))
  have m2 := seg_msgs h c.length 72 (Udr.pubOf Fp (enc c h)) hh.symm
    (fun j hj => by rw [pub_getD c h, enc_h c h j hc hj]) ⟨0, false, 1, 4, 72⟩ rfl rfl
    (seg_count c h hc _ (Or.inr rfl))
  simp only [pubMsgs, toyAirP, List.flatMap_cons, List.flatMap_nil, List.append_nil, m1, m2,
    List.map_map]
  rfl

theorem len_filter_map {α β : Type} (f : α → β) (p : β → Bool) (l : List α) :
    ((l.map f).filter p).length = l.countP fun x => p (f x) := by
  rw [List.filter_map, List.length_map, List.countP_eq_length_filter]; rfl

theorem pubCount_send (c h : Bytes) (hc : c.length ≤ 64) (hh : h.length = c.length)
    (b : Nat) (m : List Fp) :
    pubCount toyAirP (Udr.pubOf Fp (enc c h)) b true m =
      c.countP fun x => decide (0 = b ∧ [g x] = m) := by
  simp only [pubCount, pubMsgs_enc c h hc hh, List.filter_append, List.length_append,
    len_filter_map]
  have e1 : (fun x => decide ((0, true, [g x]) = (b, true, m))) =
      fun x => decide (0 = b ∧ [g x] = m) := by funext x; simp
  have e2 : h.countP (fun x => decide ((0, false, [g x]) = (b, true, m))) = 0 :=
    List.countP_eq_zero.mpr (by simp)
  rw [e1, e2, Nat.add_zero]

theorem pubCount_recv (c h : Bytes) (hc : c.length ≤ 64) (hh : h.length = c.length)
    (b : Nat) (m : List Fp) :
    pubCount toyAirP (Udr.pubOf Fp (enc c h)) b false m =
      h.countP fun x => decide (0 = b ∧ [g x] = m) := by
  simp only [pubCount, pubMsgs_enc c h hc hh, List.filter_append, List.length_append,
    len_filter_map]
  have e1 : (fun x => decide ((0, false, [g x]) = (b, false, m))) =
      fun x => decide (0 = b ∧ [g x] = m) := by funext x; simp
  have e2 : c.countP (fun x => decide ((0, true, [g x]) = (b, false, m))) = 0 :=
    List.countP_eq_zero.mpr (by simp)
  rw [e1, e2, Nat.zero_add]

theorem busCount_toy (tr : Trace Fp) (pub : List Fp) (b : Nat) (s : Bool) (m : List Fp) :
    busCount toyAirP.toAir tr pub b s m = 0 := by
  have : ∀ l : List Nat, l.foldr (fun _ acc => acc) 0 = 0 := by
    intro l; induction l with
    | nil => rfl
    | cons _ _ ih => exact ih
  simp only [busCount, busCount.go, toyAirP, toyTableP, tableBusCount, List.foldr_nil,
    Nat.add_zero]
  exact this _

/-! ## Semantic soundness and completeness through `prep` -/

theorem prep_some {c h cb' : Bytes} (hp : prep c h = some cb') :
    sortedB h = true ∧ h.length = c.length ∧ c.length ≤ 64 ∧ cb' = enc c h := by
  unfold prep at hp
  split at hp
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
    exact ⟨hc.1.1, hc.1.2, hc.2, (Option.some.inj hp).symm⟩
  · cases hp

theorem count_g (l : Bytes) (x : UInt8) :
    (l.countP fun y => decide (0 = 0 ∧ [g y] = [g x])) = l.count x := by
  rw [List.count]
  congr 1
  funext y
  by_cases hy : y = x
  · subst hy; simp
  · have : ¬ g y = g x := fun e => hy (g_inj e)
    simp [this, hy]

/-- **Semantic soundness through `prep`**: an accepted prepared statement with a
satisfying trace yields a witness (the hint itself). -/
theorem toy_soundP (c h cb' : Bytes) (tr : Trace Fp) (hp : prep c h = some cb')
    (hH : HoldsP toyAirP (Udr.pubOf Fp cb') tr) : ∃ w, toySpec.Rel c w := by
  obtain ⟨hs, hl, hc, rfl⟩ := prep_some hp
  refine ⟨h, ?_, hs⟩
  apply List.perm_iff_count.mpr
  intro x
  have := hH.balance 0 [g x]
  rw [busCount_toy, busCount_toy, pubCount_send c h hc hl, pubCount_recv c h hc hl, count_g,
    count_g] at this
  omega

/-- The honest trace: the dummy table at height `2^4`. -/
def traceOf (_c _w : Bytes) : Trace Fp := ⟨fun _ => 4, fun _ _ _ => 0⟩

theorem sorted_perm_prep (c w : Bytes) (hd : c.length ≤ 64) (hp : w.Perm c) (hs : sortedB w = true) :
    prep c w = some (enc c w) := by
  unfold prep
  rw [if_pos]
  simp [hs, hp.length_eq, hd]

theorem toy_holdsP (c w : Bytes) (hd : c.length ≤ 64) (hp : w.Perm c) :
    HoldsP toyAirP (Udr.pubOf Fp (enc c w)) (traceOf c w) := by
  have hl := hp.length_eq
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t ht
    have : t = 0 := by simp [toyAirP] at ht; omega
    subst this; exact ⟨(by decide : 1 ≤ 4), (by decide : 4 ≤ 4)⟩
  · intro t ht r _ e he
    have : t = 0 := by simp [toyAirP] at ht; omega
    subst this
    simp [toyAirP, toyTableP] at he
  · intro t ht r _ i hi
    have : t = 0 := by simp [toyAirP] at ht; omega
    subst this
    simp [toyAirP, toyTableP] at hi
  · have hlen := pubOf_enc_length c w hd (by omega)
    have h1 := seg_count c w hd ⟨0, true, 1, 0, 8⟩ (Or.inl rfl)
    have h2 := seg_count c w hd ⟨0, false, 1, 4, 72⟩ (Or.inr rfl)
    simp only [pubFit, toyAirP, List.all_cons, List.all_nil, PubSeg.fits, h1, h2, hlen,
      Bool.and_true, Bool.and_eq_true, decide_eq_true_eq]
    omega
  · intro b m
    rw [busCount_toy, busCount_toy, pubCount_send c w hd hl, pubCount_recv c w hd hl,
      Nat.zero_add, Nat.zero_add]
    exact (hp.countP_eq _).symm

/-- The v2 verifier of the toy AIR at the deployed parameters. -/
abbrev Vt : IopSpec Fp Fp8 := Prover.Np.VdP toyAirP

theorem toy_headerP (c w : Bytes) : Vt.headerOk (trHdr toyAirP.toAir (traceOf c w)) = true := by
  show (headerOk toyAirP.toAir Params.default [4] &&
    decide (minQueryLog ≤ queryLog toyAirP.toAir Params.default [4])) = true
  decide +kernel

/-- **Semantic completeness through `prep`.** -/
theorem toy_compP (c w : Bytes) (hd : toySpec.Domain c) (hr : toySpec.Rel c w) :
    ∃ cb', prep (toySpec.encodeClaim c) (hintOf c w) = some cb' ∧
      HoldsP toyAirP (Udr.pubOf Fp cb') (traceOf c w) ∧
      Vt.headerOk (trHdr toyAirP.toAir (traceOf c w)) = true :=
  ⟨enc c w, sorted_perm_prep c w hd hr.1 hr.2, toy_holdsP c w hd hr.1, toy_headerP c w⟩

theorem toy_hsplit (c w π : Bytes) (hd : toySpec.Domain c) (hr : toySpec.Rel c w) :
    split (join (hintOf c w) π) = some (hintOf c w, π) :=
  split_join w π (by have := hr.1.length_eq; show w.length ≤ 64; have : c.length ≤ 64 := hd; omega)

/-! ## Numerics -/

theorem toy_npOkP : V2.Np.NpOkP toyAirP Params.default := by
  refine ⟨⟨rfl, ?_, by decide⟩, by decide +kernel⟩
  intro T hT
  simp only [toyAirP, List.mem_singleton] at hT
  subst hT
  decide

theorem toy_NVuP : NVu toyAirP.toAir Params.default ≤ 2 ^ 30 := by decide +kernel

/-- Bytes of the inner STARK proof at any admissible header. -/
def maxInner : Nat := 2829897

theorem toy_sizeMaxSchedP : V2.SizeSched.sizeMaxSched toyAirP.toAir Params.default = maxInner := by
  decide +kernel

/-- `Vt` shares v1's header check, schedule and query parameters. -/
theorem Vt_headerOk (hdr : List Nat) :
    Vt.headerOk hdr = (Iop.verifier Fp Fp8 toyAirP.toAir Params.default).headerOk hdr := rfl

theorem Vt_schedule : Vt.schedule = (Iop.verifier Fp Fp8 toyAirP.toAir Params.default).schedule :=
  rfl

theorem Vt_numChunks : Vt.numChunks = (Iop.verifier Fp Fp8 toyAirP.toAir Params.default).numChunks :=
  rfl

theorem Vt_posPerChunk :
    Vt.posPerChunk = (Iop.verifier Fp Fp8 toyAirP.toAir Params.default).posPerChunk := rfl

theorem Vt_sizeBound (hdr : List Nat) :
    sizeBound Vt hdr = sizeBound (Iop.verifier Fp Fp8 toyAirP.toAir Params.default) hdr := by
  unfold sizeBound
  rw [Vt_schedule, Vt_numChunks, Vt_posPerChunk]

theorem toy_sizeP (hdr : List Nat) (h : Vt.headerOk hdr = true) : sizeBound Vt hdr ≤ maxInner := by
  rw [← toy_sizeMaxSchedP, Vt_sizeBound]
  rw [Vt_headerOk] at h
  exact V2.SizeSched.sizeBound_le_sched (F := Fp) (K := Fp8) toyAirP.toAir Params.default hdr
    (verifier_headerOk h).1

theorem toy_maxInner : maxInner ≤ Params.default.maxProofBytes := by decide

theorem toy_hjoin (c w π : Bytes) (hd : toySpec.Domain c) (hr : toySpec.Rel c w)
    (hπ : π.length ≤ maxInner) : (join (hintOf c w) π).length ≤ 8388608 := by
  have := hr.1.length_eq
  have hd' : c.length ≤ 64 := hd
  have : maxInner + 65 ≤ 8388608 := by decide
  simp only [join, hintOf, List.length_append, List.length_singleton]
  omega

theorem toy_lo (hdr : List Nat) (h : Vt.headerOk hdr = true) :
    8 ≤ queryLog toyAirP.toAir Params.default hdr := by
  rw [Vt_headerOk] at h
  exact (verifier_headerOk h).2

/-! ## The admission statement -/

/-- `public.bin` of the toy v2 candidate. -/
def publicBin : Bytes := Bytes.ofString "np-udr-stark-v2/toy-sorted-perm/v1"

/-- Security model from the profile JSON's `model` string (as `ZkToySpec`). -/
def secModelOf (s : String) : SecModel :=
  if s = "random_oracle" then .randomOracle else .standard

def assumptionOf (s : String) : List AssumptionId :=
  if s = "sha256-collision-resistance" then [.sha256CollisionResistance]
  else if s = "random-oracle-fiat-shamir-sha256" then [.sha256RandomOracle]
  else []

def profileOf (id model : String) (targetBits : Nat) (allowed : List String)
    (maxProverQueriesLog2 maxHashQueriesLog2 : Nat) : SecurityProfile where
  id := id
  model := secModelOf model
  targetBits := targetBits
  allowedAssumptions := allowed.flatMap assumptionOf
  maxProverQueriesLog2 := maxProverQueriesLog2
  maxHashQueriesLog2 := maxHashQueriesLog2

def challengeParamsWith (profile : SecurityProfile)
    (verifyFuel maxProofBytes maxReductionFuel : Nat) : ChallengeParams where
  spec := toySpec
  profile := profile
  verifyFuel := verifyFuel
  maxProofBytes := maxProofBytes
  maxReductionFuel := maxReductionFuel

/-- **M-v3-1: the admission statement of the toy np-udr-stark-v2 candidate with a
hint** (closed: no open obligations). -/
theorem toyP_admission (pid model : String) (tb : Nat) (allowed : List String)
    (fuel rfuel : Nat) (pd bd : Digest) (tid : String)
    (hmodel : model = "random_oracle") (htb : tb ≤ 128)
    (hallowed : "random-oracle-fiat-shamir-sha256" ∈ allowed)
    (hpub : sha256 publicBin = pd) :
    AdmissionStatement
      (challengeParamsWith (profileOf pid model tb allowed 40 64) fuel 8388608 rfuel)
      { publicDigest := pd,
        impl := .nativeTrusted bd tid (npVerifierP toySpec toyAirP split prep).toVerifier } := by
  refine admission_v2 _ _ publicBin hpub toyAirP toyAirP_tables (by decide) split prep join rfl
    hintOf toy_hsplit traceOf (fun c h cb' tr hp hH => toy_soundP c h cb' tr hp hH) toy_compP
    maxInner toy_sizeP toy_maxInner toy_hjoin ?_ ?_ htb rfl rfl 8 g2_8 toy_lo g2_8_dom
    udr2_K24_min8_ok toy_npOkP toy_NVuP
  · show secModelOf model = _
    rw [hmodel]; rfl
  · show AssumptionId.sha256RandomOracle ∈ allowed.flatMap assumptionOf
    exact List.mem_flatMap.2 ⟨_, hallowed, by simp [assumptionOf]⟩

end ZkFormal.V2.Toy
