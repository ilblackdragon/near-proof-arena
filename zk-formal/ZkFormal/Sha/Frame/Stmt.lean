import ZkFormal.Sha.Frame.Frame

/-!
# ZkFormal.Sha.Frame.Stmt — `FrameStmt` and `DigestIoStmt`

`frameStmt_of : KindStmt → BlockStmt → FrameStmt` and
`digestIoStmt_of : KindStmt → DigestIoStmt`.
-/

namespace ZkFormal.Sha.Frame

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha ZkFormal.Sha.Layout ZkFormal.Sha.View
open ZkFormal.Sha.Table

variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem filterMap_congr' {f g : Nat → Option Nat} :
    ∀ (l : List Nat), (∀ x ∈ l, f x = g x) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.filterMap_cons, List.filterMap_cons, h x (List.mem_cons_self ..),
      filterMap_congr' xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

theorem map_congr' {f g : Nat → Nat} :
    ∀ (l : List Nat), (∀ x ∈ l, f x = g x) → l.map f = l.map g
  | [], _ => rfl
  | x :: xs, h => by
    rw [List.map_cons, List.map_cons, h x (List.mem_cons_self ..),
      map_congr' xs (fun y hy => h y (List.mem_cons_of_mem _ hy))]

/-! ## Reindexing the chain's blocks as one byte stream -/

def dataF (tr : Trace Fp) (t s0 : Nat) (g : Nat) : Option Nat :=
  if FLc tr t s0 g = 1 then some (BYc tr t s0 g) else none

theorem blockData_eq (s0 i : Nat) :
    blockData tr t (s0 + 17 * i) = ((List.range 64).map (64 * i + ·)).filterMap (dataF tr t s0) := by
  unfold blockData
  rw [List.filterMap_map]
  apply filterMap_congr'
  intro kk hkk
  simp at hkk
  simp only [Function.comp, dataF]
  rw [FLc_eq _ _ _ _ _ hkk, BYc_eq _ _ _ _ _ hkk]

theorem blockBytes_eq (s0 i : Nat) :
    blockBytes tr t (s0 + 17 * i) = ((List.range 64).map (64 * i + ·)).map (BYc tr t s0) := by
  unfold blockBytes
  rw [List.map_map]
  apply map_congr'
  intro kk hkk
  simp at hkk
  simp only [Function.comp]
  rw [BYc_eq _ _ _ _ _ hkk]

theorem stream_data (s0 : Nat) : ∀ k,
    ((List.range k).map (fun i => s0 + 17 * i)).flatMap (blockData tr t) =
      (List.range (64 * k)).filterMap (dataF tr t s0) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.flatMap_append, ih,
      show 64 * (k + 1) = 64 * k + 64 by omega, List.range_add, List.filterMap_append]
    simp only [List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil]
    rw [blockData_eq]

theorem stream_bytes (s0 : Nat) : ∀ k,
    (((List.range k).map (fun i => s0 + 17 * i)).map (blockBytes tr t)).flatten =
      (List.range (64 * k)).map (BYc tr t s0) := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.map_append, List.flatten_append, ih,
      show 64 * (k + 1) = 64 * k + 64 by omega, List.range_add, List.map_append]
    simp only [List.map_cons, List.map_nil, List.flatten_cons, List.flatten_nil, List.append_nil]
    rw [blockBytes_eq]

theorem cntF_full (f : Nat → Nat) : ∀ n, (∀ g, g < n → f g = 1) → cntF f n = n := by
  intro n
  induction n with
  | zero => intro _; rfl
  | succ n ih => intro h; simp only [cntF]; rw [ih (fun g hg => h g (by omega)), h n (by omega)]

theorem getElem!_map_range (f : Nat → Nat) (L i : Nat) (hi : i < L) :
    ((List.range L).map f)[i]! = f i := by
  simp [List.getElem!_eq_getElem?_getD, hi]

/-! ## `FrameStmt` -/

theorem interactions_getElem (busBytes busDigest q : Nat) (hq : q < 16) :
    (interactions busBytes busDigest)[q]! =
      { bus := busBytes, mult := [E.c (colF q)], msg := [E.c colId, posE q, byteE q], send := false } := by
  unfold interactions
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_left (by simp; omega)]
  simp [hq]

theorem interactions_getElem16 (busBytes busDigest : Nat) :
    (interactions busBytes busDigest)[16]! =
      { bus := busDigest, mult := [E.c colDmult],
        msg := [E.c colId, E.c colNd] ++ (List.range 32).map digestByteE, send := true } := by
  unfold interactions
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by simp)]
  simp

theorem frameStmt_of (hKs : KindStmt) (hB : BlockStmt) : FrameStmt := by
  intro tr t pub hL d hd hD
  have hK := hKs tr t pub hL
  have cx := ctx_of hKs hB hL hd hD
  generalize (chainOf tr t d).length = k at cx
  generalize (chainOf tr t d).head! = s0 at cx
  have hR := frameRules hL hK cx hd hD.2
  have hdq := cx.d_eq
  have hk := cx.k_pos
  have hs0 := cx.s0_pos
  obtain ⟨hpad, hlen⟩ := pad_of_frame hR
  have hdata := hR.data_eq
  have hm : msgOf tr t d = (List.range (cntF (FLc tr t s0) (64 * k))).map (BYc tr t s0) := by
    unfold msgOf; rw [cx.chain, stream_data]; exact hdata
  generalize hL' : cntF (FLc tr t s0) (64 * k) = L at hR hm hlen hdata
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    rw [hm] at hx
    obtain ⟨g, -, rfl⟩ := List.mem_map.1 hx
    unfold BYc; exact byteAt_lt _ _
  · rw [hm, ← hdata, hpad, cx.chain, stream_bytes]
  · have := nd_row hL hK cx hd (k - 1) (by omega) 16 (by omega)
    rw [show s0 + 17 * (k - 1) + 16 = d by omega,
      show 64 * (k - 1) + 16 * min (16 + 1) 4 = 64 * k by omega, hL'] at this
    rw [this, hm, List.length_map, List.length_range]
  · intro busBytes busDigest i hi
    rw [hm, List.length_map, List.length_range] at hi
    have hk' : i / 64 < k := by
      have := hR.L_lt; omega
    have hr := row_lt hL hK cx hd hk' (j := i % 64 / 16) (by omega)
    refine ⟨_, hr, i % 16, by omega, ?_, ?_⟩
    · have := (hR.fl_iff i (by omega)).2 hi
      unfold FLc at this
      exact cell_of_nv_one this
    · rw [interactions_getElem _ _ _ (by omega)]
      simp only [Interaction.msgVal, List.map_cons, List.map_nil]
      -- identifier
      have hid1 := id_const hL hK cx hd (s0 + 17 * (i / 64) + i % 64 / 16 - (s0 - 1)) (by omega)
      have hid2 := id_const hL hK cx hd (d - (s0 - 1)) (by omega)
      rw [show s0 - 1 + (s0 + 17 * (i / 64) + i % 64 / 16 - (s0 - 1)) =
        s0 + 17 * (i / 64) + i % 64 / 16 by omega] at hid1
      rw [show s0 - 1 + (d - (s0 - 1)) = d by omega] at hid2
      -- position
      have hnd := nd_row hL hK cx hd (i / 64) hk' (i % 64 / 16) (by omega)
      rw [show min (i % 64 / 16 + 1) 4 = i % 64 / 16 + 1 by omega] at hnd
      have hsum : fSumC.eval tr t (s0 + 17 * (i / 64) + i % 64 / 16) pub =
          Fp.ofNat (cntF (FLc tr t s0) (64 * (i / 64) + 16 * (i % 64 / 16) + 16) -
            cntF (FLc tr t s0) (64 * (i / 64) + 16 * (i % 64 / 16))) := by
        unfold fSumC
        rw [ev_sum_map tr t _ pub _ (fun q => nv tr t (s0 + 17 * (i / 64) + i % 64 / 16) (colF q))
          (fun q => cell_eq_ofNat _ _ _ _), rowsum_eq tr t s0 _ _ (by omega)]
      have hbase : cntF (FLc tr t s0) (64 * (i / 64) + 16 * (i % 64 / 16)) =
          64 * (i / 64) + 16 * (i % 64 / 16) :=
        cntF_full _ _ (fun g hg => (hR.fl_iff g (by omega)).2 (by omega))
      have hadd := cntF_add (FLc tr t s0) (64 * (i / 64) + 16 * (i % 64 / 16)) 16
      generalize hS : ((List.range 16).map fun q =>
        FLc tr t s0 (64 * (i / 64) + 16 * (i % 64 / 16) + q)).sum = S at hadd
      have e1 : cntF (FLc tr t s0) (64 * (i / 64) + 16 * (i % 64 / 16 + 1)) =
          (64 * (i / 64) + 16 * (i % 64 / 16)) + S := by
        rw [show 64 * (i / 64) + 16 * (i % 64 / 16 + 1) = 64 * (i / 64) + 16 * (i % 64 / 16) + 16 by omega,
          hadd, hbase]
      have e2 : cntF (FLc tr t s0) (64 * (i / 64) + 16 * (i % 64 / 16) + 16) -
          cntF (FLc tr t s0) (64 * (i / 64) + 16 * (i % 64 / 16)) = S := by
        rw [hadd]; omega
      rw [e1] at hnd
      rw [e2] at hsum
      have hpos : (posE (i % 16)).eval tr t (s0 + 17 * (i / 64) + i % 64 / 16) pub = Fp.ofNat i := by
        unfold posE
        simp only [ev_add, ev_sub, ev_c, ev_k, hsum, hnd]
        have hq : Fp.ofNat i = Fp.ofNat (64 * (i / 64) + 16 * (i % 64 / 16)) + Fp.ofNat (i % 16) := by
          rw [← ofNat_add]; exact congrArg Fp.ofNat (by omega)
        rw [hq, ofNat_add]
        grind
      -- byte
      have hbyte : (byteE (i % 16)).eval tr t (s0 + 17 * (i / 64) + i % 64 / 16) pub =
          Fp.ofNat (BYc tr t s0 i) := by
        rw [ev_byteE hK hr (by omega)]; rfl
      have hmi : (msgOf tr t d)[i]! = BYc tr t s0 i := by rw [hm]; exact getElem!_map_range _ _ _ hi
      simp only [ev_c]
      rw [hid1, ← hid2, hpos, hbyte, hmi]

/-! ## `DigestIoStmt` -/

theorem flatMap4_getElem (f : Nat → List UInt8) (hf : ∀ x, (f x).length = 4) :
    ∀ (l : List Nat) (p : Nat) (hp : p < 4 * l.length),
      (l.flatMap f)[p]! = (f (l[p / 4]!))[p % 4]! := by
  intro l
  induction l with
  | nil => intro p hp; simp at hp
  | cons x xs ih =>
    intro p hp
    rw [List.flatMap_cons]
    by_cases h : p < 4
    · rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_left (by rw [hf]; exact h)]
      rw [show p / 4 = 0 by omega, show p % 4 = p by omega]
      simp [List.getElem!_eq_getElem?_getD]
    · rw [List.getElem!_eq_getElem?_getD, List.getElem?_append_right (by rw [hf]; omega), hf]
      have := ih (p - 4) (by simp at hp; omega)
      rw [List.getElem!_eq_getElem?_getD] at this
      rw [this, show p / 4 = (p - 4) / 4 + 1 by omega, show p % 4 = (p - 4) % 4 by omega]
      simp [List.getElem!_eq_getElem?_getD]

theorem digestIoStmt_of (hKs : KindStmt) : DigestIoStmt := by
  intro tr t pub hL d hd hm
  have hK := hKs tr t pub hL
  have hDL := dmult_rules hL hK hd hm
  refine ⟨hDL, fun busBytes busDigest => ?_⟩
  rw [interactions_getElem16]
  simp only [Interaction.msgVal, List.map_append, List.map_cons, List.map_nil, ev_c, List.cons_append,
    List.nil_append, List.cons.injEq, true_and]
  apply List.ext_getElem
  · simp [ArenaCore.SHA256.digestBytes, stateAt, List.length_flatMap, ArenaCore.Bytes.beN_length,
      Function.comp]
    rfl
  · intro p h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.map_map, List.getElem_map, List.getElem_range, Function.comp]
    unfold digestByteE
    rw [ev_bits]
    have hlen : (stateAt tr t d).length = 8 := by simp [stateAt]
    have hp : (ArenaCore.SHA256.digestBytes (stateAt tr t d))[p]'(by
        rw [List.length_map] at h2; exact h2) = (ArenaCore.SHA256.digestBytes (stateAt tr t d))[p]! := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem]; rfl
    rw [hp]
    unfold ArenaCore.SHA256.digestBytes
    rw [flatMap4_getElem (fun x => ArenaCore.Bytes.beN 4 x) (fun x => ArenaCore.Bytes.beN_length 4 x)
      (stateAt tr t d) p (by rw [hlen]; omega)]
    have hst : (stateAt tr t d)[p / 4]! = wordAt tr t d (colSt (p / 4)) := by
      unfold stateAt; exact getElem!_map_range _ 8 _ (by omega)
    rw [hst]
    have hb : (ArenaCore.Bytes.beN 4 (wordAt tr t d (colSt (p / 4))))[p % 4]! =
        (ArenaCore.Bytes.beN 4 (wordAt tr t d (colSt (p / 4))))[p % 4]'(by
          rw [ArenaCore.Bytes.beN_length]; omega) := by
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem]; rfl
    rw [hb, beN_getElem 4 _ (p % 4) (by omega)]
    apply congrArg Fp.ofNat
    unfold wordAt
    rw [show 256 ^ (4 - 1 - p % 4) = 2 ^ (8 * (3 - p % 4)) by
      rw [Nat.pow_mul, show 4 - 1 - p % 4 = 3 - p % 4 by omega]; try rfl]
    rw [ofBits_byte _ (fun b hb => b_St hK hd (by omega) hb) _ (by omega)]
    rfl

end ZkFormal.Sha.Frame
