import StateM5a.KeyDecode
import StateM5a.DecodeShape

/-!
# StateM5a.DepthBound — the depth premises of `walk_deeper` from the `NIB` lookups

`DecodeShape.walk_deeper` took two field-level premises: a descending `BR` row has `d + 1 < P`
(`hbr`) and a descending `SN` row has `cont = 0` and `d + 64 < P` (`hsn`).  Here:

* **`br_depth`** (`hbr` from `Holds`): a descending `BR` row (`gdn = 1`) is active and not at the
  key's end (`br_gdn_gEnd`: `act − gEnd = 1`), so it looks up `NIB(kid, d, nib)`; by
  `KeyDecode.nib_of_rcv`, `d < 2^21`.
* **`sn_depth`**: a descending `SN` row (`gdn = 1`) is an extension, not an absent / split op
  (`sn_gdn_gA`: `gA = 0`), so its first key nibble is looked up against the walk key
  (`b₀ = a₀ = 1`): `NIB(kid, d + 0, k₀)`, hence `d < 2^21`.
* `cont = 0` is **not** forced by the constraints (a descending extension with a key longer than
  `62 + odd` nibbles continues in `SNC` rows; that is the completeness case for long extensions).
  `walk_deeper'` therefore splits on `cont`: a short key (`cont = 0`) is discharged
  (`1 ≤ klen ≤ 64`, `d < 2^21`); for a continued head the strict deepening `d < d + klen` (in the
  field, `klen = Σ a + rl` with `rl` the `SNC` chain's `KCR` answer) is the named premise
  **`SncDeeper`**.  Discharging it needs the `KC`/`KCR` chain argument (every active `SNC` row's
  `(rid, c)` comes from the head's `KC` by a chain of length `< 2^20`, so `rl` is the chain's
  nibble count and `d + klen − 1` is a looked-up position `< 2^21`).
* **`walk_shape'`**, **`air_batched_changes'`**, **`air_batched_changesS'`**: the AIR-level
  assemblies with `hbr` / `hsn` replaced by `SncDeeper` (and `extra` sending nothing on `NIB`).
-/

namespace StateM5a.DepthBound

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.FieldRows StateM5a.FieldRows2 StateM5a.KeyDecode
open StateM5a.DecodeShape

local notation "P" => 2013265921

set_option maxRecDepth 100000

section
variable {tr : Trace Fp} {t r : Nat} {pub : List Fp}

/-! ## BR -/

set_option maxHeartbeats 4000000 in
/-- A descending `BR` row looks up the walk key's nibble at its depth (`act − gEnd = 1`). -/
theorem br_gdn_gEnd (hc : ∀ e ∈ Br.table.constraints, e.eval tr t r pub = 0)
    (hg : ev tr t r pub (Br.c "gdn") = 1) : ev tr t r pub (Br.c "act" - Br.gEnd) = 1 := by
  have hb : ∀ s ∈ ["act", "mF", "mU", "mD", "gdn", "oFD", "oFA", "oUD", "oUN",
      "oDH", "oDL", "oDN", "oD1", "oFV", "oDA", "oDS", "oSL", "oUV", "oDV", "oDZ"],
      ev tr t r pub (Br.c s) ≤ 1 := fun s hs => bool_le (hold rfl hc (FieldWalk.br_bool s hs))
  have e1 := eq_of_sub (hold rfl hc FieldWalk.br_mem_act)
  have e2 := eq_of_sub (hold rfl hc FieldWalk.br_mem_mF)
  have e3 := eq_of_sub (hold rfl hc FieldWalk.br_mem_mU)
  have e4 := eq_of_sub (hold rfl hc FieldWalk.br_mem_mD)
  have e5 := eq_of_sub (hold rfl hc FieldWalk.br_mem_gdn)
  simp only [ev_hadd] at e1 e2 e3 e4 e5
  have := hb "act" (by simp); have := hb "mF" (by simp); have := hb "mU" (by simp)
  have := hb "mD" (by simp); have := hb "oFD" (by simp); have := hb "oFA" (by simp)
  have := hb "oUD" (by simp); have := hb "oUN" (by simp); have := hb "oDH" (by simp)
  have := hb "oDL" (by simp); have := hb "oDN" (by simp); have := hb "oD1" (by simp)
  have := hb "oFV" (by simp); have := hb "oDA" (by simp); have := hb "oDS" (by simp)
  have := hb "oSL" (by simp); have := hb "oUV" (by simp); have := hb "oDV" (by simp)
  have := hb "oDZ" (by simp)
  simp (disch := omega) only [Nat.mod_eq_of_lt] at e1 e2 e3 e4 e5
  have hA : ev tr t r pub (Br.c "act") = 1 := by omega
  have hE : ev tr t r pub Br.gEnd = 0 := by
    unfold Br.gEnd
    simp only [ev_hadd]
    simp (disch := omega) only [Nat.mod_eq_of_lt]
    omega
  rw [ev_sub, hA, hE]

/-! ## SN -/

theorem sn_mem_gA : Sn.c "gA" - (Sn.c "oLA" + Sn.c "oEA" + Sn.c "oLZ" + Sn.c "oEZ" + Sn.c "oLX" +
    Sn.c "oEX") ∈ Sn.constraints := by
  unfold Sn.constraints; simp only [List.mem_append, List.mem_cons]; simp

theorem sn_mem_ba0 : (1 - Sn.c "gA") * (Sn.b 0 - Sn.a 0) ∈ Sn.constraints := by
  unfold Sn.constraints
  simp only [List.mem_append, List.mem_flatMap, List.mem_range, List.mem_cons]
  mem_search 0 (by decide : (0 : Nat) < 64)

theorem sn_bool_cont : bool (Sn.c "cont") ∈ Sn.constraints := by
  unfold Sn.constraints
  simp only [List.mem_append, List.mem_map]
  repeat apply Or.inl
  exact ⟨"cont", by simp, rfl⟩

theorem sn_b0 : Sn.b 0 = Sn.c "b" 0 := by simp [Sn.b, KMAX]

open FieldWalk2 in
set_option maxHeartbeats 4000000 in
/-- A descending `SN` row is not an absent / split op: `gA = 0`. -/
theorem sn_gdn_gA (hc : ∀ e ∈ Sn.table.constraints, e.eval tr t r pub = 0)
    (hg : ev tr t r pub (Sn.c "gdn") = 1) : ev tr t r pub (Sn.c "gA") = 0 := by
  have h1 := sn_gdn_ops hc hg
  have hE : ev tr t r pub (Sn.c "isE") = ev tr t r pub ((["oEU", "oED", "oEA", "oEZ", "oES", "oEB", "oEX",
      "oEP", "oEM"].map sc).foldl (· + ·) (sc "oEF")) := sub_eq (hold rfl hc FieldWalk.sn_mem_isE)
  rw [sn_sum hc "oEF" ["oEU", "oED", "oEA", "oEZ", "oES", "oEB", "oEX", "oEP", "oEM"] (by decide)
    (by decide)] at hE
  simp only [sc, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hE
  have hEle := sn_flag_le hc "isE" (by simp)
  have hF : ev tr t r pub ((["oEF", "oLA", "oEA"].map sc).foldl (· + ·) (sc "oLF")) =
      ev tr t r pub (Sn.c "mF") := sub_eq (hold rfl hc FieldWalk.sn_mem_mF)
  rw [sn_sum hc "oLF" ["oEF", "oLA", "oEA"] (by decide) (by decide)] at hF
  simp only [sc, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hF
  have hU : ev tr t r pub ((["oEU", "oLX", "oEX"].map sc).foldl (· + ·) (sc "oLR")) =
      ev tr t r pub (Sn.c "mU") := sub_eq (hold rfl hc FieldWalk.sn_mem_mU)
  rw [sn_sum hc "oLR" ["oEU", "oLX", "oEX"] (by decide) (by decide)] at hU
  simp only [sc, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hU
  have hD : ev tr t r pub ((["oED", "oLZ", "oEZ", "oES", "oEB"].map sc).foldl (· + ·) (sc "oLD")) =
      ev tr t r pub (Sn.c "mD") := sub_eq (hold rfl hc FieldWalk.sn_mem_mD)
  rw [sn_sum hc "oLD" ["oED", "oLZ", "oEZ", "oES", "oEB"] (by decide) (by decide)] at hD
  simp only [sc, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hD
  have hA := sn_act_sum hc
  have hAl := sn_flag_le hc "act" (by simp)
  have hG : ev tr t r pub (Sn.c "gA") = ev tr t r pub ((["oEA", "oLZ", "oEZ", "oLX", "oEX"].map sc).foldl
      (· + ·) (sc "oLA")) := sub_eq (hold rfl hc sn_mem_gA)
  rw [sn_sum hc "oLA" ["oEA", "oLZ", "oEZ", "oLX", "oEX"] (by decide) (by decide)] at hG
  simp only [sc, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil] at hG
  omega

/-- A descending `SN` row's first key nibble is looked up against the walk key: `b₀ = 1`. -/
theorem sn_gdn_b0 (hc : ∀ e ∈ Sn.table.constraints, e.eval tr t r pub = 0)
    (hg : ev tr t r pub (Sn.c "gdn") = 1) : ev tr t r pub (Sn.b 0) = 1 := by
  have hgA := sn_gdn_gA hc hg
  have ha := (FieldWalk2.sn_gdn_walk hc hg).2.2
  have e := hold rfl hc sn_mem_ba0
  rw [show ev tr t r pub ((1 - Sn.c "gA") * (Sn.b 0 - Sn.a 0)) = 0 ↔
      ev tr t r pub (Expr.mul (1 - Sn.c "gA") (Sn.b 0 - Sn.a 0)) = 0 from Iff.rfl,
    ev_mul_gate _ (ev_one_sub0 hgA)] at e
  rw [eq_of_sub e, sn_a_lt 0 (by decide)]
  exact ha

end

/-! ## From `Holds` -/

section
variable {tr : Trace Fp} {pub : List Fp}

/-- **`hbr` from `Holds`**: a descending `BR` row's depth is a looked-up key position. -/
theorem br_depth {D : Nat} {extra : List Table} {nb np : Nat} (hH : Holds (fullAir D extra nb np) pub tr)
    (hxN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false) :
    ∀ r, r < tr.height 2 → (Br.c "gdn").eval tr 2 r pub = 1 → ev tr 2 r pub (Br.c "d") < 2 ^ 21 := by
  intro r hr hg
  have hc := tbl_br D extra nb np hH r (List.mem_range.2 hr)
  have h1 := br_gdn_gEnd hc (eval_one_ev hg)
  exact (nib_of_rcv (t := 2) (g := Br.c "act" - Br.gEnd) (e₀ := Br.c "kid") (e₂ := Br.nib) hH hxN
    (by simp [m5aAir])
    (by show _ ∈ Br.interactions; exact memD_mem (by decide)) hr (ev_one_eval h1)).2

/-- **The `SN` depth bound**: a descending `SN` row's depth is a looked-up key position. -/
theorem sn_depth {D : Nat} {extra : List Table} {nb np : Nat} (hH : Holds (fullAir D extra nb np) pub tr)
    (hxN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false) :
    ∀ r, r < tr.height 3 → (Sn.c "gdn").eval tr 3 r pub = 1 → ev tr 3 r pub (Sn.c "d") < 2 ^ 21 := by
  intro r hr hg
  have hc := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
  have h1 := sn_gdn_b0 hc (eval_one_ev hg)
  have := (nib_of_rcv (t := 3) (g := Sn.b 0) (e₀ := Sn.c "kid") (e₁ := Sn.c "d" + K 0) (e₂ := Sn.k 0)
    hH hxN (by simp [m5aAir])
    (by show _ ∈ Sn.interactions; exact memD_mem (by decide)) hr (ev_one_eval h1)).2
  have hd := ev_lt (tr := tr) (t := 3) (r := r) (pub := pub) (Sn.c "d")
  rw [ev_hadd, show K 0 = Expr.const 0 from rfl, ev_const, Nat.zero_mod, Nat.add_zero,
    Nat.mod_eq_of_lt hd] at this
  exact this

/-- **The open premise for continued keys**: a descending `SN` head whose key continues in `SNC`
rows (`cont = 1`) is strictly above its child (`d < d + klen` in the field, `klen = Σ a + rl`). -/
def SncDeeper (tr : Trace Fp) (pub : List Fp) : Prop :=
  ∀ r, r < tr.height 3 → (Sn.c "gdn").eval tr 3 r pub = 1 → ev tr 3 r pub (Sn.c "cont") = 1 →
    ev tr 3 r pub (Sn.c "d") < ev tr 3 r pub (Sn.c "d" + Sn.c "klen")

/-- **Children are in the same walk and strictly deeper**, with the depth bounds discharged
(`SncDeeper` for continued keys). -/
theorem walk_deeper' {Ref Pay Res : Type} (Dc : Dec Ref Pay Res) (D : Nat) (extra : List Table)
    (nb np : Nat) (hH : Holds (fullAir D extra nb np) pub tr)
    (hxN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false) (hsc : SncDeeper tr pub) :
    ∀ x ∈ walkRows Dc tr pub, ∀ c, x.dout = some c → c.w = x.din.w ∧ x.din.d < c.d := by
  intro x hx c hc
  rcases List.mem_append.1 hx with hx | hx
  · obtain ⟨r, hr, -, rfl⟩ := mem_rowsOf hx
    simp only at hc
    split at hc
    · rename_i hg
      obtain rfl := Option.some.inj hc
      simp only [Dec.down]
      rw [vals_getD br_dd_head 0 (by decide) _ rfl, vals_getD br_di_head 0 (by decide) _ rfl,
        vals_getD br_dd_head 1 (by decide) _ rfl, vals_getD br_di_head 1 (by decide) _ rfl]
      refine ⟨rfl, ?_⟩
      change ev tr 2 r pub (Br.c "d") < ev tr 2 r pub (Br.c "d" + 1)
      have := br_depth hH hxN r hr hg
      rw [ev_hadd, ev_one, Nat.mod_eq_of_lt (by omega)]
      omega
    · simp at hc
  · obtain ⟨r, hr, -, rfl⟩ := mem_rowsOf hx
    simp only at hc
    split at hc
    · rename_i hg
      obtain rfl := Option.some.inj hc
      simp only [Dec.down]
      rw [vals_getD sn_dd_head 0 (by decide) _ rfl, vals_getD sn_di_head 0 (by decide) _ rfl,
        vals_getD sn_dd_head 1 (by decide) _ rfl, vals_getD sn_di_head 1 (by decide) _ rfl]
      refine ⟨rfl, ?_⟩
      change ev tr 3 r pub (Sn.c "d") < ev tr 3 r pub (Sn.c "d" + Sn.c "klen")
      have hc3 := tbl_sn D extra nb np hH r (List.mem_range.2 hr)
      rcases ev_bool (hold rfl hc3 sn_bool_cont) with hcont | hcont
      · have hd := sn_depth hH hxN r hr hg
        obtain ⟨h1, h2⟩ := FieldWalk2.sn_gdn_klen hc3 (eval_one_ev hg) hcont
        rw [ev_hadd, Nat.mod_eq_of_lt (by omega)]
        omega
      · exact hsc r hr hg hcont
    · simp at hc

/-- **The walk shape of the decoded rows, from `Holds`** (premise: `SncDeeper`). -/
theorem walk_shape' {Ref Pay Res : Type} (Dc : Dec Ref Pay Res) (D : Nat) (extra : List Table)
    (nb np : Nat) (hH : Holds (fullAir D extra nb np) pub tr) (hD : D ≤ 30)
    (hxN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false) (hsc : SncDeeper tr pub) :
    WalkShape (walkRoots Dc tr pub) (walkRows Dc tr pub) :=
  ⟨walk_deeper' Dc D extra nb np hH hxN hsc, walk_rootUniq Dc D extra nb np hH hD⟩

open StateM5a.Store StateM5a.BusWalk NearSpec NearSpecV3.D2 in
/-- **`air_batched_changes` without the depth premises** (`hbr`, `hsn` → `SncDeeper`). -/
theorem air_batched_changes' (hCR : Walk.Sha256CR) (σ : Store) (keyOf : Nat → List Nat)
    (Dc : Dec Ref Pay Res) (D : Nat) (extra : List Table) (nb np : Nat)
    (hH : Holds (fullAir D extra nb np) pub tr) (hD : D ≤ 30)
    (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP)
    (hxN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false) (hsc : SncDeeper tr pub)
    (hloc : ∀ r ∈ walkRows Dc tr pub, LocalOK (Sem σ keyOf) r)
    (cs : List (Bytes × Option Bytes)) (prev post : Bytes) (N : Nat) (a b : Nat → Ref)
    (hT : (tchSends (Ref.dig prev) N b).Perm (tchRecvs (Ref.dig post) cs.length N a))
    (hroot : ∀ j (hj : j < N), ∃ q ∈ walkRoots Dc tr pub, q.dn.ref = a j ∧ q.res.ref = b j ∧ q.dn.d = 0 ∧
      ∀ (hj' : j < cs.length), PayOf keyOf q.dn.pay cs[j] ∧ (cs[j].2 = none → RefKind q.res.rk))
    (T : PTrie) (hT0 : T.hashOf = prev) (hF : Full T ∧ T.wf = true) :
    ∃ T', applyChanges (some T) cs = some (some T') ∧ rootHash (some T') = post := by
  obtain ⟨hDn, hUp⟩ := walk_traffic Dc D extra nb np hH hx
  exact bus_batched_changes hCR σ keyOf (walk_shape' Dc D extra nb np hH hD hxN hsc) hDn hUp hloc cs
    prev post N a b hT hroot T hT0 hF

open StateM5a.Store StateM5a.BusWalk NearSpec NearSpecV3.D2 in
/-- **The same with the split-aware semantics `SemS`.** -/
theorem air_batched_changesS' (hCR : Walk.Sha256CR) (σ : Store) (keyOf : Nat → List Nat)
    (Dc : Dec Ref Pay Res) (D : Nat) (extra : List Table) (nb np : Nat)
    (hH : Holds (fullAir D extra nb np) pub tr) (hD : D ≤ 30)
    (hx : ∀ T ∈ extra, ∀ i ∈ T.interactions, i.bus ≠ B_DOWN ∧ i.bus ≠ B_UP)
    (hxN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false) (hsc : SncDeeper tr pub)
    (hloc : ∀ r ∈ walkRows Dc tr pub, LocalOK (SemS σ keyOf) r)
    (cs : List (Bytes × Option Bytes)) (prev post : Bytes) (N : Nat) (a b : Nat → Ref)
    (hT : (tchSends (Ref.dig prev) N b).Perm (tchRecvs (Ref.dig post) cs.length N a))
    (hroot : ∀ j (hj : j < N), ∃ q ∈ walkRoots Dc tr pub, q.dn.ref = a j ∧ q.res.ref = b j ∧ q.dn.d = 0 ∧
      ∀ (hj' : j < cs.length), PayOf keyOf q.dn.pay cs[j] ∧ (cs[j].2 = none → RefKind q.res.rk))
    (T : PTrie) (hT0 : T.hashOf = prev) (hF : Full T ∧ T.wf = true) :
    ∃ T', applyChanges (some T) cs = some (some T') ∧ rootHash (some T') = post := by
  obtain ⟨hDn, hUp⟩ := walk_traffic Dc D extra nb np hH hx
  exact bus_batched_changesS hCR σ keyOf (walk_shape' Dc D extra nb np hH hD hxN hsc) hDn hUp hloc cs
    prev post N a b hT hroot T hT0 hF

end

end StateM5a.DepthBound
