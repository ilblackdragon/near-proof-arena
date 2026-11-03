import StateM5a.KeyDecode

/-!
# StateM5a.KeyLookups — every `NIB` / `KLEN` receive of the AIR, as a row fact

Instances of `KeyDecode.nib_of_rcv` / `klen_of_rcv` for each receiving interaction (`BR`, `SN`,
`SNC`, `KCMP`), in the form the per-row decoding consumes: on row `r` of the table, when the
receive's bit is `1`,

* `NIB(x, i, n)`: `(keyOf tr (ev x))[ev i]? = some (ev n) ∧ ev i < 2^21`;
* `KLEN(x, l)`: `(keyOf tr (ev x)).length = ev l`.

Premise: `Holds` of `fullAir D extra` with `extra` sending nothing on `NIB` / `KLEN`.
Membership of each interaction in its table is checked by `decide` (`memD`).
-/

namespace StateM5a.KeyLookups

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.DecodeM5a StateM5a.KeyDecode

set_option maxRecDepth 100000

section
variable {tr : Trace Fp} {pub : List Fp} {D : Nat} {extra : List Table} {nb np : Nat}
  (hH : Holds (fullAir D extra nb np) pub tr)
  (hN : ∀ T ∈ extra, sendsOn T.interactions B_NIB = false)
  (hL : ∀ T ∈ extra, sendsOn T.interactions B_KLEN = false)
  {r : Nat}

/-- The `NIB` fact of row `r` for message `[e₀, e₁, e₂]` of table `t`. -/
def NibAt (tr : Trace Fp) (pub : List Fp) (t r : Nat) (e₀ e₁ e₂ : Expr) : Prop :=
  (keyOf tr (ev tr t r pub e₀))[ev tr t r pub e₁]? = some (ev tr t r pub e₂) ∧ ev tr t r pub e₁ < 2 ^ 21

/-- The `KLEN` fact of row `r` for message `[e₀, e₁]` of table `t`. -/
def KlenAt (tr : Trace Fp) (pub : List Fp) (t r : Nat) (e₀ e₁ : Expr) : Prop :=
  (keyOf tr (ev tr t r pub e₀)).length = ev tr t r pub e₁

include hH hN in
theorem nib_at {t : Nat} (ht : t < (m5aAir D).tables.length) {g e₀ e₁ e₂ : Expr}
    (hi : rcv B_NIB g [e₀, e₁, e₂] ∈ ((m5aAir D).tables[t]).interactions) (hr : r < tr.height t)
    (hg : g.eval tr t r pub = 1) : NibAt tr pub t r e₀ e₁ e₂ :=
  nib_of_rcv hH hN ht hi hr hg

include hH hL in
theorem klen_at {t : Nat} (ht : t < (m5aAir D).tables.length) {g e₀ e₁ : Expr}
    (hi : rcv B_KLEN g [e₀, e₁] ∈ ((m5aAir D).tables[t]).interactions) (hr : r < tr.height t)
    (hg : g.eval tr t r pub = 1) : KlenAt tr pub t r e₀ e₁ :=
  klen_of_rcv hH hL ht hi hr hg

/-! ## BR (table 2) -/

include hH hN in
theorem br_nib (hr : r < tr.height 2) (hg : (Br.c "act" - Br.gEnd).eval tr 2 r pub = 1) :
    NibAt tr pub 2 r (Br.c "kid") (Br.c "d") Br.nib :=
  nib_at hH hN (by simp [m5aAir]) (by show _ ∈ Br.interactions; exact memD_mem (by decide)) hr hg

include hH hL in
theorem br_klen (hr : r < tr.height 2) (hg : Br.gEnd.eval tr 2 r pub = 1) :
    KlenAt tr pub 2 r (Br.c "kid") (Br.c "d") :=
  klen_at hH hL (by simp [m5aAir]) (by show _ ∈ Br.interactions; exact memD_mem (by decide)) hr hg

include hH hN in
theorem br_nib_sib (hr : r < tr.height 2) (hg : (Br.c "oD1").eval tr 2 r pub = 1) :
    NibAt tr pub 2 r (Br.c "kid2") (Br.c "d") Br.sib :=
  nib_at hH hN (by simp [m5aAir]) (by show _ ∈ Br.interactions; exact memD_mem (by decide)) hr hg

include hH hN in
theorem br_nib_split (hr : r < tr.height 2) (hg : (Br.c "oSL").eval tr 2 r pub = 1) :
    NibAt tr pub 2 r (Br.c "xk") (Br.c "d") Br.sib :=
  nib_at hH hN (by simp [m5aAir]) (by show _ ∈ Br.interactions; exact memD_mem (by decide)) hr hg

/-! ## SN (table 3) -/

theorem sn_mem_key : ∀ j, j < 64 →
    memD (rcv B_NIB (Sn.b j) [Sn.c "kid", Sn.c "d" + K j, Sn.k j]) Sn.interactions = true := by decide
theorem sn_mem_key2 : ∀ j, j < 64 →
    memD (rcv B_NIB (Sn.c "g2" * Sn.a j) [Sn.c "kid2", Sn.c "d" + K j, Sn.k j]) Sn.interactions = true := by
  decide

include hH hN in
/-- Key nibble `j < jm` of an `SN` row against the walk key. -/
theorem sn_nib (j : Nat) (hj : j < 64) (hr : r < tr.height 3) (hg : (Sn.b j).eval tr 3 r pub = 1) :
    NibAt tr pub 3 r (Sn.c "kid") (Sn.c "d" + K j) (Sn.k j) :=
  nib_at hH hN (by simp [m5aAir]) (by show _ ∈ Sn.interactions; exact memD_mem (sn_mem_key j hj)) hr hg

include hH hN in
/-- Key nibble `j` of an `SN` row against the second key (`g2 · a_j`). -/
theorem sn_nib2 (j : Nat) (hj : j < 64) (hr : r < tr.height 3)
    (hg : (Sn.c "g2" * Sn.a j).eval tr 3 r pub = 1) :
    NibAt tr pub 3 r (Sn.c "kid2") (Sn.c "d" + K j) (Sn.k j) :=
  nib_at hH hN (by simp [m5aAir]) (by show _ ∈ Sn.interactions; exact memD_mem (sn_mem_key2 j hj)) hr hg

include hH hN in
theorem sn_nib_mis (hr : r < tr.height 3) (hg : (Sn.c "mN" + Sn.c "mL").eval tr 3 r pub = 1) :
    NibAt tr pub 3 r (Sn.c "kid") (Sn.c "d" + Sn.c "jm") (Sn.c "y") :=
  nib_at hH hN (by simp [m5aAir]) (by show _ ∈ Sn.interactions; exact memD_mem (by decide)) hr hg

include hH hL in
theorem sn_klen_leaf (hr : r < tr.height 3) (hg : (Sn.c "isL" * (1 - Sn.c "gA")).eval tr 3 r pub = 1) :
    KlenAt tr pub 3 r (Sn.c "kid") (Sn.c "d" + Sn.c "klen") :=
  klen_at hH hL (by simp [m5aAir]) (by show _ ∈ Sn.interactions; exact memD_mem (by decide)) hr hg

include hH hL in
theorem sn_klen_lx (hr : r < tr.height 3) (hg : (Sn.c "oLX").eval tr 3 r pub = 1) :
    KlenAt tr pub 3 r (Sn.c "kid2") (Sn.c "d" + Sn.c "klen") :=
  klen_at hH hL (by simp [m5aAir]) (by show _ ∈ Sn.interactions; exact memD_mem (by decide)) hr hg

include hH hL in
theorem sn_klen_mK (hr : r < tr.height 3) (hg : (Sn.c "mK").eval tr 3 r pub = 1) :
    KlenAt tr pub 3 r (Sn.c "kid") (Sn.c "d" + Sn.c "jm") :=
  klen_at hH hL (by simp [m5aAir]) (by show _ ∈ Sn.interactions; exact memD_mem (by decide)) hr hg

/-! ## SNC (table 8) -/

theorem snc_mem_A : ∀ j, j < 64 →
    memD (rcv B_NIB (Snc.c "fA" * Snc.a j) [Snc.c "kA", Snc.c "p" + K j, Snc.c "k" j]) Snc.interactions = true := by
  decide
theorem snc_mem_B : ∀ j, j < 64 →
    memD (rcv B_NIB (Snc.c "gB" * Snc.a j) [Snc.c "kB", Snc.c "p" + K j, Snc.c "k" j]) Snc.interactions = true := by
  decide

include hH hN in
theorem snc_nibA (j : Nat) (hj : j < 64) (hr : r < tr.height 8)
    (hg : (Snc.c "fA" * Snc.a j).eval tr 8 r pub = 1) :
    NibAt tr pub 8 r (Snc.c "kA") (Snc.c "p" + K j) (Snc.c "k" j) :=
  nib_at hH hN (by simp [m5aAir]) (by show _ ∈ Snc.interactions; exact memD_mem (snc_mem_A j hj)) hr hg

include hH hN in
theorem snc_nibB (j : Nat) (hj : j < 64) (hr : r < tr.height 8)
    (hg : (Snc.c "gB" * Snc.a j).eval tr 8 r pub = 1) :
    NibAt tr pub 8 r (Snc.c "kB") (Snc.c "p" + K j) (Snc.c "k" j) :=
  nib_at hH hN (by simp [m5aAir]) (by show _ ∈ Snc.interactions; exact memD_mem (snc_mem_B j hj)) hr hg

/-! ## KCMP (table 4) -/

include hH hN in
theorem kcmp_nib_a (hr : r < tr.height 4) (hg : (Kcmp.c "act" * (1 - Kcmp.c "fin")).eval tr 4 r pub = 1) :
    NibAt tr pub 4 r (Kcmp.c "ka") (Kcmp.c "j") (Kcmp.c "x") ∧ NibAt tr pub 4 r (Kcmp.c "kb") (Kcmp.c "j") (Kcmp.c "x") :=
  ⟨nib_at hH hN (by simp [m5aAir]) (by show _ ∈ Kcmp.interactions; exact memD_mem (by decide)) hr hg,
   nib_at hH hN (by simp [m5aAir]) (by show _ ∈ Kcmp.interactions; exact memD_mem (by decide)) hr hg⟩

include hH hN in
theorem kcmp_nib_xa (hr : r < tr.height 4) (hg : (Kcmp.c "fin" * (1 - Kcmp.c "pre")).eval tr 4 r pub = 1) :
    NibAt tr pub 4 r (Kcmp.c "ka") (Kcmp.c "j") (Kcmp.c "xa") :=
  nib_at hH hN (by simp [m5aAir]) (by show _ ∈ Kcmp.interactions; exact memD_mem (by decide)) hr hg

include hH hN in
theorem kcmp_nib_xb (hr : r < tr.height 4) (hg : (Kcmp.c "fin").eval tr 4 r pub = 1) :
    NibAt tr pub 4 r (Kcmp.c "kb") (Kcmp.c "j") (Kcmp.c "xb") :=
  nib_at hH hN (by simp [m5aAir]) (by show _ ∈ Kcmp.interactions; exact memD_mem (by decide)) hr hg

include hH hL in
theorem kcmp_klen (hr : r < tr.height 4) (hg : (Kcmp.c "fin" * Kcmp.c "pre").eval tr 4 r pub = 1) :
    KlenAt tr pub 4 r (Kcmp.c "ka") (Kcmp.c "j") :=
  klen_at hH hL (by simp [m5aAir]) (by show _ ∈ Kcmp.interactions; exact memD_mem (by decide)) hr hg

end

end StateM5a.KeyLookups
