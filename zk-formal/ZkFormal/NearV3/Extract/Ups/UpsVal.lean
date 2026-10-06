import ZkFormal.NearV3.Extract.Ups.UpsSrc

/-!
# ZkFormal.NearV3.Extract.Ups.UpsVal — the new value from the scheduler codec (M7e, step 1)

`upsV3` receives the new value of instance `τ` from the scheduler: its length on `SPLEN (τ, L)` (`W0`)
and its bytes on `SPOST (τ, pos, b)` (value rows `4 … 3 + L`), and re-sends the bytes on
`BYTES (msgId 12 (512τ), pos, b)` for the value digest.

**Interface** (`SchedVal v sv`, owed to the scheduler lane, V3-D0-DESIGN §12): `sv τ` is the new value of
instance `τ`; every `SPLEN` receive of `upsV3` is a scheduler send `[τ, |sv τ|]` and every `SPOST` receive a
send `[τ, d, (sv τ)[d]]` with `d < |sv τ|` (as `Fp` images: a lookup into the scheduler's sends), and
`|sv τ| < 2^24`.

* **`ups_valRows`**: the value rows carry `sv τ` and their number is `|sv τ|`;
* **`ups_vlen`**: `|sv τ| = L0 + 256·L1 + 65536·L2` (`UpsExt0.vlen`), given the limbs are bytes;
* **`ups_digV`**: a `DIGEST` lookup of id `msgId 12 (512τ)` at length `|sv τ|` returns `sha256 (sv τ)`
  (`UpsExt0.digV`; `sha_core` with the value rows' `BYTES` sends).

`vbytes` (`L0 L1 L2 < 256`) is **not** constrained by the table on `W0`: SHA bounds the limbs only where
a part emits them (a fresh `VLEN` field).  It is a hypothesis here (STATUS §6 register).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.NearV3.UpsRows

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl ZkFormal.NearV3.UpsV3

/-- **Scheduler ↔ `upsV3` codec interface**: the new value `sv τ` of every instance. -/
structure SchedVal (v : List UpsSeg) (sv : Nat → NearSpec.Bytes) : Prop where
  splen : ∀ m ∈ (upsTraffic v).recvs B_SPLEN, ∃ τ, τ < P ∧ m.toFp = Msg.toFp [τ, (sv τ).length]
  spost : ∀ m ∈ (upsTraffic v).recvs B_SPOST, ∃ τ d, τ < P ∧ d < (sv τ).length ∧
    m.toFp = Msg.toFp [τ, d, ((sv τ).map UInt8.toNat).getD d 0]
  len : ∀ τ, (sv τ).length < 2 ^ 24

theorem getD_byte (l : NearSpec.Bytes) (d : Nat) : (l.map UInt8.toNat).getD d 0 < 256 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[d]? with
  | none => simp
  | some x => simp only [Option.map_some, Option.getD_some]; exact x.toNat_lt

theorem toFp3 {a b c a' b' c' : Nat} (h1 : a < P) (h2 : b < P) (h3 : c < P) (h1' : a' < P) (h2' : b' < P)
    (h3' : c' < P) (h : Msg.toFp [a, b, c] = Msg.toFp [a', b', c']) : a = a' ∧ b = b' ∧ c = c' := by
  have := Link.toFp_inj (a := [a, b, c]) (b := [a', b', c'])
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption)
    (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> assumption) h
  simpa using this

attribute [local irreducible] UpsSeg.row UpsSeg.next

section
variable {v : List UpsSeg} (hw : UpsWf v) {sv : Nat → NearSpec.Bytes} (SV : SchedVal v sv)
  {s : UpsSeg} (hs : s ∈ v) {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
  (hL : UpsLayout s L ps fls ws)
include hw SV hs hL

/-- **The value rows** carry the scheduler's value. -/
theorem ups_valRow (d : Nat) (hd : d < L) :
    d < (sv (s.row 0 tau)).length ∧ s.row (4 + d) b = ((sv (s.row 0 tau)).map UInt8.toNat).getD d 0 := by
  have hlt : 4 + d < s.rows.length := by have := hL.value.2.1; omega
  have hm : [s.row (4 + d) tau, d, s.row (4 + d) b] ∈ (upsTraffic v).recvs B_SPOST :=
    mem_upsRecvs.2 ⟨s, hs, 4 + d, hlt, by rw [hL.msgsV d hd B_SPOST false]; simp⟩
  obtain ⟨τ, d', hτ, hd', he⟩ := SV.spost _ hm
  have hP := P_lit
  have hlen := lenLe hw hs
  have hsl := SV.len τ
  obtain ⟨e1, e2, e3⟩ := toFp3 (rowLt hw hs _ _) (by omega) (rowLt hw hs _ _) hτ (by omega)
    (by have := getD_byte (sv τ) d'; omega) he
  rw [hL.segc _ hlt tau (by decide)] at e1
  subst e1; subst e2
  exact ⟨hd', e3⟩

/-- **The value length**: `|sv τ|` is the number of value rows and the `W0` limbs (when they are bytes). -/
theorem ups_vlen (hvb : s.row 0 L0 < 256 ∧ s.row 0 L1 < 256 ∧ s.row 0 L2 < 256) :
    (sv (s.row 0 tau)).length = s.row 0 L0 + 256 * s.row 0 L1 + 65536 * s.row 0 L2 ∧
      (sv (s.row 0 tau)).length = L := by
  have hP := P_lit
  have hlen := lenLe hw hs
  have hsl := SV.len (s.row 0 tau)
  obtain ⟨hL1, hL2, -⟩ := hL.value
  -- `SPLEN`
  have hm : [s.row 0 tau, (s.row 0 L0 + 256 * s.row 0 L1 + 65536 * s.row 0 L2) % P] ∈
      (upsTraffic v).recvs B_SPLEN :=
    mem_upsRecvs.2 ⟨s, hs, 0, by omega, by
      rw [hL.msgsW 0 (by omega) B_SPLEN false]; simp [hL.walk.2.1]⟩
  obtain ⟨τ, hτ, he⟩ := SV.splen _ hm
  have e := Link.toFp_inj (a := [s.row 0 tau, (s.row 0 L0 + 256 * s.row 0 L1 + 65536 * s.row 0 L2) % P])
    (b := [τ, (sv τ).length])
    (by intro x hx; simp at hx; rcases hx with rfl | rfl
        · exact rowLt hw hs _ _
        · exact Nat.mod_lt _ (by omega))
    (by intro x hx; simp at hx; rcases hx with rfl | rfl
        · exact hτ
        · have := SV.len τ; omega) he
  simp only [List.cons.injEq, and_true] at e
  obtain ⟨e1, e2⟩ := e
  subst e1
  rw [Nat.mod_eq_of_lt (by omega)] at e2
  refine ⟨e2.symm, ?_⟩
  -- the last value row: `qpos + 1 = L` in `Fp`
  have hlt : 4 + (L - 1) < s.rows.length := by omega
  obtain ⟨hvb1, hq, -, hpl⟩ := hL.value.2.2 (L - 1) (by omega)
  have F := (layoutRow (okRow hw hs hlt) (rowLt hw hs _) (nextLt hw hs _)).2.2.2.2.2.2.2.2.2.2.2.2 hvb1
    (hpl.2 (by omega))
  rw [hq, hL.segc _ hlt L0 (by decide), hL.segc _ hlt L1 (by decide), hL.segc _ hlt L2 (by decide)] at F
  have F' : ((L - 1 + 1 : Nat) : Fp) = ((s.row 0 L0 + 256 * s.row 0 L1 + 65536 * s.row 0 L2 : Nat) : Fp) := by
    rw [natCast_add, natCast_add, natCast_add, natCast_mul, natCast_mul, cast1]; grind
  have := natv (by omega) (by omega) F'
  omega

end

/-- **The value digest**: a `DIGEST` lookup of id `msgId 12 (512τ)` at length `|sv τ|` returns
`sha256 (sv τ)`. -/
theorem ups_digV {v : List UpsSeg} (hw : UpsWf v) {sv : Nat → NearSpec.Bytes} (SV : SchedVal v sv)
    {shaS shaR : Nat → List Fp → Nat} (hsha : ShaFacts shaS shaR)
    (others : List Msg) (hbytes : ∀ m, shaR B_BYTES m = cnt ((upsTraffic v).sends B_BYTES ++ others) m)
    (hoth : ∀ m ∈ others, ∀ a, m.head? = some a → a < P ∧ a % 16 ≠ K_VUPS)
    (hdig : ∀ m ∈ (upsTraffic v).recvs B_DIGEST, 0 < shaS B_DIGEST m.toFp)
    (htau : UpsTauDistinct v) (hB : UpsIdBound v)
    {s : UpsSeg} (hs : s ∈ v) {L : Nat} {ps : List (Nat × Nat)} {fls : List (List (Nat × Nat))} {ws : List Nat}
    (hL : UpsLayout s L ps fls ws) :
    ∀ i, i < s.rows.length → s.row i gD = 1 → s.row i dI = upsIdN (s.row 0 tau) 0 →
      s.row i dL = (sv (s.row 0 tau)).length → regN (s.row i) = (NearSpec.sha256 (sv (s.row 0 tau))).map UInt8.toNat := by
  intro i hi hg hI hLn
  obtain ⟨hτ, -⟩ := hB s hs
  have hP := P_lit
  let enc := (sv (s.row 0 tau)).map UInt8.toNat
  have hencL : enc.length = (sv (s.row 0 tau)).length := by simp [enc]
  have hsl := SV.len (s.row 0 tau)
  have hrecv : 0 < shaS B_DIGEST (digMsg (upsIdN (s.row 0 tau) 0) enc.length (regN (s.row i))).toFp := by
    have := hdig _ (mem_upsRecvs.2 ⟨s, hs, i, hi, digIn hw hs hL hi hg⟩)
    rwa [hI, hLn, ← hencL] at this
  have hS : ∀ m ∈ (upsTraffic v).sends B_BYTES ++ others, ∀ a, m.head? = some a →
      Fp.ofNat a = Fp.ofNat (upsIdN (s.row 0 tau) 0) →
      ∃ d, d < enc.length ∧ m = [upsIdN (s.row 0 tau) 0, d, enc.getD d 0] := by
    intro m hm a ha he
    rcases List.mem_append.1 hm with hm | hm
    · obtain ⟨s', hs', i', hi', hm'⟩ := mem_upsSends.1 hm
      obtain ⟨L', ps', fls', ws', hL'⟩ := ups_layout hw s' hs'
      obtain ⟨ci', ti', di', si', kd', sdx', hP'⟩ := ups_plan hw hs' hL'
      obtain ⟨hτ', hps2⟩ := hB s' hs'
      have hps2' := hps2 L' ps' fls' ws' hL'
      rcases Nat.lt_or_ge i' 4 with h4 | h4
      · rw [hL'.msgsW i' h4 B_BYTES true] at hm'
        simp [B_BYTES, B_MIDROOT, B_ROOT, B_DIGEST, B_S0F, B_SPLEN, B_EDGE, B_BMAP] at hm'
      rcases Nat.lt_or_ge i' (4 + L') with hv | hv
      · have hd' : i' - 4 < L' := by omega
        rw [show i' = 4 + (i' - 4) by omega, hL'.msgsV (i' - 4) hd' B_BYTES true] at hm'
        simp [B_BYTES, B_SPOST] at hm'
        subst hm'
        simp only [List.head?_cons, Option.some.injEq] at ha
        subst ha
        have e := Link.ofNat_inj (upsIdN_lt _ _) (upsIdN_lt _ _) he
        have hlt' : 4 + (i' - 4) < s'.rows.length := by omega
        rw [hL'.segc _ hlt' tau (by decide)] at e
        obtain ⟨et, -⟩ := upsIdN_inj hτ' (by omega) hτ (by omega) e
        have hss : s' = s := htau s' hs' s hs et
        subst hss
        obtain ⟨hdl, hb⟩ := ups_valRow hw SV hs' hL' (i' - 4) hd'
        exact ⟨i' - 4, by rw [hencL]; exact hdl, by rw [hL'.segc _ hlt' tau (by decide), hb]⟩
      · rw [hL'.msgsQ i' hv hi' B_BYTES true] at hm'
        simp [B_BYTES, B_DIGEST, B_UPB, B_MEMD] at hm'
        subst hm'
        simp only [List.head?_cons, Option.some.injEq] at ha
        subst ha
        obtain ⟨k', hk', e1, e2⟩ := partRow hw hs' hL' hP' hv hi'
        have hj : s'.row i' j = k' + 1 := by
          rw [show i' = ps'[k'].1 + (i' - ps'[k'].1) by omega, partPc hw hs' hL' hP' k' hk' _ (by omega) (by decide)]
          exact (hL'.part k' hk').1
        have e := Link.ofNat_inj (upsIdN_lt _ _) (upsIdN_lt _ _) he
        rw [hL'.segc _ hi' tau (by decide), hj] at e
        have := (upsIdN_inj hτ' (by omega) hτ (by omega) e).2
        omega
    · obtain ⟨h1, h2⟩ := hoth m hm a ha
      have e := Link.ofNat_inj h1 (upsIdN_lt _ _) he
      rw [e, upsIdN_val hτ (by omega)] at h2
      unfold K_VUPS at h2; omega
  have core := Link.sha_core hsha _ hbytes (upsIdN_lt _ _) (fun x hx => by
      simp only [enc, List.mem_map] at hx
      obtain ⟨y, -, rfl⟩ := hx; have := y.toNat_lt; omega)
    (by rw [hencL]; omega) (fun x hx => by
      simp only [regN, List.mem_map, List.mem_range] at hx
      obtain ⟨d, -, rfl⟩ := hx; exact rowLt hw hs _ _) hS hrecv
  rw [core.2]
  simp only [enc, toBytes, List.map_map]
  congr 2
  conv => rhs; rw [← List.map_id (sv (s.row 0 tau))]
  apply List.map_congr_left
  intro x _
  simp

end ZkFormal.NearV3.UpsRows
