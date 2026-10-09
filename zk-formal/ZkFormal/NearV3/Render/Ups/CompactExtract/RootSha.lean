import ZkFormal.NearV3.Render.Ups.CompactExtract.NodeSha
import ZkFormal.NearV3.Render.Ups.CompactExtract.ByteRows
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl UpsV3 UpsRows
section
variable {C D : URow} (ok : RowOk C D) (hC : ∀ x, C x < P)
include ok hC

theorem w3dI (hw3 : C wt3 = 1) :
    ((C dI : Nat) : Fp) = (K_VUPS : Nat) + ((16 : Nat) : Fp) * (((512 : Nat) : Fp) * ((C tau : Nat) : Fp) + ((C nQ : Nat) : Fp)) := by
  have f := fact ok (e := .mul (c wt3) (sub (c dI) (upsId (c nQ)))) (memDigest (by simp [cDigest]))
  try simp only [upsId, mid] at f
  uev_simp
  simp only [cast_ofNat, hw3, cast1] at f
  grind

theorem w3dL (hw3 : C wt3 = 1) : ((C dL : Nat) : Fp) = ((C rlen : Nat) : Fp) := by
  have f := fact ok (e := .mul (c wt3) (sub (c dL) (c rlen))) (memDigest (by simp [cDigest]))
  uev_simp
  simp only [cast_ofNat, hw3, cast1] at f
  grind

end

section
variable {C D : URow} (ok : RowOk C D) (hC : ∀ x, C x < P) (hD : ∀ x, D x < P)
include ok hC hD

theorem w3gD (hw3 : C wt3 = 1) (hq : C qb = 0) : C gD = 1 := by
  have f := factN ok hC hD (e := sub (c gD) (.add (mul3 (c qb) (c fs) winFr) (c wt3))) (memDigest (by simp [cDigest]))
  simp only [winFr] at f
  nev_simp at f
  have := hC gD
  rw [P_lit] at this
  simp [hq, hw3] at f
  omega

end

attribute [local irreducible] UpsSeg.row UpsSeg.next
section
variable {v : List UpsSeg} (hw : Wf v) {s : UpsSeg} (hs : s∈v)
    {ps : List (Nat×Nat)} {fls : List (List (Nat×Nat))} {ws : List Nat}
    (hL : UpsLayout s ps fls ws) {ci ti di si : Nat} {kd sdx : Nat→Nat}
    (hP : UpsPlan s ps ci ti di si kd sdx)
include hw hs hL hP
theorem qlenPart (k : Nat) (hk : k < ps.length) : s.row ps[k].1 UpsV3.qlen = ps[k].2 := by
  obtain ⟨-, U⟩ := hL.part k hk
  have hℓ := U.pos
  have hle := U.le
  have hm := lenLe hw hs
  have hr := U.rows (ps[k].2 - 1) (by omega)
  have hlt : ps[k].1 + (ps[k].2 - 1) < s.rows.length := by omega
  have F := (layoutRow (nodeRowOk (okRow hw hs hlt) (rowLt hw hs _) hr.1) (rowLt hw hs _) (nextLt hw hs _)).2.2.2.2.2.2.2.2.2.2.2.1 hr.1
    (hr.2.2.2.1.2 (by omega))
  rw [hr.2.1, hr.2.2.2.2 UpsV3.qlen (by decide)] at F
  have e : ((ps[k].2 : Nat) : Fp) = ((s.row ps[k].1 UpsV3.qlen : Nat) : Fp) := by
    rw [← F, show ps[k].2 = ps[k].2 - 1 + 1 by omega, natCast_add]; rfl
  exact (natv (by rw [P_lit]; omega) (rowLt hw hs _ _) e).symm

theorem rootRow (k : Nat) (hk : k < ps.length) (hroot : k + 1 = ps.length) :
    3 < s.rows.length ∧ s.row 3 gD = 1 ∧ s.row 3 dI = upsIdN (s.row 0 tau) (k + 1) ∧ s.row 3 dL = ps[k].2 := by
  obtain ⟨h4, -, -, -, hw3⟩ := hL.walk
  have hlt : 3 < s.rows.length := by omega
  have ok3 := okRow hw hs hlt
  have hwk := hL.wk 3 (by omega)
  have hq : s.row 3 qb = 0 := by
    obtain ⟨ha, hact, -⟩ := kinds ok3 (rowLt hw hs _) (nextLt hw hs _)
    omega
  obtain ⟨hlt0, hq0, hpf⟩ := pFirst hw hs hL k hk
  have hr := (hP.root k hk).2 hroot
  obtain ⟨-, hjn, hql⟩ := rootPart (okRow hw hs hlt0) (rowLt hw hs _) (nextLt hw hs _) hq0 hr
  have hj : s.row ps[k].1 j = k + 1 := (hL.part k hk).1
  have sc := hL.segc
  have hnQ : s.row 3 nQ = k + 1 := by
    rw [sc 3 hlt nQ (by decide), ← sc _ hlt0 nQ (by decide), ← hjn, hj]
  have hrl : s.row 3 rlen = ps[k].2 := by
    rw [sc 3 hlt rlen (by decide), ← sc _ hlt0 rlen (by decide), ← hql, qlenPart hw hs hL hP k hk]
  refine ⟨hlt, w3gD ok3 (rowLt hw hs _) (nextLt hw hs _) hw3 hq, ?_, ?_⟩
  · have := dIj_nat (rowLt hw hs _ _) (w3dI ok3 (rowLt hw hs _) hw3)
    rw [this, hnQ, sc 3 hlt tau (by decide)]
  · rw [natv (rowLt hw hs _ _) (rowLt hw hs _ _) (w3dL ok3 (rowLt hw hs _) hw3), hrl]

/-- The root output bytes and post-root register are authenticated by SHA;
this is the base case for downward authentication of every child part. -/
theorem root_authenticated (hsha : UpsShaSeg s ps) (k : Nat) (hk : k<ps.length)
    (hroot : k+1=ps.length) :
    (∀d,d<ps[k].2 → s.row (ps[k].1+d) b<256) ∧
      regN (s.row 3)=(NearSpec.sha256 ((rowsB s ps[k].1 ps[k].2).map UInt8.ofNat)).map UInt8.toNat := by
  obtain ⟨hr,hg,hi,hl⟩:=rootRow hw hs hL hP k hk hroot
  exact hsha 3 hr hg k hk hi hl
end
end ZkFormal.NearV3.Render.UpsRelay.Extract
