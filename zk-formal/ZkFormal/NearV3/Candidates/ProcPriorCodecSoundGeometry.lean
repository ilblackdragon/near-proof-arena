import ZkFormal.NearV3.Candidates.ProcPriorCodecSoundSender
namespace ZkFormal.NearV3.Candidates.ProcPriorCodecSoundGeometry
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Chacha ZkFormal.Chacha.Table.E
open ZkFormal.NearV3.Sched ZkFormal.NearV3.Sched.Codec
abbrev CLocal := ProcPriorCodecSoundRows.CLocal

theorem kind_member (e : Expr) (he:e∈cKind) (hn:ProcPriorCodecActual.retiredKind.contains e=false) :
    e∈ProcPriorCodecActual.constraints := by
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_filter.mpr ⟨he,by simp [hn]⟩

theorem rec_member (e : Expr) (he:e∈cRec) (hn:ProcPriorCodecActual.retiredRec.contains e=false) :
    e∈ProcPriorCodecActual.constraints := by
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_filter.mpr ⟨he,by simp [hn]⟩

def flags : List Nat := [act,kH,kR,kZ,kA,kF,fS,fR,fA,pres,e7,rs]

theorem flag_member (x : Nat) (hx:x∈flags) : Table.boolC x∈ProcPriorCodecActual.constraints := by
  apply kind_member
  · have hh:∀x∈flags,x∈boolCols := by decide +kernel
    unfold cKind
    repeat first | apply List.mem_append_left
    exact List.mem_map.mpr ⟨x,hh x hx,rfl⟩
  · have hh:∀x∈flags,ProcPriorCodecActual.retiredKind.contains (Table.boolC x)=false := by decide +kernel
    exact hh x hx

section
variable {tr : Trace Fp} {t : Nat} {pub : List Fp}

theorem kinds (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) :
    cv tr t r act ≤ 1 ∧ cv tr t r kH ≤ 1 ∧ cv tr t r kR ≤ 1 ∧ cv tr t r kZ ≤ 1 ∧
      cv tr t r kA ≤ 1 ∧ cv tr t r kF ≤ 1 ∧ cv tr t r fS ≤ 1 ∧ cv tr t r fR ≤ 1 ∧
      cv tr t r fA ≤ 1 ∧ cv tr t r pres ≤ 1 ∧
      cv tr t r act = cv tr t r kH + cv tr t r kR + cv tr t r kZ + cv tr t r kA ∧
      cv tr t r kR = cv tr t r fS + cv tr t r fR + cv tr t r fA ∧
      cv tr t r kF ≤ cv tr t r kH := by
  have b := fun x (hx : x ∈ flags) => hL.bool hr (flag_member x hx)
  have hA := b act (by simp [flags]); have hH := b kH (by simp [flags])
  have hR := b kR (by simp [flags]); have hZ := b kZ (by simp [flags])
  have hAa := b kA (by simp [flags]); have hF := b kF (by simp [flags])
  have hS := b fS (by simp [flags]); have hRr := b fR (by simp [flags])
  have hAl := b fA (by simp [flags]); have hP := b pres (by simp [flags])
  obtain ⟨q1, c1⟩ := Mem.zdvd hL hr (e := sub (c act) (.add (c kH) (.add (c kR) (.add (c kZ) (c kA)))))
    (kind_member _ (by simp [cKind]) (by decide +kernel))
  obtain ⟨q2, c2⟩ := Mem.zdvd hL hr (e := sub (c kR) (.add (c fS) (.add (c fR) (c fA))))
    (kind_member _ (by simp [cKind]) (by decide +kernel))
  obtain ⟨q3, c3⟩ := Mem.zdvd hL hr (e := .mul (c kF) (notE (c kH))) (kind_member _ (by simp [cKind]) (by decide +kernel))
  zs c1 []; zs c2 []; zs c3 []
  refine ⟨hA, hH, hR, hZ, hAa, hF, hS, hRr, hAl, hP, by omega, by omega, ?_⟩
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hF with h | h <;>
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hH with h' | h' <;> rw [h, h'] at c3 ⊢ <;> omega

/-- An active row is not the last row. -/
theorem act_next (hL : CLocal tr t pub) {r : Nat} (hr : r < tr.height t) (ha : cv tr t r act = 1) :
    r + 1 < tr.height t := by
  rcases Nat.lt_or_ge (r + 1) (tr.height t) with h | h
  · exact h
  · obtain ⟨q, c1⟩ := Mem.zdvd hL hr (e := .mul .isLast (c act)) (kind_member _ (by simp [cKind]) (by decide +kernel))
    simp only [zev_mul, zev_c, cur_cv, ha] at c1
    simp only [zev, tenv, ite_eq_left (show r + 1 = tr.height t by omega)] at c1
    omega

theorem sender_kind (hL:CLocal tr t pub) {r : Nat} (hr:r<tr.height t)
    (hS:cv tr t r fS=1) : cv tr t r kR=1 ∧ cv tr t r act=1 ∧
      cv tr t r kH+cv tr t r kR+cv tr t r kZ=1 := by
  have hh:=kinds hL hr
  omega

theorem e7_zero (hL:CLocal tr t pub) {r : Nat} (hr:r<tr.height t)
    (hR:cv tr t r kR=1) (hg:cv tr t r g<7) : cv tr t r e7=0 := by
  have hb:=hL.bool hr (flag_member e7 (by simp [flags]))
  obtain ⟨q,hq⟩:=Mem.zdvd hL hr (kind_member
    (.mul (c kR) (.mul (sub (c g) (k 7)) (c e7))) (by simp [cKind,isZ]) (by decide +kernel))
  zs hq [hR]
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with hz|hz
  · exact hz
  · rw [hz] at hq
    omega

theorem sender_step (hL:CLocal tr t pub) {r x : Nat} (hr:r<tr.height t)
    (hS:cv tr t r fS=1) (hg:cv tr t r g=x) (hx:x<7) :
    r+1<tr.height t ∧ cv tr t (r+1) fS=1 ∧ cv tr t (r+1) g=x+1 := by
  obtain ⟨hR,hA,_⟩:=sender_kind hL hr hS
  have h7:=e7_zero hL hr hR (by omega)
  have hr1:=act_next hL hr hA
  obtain ⟨q1,h1⟩:=Mem.zdvd hL hr (rec_member
    (mul3 (c kR) (notE (c e7)) (sub (n fS) (c fS))) (by simp [cRec]) (by decide +kernel))
  obtain ⟨q2,h2⟩:=Mem.zdvd hL hr (rec_member
    (mul3 (c kR) (notE (c e7)) (sub (n g) (.add (c g) (k 1)))) (by simp [cRec]) (by decide +kernel))
  zs h1 [hR,h7,hS,nx hr1]
  zs h2 [hR,h7,hg,nx hr1]
  have := Codec.lt (tr:=tr) (t:=t) (r+1) fS
  have := Codec.lt (tr:=tr) (t:=t) (r+1) g
  exact ⟨hr1,by omega,by omega⟩

theorem start (hL:CLocal tr t pub) {r : Nat} (hr:r<tr.height t) (hs:cv tr t r rs=1) :
    cv tr t r fS=1 ∧ cv tr t r g=0 := by
  obtain ⟨q1,h1⟩:=Mem.zdvd hL hr (rec_member (.mul (c rs) (notE (c fS))) (by simp [cRec]) (by decide +kernel))
  obtain ⟨q2,h2⟩:=Mem.zdvd hL hr (rec_member (.mul (c rs) (c g)) (by simp [cRec]) (by decide +kernel))
  zs h1 [hs]
  zs h2 [hs]
  have := Codec.lt (tr:=tr) (t:=t) r fS
  have := Codec.lt (tr:=tr) (t:=t) r g
  constructor <;> omega

/-- Record-start flags force the actual eight sender rows, including physical
row bounds and byte indices, using only retained corrected equations. -/
theorem sender_walk (hL:CLocal tr t pub) {r : Nat} (hr:r<tr.height t)
    (hs:cv tr t r rs=1) :
    ∀i,i<8→r+i<tr.height t ∧ cv tr t (r+i) fS=1 ∧ cv tr t (r+i) g=i ∧
      cv tr t (r+i) kH+cv tr t (r+i) kR+cv tr t (r+i) kZ=1 ∧
      (i<7→cv tr t (r+i) e7=0) := by
  intro i hi
  have hrow:∀j,j<8→r+j<tr.height t ∧ cv tr t (r+j) fS=1 ∧ cv tr t (r+j) g=j := by
    intro j
    induction j with
    | zero=>
      intro _
      obtain ⟨hS,hg⟩:=start hL hr hs
      simpa using And.intro hr (And.intro hS hg)
    | succ j ih=>
      intro hj
      obtain ⟨hrj,hSj,hgj⟩:=ih (by omega)
      simpa only [Nat.add_assoc] using sender_step hL hrj hSj hgj (by omega)
  obtain ⟨hri,hSi,hgi⟩:=hrow i hi
  obtain ⟨hR,_,henc⟩:=sender_kind hL hri hSi
  exact ⟨hri,hSi,hgi,henc,fun hi7=>e7_zero hL hri hR (by omega)⟩

/-- A single record-start fact replaces all independent row-phase and range
premises of sender_limb_ranges. This is arbitrary-trace semantic extraction,
not a theorem restricted to generated rows. -/
theorem start_bytes (hL:CLocal tr t pub) {r : Nat} (hr:r<tr.height t)
    (hs:cv tr t r rs=1) :
    r+7<tr.height t ∧
    (∀i,i<8→cv tr t r (prbit i)=cv tr t (r+i) bpost ∧ cv tr t r (prbit i)<256) ∧
    cv tr t r (prbit 0)+256*cv tr t r (prbit 1)+65536*cv tr t r (prbit 2)<2^24 ∧
    cv tr t r (prbit 3)+256*cv tr t r (prbit 4)+65536*cv tr t r (prbit 5)<2^24 ∧
    cv tr t r (prbit 6)+256*cv tr t r (prbit 7)<2^16 := by
  have hw:=sender_walk hL hr hs
  have hr7:=(hw 7 (by decide)).1
  refine ⟨hr7,?_⟩
  exact ProcPriorCodecSoundSender.sender_limb_ranges hL r hr7
    (fun i hi=>(hw i hi).2.1)
    (fun i hi=>(hw i (by omega)).2.2.2.2 hi)
    (fun i hi=>(hw i hi).2.2.2.1)

/-- A live corrected publicID multiplicity forces a record start. This lets
bus ownership select the byte-extraction theorem without a separate rs fact. -/
theorem public_id_start (hL:CLocal tr t pub) {r : Nat} (hr:r<tr.height t)
    (hm:(Expr.mul (c rs) (c nzb)).eval tr t r pub=1) : cv tr t r rs=1 := by
  have hb:=hL.bool hr (flag_member rs (by simp [flags]))
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hb with hz|hz
  · have hc:tr.cell t r rs=0 := by
      have he:(c rs).eval tr t r pub=Fp.ofNat (cv tr t r rs) := (Fp.ofNat_toNat _).symm
      rw [hz] at he
      exact he
    change tr.cell t r rs*tr.cell t r nzb=1 at hm
    rw [hc] at hm
    have hh:(0:Fp)≠1 := by decide +kernel
    exact (hh (by grind only)).elim
  · exact hz

end
end ZkFormal.NearV3.Candidates.ProcPriorCodecSoundGeometry
