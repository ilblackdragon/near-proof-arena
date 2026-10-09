import ZkFormal.NearV3.Rcpt.Extract.V.ReceiptIds

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3
variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub) {y : RS}
variable (lay : Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
include hL lay

/-- Exact physical receiver field. -/
theorem route_receiver : RFld tr tt y.s (lkRow y 0) y.Lv sV := by
  exact lay.flds (sV,8+y.Lp,y.Lv) (by simp [plan])

/-- The routing end marker is the first receipt-ID row. -/
theorem route_end : RFld tr tt y.s (lkRow y y.Lv) 32 sRID := by
  have F := lay.flds (sRID,8+y.Lp+y.Lv,32) (by simp [plan])
  simpa [lkRow,Nat.add_assoc] using F

theorem route_height (k : Nat) (hk : k≤y.Lv) : lkRow y k<tr.height tt := by
  have hm : (sRID,8+y.Lp+y.Lv,32)∈plan y.h y.Lp y.Lv y.Ls y.kt := by simp [plan]
  have hh := plan_le y.h y.Lp y.Lv y.Ls y.kt _ hm
  have hf := lay.fin
  simp only at hh
  unfold lkRow
  omega

/-- The routing expression covers exactly the receiver bytes and the end marker. -/
theorem route_enabled (k : Nat) (hk : k≤y.Lv) : rwE.eval tr tt (lkRow y k) pub=1 := by
  by_cases he : k=y.Lv
  · subst k
    have F := route_end hL lay
    have hs : tr.cell tt (lkRow y y.Lv) sRID=1 := by simpa using F.fld.st 0 (by decide)
    have hf : tr.cell tt (lkRow y y.Lv) fs=1 := by simpa using F.fld.fs 0 (by decide)
    have ho := oneHot hL (route_height hL lay _ (by omega)) (by simp [states]) hs
    simp only [rwE,eval_add,eval_mul,eval_c,hs,hf,ho.2 sV (by simp [states]) (by decide)]
    grind
  · have F := route_receiver hL lay
    have hs : tr.cell tt (lkRow y k) sV=1 := by simpa [lkRow] using F.fld.st k (by omega)
    have ho := oneHot hL (route_height hL lay _ hk) (by simp [states]) hs
    simp only [rwE,eval_add,eval_mul,eval_c,hs,ho.2 sRID (by simp [states]) (by decide)]
    grind

/-- Routing lookup gate is the boolean union of the two equal-prefix flags. -/
theorem route_gate (k : Nat) (hk : k≤y.Lv) :
    tr.cell tt (lkRow y k) gBd = tr.cell tt (lkRow y k) eqL+tr.cell tt (lkRow y k) eqH-
      tr.cell tt (lkRow y k) eqL*tr.cell tt (lkRow y k) eqH := by
  have cc := con hL (route_height hL lay k hk)
    (e:=sub (c gBd) (.mul rwE (orE (c eqL) (c eqH)))) (mem_ro (by simp [cRoute]))
  simp only [orE,eval_sub,eval_add,eval_mul,eval_c,route_enabled hL lay k hk] at cc
  grind

/-- Equal-prefix flags advance with the actual byte-equality gates. -/
theorem route_step (k : Nat) (hk : k<y.Lv) :
    tr.cell tt (lkRow y (k+1)) eqL=tr.cell tt (lkRow y k) eqL*tr.cell tt (lkRow y k) eL ∧
    tr.cell tt (lkRow y (k+1)) eqH=tr.cell tt (lkRow y k) eqH*tr.cell tt (lkRow y k) eH := by
  have hq := route_height hL lay k (by omega)
  have hn : lkRow y k+1<tr.height tt := by have := route_height hL lay (k+1) (by omega); simpa [lkRow,Nat.add_assoc] using this
  have F := route_receiver hL lay
  have hs : tr.cell tt (lkRow y k) sV=1 := by simpa [lkRow] using F.fld.st k hk
  have cl := con hL hq (e:=.mul (c sV) (sub (n eqL) (.mul (c eqL) (c eL)))) (mem_ro (by simp [cRoute]))
  have ch := con hL hq (e:=.mul (c sV) (sub (n eqH) (.mul (c eqH) (c eH)))) (mem_ro (by simp [cRoute]))
  simp only [eval_mul,eval_sub,eval_c,eval_n,nxt hn,hs] at cl ch
  have he : lkRow y k+1=lkRow y (k+1) := by simp [lkRow,Nat.add_assoc]
  rw [he] at cl ch
  grind

/-- Initial prefix flags always select at least the first boundary byte. -/
theorem route_start : tr.cell tt (lkRow y 0) eqL=1 ∧
    tr.cell tt (lkRow y 0) eqH=1-tr.cell tt (lkRow y 0) hnB ∧
    tr.cell tt (lkRow y 0) gBd=1 := by
  have F := route_receiver hL lay
  have hp := F.fld.pos
  have hs : tr.cell tt (lkRow y 0) sV=1 := by simpa using F.fld.st 0 hp
  have hf : tr.cell tt (lkRow y 0) fs=1 := by simpa using F.fld.fs 0 hp
  have hq := route_height hL lay 0 (by omega)
  have cl := con hL hq (e:=mul3 (c sV) (c fs) (sub (c eqL) (k 1))) (mem_ro (by simp [cRoute]))
  have ch := con hL hq (e:=mul3 (c sV) (c fs) (sub (c eqH) (Dsl.not (c hnB)))) (mem_ro (by simp [cRoute]))
  simp only [eval_mul3,eval_sub,eval_not,eval_c,eval_k,hs,hf] at cl ch
  have hl : tr.cell tt (lkRow y 0) eqL=1 := by grind
  have hg := route_gate hL lay 0 (by omega)
  rw [hl] at hg
  exact ⟨hl,by grind,by grind⟩

/-- Once both prefix comparisons have ended, no later routing lookup can reopen. -/
theorem route_no_reopen (k : Nat) (hk : k<y.Lv) (hg : tr.cell tt (lkRow y k) gBd=0) :
    tr.cell tt (lkRow y (k+1)) gBd=0 := by
  have hq := route_height hL lay k (by omega)
  have hb := route_gate hL lay k (by omega)
  have hl := isBool hL hq (x:=eqL) (by simp [boolCols])
  have hh := isBool hL hq (x:=eqH) (by simp [boolCols])
  have hz : tr.cell tt (lkRow y k) eqL=0 ∧ tr.cell tt (lkRow y k) eqH=0 := by
    rcases hl with hl|hl <;> rcases hh with hh|hh <;> rw [hl,hh,hg] at hb <;> grind
  have he := route_step hL lay k hk
  have hn := route_gate hL lay (k+1) (by omega)
  rw [hz.1,hz.2] at he
  rw [he.1,he.2] at hn
  grind

end ZkFormal.NearV3.RcptV3Proof
