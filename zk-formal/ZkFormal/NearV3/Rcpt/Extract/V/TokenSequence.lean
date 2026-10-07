import ZkFormal.NearV3.Rcpt.Extract.V.TokenValues

namespace ZkFormal.NearV3.RcptV3Proof
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3

/-- The actual token endpoints of consecutive receipt layouts form one sequence. -/
def TokenRun (tr : Trace Fp) (tt : Nat) : List RS→Nat→Nat→Prop
  | [],a,z => a=z
  | y::ys,a,z => a=tokenIn tr tt y ∧ TokenRun tr tt ys (tokenOut tr tt y) z

theorem TokenRun.append {tr : Trace Fp} {tt : Nat} {xs ys : List RS} {a b c : Nat}
    (hx : TokenRun tr tt xs a b) (hy : TokenRun tr tt ys b c) : TokenRun tr tt (xs++ys) a c := by
  induction xs generalizing a with
  | nil => simp only [TokenRun] at hx; simpa [hx] using hy
  | cons x xs ih => exact ⟨hx.1,ih hx.2⟩

variable {tr : Trace Fp} {pub : List Fp} {tt : Nat}
variable (hL : TableLocal RcptV3.table tr tt pub)
include hL

/-- Actual adjacent receipt rows compose their token endpoints. -/
theorem receipt_token_run (xs : List RS) (s a : Nat) (hne : xs≠[])
    (hc : Consec s (segsOf xs))
    (hw : ∀ y∈xs,Layout tr tt y.s y.h y.Lp y.Lv y.Ls y.kt)
    (hfirst : ∀ y ys,xs=y::ys → a=tokenIn tr tt y) :
    TokenRun tr tt xs a (tokenAt tr tt (segEnd s (segsOf xs)-1)) := by
  induction xs generalizing s a with
  | nil => contradiction
  | cons y ys ih =>
    refine ⟨hfirst y ys rfl,?_⟩
    cases ys with
    | nil =>
      have hh := tokenOut_last hL (hw y (by simp))
      simpa [TokenRun,segsOf,segEnd] using hh
    | cons z zs =>
      apply ih (s+y.tot) (tokenOut tr tt y) (by simp) hc.2 (fun w hw' => hw w (by simp [hw']))
      intro z' zs' he
      have hh : z'=z := by have := congrArg List.head? he; simpa using this.symm
      subst z'
      exact (tokenIn_next hL (hw y (by simp)) (hw z (by simp)) (by rw [hc.1]; exact hc.2.1)).symm

/-- Each complete list block has one exact token run, including empty lists. -/
theorem ListBlockWf.token_run {B : ListBlock} (h : ListBlockWf tr tt B) :
    TokenRun tr tt B.receipts (tokenAt tr tt B.start) (tokenAt tr tt (B.stop-1)) := by
  cases he : B.receipts with
  | nil =>
    exact (tokenAt_eq (h.empty_terminal_tokens hL he)).symm
  | cons y ys =>
    have hh := receipt_token_run hL B.receipts (B.start+12) (tokenAt tr tt B.start) (by simp [he]) h.consecutive h.layouts ?_
    · simpa only [he,ListBlock.stop] using hh
    · intro z zs hz
      have hc := h.consecutive
      rw [hz] at hc
      exact (tokenAt_eq (h.first_tokens hL (h.layouts z (by simp [hz])) hc.1)).symm

/-- Empty and nonempty lists compose into the table's single global token run. -/
theorem ListChain.token_run {s e : Nat} {bs : List ListBlock} (h : ListChain tr tt s bs e) :
    TokenRun tr tt (bs.flatMap ListBlock.receipts) (tokenAt tr tt s) (tokenAt tr tt (e-1)) := by
  induction h with
  | last hw _ => simpa using hw.token_run hL
  | @cons B tail e hw ht ih =>
    obtain ⟨C,hs,hc⟩ := ht.first_wf
    have ha : tr.cell tt B.stop act=1 := by
      have hst : tr.cell tt C.start sCL=1 := by simpa using hc.header.st 0 (by decide)
      rw [←hs]
      exact (oneHot hL (by have := hc.header_fin; omega) (by simp [states]) hst).1
    have hn := hw.next_tokens hL ha
    have hh := hw.token_run hL
    rw [←hn] at hh
    exact hh.append ih

/-- The global token run starts at the native zero token value. -/
theorem ListChain.zero_token_run {e : Nat} {bs : List ListBlock} (h : ListChain tr tt 0 bs e) :
    TokenRun tr tt (bs.flatMap ListBlock.receipts) 0 (tokenAt tr tt (e-1)) := by
  have hh := h.token_run hL
  have hp := height_ge hL
  rwa [tokenAt_zero hL (by omega)] at hh

end ZkFormal.NearV3.RcptV3Proof
