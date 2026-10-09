import ZkFormal.NearV3.Assembly.RoutingQTrace

namespace ZkFormal.NearV3.Assembly.RoutingQCandidate
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near ZkFormal.Near.Dsl RcptV3 RcptV3Proof

/-- The old control constraints themselves force every first receiver row to
follow a receiver-length row; the cyclic final-to-first edge is excluded too. -/
theorem receiver_predecessor {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL : TableLocal RcptV3.table tr t pub) {r : Nat} (hr : r<tr.height t)
    (hs : startsReceiver tr t ((r+1)%tr.height t)) : tr.cell t r sVL=1 := by
  have hheight : 0<tr.height t := by omega
  have hnr : r+1<tr.height t := by
    by_cases hn : r+1<tr.height t
    · exact hn
    exfalso
    have he : r+1=tr.height t := by omega
    have hv : tr.cell t 0 sV=1 := by simpa [startsReceiver,he] using hs.1
    have hz := (oneHot hL hheight (by simp [states]) (row0 hL hheight).1).2 sV
      (by simp [states]) (by decide)
    rw [hz] at hv
    exact fp_zero_ne_one hv
  rw [Nat.mod_eq_of_lt hnr] at hs
  have hot := oneHot hL hnr (by simp [states]) hs.1
  have ha : tr.cell t r act=1 := by
    rcases isBool hL hr (show act∈boolCols by simp [boolCols]) with ha|ha
    · have hz := pad hL hnr ha
      rw [hot.1] at hz; exact False.elim (fp_zero_ne_one hz.symm)
    · exact ha
  have he : tr.cell t r fe=1 := by
    rcases isBool hL hr (show fe∈boolCols by simp [boolCols]) with he|he
    · have hz := (inField hL hnr ha he).2.2.1
      rw [hs.2] at hz; exact False.elim (fp_zero_ne_one hz.symm)
    · exact he
  have hnz : ∀s∈states,s≠sV → tr.cell t (r+1) s=0 := hot.2
  have transition (x y : Nat) (g : Expr) (hm : (x,y,g)∈RcptV3.succ)
      (hy : y∈states) (hyv : y≠sV) : tr.cell t r x*g.eval tr t r pub=0 := by
    have hm' : Expr.mul (mul3 (c fe) (c x) g) (Dsl.not (n y))∈cStates := by
      have hm'' := List.mem_map_of_mem (f := fun (p : Nat×Nat×Expr)=>
        Expr.mul (mul3 (c fe) (c p.1) p.2.2) (Dsl.not (n p.2.1))) hm
      unfold cStates; simp only [List.mem_append,hm'',true_or,or_true]
    have hc := hL.constr r hr _ (mem_st hm')
    simp only [eval_mul,eval_mul3,eval_c,eval_not,eval_n,nxt hnr,he,hnz y hy hyv] at hc
    grind
  have hb := hL.constr r hr (mul3 brkE (n act) (Dsl.not (.add (n sPL) (n sCL))))
    (mem_st (by simp [cStates]))
  simp only [brkE,lhEnd,eval_mul3,eval_mul,eval_add,eval_c,eval_n,eval_not,nxt hnr,
    he,hot.1,hnz sPL (by simp [states]) (by decide),
    hnz sCL (by simp [states]) (by decide)] at hb
  have hrl := (bounds hL hr).1
  rw [he] at hrl
  have hsum := sumStates hL hr
  rw [ha] at hsum
  simp only [states,fsum] at hsum
  -- The field successor equations below leave only the receiver-length state.
  have h1 := transition sPL sP (k 1) (by simp [RcptV3.succ]) (by simp [states]) (by decide)
  have h2 := transition sP sVL (k 1) (by simp [RcptV3.succ]) (by simp [states]) (by decide)
  have h3 := transition sV sRID (k 1) (by simp [RcptV3.succ]) (by simp [states]) (by decide)
  have h4 := transition sRID sT0 (k 1) (by simp [RcptV3.succ]) (by simp [states]) (by decide)
  have h5 := transition sT0 sSL (k 1) (by simp [RcptV3.succ]) (by simp [states]) (by decide)
  have h6 := transition sSL sS (k 1) (by simp [RcptV3.succ]) (by simp [states]) (by decide)
  have h7 := transition sS sKT (k 1) (by simp [RcptV3.succ]) (by simp [states]) (by decide)
  have h8 := transition sKT sPK (k 1) (by simp [RcptV3.succ]) (by simp [states]) (by decide)
  have h9 := transition sPK sGP (k 1) (by simp [RcptV3.succ]) (by simp [states]) (by decide)
  have h10 := transition sGP sTL (k 1) (by simp [RcptV3.succ]) (by simp [states]) (by decide)
  have h11 := transition sTL sDEP (k 1) (by simp [RcptV3.succ]) (by simp [states]) (by decide)
  have h12 := transition sDEP sXP0 (k 1) (by simp [RcptV3.succ]) (by simp [states]) (by decide)
  have h13 := transition sXP0 sXRI (c RcptV3.hr) (by simp [RcptV3.succ]) (by simp [states]) (by decide)
  have h14 := transition sXP0 sXG (Dsl.not (c RcptV3.hr)) (by simp [RcptV3.succ]) (by simp [states]) (by decide)
  have h15 := transition sXRI sXG (k 1) (by simp [RcptV3.succ]) (by simp [states]) (by decide)
  have h16 := transition sXG sXST (k 1) (by simp [RcptV3.succ]) (by simp [states]) (by decide)
  have h17 := transition sXST sXL0 (k 1) (by simp [RcptV3.succ]) (by simp [states]) (by decide)
  have h18 := transition sXL0 sXLH (k 1) (by simp [RcptV3.succ]) (by simp [states]) (by decide)
  have h19 := transition sXLH sXRH (c RcptV3.hr) (by simp [RcptV3.succ]) (by simp [states]) (by decide)
  have h20 := transition sXRH sXRF (k 1) (by simp [RcptV3.succ]) (by simp [states]) (by decide)
  have h21 := transition sXRF sXRZ (k 1) (by simp [RcptV3.succ]) (by simp [states]) (by decide)
  simp only [eval_k,eval_c,eval_not] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 h17 h18 h19 h20 h21
  grind only

/-- Complete local trace patch with no renderer-shape premise: only the honest
interval-index bound is required in addition to the original local constraints. -/
theorem patch_local_of_q_bound {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL : TableLocal RcptV3.table tr t pub)
    (hQ : ∀r,r<tr.height t → startsReceiver tr t r → cv tr t r q<128) :
    TableLocal candidateTable (patchTrace tr t) t pub :=
  patch_local hL hQ (fun _ hr hs=>receiver_predecessor hL hr hs)

end ZkFormal.NearV3.Assembly.RoutingQCandidate
