import ZkFormal.NearV3.Rcpt.Extract.RcptView

/-!
# ZkFormal.NearV3.Rcpt.Link.Srec — the signer = receiver test of system receipts

For receipt `x` (index `r`) the `SREC` traffic is: sends `(r, i, v_i)` for the receiver rows
with `gv_i`, receives `(r, i, sx_i)` for the signer rows with `gs_i` (`rSends`/`rRecvs`).  If the
balance restricted to messages of receipt `r` holds (only this receipt uses `r`), then with
`RcptE.Wf`'s `ee` / `neq` facts:

* `srec_ee`: `ee ⇒ signer = receiver`;
* `srec_neq`: `sys ∧ ¬ee ⇒ signer ≠ receiver`.
-/

namespace ZkFormal.NearV3

open ZkFormal.Near

def srecS (r : Nat) (x : RcptE) : List Msg :=
  ((List.range x.v.length).filter fun i => x.gv.getD i false).map fun i => [r, i, x.v.getD i 0]
def srecR (r : Nat) (x : RcptE) : List Msg :=
  ((List.range x.s.length).filter fun i => x.gs.getD i false).map fun i => [r, i, x.sx.getD i 0]

/-- Every received message of receipt `r` is sent by it. -/
def SrecBal (r : Nat) (x : RcptE) : Prop := ∀ m ∈ srecR r x, m ∈ srecS r x

theorem srec_recv_val {r : Nat} {x : RcptE} (H : SrecBal r x) {i : Nat} (hi : i < x.s.length)
    (hg : x.gs.getD i false = true) : i < x.v.length ∧ x.sx.getD i 0 = x.v.getD i 0 := by
  have hm : [r, i, x.sx.getD i 0] ∈ srecR r x :=
    List.mem_map.mpr ⟨i, List.mem_filter.mpr ⟨List.mem_range.mpr hi, hg⟩, rfl⟩
  obtain ⟨i', hi', he⟩ := List.mem_map.mp (H _ hm)
  simp only [List.cons.injEq] at he
  obtain ⟨-, rfl, he, -⟩ := he
  exact ⟨List.mem_range.mp (List.mem_filter.mp hi').1, he.symm⟩

/-- **`ee ⇒ signer = receiver`.** -/
theorem srec_ee {r tok tok' : Nat} {bgpB : List Nat} {x : RcptE} (W : x.Wf r bgpB tok tok')
    (H : SrecBal r x) (he : x.ee = true) : x.s = x.v := by
  obtain ⟨-, hlen, -, hgs, hsx⟩ := W.ee he
  apply List.ext_getElem hlen
  intro i h1 h2
  have := srec_recv_val H h1 (hgs i h1)
  rw [hsx i h1] at this
  simpa [List.getD_eq_getElem?_getD, h1, h2] using this.2

/-- **`sys ∧ ¬ee ⇒ signer ≠ receiver`.** -/
theorem srec_neq {r tok tok' : Nat} {bgpB : List Nat} {x : RcptE} (W : x.Wf r bgpB tok tok')
    (H : SrecBal r x) (hs : x.sys = true) (he : x.ee = false) : x.s ≠ x.v := by
  intro heq
  rcases W.neq hs he with hl | ⟨i, hi, hg, hne⟩
  · exact hl (by rw [heq])
  · have := (srec_recv_val H hi hg).2
    exact hne (by rw [this, heq])

end ZkFormal.NearV3
