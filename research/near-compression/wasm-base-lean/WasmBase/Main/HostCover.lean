import WasmBase.Main.HostSigmaBridge

/-!
# WasmBase.Main.HostCover — `HostReadCovered` from the row's consumed messages (E2E M6.2)

`HostReadCovered` (`Main/HostSigmaBridge.lean`) asks that every related pre-state on the σ-thread at a
HOST row agree with the honest pre-state `sH` on the code position, the top `k` stack entries and the
bytes of the arm's read set (with the page count).  Here it is **derived** from:

* the STATE message `inS` (same `X.offOf E.k + pc`, same `sb`) and `Ctx.loc_unique`: the same checked
  function and pc, hence (`RelW.height`) the same stack size;
* `MsgCoverStk cons n k` — the row consumes, for each of the top `k` stack slots, a space-0 message.
  Under `RelW.live` such a message is the encoding of the stack entry at that slot
  (`RelW.stack_msg`), in **both** states; the encoding is injective on integer values (`enc_num_inj`),
  so the entries are equal.  For a HOST row the argument messages are `argMsg tr r j` at slot
  `sb + h − np + j` (`host_row_cons`, `host_arg_slot`), i.e. `k = np`;
* `MsgCoverMem cons B` — the row consumes a space-3 message at every address of `B`.  Under
  `RelW.live` a space-3 message is in the environment's live set (`envSep`: stack is space 0, locals
  `16 + cid`), and `HeapOK.mem` makes it `encB a (readByte s a)`: the byte is pinned in both states.
  For a HOST row these are its HOSTB consumptions (`hostbConsH`); the honest coverage condition is
  that **the HOSTB reads of the row include `readSetOf name s_k`**;
* **page count — not pinned by `RelW`.**  `HeapOK` speaks only of the addresses in `T` (all
  `< memBytes`) and of the globals; no clause and no message of the current segment relation fixes
  `s.pages.size` (the space-8 size message `pages(state) = live [8,0,0,pages,…]` is a named
  obligation of the grow AIR, `Main/SegGrow.lean` header, not a `RelW` field).  The minimal extra
  trace fact is `HostPagesPinned`: the related pre-states at the row have the honest page count
  (it would follow from a `RelW` clause "the live space-8 message carries `pages.size`" plus the HOST
  row consuming that message).

**`hostReadCovered_of_msgs`** assembles these into `HostReadCovered`, and
**`holdRowSσ_of_msgs`** gives `HoldRowSσ` from single-state honest facts + `HostCallAt` + the two
message-coverage conditions + `HostPagesPinned` + `HostEffRely`.
-/

namespace WasmBase

open ZkFormal.Algebra Chips
open NearSpecV3.Wasm hiding P
open HostFoot TwoRun
set_option linter.unusedSimpArgs false
set_option maxRecDepth 100000

/-! ## 1. The encodings are injective on what they pin -/

/-- The encoding of an integer value determines it. -/
theorem enc_num_inj {sp i tp tp' : Nat} {v v' : Val} (hv : isNum v) (hv' : isNum v')
    (h : enc sp i v tp = enc sp i v' tp') : v = v' := by
  simp only [enc, Msg.mk.injEq] at h
  obtain ⟨-, -, htag, h0, h1, h2, h3, -⟩ := h
  have hb : ∀ w : Val, isNum w → vNum w < 2 ^ 64 := by
    intro w hw
    cases w with
    | i32 x => have := x.toNat_lt; simp only [vNum]; omega
    | i64 x => exact x.toNat_lt
    | _ => exact hw.elim
  have hlt := hb v hv; have hlt' := hb v' hv'
  have hn : vNum v = vNum v' := by omega
  cases v with
  | i32 x =>
    cases v' with
    | i32 y => simp only [vNum] at hn; exact congrArg Val.i32 (UInt32.toNat_inj.mp hn)
    | i64 y => simp [vTag] at htag
    | _ => exact hv'.elim
  | i64 x =>
    cases v' with
    | i32 y => simp [vTag] at htag
    | i64 y => simp only [vNum] at hn; exact congrArg Val.i64 (UInt64.toNat_inj.mp hn)
    | _ => exact hv'.elim
  | _ => exact hv.elim

/-- A live space-3 message pins the byte at its address. -/
theorem RelW.byte_msg {X : Ctx} {E : Env} {s : St} {f : Frame} {tps tpl : Nat → Nat} {t pc S : Nat}
    {live : Msg → Prop} {a b : Nat} (R : RelW X E s f tps tpl t pc S live a b) {x : Msg} (hx : live x)
    (hs : x.space = 3) : (readByte s x.slot).toNat = x.l0 := by
  have hE : E.live x := by
    rcases (R.live x).mp hx with h | h | h
    · obtain ⟨i, -, rfl⟩ := mem_stackView.mp h; simp [enc] at hs
    · obtain ⟨j, -, rfl⟩ := mem_localView.mp h; simp [enc, Env.lsp] at hs; omega
    · exact h
  obtain ⟨T, tpm, -, -, -, hv⟩ := R.heap.mem
  obtain ⟨c, -, rfl⟩ := mem_memView.mp ((hv x hs).mp hE)
  rfl

/-! ## 2. Message-level coverage conditions -/

/-- The row consumes a space-0 message at each of the stack slots `n − k, …, n − 1`. -/
def MsgCoverStk (cons : List Msg) (n k : Nat) : Prop :=
  ∀ j, j < k → ∃ x ∈ cons, x.space = 0 ∧ x.slot = n - k + j

/-- The row consumes a space-3 message at every address of `B`. -/
def MsgCoverMem (cons : List Msg) (B : Nat → Prop) : Prop :=
  ∀ b, B b → ∃ x ∈ cons, x.space = 3 ∧ x.slot = b

/-- **The page-count premise** (not a `RelW` fact): related pre-states on the thread at the row
have the honest page count. -/
def HostPagesPinned (X : Ctx) (σ : Nat → St) (inS : List F) (cons : List Msg) (sgin : Nat × Nat)
    (sH : St) : Prop :=
  ∀ E s f tps tpl t pc S live, RowPre X (SigJ σ) inS cons sgin E s f tps tpl t pc S live →
    s.pages.size = sH.pages.size

/-! ## 2b. The coverage conditions at a HOST row of the trace -/

/-- The HOST row's argument messages are among its consumed messages (`host_row_cons`). -/
theorem argMsg_mem_consCHS {tr : Trace} {pub : List F} {r j : Nat} (hj : j < Host.nArgs)
    (hpf : rowNat tr 22 r (Host.pf j) = 1) : argMsg tr r j ∈ consCHS tr pub (22, r) := by
  have hc : argMsg tr r j ∈ rowCons Host.table tr pub 22 r := by
    rw [host_row_cons]
    exact List.mem_flatMap.mpr ⟨j, by simpa [Host.argRange] using hj, by simp [hpf]⟩
  have e : rowConsM tr pub (22, r) = rowCons Host.table tr pub 22 r := by simp [rowConsM, chipTM2]
  unfold consCHS consCHM2
  exact List.mem_append_left _ (List.mem_append_left _ (e ▸ hc))

/-- **Stack coverage at a HOST row**: if the first `k` argument flags are set and the argument slots
are the top `k` slots (`host_arg_slot`: `hostSlot tr r j = size − np + j`, with `np = k`), the row
covers the top `k` stack slots. -/
theorem msgCoverStk_of_host {tr : Trace} {pub : List F} {r n k : Nat} (hk : k ≤ Host.nArgs)
    (hpf : ∀ j, j < k → rowNat tr 22 r (Host.pf j) = 1)
    (hslot : ∀ j, j < k → hostSlot tr r j = n - k + j) :
    MsgCoverStk (consCHS tr pub (22, r)) n k :=
  fun j hj => ⟨argMsg tr r j, argMsg_mem_consCHS (by omega) (hpf j hj), rfl, hslot j hj⟩

/-- **Memory coverage at a HOST row** from its HOSTB consumptions: "the HOSTB reads of the row
include the read set". -/
theorem msgCoverMem_of_hostb {tr : Trace} {pub : List F} {r : Nat} {B : Nat → Prop}
    (h : MsgCoverMem (hostbConsOf tr pub r) B) : MsgCoverMem (consCHS tr pub (22, r)) B := by
  intro b hb
  obtain ⟨x, hx, h1, h2⟩ := h b hb
  refine ⟨x, ?_, h1, h2⟩
  unfold consCHS consCHM2 hostbConsH
  simp only [if_true]
  exact List.mem_append_left _ (List.mem_append_right _ (List.mem_append_left _ hx))

/-! ## 3. `HostReadCovered` -/

theorem topK_eq_of {s s' : St} {k : Nat} (hn : s.stack.size = s'.stack.size)
    (h : ∀ i, s.stack.size - k ≤ i → i < s.stack.size → s.stack[i]?.getD default = s'.stack[i]?.getD default) :
    topK k s = topK k s' := by
  unfold topK
  apply Array.ext
  · simp [hn]
  · intro i h1 h2
    simp only [Array.size_extract] at h1 h2
    simp only [Array.getElem_extract]
    have := h (s.stack.size - k + i) (by omega) (by omega)
    rw [Array.getElem?_eq_getElem (by omega), Array.getElem?_eq_getElem (by omega)] at this
    simp only [Option.getD_some] at this
    rw [this]; congr 1; omega

/-- **`hostReadCovered_of_msgs`**: `HostReadCovered` from the honest pre-state's `RowPre`, the
row's consumed stack messages for the top `k` slots, its consumed space-3 messages on the read set,
and the page-count premise. -/
theorem hostReadCovered_of_msgs {X : Ctx} {σ : Nat → St} {inS : List F} {cons : List Msg}
    {sgin : Nat × Nat} {name : String} {k : Nat} {EH : Env} {sH : St} {fH : Frame} {tpsH tplH : Nat → Nat}
    {tH pcH SH : Nat} {liveH : Msg → Prop}
    (hpre : RowPre X (SigJ σ) inS cons sgin EH sH fH tpsH tplH tH pcH SH liveH)
    (hnk : nargs name ≤ k) (hkH : k ≤ sH.stack.size)
    (hstk : MsgCoverStk cons sH.stack.size k) (hmem : MsgCoverMem cons (readSetOf name sH))
    (hpg : HostPagesPinned X σ inS cons sgin sH) :
    HostReadCovered X σ inS cons sgin name k sH fH := by
  refine ⟨hnk, hkH, fun E s f tps tpl t pc S live hp => ?_⟩
  have hpg1 := hpg E s f tps tpl t pc S live hp
  obtain ⟨RH, -, hinH, hlH, ht1H, hSH, -⟩ := hpre
  obtain ⟨R, -, hin, hl, ht1, hS1, -⟩ := hp
  have hP := P_val
  -- the code position and the frame base from the STATE message
  have e := hinH.symm.trans hin
  simp only [stMsg, List.cons.injEq] at e
  obtain ⟨e0, -, -, -, e4, -⟩ := e
  have hoffH := X.off_bound RH.kLt
  have hoff := X.off_bound R.kLt
  have htot : X.M.codeSize < 2 ^ 20 := X.mf.total
  have hpcH := RH.pcLt
  have hpc := R.pcLt
  have e0' : X.offOf EH.k + pcH = X.offOf E.k + pc := natEq e0 (by omega) (by omega)
  obtain ⟨ek, epc⟩ := X.loc_unique RH.kLt hpcH R.kLt hpc e0'
  have esb : EH.sb = E.sb := natEq e4 (by have := RH.sbLt; omega) (by have := R.sbLt; omega)
  have hfn : f.fn = fH.fn := by rw [R.fn, RH.fn, ek]
  have hfpc : f.pc = fH.pc := by rw [R.pcEq, RH.pcEq, epc]
  -- the same stack size
  have hh := RH.height
  have hh' := R.height
  rw [ek, epc] at hh
  rw [hh] at hh'
  have hsz : sH.stack.size = s.stack.size := by
    have := Option.some.inj hh'; have := RH.sbLe; have := R.sbLe; omega
  refine ⟨hfn, hfpc, by omega, ?_, ?_⟩
  · -- the top `k` entries: pinned by the consumed stack messages
    apply topK_eq_of hsz
    intro i h1 h2
    obtain ⟨x, hx, hsp, hsl⟩ := hstk (i - (sH.stack.size - k)) (by omega)
    have hsl' : x.slot = i := by omega
    have m1 := RH.stack_msg (hlH x hx) hsp (by omega)
    have m2 := R.stack_msg (hl x hx) hsp (by omega)
    rw [hsl'] at m1 m2
    have hn1 := RH.numS i h2
    have hn2 := R.numS i (by omega)
    exact enc_num_inj hn1 hn2 (m1.symm.trans m2)
  · -- the bytes of the read set: pinned by the consumed space-3 messages
    refine ⟨RH.heap.pages, R.heap.pages, hpg1.symm, fun b hb => ?_⟩
    obtain ⟨x, hx, hsp, hsl⟩ := hmem b hb
    have m1 := RH.byte_msg (hlH x hx) hsp
    have m2 := R.byte_msg (hl x hx) hsp
    rw [hsl] at m1 m2
    exact UInt8.toNat_inj.mp (m1.trans m2.symm)

/-! ## 4. `HoldRowSσ` from message coverage -/

/-- **`holdRowSσ_of_msgs` (M6.2).**  `HoldRowSσ` from, at every active HOST row: one honest pre-state on
the thread with its row spec; the row's code facts (`HostCallAt`); the row consuming the top
`k ≥ nargs name` stack messages and a space-3 message at every address of the honest read set
(`readSetOf name sH`: the HOSTB reads include the read set); the page-count premise; the σ-free
rely; plus the flat row facts. -/
theorem holdRowSσ_of_msgs {X : Ctx} {tr : Trace} {pub : List F} {sg : Nat → Nat × Nat} {σ : Nat → St}
    (h : ∀ r, r < tr.height 22 → rowAct Host.table tr pub 22 r →
      ∃ (EH : Env) (sH : St) (fH : Frame) (tpsH tplH : Nat → Nat) (tH pcH SH : Nat) (liveH : Msg → Prop)
        (name : String) (k : Nat),
        RowPre X (SigJ σ) (rowInM tr pub (22, r)) (consCHS tr pub (22, r)) (sg (rowNat tr 22 r 1))
          EH sH fH tpsH tplH tH pcH SH liveH ∧
        RowSpecAt X (SigJ σ) (rowOutM tr pub (22, r)) (consCHS tr pub (22, r)) (prodCHS tr pub (22, r))
          (sg (rowNat tr 22 r 1)) (sg (rowNat tr 22 r 1 + 1)) sH fH tpsH tplH tH SH liveH ∧
        HostCallAt X (rowInM tr pub (22, r)) (consCHS tr pub (22, r)) (sg (rowNat tr 22 r 1)) σ name ∧
        nargs name ≤ k ∧ k ≤ sH.stack.size ∧
        MsgCoverStk (consCHS tr pub (22, r)) sH.stack.size k ∧
        MsgCoverMem (consCHS tr pub (22, r)) (readSetOf name sH) ∧
        HostPagesPinned X σ (rowInM tr pub (22, r)) (consCHS tr pub (22, r)) (sg (rowNat tr 22 r 1)) sH ∧
        HostEffRely X σ (rowInM tr pub (22, r)) (consCHS tr pub (22, r)) (prodCHS tr pub (22, r))
          (sg (rowNat tr 22 r 1)) (sg (rowNat tr 22 r 1 + 1)) sH liveH)
    (hflat : ∀ r, r < tr.height 22 → rowAct Host.table tr pub 22 r →
      RowFactsFlat X (rowInM tr pub (22, r)) (rowOutM tr pub (22, r)) (consCHS tr pub (22, r))
        (prodCHS tr pub (22, r))) :
    HoldRowSσ X tr pub sg σ := by
  refine holdRowSσ_of_cover (fun r hr ha => ?_) hflat
  obtain ⟨EH, sH, fH, tpsH, tplH, tH, pcH, SH, liveH, name, k, hpre, hH, hcall, hnk, hkH, hstk, hmem, hpg, hrely⟩ :=
    h r hr ha
  exact ⟨EH, sH, fH, tpsH, tplH, tH, pcH, SH, liveH, name, k, hpre, hH, hcall,
    hostReadCovered_of_msgs hpre hnk hkH hstk hmem hpg, hrely⟩

#print axioms enc_num_inj
#print axioms RelW.byte_msg
#print axioms hostReadCovered_of_msgs
#print axioms holdRowSσ_of_msgs
#print axioms msgCoverStk_of_host
#print axioms msgCoverMem_of_hostb

end WasmBase
