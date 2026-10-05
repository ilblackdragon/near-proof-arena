import ZkFormal.Bcs.StarkRefine
import ZkFormal.Bcs.Multiproof

/-!
# ZkFormal.Bcs.StarkMain — L4's compiled verifier certifies `AcceptsIn`

`compile_accepts : CompileAcceptsStmt`.
-/

set_option linter.unusedSimpArgs false
set_option linter.deprecated false
set_option linter.unusedSectionVars false

namespace ZkFormal.Bcs.Adapter

open ArenaCore ArenaCore.Security ZkFormal Lean.Grind

theorem parsePrefix_inv {F K : Type} [Field F] [Field K] [Stark.StarkField F K] [DecidableEq F]
    (V : Stark.IopSpec F K) (pb : Bytes) (hdr : List Nat) (ps : List (Stark.PSlot K)) (rest : Bytes)
    (h : Stark.parsePrefix (F := F) V pb = some (hdr, ps, rest)) :
    V.headerOk hdr = true ∧ Stark.parseSlots (F := F) hdr (V.schedule hdr) pb = some (ps, rest) := by
  unfold Stark.parsePrefix at h
  split at h
  · cases h
  · rename_i hdr' r' _
    split at h
    · rename_i hok
      split at h
      · cases h
      · rename_i ps' rest' hps
        cases h
        exact ⟨hok, hps⟩
    · cases h

theorem evalT_bind_some {α β : Type} {tbl : Table} {oa : OracleComp hashSpec α}
    {f : α → OracleComp hashSpec β} {b : β} (h : evalT tbl (OracleComp.bind oa f) = some b) :
    ∃ a, evalT tbl oa = some a ∧ evalT tbl (f a) = some b := by
  rw [evalT_bind] at h
  cases ha : evalT tbl oa with
  | none => rw [ha] at h; cases h
  | some a => rw [ha] at h; exact ⟨a, rfl, h⟩

theorem compile_accepts_of (hmp : MultiproofStmt) : CompileAcceptsStmt := by
  intro F K _ _ _ _ V hV tbl pub cb pb wf hev
  unfold Stark.Bcs.compile at hev
  split at hev
  · simp [evalT] at hev
  split at hev
  · simp [evalT] at hev
  rename_i hdr ps rest hpp
  obtain ⟨hok, hps⟩ := parsePrefix_inv V pb hdr ps rest hpp
  obtain ⟨d0, h0, hev⟩ := evalT_bind_some hev
  obtain ⟨⟨entries, dfin⟩, hch, hev⟩ := evalT_bind_some hev
  obtain ⟨answers, hans, hev⟩ := evalT_bind_some hev
  obtain ⟨res, hopen, hev⟩ := evalT_bind_some hev
  cases res with
  | none => simp [evalT] at hev
  | some opr =>
  obtain ⟨ops, r⟩ := opr
  simp only [evalT, Option.some.injEq, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hev
  obtain ⟨⟨⟨_, hlen⟩, hglob⟩, hchk⟩ := hev
  have hfa := parseSlots_rel (F := F) hdr _ pb ps rest hps
  -- the transcript chain
  have hinit : WHin tbl (initMsg (ctxOf pub) cb) d0 := by
    have := (evalT_starkWH tbl _ _ _).mp h0
    have e : initMsg (ctxOf pub) cb = Stark.tagInit :: Stark.initMsg pub cb := by
      simp [initMsg, Stark.initMsg, ctxOf, tagInit, Stark.tagInit, List.append_assoc]
    rw [e]; exact this
  obtain ⟨es, hrel, hchain⟩ := chain_refine wf (ctxOf pub) cb ps d0 [] entries dfin
    (roots_ok hdr _ ps hfa (hV.roots hdr hok)) (Chain.init d0 hinit) hch
  rw [List.nil_append] at hchain
  obtain ⟨psH, ssH, hsched⟩ := hV.first hdr hok
  have hvh0 : viewHeader V es [] = some hdr :=
    viewHeader_eq V hdr psH ssH ps entries es [] (hsched ▸ hfa) hrel
  have hvh := viewHeader_take V es hdr hvh0
  obtain ⟨hal_len, hlook⟩ := queryAnswers_spec tbl dfin V.numChunks answers hans
  refine ⟨es, dfin, hchain, fun j hj => ?_⟩
  have hj' : j < answers.length := by simp only [adapt] at hj; omega
  refine ⟨answers[j], hlook j hj', fun x hx => ?_⟩
  -- the query position is one of L4's positions
  have hx' : x ∈ V.positions (V.queryLog hdr) answers := by
    simp only [adapt, hvh0] at hx
    unfold Stark.IopSpec.positions at hx ⊢
    simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil] at hx
    exact List.mem_flatMap.mpr ⟨_, List.getElem_mem _, hx⟩
  -- the oracles, aligned
  have hal := align (F := F) hdr es (V.schedule hdr) (V.schedule hdr) ps entries es [] [] rfl rfl rfl hfa hrel
  rw [entOr_eq] at hopen hlen
  have hml := openAll_spec (F := F) tbl _ _ _ rest ops r hopen
  have hdep : ∀ g ∈ (Stark.schedOracles (V.schedule hdr)).zip (entOr entries),
      Stark.treeLog g.1 ≤ V.queryLog hdr := fun g hg =>
    hV.depth hdr hok g.1 (List.of_mem_zip hg).1
  obtain ⟨vals, hv, hrows⟩ := build hmp V tbl wf cb es hdr hvh _ x hx' _ _ ops hal hml hdep
  have hfst : ((Stark.schedOracles (V.schedule hdr)).zip (entOr entries)).map Prod.fst =
      Stark.schedOracles (V.schedule hdr) := List.map_fst_zip (by omega)
  rw [hfst] at hrows
  refine ⟨vals, ?_, ?_⟩
  · simp only [adapt, opensA, hvh0]
    exact hv
  · simp only [adapt, decideA, decodeView, hvh0, hok, if_true, decodeEntries_eq hdr _ ps entries es hfa hrel,
      Option.map_some, hrows, Bool.and_eq_true]
    exact ⟨hglob, hchk x hx'⟩

/-- **L4's compiled verifier certifies `AcceptsIn`.** -/
theorem compile_accepts : CompileAcceptsStmt :=
  compile_accepts_of Multiproof.multiproof_sound

end ZkFormal.Bcs.Adapter
