import ZkFormal.NearV3.Sched.Pub.Prep
import ZkFormal.V3.RefundCodec

/-! Runtime forwarding implies the native gas-only forwarding step. -/
namespace ZkFormal.NearV3.Assembly

open NearSpec NearSpec.TransferV1 NearSpecV3 Sched

def gasView (ls : List Limit) : List (Nat × Nat) := ls.map fun l => (l.shard, l.gas)

/-- One step of the exact gas-only fold in `fwdGasOk`. -/
def gasForward (ctx : ApplyCtx) (ls : List (Nat × Nat)) (r : Receipt) : Option (List (Nat × Nat)) :=
  let s := ctx.layout.shardOf r.receiverId
  let gas := refundCongestionGas r.receiverId
  let g := ((ls.find? (·.1 == s)).map (·.2)).getD GASMAX
  if g ≥ min gas allowedShardOutgoingGas then
    some (ls.map fun (x, y) => if x == s then (x, g - gas) else (x, y))
  else none

private theorem gasView_get (ls : List Limit) (s : Nat) :
    (((gasView ls).find? (·.1 == s)).map (·.2)).getD GASMAX = (Limit.get ls s).gas := by
  induction ls with
  | nil => rfl
  | cons l ls ih =>
    simp only [gasView, List.map_cons, List.find?_cons, Limit.get] at *
    split <;> simp_all

theorem receipt_size_pos (r : Receipt) : 0 < min r.encode.length maxReceiptSize := by
  simp only [Receipt.encode, List.length_append, List.length_cons, List.length_nil]
  unfold maxReceiptSize
  omega

/-- A forwarded receipt must use an existing status limit: the default has zero
bytes and every encoded receipt has positive size. -/
theorem tryForward_has_limit {ctx : ApplyCtx} {ls ls' : List Limit} {r : Receipt}
    (h : tryForward ctx ls r = some ls') :
    ∃ l ∈ ls, l.shard = ctx.layout.shardOf r.receiverId := by
  unfold tryForward at h
  dsimp only at h
  split at h
  · rename_i hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    cases hf : ls.find? (·.shard == ctx.layout.shardOf r.receiverId) with
    | none =>
      have hs := receipt_size_pos r
      simp only [Limit.get, hf, Option.getD_none] at hg
      omega
    | some l =>
      exact ⟨l, List.mem_of_find?_eq_some hf, beq_iff_eq.mp (List.find?_some (p := fun x : Limit => x.shard == ctx.layout.shardOf r.receiverId) hf)⟩
  · cases h

private theorem gasView_put {ls : List Limit} {s gas size : Nat}
    (hex : ∃ l ∈ ls, l.shard = s) :
    gasView (Limit.put ls ⟨s, gas, size⟩) =
      (gasView ls).map (fun (x, y) => if x == s then (x, gas) else (x, y)) := by
  have hany : ls.any (·.shard == s) = true := by
    rcases hex with ⟨l, hl, he⟩
    exact List.any_eq_true.mpr ⟨l, hl, beq_iff_eq.mpr he⟩
  simp only [Limit.put, hany, ↓reduceIte, gasView, List.map_map]
  apply List.map_congr_left
  intro l _
  dsimp only [Function.comp_def]
  split
  · rename_i he
    exact congrArg (fun x => (x, gas)) (beq_iff_eq.mp he).symm
  · rfl

theorem tryForward_gas {ctx : ApplyCtx} {ls ls' : List Limit} {r : Receipt}
    (h : tryForward ctx ls r = some ls') :
    gasForward ctx (gasView ls) r = some (gasView ls') := by
  have hex := tryForward_has_limit h
  unfold tryForward at h
  dsimp only at h
  split at h
  · rename_i hg
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    cases h
    unfold gasForward
    dsimp only
    simp only [gasView_get, hg.1, ↓reduceIte, gasView_put hex]
  · cases h

/-- The exact forwarding fold used for the refunds of an ordinary receipt. -/
def forwardRun (ctx : ApplyCtx) (ls : List Limit) (rs : List Receipt) : Except String (List Limit) :=
  rs.foldlM (fun ls rf => match tryForward ctx ls rf with
    | some ls' => .ok ls'
    | none => .error "out of domain (e.forwarded): generated receipt buffered") ls

theorem forwardRun_gas (ctx : ApplyCtx) :
    ∀ (rs : List Receipt) (ls ls' : List Limit), forwardRun ctx ls rs = .ok ls' →
      rs.foldlM (gasForward ctx) (gasView ls) = some (gasView ls')
  | [], ls, ls', h => by cases h; rfl
  | r :: rs, ls, ls', h => by
    unfold forwardRun at h
    simp only [List.foldlM_cons] at h ⊢
    cases hs : tryForward ctx ls r with
    | none => simp [hs, bind, Except.bind] at h
    | some next =>
      simp only [hs, bind, Except.bind] at h
      rw [tryForward_gas hs]
      exact forwardRun_gas ctx rs next ls' h

private theorem foldl_bind {α β : Type} (f : β → α → Option β) :
    ∀ (xs : List α) (acc : Option β),
      xs.foldl (fun a x => a.bind (f · x)) acc = acc.bind (xs.foldlM f)
  | [], acc => by cases acc <;> rfl
  | x :: xs, acc => by
    simp only [List.foldl_cons, List.foldlM_cons]
    rw [foldl_bind]
    cases acc <;> rfl

/-- Successful runtime forwarding from the actual initial status limits proves
the complete native gas-only check on that refund stream. -/
theorem forwardRun_fwdGasOk {ctx : ApplyCtx} {so : SchedOut} {rs : List Receipt} {ls' : List Limit}
    (h : forwardRun ctx (ctx.statuses.map fun (s, ci, missed) =>
      ⟨s, if s == ctx.own then GASMAX else prims.outGas ci missed ctx.own,
        so.grant ctx.own s⟩) rs = .ok ls') : fwdGasOk ctx rs = true := by
  have hg := forwardRun_gas ctx rs _ _ h
  unfold fwdGasOk
  change (rs.foldl (fun acc r => acc.bind (gasForward ctx · r))
    (some (ctx.statuses.map fun (s, ci, missed) =>
      (s, if s == ctx.own then GASMAX else prims.outGas ci missed ctx.own)))).isSome = true
  rw [foldl_bind]
  simp only [Option.bind_some]
  have he : gasView (ctx.statuses.map fun (s, ci, missed) =>
      ⟨s, if s == ctx.own then GASMAX else prims.outGas ci missed ctx.own,
        so.grant ctx.own s⟩) = ctx.statuses.map (fun (s, ci, missed) =>
      (s, if s == ctx.own then GASMAX else prims.outGas ci missed ctx.own)) := by
    simp [gasView, List.map_map, Function.comp_def]
  rw [he] at hg
  rw [hg]
  rfl

private theorem ordinary_refunds_prefix {ctx : Ctx} {st st' : Acc} {r : Receipt}
    (h : applyReceipt ctx st r = some st') : ∃ added, st'.refunds = st.refunds ++ added := by
  unfold applyReceipt at h
  repeat' (first | (cases h; done) | (split at h) | (dsimp only at h))
  all_goals (cases h; exact ⟨_, rfl⟩)

theorem forwardRun_append (ctx : ApplyCtx) (ls : List Limit) (xs ys : List Receipt) :
    forwardRun ctx ls (xs ++ ys) = (forwardRun ctx ls xs >>= fun ls' => forwardRun ctx ls' ys) := by
  exact List.foldlM_append

/-- Collecting runtime refunds commutes with their incremental forwarding.
The refund stream is derived from the successful receipt execution. -/
theorem applyReceipts_forwardRun (ctx : ApplyCtx) :
    ∀ (rs : List Receipt) (i : Nat) (acc : Acc) (ls : List Limit) (out : Acc × List Limit),
      applyReceipts ctx i (acc, ls) rs = .ok out →
      ∃ added, out.1.refunds = acc.refunds ++ added ∧ forwardRun ctx ls added = .ok out.2
  | [], _, acc, ls, out, h => by
    cases h
    exact ⟨[], by simp, rfl⟩
  | r :: rs, i, acc, ls, out, h => by
    simp only [applyReceipts] at h
    split at h
    · cases h
    split at h
    · obtain ⟨acc', ha, h⟩ := bind_ok h
      obtain ⟨added, he, hf⟩ := applyReceipts_forwardRun ctx rs (i + 1) acc' ls out h
      exact ⟨added, by rw [he, V3.applySystemReceipt_refunds ha], hf⟩
    · split at h
      · split at h <;> cases h
      · rename_i acc' ha
        obtain ⟨next, hn, h⟩ := bind_ok h
        obtain ⟨fresh, hfr⟩ := ordinary_refunds_prefix ha
        obtain ⟨added, he, hf⟩ := applyReceipts_forwardRun ctx rs (i + 1) acc' next out h
        refine ⟨fresh ++ added, by rw [he, hfr, List.append_assoc], ?_⟩
        have hn' : forwardRun ctx ls fresh = .ok next := by
          simp only [hfr, List.drop_left] at hn
          unfold forwardRun
          refine Eq.trans ?_ hn
          congr 1
        rw [forwardRun_append, hn']
        exact hf

theorem applyNewChunk_fwdGasOk {ctx : ApplyCtx} {t : PTrie} {rs : List Receipt} {out : MainOut}
    (h : applyNewChunk prims ctx t rs = .ok out) : fwdGasOk ctx out.outgoing = true := by
  unfold applyNewChunk at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨⟨_, so⟩, _, h⟩ := bind_ok h
  dsimp only at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨⟨acc, ls⟩, ha, h⟩ := bind_ok h
  dsimp only at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  cases h
  obtain ⟨added, he, hf⟩ := applyReceipts_forwardRun ctx rs 0 _ _ _ ha
  simp only [List.nil_append] at he
  rw [he]
  exact forwardRun_fwdGasOk hf

theorem tryForward_shards {ctx : ApplyCtx} {ls ls' : List Limit} {r : Receipt}
    (h : tryForward ctx ls r = some ls') : ls'.map Limit.shard = ls.map Limit.shard := by
  obtain ⟨l, hl, he⟩ := tryForward_has_limit h
  have hany : ls.any (·.shard == ctx.layout.shardOf r.receiverId) = true :=
    List.any_eq_true.mpr ⟨l, hl, beq_iff_eq.mpr he⟩
  unfold tryForward at h
  dsimp only at h
  split at h
  · cases h
    simp only [Limit.put, hany, ↓reduceIte, List.map_map]
    apply List.map_congr_left
    intro l _
    dsimp only [Function.comp_def]
    split
    · rename_i he
      exact (beq_iff_eq.mp he).symm
    · rfl
  · cases h

theorem forwardRun_destinations (ctx : ApplyCtx) :
    ∀ (rs : List Receipt) (ls ls' : List Limit), forwardRun ctx ls rs = .ok ls' →
      ∀ r ∈ rs, ctx.layout.shardOf r.receiverId ∈ ls.map Limit.shard
  | [], _, _, _ => by simp
  | r :: rs, ls, ls', h => by
    unfold forwardRun at h
    simp only [List.foldlM_cons] at h
    cases hs : tryForward ctx ls r with
    | none => simp [hs, bind, Except.bind] at h
    | some next =>
      simp only [hs, bind, Except.bind] at h
      intro rf hrf
      rcases List.mem_cons.1 hrf with rfl | hrf
      · obtain ⟨l, hl, he⟩ := tryForward_has_limit hs
        exact List.mem_map.mpr ⟨l, hl, he⟩
      · rw [← tryForward_shards hs]
        exact forwardRun_destinations ctx rs next ls' h rf hrf

private theorem statusFold_mem (s : Nat) :
    ∀ (xs : List (Nat × Congestion × Nat)) (acc : List Nat),
      s ∈ xs.foldl (fun acc (sh, _, _) => if acc.contains sh then acc else acc ++ [sh]) acc ↔
        s ∈ acc ∨ s ∈ xs.map (·.1)
  | [], acc => by simp
  | (sh, ci, missed) :: xs, acc => by
    simp only [List.foldl_cons, List.map_cons]
    split
    · rename_i hs
      rw [statusFold_mem]
      have hm : sh ∈ acc := List.contains_iff_mem.mp hs
      simp only [List.mem_cons]
      constructor
      · intro h; exact h.elim Or.inl (fun hm => Or.inr (Or.inr hm))
      · rintro (h | rfl | h)
        · exact Or.inl h
        · exact Or.inl hm
        · exact Or.inr h
    · rw [statusFold_mem]
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
      exact or_assoc

theorem statusShards_mem (ctx : ApplyCtx) (s : Nat) :
    s ∈ statusShards ctx ↔ s ∈ ctx.statuses.map (·.1) := by
  unfold statusShards
  rw [statusFold_mem]
  simp

theorem forwardRun_status_guard {ctx : ApplyCtx} {so : SchedOut} {rs : List Receipt} {ls' : List Limit}
    (h : forwardRun ctx (ctx.statuses.map fun (s, ci, missed) =>
      ⟨s, if s == ctx.own then GASMAX else prims.outGas ci missed ctx.own,
        so.grant ctx.own s⟩) rs = .ok ls') :
    (rs.all fun r => (statusShards ctx).contains (ctx.layout.shardOf r.receiverId)) = true := by
  apply List.all_eq_true.mpr
  intro r hr
  apply List.contains_iff_mem.mpr
  apply (statusShards_mem ctx _).mpr
  simpa only [List.map_map, Function.comp_def] using forwardRun_destinations ctx rs _ _ h r hr

theorem applyNewChunk_status_guard {ctx : ApplyCtx} {t : PTrie} {rs : List Receipt} {out : MainOut}
    (h : applyNewChunk prims ctx t rs = .ok out) :
    (out.outgoing.all fun r => (statusShards ctx).contains (ctx.layout.shardOf r.receiverId)) = true := by
  unfold applyNewChunk at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨⟨_, so⟩, _, h⟩ := bind_ok h
  dsimp only at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨⟨acc, ls⟩, ha, h⟩ := bind_ok h
  dsimp only at h
  obtain ⟨_, _, h⟩ := bind_ok h
  obtain ⟨_, _, h⟩ := bind_ok h
  cases h
  obtain ⟨added, he, hf⟩ := applyReceipts_forwardRun ctx rs 0 _ _ _ ha
  simp only [List.nil_append] at he
  rw [he]
  exact forwardRun_status_guard hf

end ZkFormal.NearV3.Assembly
