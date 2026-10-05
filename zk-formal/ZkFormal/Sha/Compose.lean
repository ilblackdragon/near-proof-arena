import ZkFormal.Sha.Statements

/-!
# ZkFormal.Sha.Compose — lane L5 top theorems from the sublemma statements

* `shaLocal_of_holds` — `Air.Holds` gives the SHA table's local facts;
* `sha_block_sound` — one block is one `compress` (= `BlockStmt`);
* `sha_bus_sound` — every claimed `(m, d)` has `d = ArenaCore.sha256 m`;
* `sha_digest_contract` — the digest-bus contract consumed by lane L6: an
  active digest interaction carries `(Id, |m|, sha256 m)` and every byte of
  `m` is received on the bytes bus under the same `Id`;
* `sha_complete` — the honest trace satisfies the table and its bus traffic is
  exactly the messages' bytes and digests.
-/

namespace ZkFormal.Sha

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Layout ZkFormal.Sha.View

theorem shaLocal_of_holds {A : Air} {pub : List Fp} {tr : Trace Fp} (h : Holds A pub tr)
    {t busBytes busDigest : Nat} (ht : t < A.tables.length)
    (hT : A.tables[t] = Table.table busBytes busDigest) : ShaLocal tr t pub where
  log_ge := (h.logBound t ht).1
  log_le := by have := (h.logBound t ht).2; rw [hT] at this; exact this
  constr := fun r hr e he => h.constr t ht r hr e (by rw [hT]; exact he)

theorem sha_block_sound (hB : BlockStmt) {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL : ShaLocal tr t pub) {s : Nat} (hs : s < tr.height t) (h0 : nv tr t s (colR 0) = 1) :
    stateAt tr t (s + 16) = ArenaCore.SHA256.compress (stateAt tr t (s - 1)) (blockBytes tr t s) :=
  (hB tr t pub hL s hs h0).2.2.2.2

theorem blockBytes_length (tr : Trace Fp) (t s : Nat) : (blockBytes tr t s).length = 64 := by
  simp [blockBytes]

/-- Folding the blocks of a chain. -/
theorem chain_fold (hB : BlockStmt) {tr : Trace Fp} {t : Nat} {pub : List Fp}
    (hL : ShaLocal tr t pub) :
    ∀ (ss : List Nat), ss ≠ [] → (∀ s ∈ ss, s < tr.height t ∧ nv tr t s (colR 0) = 1) →
      (∀ i, i + 1 < ss.length → ss[i]! + 17 = ss[i + 1]!) →
      stateAt tr t (ss.getLast! + 16) =
        (ss.map (blockBytes tr t)).foldl ArenaCore.SHA256.compress (stateAt tr t (ss.head! - 1)) := by
  intro ss
  induction ss with
  | nil => intro h; exact absurd rfl h
  | cons s rest ih =>
    intro _ hmem hstep
    have hs := hmem s (List.mem_cons_self ..)
    have hblk := sha_block_sound hB hL hs.1 hs.2
    cases rest with
    | nil =>
      show stateAt tr t (s + 16) = ArenaCore.SHA256.compress (stateAt tr t (s - 1)) (blockBytes tr t s)
      exact hblk
    | cons s' rest' =>
      have h17 : s + 17 = s' := hstep 0 (by simp)
      have ih' := ih (by simp) (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
        (fun i hi => by have := hstep (i + 1) (by simp at hi ⊢; omega); simpa using this)
      have e1 : (s :: s' :: rest').head! = s := rfl
      have e2 : (s' :: rest').head! = s' := rfl
      have e3 : (s :: s' :: rest').getLast! = (s' :: rest').getLast! := by
        simp [List.getLast!_eq_getLast?_getD, List.getLast?_cons_cons]
      rw [e3, ih', e1, e2, List.map_cons, List.map_cons, List.foldl_cons, List.foldl_cons,
        List.map_cons, List.foldl_cons, ← hblk, show s' - 1 = s + 16 by omega]

theorem head!_mem_of_ne_nil {l : List Nat} (h : l ≠ []) : l.head! ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons x xs => exact List.mem_cons_self ..

theorem map_toNat_ofNat (m : List Nat) (h : ∀ x ∈ m, x < 256) :
    (m.map UInt8.ofNat).map UInt8.toNat = m := by
  induction m with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, List.cons.injEq]
    refine ⟨?_, ih (fun y hy => h y (List.mem_cons_of_mem _ hy))⟩
    have := h x (List.mem_cons_self ..)
    simp; omega

/-- The digest of the message ending at a digest row. -/
theorem digest_row_sound (hB : BlockStmt) (hIV : IVStmt) (hC : ChainStmt) (hF : FrameStmt)
    {tr : Trace Fp} {t : Nat} {pub : List Fp} (hL : ShaLocal tr t pub)
    {d : Nat} (hd : d < tr.height t) (hD : IsDigestRow tr t d) :
    ArenaCore.SHA256.digestBytes (stateAt tr t d) = ArenaCore.sha256 ((msgOf tr t d).map UInt8.ofNat) := by
  obtain ⟨hne, hmem, h1, hS, hstep, hlast⟩ := hC tr t pub hL d hd hD
  obtain ⟨h256, hpad, -, -⟩ := hF tr t pub hL d hd hD
  have hfold := chain_fold hB hL _ hne hmem hstep
  have hiv := hIV tr t pub hL _ (by have := (hmem _ (head!_mem_of_ne_nil hne)).1; omega) hS
  rw [hiv, hlast] at hfold
  rw [hfold, ArenaCore.sha256]
  symm
  apply Spec.sha256_eq_foldl
  · intro b hb
    simp only [List.mem_map] at hb
    obtain ⟨s, -, rfl⟩ := hb
    exact blockBytes_length tr t s
  · rw [map_toNat_ofNat _ h256]; exact hpad

/-- **Bus soundness**: every `(m, d)` the table claims has `d = sha256 m`. -/
theorem sha_bus_sound (hB : BlockStmt) (hIV : IVStmt) (hC : ChainStmt) (hF : FrameStmt)
    {tr : Trace Fp} {t : Nat} {pub : List Fp} (hL : ShaLocal tr t pub) :
    ∀ p ∈ digests tr t, p.2 = ArenaCore.sha256 p.1 := by
  intro p hp
  simp only [digests, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq] at hp
  obtain ⟨d, ⟨hd, hD⟩, rfl⟩ := hp
  exact digest_row_sound hB hIV hC hF hL hd hD

/-- **The digest-bus contract** (consumed by lane L6).  If the digest
interaction is active on row `d`, then there is a claimed pair `(m, dg)` with
`dg = sha256 m`, the interaction's message is `(Id, |m|, dg)`, and every
byte `m[i]` is received on the bytes bus as `(Id, i, m[i])` by some row of the
table with multiplicity one. -/
theorem sha_digest_contract (hB : BlockStmt) (hIV : IVStmt) (hC : ChainStmt) (hF : FrameStmt)
    (hIO : DigestIoStmt) {tr : Trace Fp} {t : Nat} {pub : List Fp} (hL : ShaLocal tr t pub)
    (busBytes busDigest : Nat) {d : Nat} (hd : d < tr.height t) (hm : tr.cell t d colDmult = 1) :
    ∃ m dg, (m, dg) ∈ digests tr t ∧ dg = ArenaCore.sha256 m ∧
      (Table.interactions busBytes busDigest)[16]!.msgVal tr t d pub =
        [tr.cell t d colId, Fp.ofNat m.length] ++ dg.map (fun x => Fp.ofNat x.toNat) ∧
      ∀ i, i < m.length → ∃ r, r < tr.height t ∧ ∃ q, q < 16 ∧ tr.cell t r (colF q) = 1 ∧
        (Table.interactions busBytes busDigest)[q]!.msgVal tr t r pub =
          [tr.cell t d colId, Fp.ofNat i, Fp.ofNat (m[i]!).toNat] := by
  obtain ⟨hD, hio⟩ := hIO tr t pub hL d hd hm
  obtain ⟨h256, -, hnd, hbytes⟩ := hF tr t pub hL d hd hD
  refine ⟨(msgOf tr t d).map UInt8.ofNat, ArenaCore.SHA256.digestBytes (stateAt tr t d), ?_,
    digest_row_sound hB hIV hC hF hL hd hD, ?_, ?_⟩
  · simp only [digests, List.mem_map, List.mem_filter, List.mem_range, decide_eq_true_eq]
    exact ⟨d, ⟨hd, hD⟩, rfl⟩
  · rw [hio busBytes busDigest, hnd, List.length_map]
  · intro i hi
    rw [List.length_map] at hi
    obtain ⟨r, hr, q, hq, hf, hmsg⟩ := hbytes busBytes busDigest i hi
    refine ⟨r, hr, q, hq, hf, ?_⟩
    rw [hmsg]
    have hx := h256 _ (List.getElem_mem hi)
    simp only [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem?_map,
      Option.map_some, Option.getD_some]
    have e : (UInt8.ofNat (msgOf tr t d)[i]).toNat = (msgOf tr t d)[i] := by
      simp only [UInt8.toNat_ofNat']; exact Nat.mod_eq_of_lt (by simpa using hx)
    rw [e]

/-- **Completeness.** -/
theorem sha_complete
    (hBool : CompleteFamStmt Table.cBool) (hKind : CompleteFamStmt Table.cKind)
    (hIVc : CompleteFamStmt Table.cIV) (hRound : CompleteFamStmt Table.cRound)
    (hSched : CompleteFamStmt Table.cSched) (hHelp : CompleteFamStmt Table.cHelp)
    (hDig : CompleteFamStmt Table.cDigest) (hFrame : CompleteFamStmt Table.cFrame)
    (hLog : LogStmt) (hBits : MultBitsStmt) (hTraffic : TrafficStmt)
    (msgs : List Gen.Msg) (hok : MsgsOk msgs) (t : Nat) (pub : List Fp) :
    ShaLocal (honestTrace msgs) t pub ∧
    (∀ r, r < (honestTrace msgs).height t → ∀ busBytes busDigest,
      ∀ i ∈ Table.interactions busBytes busDigest, ∀ b ∈ i.mult,
        b.eval (honestTrace msgs) t r pub = 0 ∨ b.eval (honestTrace msgs) t r pub = 1) ∧
    TrafficStmt := by
  refine ⟨⟨(hLog msgs hok t).1, (hLog msgs hok t).2, ?_⟩, hBits msgs hok t pub, hTraffic⟩
  intro r hr e he
  simp only [Table.constraints, List.mem_append] at he
  rcases he with ((((((he | he) | he) | he) | he) | he) | he) | he
  · exact hBool msgs hok t pub r hr e he
  · exact hKind msgs hok t pub r hr e he
  · exact hIVc msgs hok t pub r hr e he
  · exact hRound msgs hok t pub r hr e he
  · exact hSched msgs hok t pub r hr e he
  · exact hHelp msgs hok t pub r hr e he
  · exact hDig msgs hok t pub r hr e he
  · exact hFrame msgs hok t pub r hr e he

end ZkFormal.Sha
