import ReexecV3D3.Logged.LM

/-!
# `TrieUpdate` reads over the lazy pre-state trie (mirror of `D2/State.lean`)

The overlay (`committed`, `prosp`) is unchanged; every read that reaches the pre-state trie goes
through `LazyTrie` from the transition's pre-state root. `Ovl.wt o t` is `o` with trie `t`; the
original operations run on `o.wt T` (`T` the revealed pre-state), the mirrors on `o`.
-/

namespace ReexecV3D3.Logged

open NearSpec NearSpecV3 NearSpecV3.D2

/-- The revealed pre-state of the transition with root `root` over the store `s`. -/
abbrev preT (s : HStore) (root : Bytes) : PTrie := revealAll s revealFuel root

end ReexecV3D3.Logged

namespace NearSpecV3.D2

open NearSpec NearSpecV3 ReexecV3D3.Logged

@[reducible] def Ovl.wt (o : Ovl) (t : PTrie) : Ovl := { o with trie := t }

@[reducible] def Env.ws (e : Env) (st : HStore) : Env := { e with store := st }

def trieFindL (k : Bytes) : LM (Option (Option Bytes)) := fun root => findL (.lz root revealFuel) (nibbles k)
def trieFindRefL (k : Bytes) : LM (Option (Option Nat)) :=
  fun root => findRefL (.lz root revealFuel) (nibbles k)
def triePrefixL (pre : Bytes) : LM (Option (List (List Nat))) :=
  fun root => prefixKeysL (.lz root revealFuel) (nibbles pre) []

def Ovl.getL (o : Ovl) (k : Bytes) (what : String) : LM (Option Bytes) :=
  match o.lookup k with
  | some v => pure v
  | none => do
    match ← trieFindL k with
    | some v => pure v
    | none => throw (missing what)

def Ovl.refLenL (o : Ovl) (k : Bytes) (what : String) : LM (Option Nat) :=
  match o.lookup k with
  | some v => pure (v.map List.length)
  | none => do
    match ← trieFindRefL k with
    | some (some l) => pure (some l)
    | some none => pure none
    | none => throw (missing what)

def Ovl.containsL (o : Ovl) (k : Bytes) (what : String) : LM Bool := do
  pure (← o.refLenL k what).isSome

def Ovl.iterKeysL (o : Ovl) (pre : Bytes) (what : String) : LM (List Bytes) := do
  let tk ← match ← triePrefixL pre with
    | some ks => pure (ks.map unnibble)
    | none => throw (missing what)
  let ovl := (sortKV (o.prosp.foldl (fun c (k, v) => kvPut k v c) o.committed)).filter
    fun (k, _) => isBytePrefix pre k
  let fromTrie := tk.filter fun k => (kvFind k ovl).isNone
  let fromOvl := (ovl.filter fun (_, v) => v.isSome).map (·.1)
  pure ((sortKV ((fromTrie ++ fromOvl).map fun k => (k, none))).map (·.1))

def Ovl.finalizeL (o : Ovl) : LM Bytes := do
  let t0 ← LM.lift (preTrieL (← LM.root))
  match ← LM.lift (applyChangesL t0 (sortKV o.committed)) with
  | some t => pure (rootHashL t)
  | none => throw (missing "finalize: trie update path")

def Ovl.getAcctL (o : Ovl) (a : Bytes) : LM (Option Acct) := do
  match ← o.getL (kAccount a) "account" with
  | none => pure none
  | some raw => match decodeAcct raw with
    | some x => pure (some x)
    | none => throw (inconsistent "account")

def Ovl.getAKRawL (o : Ovl) (k : Bytes) : LM (Option AK) := do
  match ← o.getL k "access key" with
  | none => pure none
  | some raw => match decodeAK raw with
    | some x => pure (some x)
    | none => throw (inconsistent "access key")

def Ovl.getAKL (o : Ovl) (a : Bytes) (pk : PublicKey) : LM (Option AK) :=
  o.getAKRawL (kAK a pk)

def Ovl.getU64L (o : Ovl) (k : Bytes) (what : String) : LM (Option Nat) := do
  match ← o.getL k what with
  | none => pure none
  | some raw => match decodeU64 raw with
    | some n => pure (some n)
    | none => throw (inconsistent what)

def Ovl.getIndicesL (o : Ovl) (k : Bytes) (what : String) : LM (Nat × Nat) := do
  match ← o.getL k what with
  | none => pure (0, 0)
  | some raw => if raw.length == 16 then pure (leNat (raw.take 8), leNat (raw.drop 8))
                else throw (inconsistent what)

end NearSpecV3.D2

namespace ReexecV3D3.Logged

open NearSpec NearSpecV3 NearSpecV3.D2

/-! ## Specs -/

section
variable {s : HStore} {root : Bytes}

theorem ev_trieFindL (k : Bytes) :
    LM.ev s root (trieFindL k) = .ok ((preT s root).find (nibbles k)) := (findL_spec s).1 _ _

theorem ev_trieFindRefL (k : Bytes) :
    LM.ev s root (trieFindRefL k) = .ok (((preT s root).findRef (nibbles k)).map (·.map Slot.len)) :=
  (findRefL_spec s).1 _ _

theorem ev_triePrefixL (pre : Bytes) :
    LM.ev s root (triePrefixL pre) = .ok ((preT s root).prefixKeys (nibbles pre) []) :=
  (prefixKeysL_spec s).1 _ _ _

theorem R_get (o : Ovl) (k : Bytes) (what : String) :
    R s root (o.getL k what) ((o.wt (preT s root)).get k what) id := by
  unfold R Ovl.get Ovl.getL
  have hl : (o.wt (preT s root)).lookup k = o.lookup k := rfl
  rw [hl]
  cases o.lookup k with
  | some v => rfl
  | none =>
    simp only [LM.ev_bind, ev_trieFindL]
    simp only [bind, Except.bind]
    try dsimp only
    cases (preT s root).find (nibbles k) <;> rfl

theorem R_refLen (o : Ovl) (k : Bytes) (what : String) :
    R s root (o.refLenL k what) ((o.wt (preT s root)).refLen k what) id := by
  unfold R Ovl.refLen Ovl.refLenL
  have hl : (o.wt (preT s root)).lookup k = o.lookup k := rfl
  rw [hl]
  cases o.lookup k with
  | some v => rfl
  | none =>
    simp only [LM.ev_bind, ev_trieFindRefL]
    simp only [bind, Except.bind]
    try dsimp only
    cases (preT s root).findRef (nibbles k) with
    | none => rfl
    | some x => cases x <;> rfl

theorem R_contains (o : Ovl) (k : Bytes) (what : String) :
    R s root (o.containsL k what) ((o.wt (preT s root)).contains k what) id := by
  have h := R_refLen (s := s) (root := root) o k what
  unfold R at h ⊢
  unfold Ovl.contains Ovl.containsL
  rw [h, LM.ev_bind]
  cases LM.ev s root (o.refLenL k what) <;> rfl

theorem R_iterKeys (o : Ovl) (pre : Bytes) (what : String) :
    R s root (o.iterKeysL pre what) ((o.wt (preT s root)).iterKeys pre what) id := by
  unfold R Ovl.iterKeys Ovl.iterKeysL
  rw [LM.ev_bind, ev_triePrefixL]
  simp only [bind, Except.bind]
  cases (preT s root).prefixKeys (nibbles pre) [] <;> rfl

theorem R_finalize (hs : HInv s) (o : Ovl) :
    R s root (o.finalizeL) ((o.wt (preT s root)).finalize) id := by
  obtain ⟨t0, ht0, ht0'⟩ := preTrieL_spec s root
  obtain ⟨o2, ho2, ho2'⟩ := applyChangesL_spec s t0 (sortKV o.committed)
  rw [ht0'] at ho2'
  have h0 : (o.wt (preT s root)).finalize =
      match applyChanges (t0Of s root) (sortKV o.committed) with
      | some t => .ok (rootHash t)
      | none => .error (missing "finalize: trie update path") := by
    unfold Ovl.finalize t0Of; simp only [Ovl.wt, preT]
    cases revealAll s revealFuel root <;> rfl
  have h1 : LM.ev s root o.finalizeL =
      match (generalizing := false) o2 with
      | some t => .ok (rootHashL t)
      | none => .error (missing "finalize: trie update path") := by
    unfold Ovl.finalizeL
    rw [LM.ev_bind, LM.ev_root]
    simp only [ex_ok_bind]
    rw [LM.ev_bind, LM.ev_lift, ht0]
    simp only [ex_ok_bind]
    rw [LM.ev_bind, LM.ev_lift, ho2]
    simp only [ex_ok_bind]
    cases o2 <;> rfl
  unfold R
  rw [h0, h1, ← ho2']
  clear ho2 ho2' h1
  cases o2 with
  | none => rfl
  | some t => simp [rootHashL_spec hs]

theorem R_getAcct (o : Ovl) (a : Bytes) :
    R s root (o.getAcctL a) ((o.wt (preT s root)).getAcct a) id := by
  unfold Ovl.getAcct Ovl.getAcctL
  apply R_bind (R_get o (kAccount a) "account")
  intro b
  cases b with
  | none => exact R_pure rfl
  | some raw => dsimp only [id]; cases decodeAcct raw <;> first | exact R_pure rfl | exact R_throw _

theorem R_getAKRaw (o : Ovl) (k : Bytes) :
    R s root (o.getAKRawL k) ((o.wt (preT s root)).getAKRaw k) id := by
  unfold Ovl.getAKRaw Ovl.getAKRawL
  apply R_bind (R_get o k "access key")
  intro b
  cases b with
  | none => exact R_pure rfl
  | some raw => dsimp only [id]; cases decodeAK raw <;> first | exact R_pure rfl | exact R_throw _

theorem R_getAK (o : Ovl) (a : Bytes) (pk : PublicKey) :
    R s root (o.getAKL a pk) ((o.wt (preT s root)).getAK a pk) id := R_getAKRaw o (kAK a pk)

theorem R_getU64 (o : Ovl) (k : Bytes) (what : String) :
    R s root (o.getU64L k what) ((o.wt (preT s root)).getU64 k what) id := by
  unfold Ovl.getU64 Ovl.getU64L
  apply R_bind (R_get o k what)
  intro b
  cases b with
  | none => exact R_pure rfl
  | some raw => dsimp only [id]; cases decodeU64 raw <;> first | exact R_pure rfl | exact R_throw _

theorem R_getIndices (o : Ovl) (k : Bytes) (what : String) :
    R s root (o.getIndicesL k what) ((o.wt (preT s root)).getIndices k what) id := by
  unfold Ovl.getIndices Ovl.getIndicesL
  apply R_bind (R_get o k what)
  intro b
  cases b with
  | none => exact R_pure rfl
  | some raw => dsimp only [id]; exact R_ite _ _ rfl (R_pure rfl) (R_throw _)

/-! ## Call-site forms (the original's arguments are free; equations closed by `rfl`) -/

theorem R_get' (o : Ovl) {oO : Ovl} (h : oO = o.wt (preT s root)) (k : Bytes) (what : String) :
    R s root (o.getL k what) (oO.get k what) id := h ▸ R_get o k what
theorem R_refLen' (o : Ovl) {oO : Ovl} (h : oO = o.wt (preT s root)) (k : Bytes) (what : String) :
    R s root (o.refLenL k what) (oO.refLen k what) id := h ▸ R_refLen o k what
theorem R_contains' (o : Ovl) {oO : Ovl} (h : oO = o.wt (preT s root)) (k : Bytes) (what : String) :
    R s root (o.containsL k what) (oO.contains k what) id := h ▸ R_contains o k what
theorem R_iterKeys' (o : Ovl) {oO : Ovl} (h : oO = o.wt (preT s root)) (pre : Bytes) (what : String) :
    R s root (o.iterKeysL pre what) (oO.iterKeys pre what) id := h ▸ R_iterKeys o pre what
theorem R_getAcct' (o : Ovl) {oO : Ovl} (h : oO = o.wt (preT s root)) (a : Bytes) :
    R s root (o.getAcctL a) (oO.getAcct a) id := h ▸ R_getAcct o a
theorem R_getAKRaw' (o : Ovl) {oO : Ovl} (h : oO = o.wt (preT s root)) (k : Bytes) :
    R s root (o.getAKRawL k) (oO.getAKRaw k) id := h ▸ R_getAKRaw o k
theorem R_getAK' (o : Ovl) {oO : Ovl} (h : oO = o.wt (preT s root)) (a : Bytes) (pk : PublicKey) :
    R s root (o.getAKL a pk) (oO.getAK a pk) id := h ▸ R_getAK o a pk
theorem R_getU64' (o : Ovl) {oO : Ovl} (h : oO = o.wt (preT s root)) (k : Bytes) (what : String) :
    R s root (o.getU64L k what) (oO.getU64 k what) id := h ▸ R_getU64 o k what
theorem R_getIndices' (o : Ovl) {oO : Ovl} (h : oO = o.wt (preT s root)) (k : Bytes) (what : String) :
    R s root (o.getIndicesL k what) (oO.getIndices k what) id := h ▸ R_getIndices o k what
theorem R_finalize' (hs : HInv s) (o : Ovl) {oO : Ovl} (h : oO = o.wt (preT s root)) :
    R s root (o.finalizeL) (oO.finalize) id := h ▸ R_finalize hs o

end

end ReexecV3D3.Logged
