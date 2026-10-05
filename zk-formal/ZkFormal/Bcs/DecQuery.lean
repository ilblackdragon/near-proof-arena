import ZkFormal.Bcs.TransStatements
import ZkFormal.Bcs.StarkAlign

/-!
# ZkFormal.Bcs.DecQuery — a decodable complete view decodes to a shaped transcript

`decQuery : DecQueryStmt`.  The verifier's `decodeView` and the transport's
`decodePT` parse the same clear bytes along the same schedule, so they
succeed together (`decEntries_of`); the decoded transcript erases to the
verifier's, fits the schedule (`Shaped`), and its true openings at `x` are the
rows the verifier reads from the extracted oracles (`rowAt` on both sides).
-/

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace ZkFormal.Bcs.Transport

open ArenaCore ArenaCore.Security ZkFormal Lean.Grind
open Adapter (parseClear decodeEntries rowsAll rowsOf rowAt normRow oracleShapes oracleIndexFrom)

/-! ## `Forall2` helpers -/

theorem f2_split {α β : Type} {R : α → β → Prop} : ∀ {a1 a2 : List α} {b : List β},
    Forall2 R (a1 ++ a2) b → ∃ b1 b2, b = b1 ++ b2 ∧ Forall2 R a1 b1 ∧ Forall2 R a2 b2
  | [], _, b, h => ⟨[], b, rfl, .nil, h⟩
  | _ :: _, _, _, h => by
    cases h with
    | cons hab h' =>
      obtain ⟨b1, b2, rfl, h1, h2⟩ := f2_split h'
      exact ⟨_ :: b1, b2, rfl, .cons hab h1, h2⟩

theorem f2_get {α β : Type} {R : α → β → Prop} : ∀ {l : List α} {l' : List β}, Forall2 R l l' →
    ∀ k (hk : k < l.length), ∃ b, l'[k]? = some b ∧ R l[k] b
  | _, _, .nil, k, hk => by simp at hk
  | _, _, .cons h _, 0, _ => ⟨_, rfl, h⟩
  | _, _, .cons _ hl, k + 1, hk => by simpa using f2_get hl k (by simpa using hk)

theorem f2_unmap {α β γ : Type} {R : β → γ → Prop} (f : α → β) :
    ∀ {l : List α} {l' : List γ}, Forall2 R (l.map f) l' → Forall2 (fun a c => R (f a) c) l l'
  | [], _, h => by cases h; exact .nil
  | _ :: _, _, h => by cases h with | cons h1 h2 => exact .cons h1 (f2_unmap f h2)

theorem f2_imp {α β : Type} {R S : α → β → Prop} (hRS : ∀ a b, R a b → S a b) :
    ∀ {l : List α} {l' : List β}, Forall2 R l l' → Forall2 S l l'
  | _, _, .nil => .nil
  | _, _, .cons h hl => .cons (hRS _ _ h) (f2_imp hRS hl)

section
variable {F K : Type} [Field F] [Field K] [Stark.StarkField F K] [DecidableEq F]

/-! ## Parsing the clear bytes -/

/-- A parsed part matches its schedule part. -/
def PartMatch (hdr : List Nat) : Stark.Part → Stark.PartV K Unit → Prop
  | .header n, .header l => l = hdr ∧ l.length = n
  | .oracle _, .oracle _ => True
  | .elems n, .elems xs => xs.length = n
  | _, _ => False

theorem parseClear_match (hdr : List Nat) : ∀ (parts : List Stark.Part) (c : Bytes)
    (vs : List (Stark.PartV K Unit)) (r : Bytes),
    parseClear (F := F) (K := K) hdr parts c = some (vs, r) → Forall2 (PartMatch hdr) parts vs
  | [], c, vs, r, h => by
    simp [parseClear] at h; obtain ⟨rfl, -⟩ := h; exact .nil
  | p :: ps, c, vs, r, h => by
    cases p with
    | header n =>
      simp only [parseClear] at h
      cases hr : Stark.readHeader n c with
      | none => simp [hr] at h
      | some lr =>
        obtain ⟨l, r1⟩ := lr
        by_cases hl : (l == hdr) = true
        · cases hrest : parseClear (F := F) (K := K) hdr ps r1 with
          | none => simp [hr, hl, hrest] at h
          | some p2 =>
            obtain ⟨vs', r''⟩ := p2
            simp [hr, hl, hrest] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .cons ⟨by simpa using hl, Adapter.readHeader_length hr⟩
              (parseClear_match hdr ps r1 vs' r'' hrest)
        · simp [hr, hl] at h
    | oracle m =>
      simp only [parseClear] at h
      cases hrest : parseClear (F := F) (K := K) hdr ps c with
      | none => simp [hrest] at h
      | some p2 =>
        obtain ⟨vs', r''⟩ := p2
        simp [hrest] at h
        obtain ⟨rfl, rfl⟩ := h
        exact .cons trivial (parseClear_match hdr ps c vs' r'' hrest)
    | elems n =>
      simp only [parseClear] at h
      cases hr : Stark.readKs (F := F) (K := K) n c with
      | none => simp [hr] at h
      | some lr =>
        obtain ⟨xs, r1⟩ := lr
        cases hrest : parseClear (F := F) (K := K) hdr ps r1 with
        | none => simp [hr, hrest] at h
        | some p2 =>
          obtain ⟨vs', r''⟩ := p2
          simp [hr, hrest] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .cons (Adapter.readKs_length hr) (parseClear_match hdr ps r1 vs' r'' hrest)

/-! ## Decoded oracles -/

def partO : Stark.PartV K (Stark.Oracle F) → Option (Stark.Oracle F)
  | .oracle o => some o
  | _ => none

def entO : Stark.Entry K (Stark.Oracle F) → List (Stark.Oracle F)
  | .msg ps => ps.filterMap partO
  | .chal _ => []

theorem oracles_eq (cb : Bytes) (des : List (Stark.Entry K (Stark.Oracle F))) :
    (⟨cb, des⟩ : Stark.PT K (Stark.Oracle F)).oracles = des.flatMap entO := by
  unfold Stark.PT.oracles
  congr 1
  funext e
  cases e with
  | msg ps =>
    simp only [entO]
    congr 1
    funext p
    cases p <;> rfl
  | chal _ => rfl

theorem normRow_length (w : Nat) (row : List F) : (normRow w row).length = w := by
  unfold normRow; split <;> simp_all

theorem decMats_fits (mats : List (Nat × Nat)) (f : Nat × Nat → Option Bytes) :
    ∀ (ms : List (Nat × Nat)) (seen : List Nat),
      Forall2 (fun (M : Stark.Mat F) (sh : Nat × Nat) =>
        M.log = sh.1 ∧ M.width = sh.2 ∧ ∀ i, (M.row i).length = M.width) (decMats mats f ms seen) ms
  | [], _ => .nil
  | (m, w) :: ms, seen => .cons ⟨rfl, rfl, fun i => by
      simp only
      split <;> simp [rowAt, normRow_length]⟩ (decMats_fits mats f ms _)

theorem decOracle_fits (mats : List (Nat × Nat)) (f : Nat × Nat → Option Bytes) :
    Udr.PartV.Fits (K := K) (.oracle (decOracle (F := F) mats f)) (.oracle mats) := by
  have h := decMats_fits (F := F) mats f mats []
  refine ⟨Adapter.Forall2.length h, fun k hk => ?_⟩
  obtain ⟨sh, hsh, h1, h2, h3⟩ := f2_get h k hk
  exact ⟨sh, hsh, h1, h2, fun i _ => h3 i⟩

theorem decMats_rows (mats : List (Nat × Nat)) (f : Nat × Nat → Option Bytes) (n0 x : Nat) :
    ∀ (ms : List (Nat × Nat)) (seen : List Nat) (vals : List Bytes),
      Forall2 (fun mw v => f (mw.1, x >>> (n0 - mw.1)) = some v) ms vals →
      (decMats (F := F) mats f ms seen).map (fun M => M.row (x >>> (n0 - M.log))) =
        rowsOf (F := F) mats ms seen vals
  | [], _, _, .nil => by simp [decMats, rowsOf]
  | (m, w) :: ms, seen, v :: vals, .cons h hs => by
    simp only at h
    simp only [decMats, List.map_cons, rowsOf, h]
    rw [decMats_rows mats f n0 x ms (m :: seen) vals hs]

/-- The decoded parts of a message. -/
theorem fill_spec (os : List (Nat × Nat → Option Bytes)) (hdr : List Nat) :
    ∀ (parts : List Stark.Part) (vs : List (Stark.PartV K Unit)) (t : Nat),
      Forall2 (PartMatch hdr) parts vs →
      (fill (F := F) os parts vs t).map Stark.PT.PartV.erase = vs ∧
      Forall2 Udr.PartV.Fits (fill (F := F) os parts vs t) parts ∧
      (fill (F := F) os parts vs t).filterMap partO =
        ((oracleShapes parts).zipIdx t).map (fun mt => decOracle (F := F) mt.1 (os.getD mt.2 fun _ => none))
  | [], [], t, .nil => ⟨by simp [fill], by simp only [fill]; exact .nil, by simp [fill, oracleShapes]⟩
  | p :: ps, v :: vs, t, .cons h hs => by
    cases p <;> cases v <;> simp only [PartMatch] at h
    · obtain ⟨_, hl⟩ := h
      obtain ⟨i1, i2, i3⟩ := fill_spec os hdr ps vs t hs
      refine ⟨by simp [fill, i1, Stark.PT.PartV.erase], .cons hl i2, ?_⟩
      simp only [fill, List.filterMap_cons, partO, i3]
      rfl
    · rename_i mats u
      obtain ⟨i1, i2, i3⟩ := fill_spec os hdr ps vs (t + 1) hs
      refine ⟨by simp [fill, i1, Stark.PT.PartV.erase], .cons (decOracle_fits mats _) i2, ?_⟩
      simp only [fill, List.filterMap_cons, partO, i3]
      simp [oracleShapes, List.zipIdx_cons]
    · obtain ⟨i1, i2, i3⟩ := fill_spec os hdr ps vs t hs
      refine ⟨by simp [fill, i1, Stark.PT.PartV.erase], .cons h i2, ?_⟩
      simp only [fill, List.filterMap_cons, partO, i3]
      rfl
  | [], _ :: _, _, h => by cases h
  | _ :: _, [], _, h => by cases h

/-- The rows of one message's oracles. -/
theorem msg_rows (τ : PT mmcs) (r : Nat) (roots : List Bytes) (raw : Bytes)
    (os : List (Nat × Nat → Option Bytes)) (hr : τ.entries[r]? = some (.msg roots raw os)) (n0 x : Nat) :
    ∀ (L : List (List (Nat × Nat))) (t0 : Nat) (vals : List Bytes),
      Forall2 (fun (q : Nat × Nat × (Nat × Nat)) v => τ.oracle q.1 q.2.1 q.2.2 = some v)
        (((L.zipIdx t0).map fun mt => (r, mt.2, mt.1)).flatMap fun rtm =>
          rtm.2.2.map fun mw => (rtm.1, rtm.2.1, (mw.1, x >>> (n0 - mw.1)))) vals →
      rowsAll (F := F) L vals = (L.zipIdx t0).map
        (fun mt => (decOracle (F := F) mt.1 (os.getD mt.2 fun _ => none)).map fun M => M.row (x >>> (n0 - M.log)))
  | [], t0, vals, h => by simp at h; cases h; simp [rowsAll]
  | mats :: L, t0, vals, h => by
    simp only [List.zipIdx_cons, List.map_cons, List.flatMap_cons] at h ⊢
    obtain ⟨v1, v2, rfl, h1, h2⟩ := f2_split h
    have h1' := f2_unmap _ h1
    rw [Adapter.rowsAll_append mats L v1 v2 (Adapter.Forall2.length h1').symm]
    congr 1
    · unfold decOracle
      refine (decMats_rows mats _ n0 x mats [] v1 (f2_imp (fun mw v hv => ?_) h1')).symm
      simp only [PT.oracle, hr, Option.bind_some, Entry.oracles] at hv
      rw [List.getD_eq_getElem?_getD]
      have key : ∀ (o : Option (Nat × Nat → Option Bytes)) p v, o.bind (fun f => f p) = some v →
          (o.getD fun _ => none) p = some v := by
        intro o p v h; cases o <;> simp_all
      exact key _ _ _ hv
    · exact msg_rows τ r roots raw os hr n0 x L (t0 + 1) v2 h2

/-- The opened positions of an oracle block. -/
def gA (n0 x : Nat) (rtm : Nat × Nat × List (Nat × Nat)) : List (Nat × Nat × (Nat × Nat)) :=
  rtm.2.2.map fun mw => (rtm.1, rtm.2.1, (mw.1, x >>> (n0 - mw.1)))

/-! ## The main induction -/

theorem decEntries_of (hdr : List Nat) (n0 : Nat) (τ : PT mmcs) :
    ∀ (sched : List Stark.Slot) (es pre : List (Entry mmcs)) (eu : List (Stark.Entry K Unit)),
      τ.entries = pre ++ es → decodeEntries (F := F) hdr sched (es.map Entry.view) = some eu →
      ∃ des, decEntries (F := F) hdr sched es = some des ∧ des.map Stark.PT.Entry.erase = eu ∧
        Forall2 Udr.Entry.Fits des sched ∧
        ∀ x vals, Forall2 (fun (q : Nat × Nat × (Nat × Nat)) v => τ.oracle q.1 q.2.1 q.2.2 = some v)
          ((oracleIndexFrom pre.length sched).flatMap (gA n0 x)) vals →
          rowsAll (F := F) (Stark.schedOracles sched) vals =
            (des.flatMap entO).map (fun o => o.map fun M => M.row (x >>> (n0 - M.log)))
  | [], [], pre, eu, _, h => by
    simp [decodeEntries] at h; subst h
    refine ⟨[], by simp [decEntries], rfl, .nil, fun x vals hv => ?_⟩
    simp [oracleIndexFrom] at hv; cases hv; simp [rowsAll, Stark.schedOracles]
  | .msg parts :: ss, .msg roots clear os :: es, pre, eu, hE, h => by
    simp only [List.map_cons, Entry.view, decodeEntries] at h
    split at h
    · rename_i vs hp
      cases heu : decodeEntries (F := F) hdr ss (es.map Entry.view) with
      | none => simp [heu] at h
      | some eu' =>
        simp only [heu, Option.map_some, Option.some.injEq] at h
        subst h
        obtain ⟨des', h1, h2, h3, h4⟩ := decEntries_of hdr n0 τ ss es (pre ++ [.msg roots clear os]) eu'
          (by simp [hE]) heu
        have hm := parseClear_match hdr parts clear vs [] hp
        obtain ⟨f1, f2, f3⟩ := fill_spec (F := F) os hdr parts vs 0 hm
        refine ⟨.msg (fill (F := F) os parts vs 0) :: des', ?_, ?_, ?_, ?_⟩
        · simp [decEntries, hp, h1]
        · simp [Stark.PT.Entry.erase, f1, h2]
        · refine .cons ⟨Adapter.Forall2.length f2, fun k hk => f2_get f2 k hk⟩ h3
        · intro x vals hv
          have e3 : oracleIndexFrom pre.length (.msg parts :: ss) =
              (oracleShapes parts).zipIdx.map (fun (mt : List (Nat × Nat) × Nat) => (pre.length, mt.2, mt.1)) ++
                oracleIndexFrom (pre.length + 1) ss := by
            simp only [oracleIndexFrom, List.zipIdx_cons, List.flatMap_cons]
          rw [e3, List.flatMap_append] at hv
          obtain ⟨v1, v2, rfl, hv1, hv2⟩ := f2_split hv
          have hr : τ.entries[pre.length]? = some (.msg roots clear os) := by simp [hE]
          have r1 := msg_rows (F := F) τ pre.length roots clear os hr n0 x (oracleShapes parts) 0 v1 hv1
          have r2 := h4 x v2 (by simpa using hv2)
          have hl1 : v1.length = ((oracleShapes parts).map List.length).sum := by
            have := Adapter.Forall2.length hv1
            rw [← this]
            clear r1 hv1 this
            generalize oracleShapes parts = L
            suffices ∀ t0, (((L.zipIdx t0).map fun mt => (pre.length, mt.2, mt.1)).flatMap (gA n0 x)).length =
                (L.map List.length).sum from this 0
            induction L with
            | nil => simp
            | cons a L ih => intro t0; simp [List.zipIdx_cons, gA, ih]
          have e1 : Stark.schedOracles (.msg parts :: ss) = oracleShapes parts ++ Stark.schedOracles ss := rfl
          rw [e1, rowsAll_app _ _ _ _ hl1, r1, r2]
          simp only [List.flatMap_cons, entO, f3, List.map_append, List.map_map]
          rfl
    · simp at h
  | .chal ood :: ss, .chal y :: es, pre, eu, hE, h => by
    simp only [List.map_cons, Entry.view, decodeEntries] at h
    cases heu : decodeEntries (F := F) hdr ss (es.map Entry.view) with
    | none => simp [heu] at h
    | some eu' =>
      simp only [heu, Option.map_some, Option.some.injEq] at h
      subst h
      obtain ⟨des', h1, h2, h3, h4⟩ := decEntries_of hdr n0 τ ss es (pre ++ [.chal y]) eu'
        (by simp [hE]) heu
      refine ⟨.chal (if ood then Stark.decodeOod (F := F) y else Stark.decodeChal (F := F) y) :: des',
        ?_, ?_, .cons trivial h3, ?_⟩
      · simp [decEntries, h1]
      · simp [Stark.PT.Entry.erase, h2]
      · intro x vals hv
        have e3 : oracleIndexFrom pre.length (.chal ood :: ss) = oracleIndexFrom (pre.length + 1) ss := by
          simp only [oracleIndexFrom, List.zipIdx_cons, List.flatMap_cons, List.nil_append]
        rw [e3] at hv
        exact h4 x vals (by simpa using hv)
  | [], _ :: _, _, _, _, h => by simp [decodeEntries] at h
  | _ :: _, [], _, _, _, h => by simp [decodeEntries] at h
  | .msg _ :: _, .chal _ :: _, _, _, _, h => by simp [decodeEntries, Entry.view] at h
  | .chal _ :: _, .msg _ _ _ :: _, _, _, _, h => by simp [decodeEntries, Entry.view] at h
where
  rowsAll_app (os1 os2 : List (List (Nat × Nat))) (v1 v2 : List Bytes)
      (hl : v1.length = (os1.map List.length).sum) :
      rowsAll (F := F) (os1 ++ os2) (v1 ++ v2) = rowsAll (F := F) os1 v1 ++ rowsAll (F := F) os2 v2 := by
    induction os1 generalizing v1 with
    | nil => simp at hl; subst hl; simp [rowsAll]
    | cons mats os1 ih =>
      simp only [List.cons_append, rowsAll]
      have hd : (v1 ++ v2).take mats.length = v1.take mats.length := by
        rw [List.take_append_of_le_length (by simp at hl; omega)]
      have hd2 : (v1 ++ v2).drop mats.length = v1.drop mats.length ++ v2 := by
        rw [List.drop_append_of_le_length (by simp at hl; omega)]
      rw [hd, hd2, ih _ (by simp at hl ⊢; omega)]


/-! ## Header -/

theorem header?_erase {O : Type} (σ : Stark.PT K O) : σ.erase.header? = σ.header? := by
  obtain ⟨cb, es⟩ := σ
  cases es with
  | nil => rfl
  | cons e es =>
    cases e with
    | chal _ => rfl
    | msg ps =>
      cases ps with
      | nil => rfl
      | cons p ps => cases p <;> rfl

theorem eu_header (hdr : List Nat) (n : Nat) (ps : List Stark.Part) (ss : List Stark.Slot)
    (e : EntryV) (es : List EntryV) (eu : List (Stark.Entry K Unit))
    (h : decodeEntries (F := F) hdr (.msg (.header n :: ps) :: ss) (e :: es) = some eu) (cb : Bytes) :
    (⟨cb, eu⟩ : Stark.PT K Unit).header? = some hdr := by
  cases e with
  | chal _ => simp [decodeEntries] at h
  | msg roots c =>
    simp only [decodeEntries] at h
    split at h
    · rename_i vs hp
      have hm := parseClear_match hdr _ c vs [] hp
      cases hm with
      | @cons _ v _ _ h1 _ =>
        cases v with
        | header l =>
          obtain ⟨rfl, -⟩ := h1
          cases heu : decodeEntries (F := F) l ss es with
          | none => simp [heu] at h
          | some eu' =>
            simp only [heu, Option.map_some, Option.some.injEq] at h
            subst h; rfl
        | oracle _ => exact h1.elim
        | elems _ => exact h1.elim
    · simp at h

end

/-! ## The statement -/

theorem decQuery : DecQueryStmt := by
  intro F K _ _ _ _ V hS τ hdr σu hd
  obtain ⟨cb, entries⟩ := τ
  unfold Adapter.decodeView at hd
  simp only [PT.view] at hd
  cases hvh : Adapter.viewHeader V (entries.map Entry.view) [] with
  | none => simp [hvh] at hd
  | some h0 =>
    rw [hvh] at hd
    simp only at hd
    by_cases hok : V.headerOk h0 = true
    · simp only [hok, ↓reduceIte] at hd
      cases hde : decodeEntries (F := F) h0 (V.schedule h0) (entries.map Entry.view) with
      | none => simp [hde] at hd
      | some eu =>
        simp only [hde, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hd
        obtain ⟨rfl, rfl⟩ := hd
        obtain ⟨ps, ss, hsch⟩ := hS.first h0 hok
        cases entries with
        | nil => rw [hsch] at hde; simp [decodeEntries] at hde
        | cons e es =>
          have hH0 : (⟨cb, eu⟩ : Stark.PT K Unit).header? = some h0 := by
            rw [hsch] at hde
            exact eu_header h0 _ ps ss _ _ eu hde cb
          obtain ⟨des, h1, h2, h3, h4⟩ := decEntries_of (F := F) h0 (V.queryLog h0) ⟨cb, e :: es⟩
            (V.schedule h0) (e :: es) [] eu rfl hde
          have hE : (⟨cb, des⟩ : Stark.PT K (Stark.Oracle F)).erase = ⟨cb, eu⟩ := by
            simp [Stark.PT.erase, h2]
          have hH : (⟨cb, des⟩ : Stark.PT K (Stark.Oracle F)).header? = some h0 := by
            rw [← header?_erase, hE, hH0]
          have hsl : V.slots (⟨cb, des⟩ : Stark.PT K (Stark.Oracle F)) = V.schedule h0 := by
            unfold Stark.IopSpec.slots; rw [hH]
          have hlen := Adapter.Forall2.length h3
          refine ⟨⟨cb, des⟩, ?_, hE, ⟨by simp [hH], by simp [hsl, hlen]⟩, ⟨?_, by simp [hsl, hlen], ?_⟩, ?_, ?_⟩
          · unfold decodePT
            simp only [PT.view, List.map_cons]
            rw [← List.map_cons, hvh]
            simp [hok, h1]
          · intro l hl; rw [hH] at hl; cases hl; exact hok
          · intro k hk
            rw [hsl]
            exact f2_get h3 k hk
          · unfold Stark.IopSpec.domSize; rw [hH]
          · intro x vals hv
            unfold Adapter.opensA at hv
            simp only [PT.view] at hv
            rw [hvh] at hv
            unfold Stark.IopSpec.trueOpenings
            rw [hH, oracles_eq]
            exact h4 x vals hv
    · simp [hok] at hd

end ZkFormal.Bcs.Transport
