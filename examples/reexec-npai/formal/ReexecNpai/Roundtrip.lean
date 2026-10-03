import ReexecNpai.Canon

/-!
# Round trip and size of the `reexec-npai-v1` proof codec

* `decodeProof_encodeProof`: decoding inverts encoding on every witness of an
  in-domain true claim (`Encodable`);
* `encodeProof_length_le` / `cntT_le`: honest proofs are small;
* `decTrie_some` / `decodeProof_some`: whatever decodes has the length of the
  honest encoding of the decoded witness (placeholders have fixed width), and
  decoded tries are well formed and revealed at the root.
-/

set_option linter.unusedSimpArgs false
set_option maxRecDepth 8000

namespace ReexecNpai

open NearSpec NearSpec.TransferV1

/-! ## Primitive readers -/

theorem readU8_append (x : Nat) (rest : Bytes) (h : x < 256) :
    readU8 (u8 x ++ rest) = some (x, rest) :=
  readLE_append 1 x rest (by simpa using h)

theorem readU16_append (x : Nat) (rest : Bytes) (h : x < 65536) :
    readU16 (u16 x ++ rest) = some (x, rest) :=
  readLE_append 2 x rest (by simpa using h)

theorem readU32_append (x : Nat) (rest : Bytes) (h : x < 4294967296) :
    readU32 (u32 x ++ rest) = some (x, rest) :=
  readLE_append 4 x rest (by simpa using h)

theorem readU64_append (x : Nat) (rest : Bytes) (h : x < 18446744073709551616) :
    readU64 (u64 x ++ rest) = some (x, rest) :=
  readLE_append 8 x rest (by simpa using h)

theorem readU128_append (x : Nat) (rest : Bytes) (h : x < Params.two128) :
    readU128 (u128 x ++ rest) = some (x, rest) :=
  readLE_append 16 x rest (by simpa [Params.two128] using h)

theorem readHash_append (x rest : Bytes) (h : x.length = 32) :
    readHash (x ++ rest) = some (x, rest) := by
  have := takeN_append x rest; rw [h] at this; exact this

theorem takeN_append' (n : Nat) (x rest : Bytes) (h : x.length = n) :
    takeN n (x ++ rest) = some (x, rest) := by
  subst h; exact takeN_append x rest

theorem readBorsh_append (b rest : Bytes) (h : b.length < 4294967296) :
    readBorshBytes (borshBytes b ++ rest) = some (b, rest) :=
  readBorshBytes_append b rest (by simpa using h)

theorem readBorsh_append' (b rest : Bytes) (h : b.length < 4294967296) :
    readBorshBytes (u32 b.length ++ (b ++ rest)) = some (b, rest) := by
  have := readBorsh_append b rest h
  simpa [borshBytes] using this

theorem readU8_cons (b : UInt8) (x : Bytes) : readU8 (b :: x) = some (b.toNat, x) := by
  simp [readU8, readLE, takeN, leNat]

@[simp] theorem u8_length (x : Nat) : (u8 x).length = 1 := leN_length 1 x
@[simp] theorem u16_length (x : Nat) : (u16 x).length = 2 := leN_length 2 x
@[simp] theorem u32_length (x : Nat) : (u32 x).length = 4 := leN_length 4 x
@[simp] theorem u64_length (x : Nat) : (u64 x).length = 8 := leN_length 8 x
@[simp] theorem u128_length (x : Nat) : (u128 x).length = 16 := leN_length 16 x
@[simp] theorem borshBytes_length (b : Bytes) : (borshBytes b).length = 4 + b.length := by
  simp [borshBytes]
@[simp] theorem zeros_length (n : Nat) : (zeros n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [zeros, ih]

/-! ## Hex-prefix keys -/

theorem packNibbles_length : ∀ l : List Nat, (packNibbles l).length = l.length / 2
  | [] => rfl
  | [_] => by simp [packNibbles]
  | _ :: _ :: rest => by
    simp only [packNibbles, List.length_cons, packNibbles_length rest]
    omega

theorem hexPrefix_length (k : List Nat) (b : Bool) : (hexPrefix k b).length = 1 + k.length / 2 := by
  rcases k with _ | ⟨n, rest⟩
  · simp [hexPrefix, packNibbles]
  · by_cases h : (rest.length + 1) % 2 = 1
    · simp only [hexPrefix, List.length_cons, h, packNibbles_length]
      omega
    · have h0 : (rest.length + 1) % 2 = 0 := by omega
      simp only [hexPrefix, List.length_cons, h0, packNibbles_length]
      omega

theorem nibbles_length (bs : Bytes) : (nibbles bs).length = 2 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [nibbles, ih]; omega

theorem nibbles_ok (bs : Bytes) : nibblesOk (nibbles bs) = true := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [nibblesOk, nibbles, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at ih ⊢
    exact ⟨Nat.div_lt_of_lt_mul (by have := b.toNat_lt; omega), Nat.mod_lt _ (by omega), ih⟩

theorem packNibbles_nibbles (bs : Bytes) : packNibbles (nibbles bs) = bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [nibbles, packNibbles, ih, List.cons.injEq, and_true]
    have : b.toNat / 16 * 16 + b.toNat % 16 = b.toNat := by omega
    rw [this]; simp

theorem nibbles_packNibbles : ∀ k : List Nat, nibblesOk k = true → k.length % 2 = 0 →
    nibbles (packNibbles k) = k
  | [], _, _ => rfl
  | [_], _, h => by simp at h
  | a :: b :: rest, hk, hl => by
    simp only [nibblesOk, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hk
    obtain ⟨ha, hb, hr⟩ := hk
    have ih := nibbles_packNibbles rest hr (by simp at hl; omega)
    simp only [packNibbles, nibbles, ih]
    have : (UInt8.ofNat (a * 16 + b)).toNat = a * 16 + b := by
      simp [UInt8.toNat_ofNat]; omega
    rw [this]
    have e1 : (a * 16 + b) / 16 = a := by omega
    have e2 : (a * 16 + b) % 16 = b := by omega
    rw [e1, e2]

theorem keyOfHP_hexPrefix (k : List Nat) (leaf : Bool) (hk : nibblesOk k = true) :
    keyOfHP leaf (hexPrefix k leaf) = some k := by
  rcases k with _ | ⟨n, rest⟩
  · cases leaf <;> simp [hexPrefix, keyOfHP, packNibbles, nibbles]
  · simp only [nibblesOk, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hk
    obtain ⟨hn, hr⟩ := hk
    by_cases h : (rest.length + 1) % 2 = 1
    · have hr2 : rest.length % 2 = 0 := by omega
      simp only [hexPrefix, List.length_cons, h]
      have hnp := nibbles_packNibbles rest hr hr2
      cases leaf
      · have : (UInt8.ofNat (16 + n + 0)).toNat = 16 + n := by simp [UInt8.toNat_ofNat]; omega
        simp only [keyOfHP, Bool.false_eq_true, ite_false, hnp, Nat.add_zero] at this ⊢
        rw [this, ite_eq_right (by omega), ite_eq_left (by omega)]
        congr; omega
      · have : (UInt8.ofNat (16 + n + 32)).toNat = 48 + n := by simp [UInt8.toNat_ofNat]; omega
        simp only [keyOfHP, ite_true, hnp]
        rw [this, ite_eq_right (by omega), ite_eq_left (by omega)]
        congr; omega
    · have h0 : (rest.length + 1) % 2 = 0 := by omega
      have hnp := nibbles_packNibbles (n :: rest) (by simp [nibblesOk, hn]; simpa [nibblesOk] using hr) h0
      simp only [hexPrefix, List.length_cons, h0]
      cases leaf <;> simp [keyOfHP, hnp]

theorem hexPrefix_keyOfHP {leaf : Bool} {hp : Bytes} {k : List Nat} (e : keyOfHP leaf hp = some k) :
    hexPrefix k leaf = hp ∧ nibblesOk k = true := by
  rcases hp with _ | ⟨b, tl⟩
  · simp [keyOfHP] at e
  · have hb := b.toNat_lt
    have hok := nibbles_ok tl
    have hnl := nibbles_length tl
    have hpn := packNibbles_nibbles tl
    -- even case
    have even : ∀ lb : Nat, b.toNat = lb → k = nibbles tl → (lb = if leaf then 32 else 0) →
        hexPrefix k leaf = b :: tl ∧ nibblesOk k = true := by
      intro lb hlb hk hlbv
      subst hk
      refine ⟨?_, hok⟩
      rcases hnt : nibbles tl with _ | ⟨n, rest⟩
      · have : tl = [] := by cases tl <;> simp_all [nibbles]
        subst this
        simp only [hexPrefix, List.length_nil, packNibbles, List.cons.injEq, and_true]
        apply UInt8.toNat_inj.mp
        cases leaf <;> simp_all
      · have hl : ¬ ((rest.length + 1) % 2 = 1) := by
          have := congrArg List.length hnt; simp at this; omega
        rw [hnt] at hpn
        simp only [hexPrefix, List.length_cons]
        split
        · next h => omega
        · rw [hpn]
          congr 1
          apply UInt8.toNat_inj.mp
          cases leaf <;> simp_all
    have odd : ∀ lb : Nat, 16 + lb ≤ b.toNat → b.toNat < 32 + lb → k = (b.toNat - (16 + lb)) :: nibbles tl →
        (lb = if leaf then 32 else 0) → hexPrefix k leaf = b :: tl ∧ nibblesOk k = true := by
      intro lb h1 h2 hk hlbv
      subst hk
      refine ⟨?_, ?_⟩
      · have hl : ((nibbles tl).length + 1) % 2 = 1 := by omega
        simp only [hexPrefix, List.length_cons, hl, packNibbles_nibbles]
        congr 1
        apply UInt8.toNat_inj.mp
        cases leaf <;> simp_all [UInt8.toNat_ofNat] <;> omega
      · simp only [nibblesOk, List.all_cons, Bool.and_eq_true, decide_eq_true_eq]
        exact ⟨by omega, by simpa [nibblesOk] using hok⟩
    cases leaf
    · simp only [keyOfHP, Bool.false_eq_true, ite_false] at e
      by_cases c1 : b.toNat = 0
      · simp only [c1, ite_true, Option.some.injEq] at e
        exact even 0 c1 e.symm rfl
      · by_cases c2 : 16 + 0 ≤ b.toNat ∧ b.toNat < 32 + 0
        · rw [ite_eq_right c1, ite_eq_left c2, Option.some.injEq] at e
          exact odd 0 c2.1 c2.2 e.symm rfl
        · simp [c1, c2] at e
    · simp only [keyOfHP, ite_true] at e
      by_cases c1 : b.toNat = 32
      · simp only [c1, ite_true, Option.some.injEq] at e
        exact even 32 c1 e.symm rfl
      · by_cases c2 : 16 + 32 ≤ b.toNat ∧ b.toNat < 32 + 32
        · rw [ite_eq_right c1, ite_eq_left c2, Option.some.injEq] at e
          exact odd 32 c2.1 c2.2 e.symm rfl
        · simp [c1, c2] at e

/-! ## Child slots -/

def bm0 : Kids → Nat
  | .nil => 0
  | .none r => 2 * bm0 r
  | .some _ r => 1 + 2 * bm0 r

def ex0 : Kids → Nat
  | .nil => 0
  | .none r => 2 * ex0 r
  | .some c r => (if revealed c then 1 else 0) + 2 * ex0 r

/-- The revealed children, in index order. -/
def revKids : Kids → List PTrie
  | .nil => []
  | .none r => revKids r
  | .some c r => if revealed c then c :: revKids r else revKids r

def slotList : Kids → List Bytes
  | .nil => []
  | .none r => slotList r
  | .some c r => slotOf c :: slotList r

theorem kidsBitmap_eq : ∀ (cs : Kids) (i : Nat), kidsBitmap cs i = 2 ^ i * bm0 cs
  | .nil, i => by simp [kidsBitmap, bm0]
  | .none r, i => by
    simp only [kidsBitmap, bm0, kidsBitmap_eq r (i + 1), Nat.pow_succ]
    rw [Nat.mul_assoc]
  | .some _ r, i => by
    simp only [kidsBitmap, bm0, kidsBitmap_eq r (i + 1), Nat.pow_succ]
    rw [Nat.mul_add, Nat.mul_assoc, Nat.mul_one]

theorem expBits_eq : ∀ (cs : Kids) (i : Nat), expBits cs i = 2 ^ i * ex0 cs
  | .nil, i => by simp [expBits, ex0]
  | .none r, i => by
    simp only [expBits, ex0, expBits_eq r (i + 1), Nat.pow_succ]
    rw [Nat.mul_assoc]
  | .some c r, i => by
    simp only [expBits, ex0, expBits_eq r (i + 1), Nat.pow_succ]
    rw [Nat.mul_add, Nat.mul_assoc]
    cases revealed c <;> simp

theorem ex0_le_bm0 : ∀ cs : Kids, ex0 cs ≤ bm0 cs
  | .nil => by simp [ex0, bm0]
  | .none r => by have := ex0_le_bm0 r; simp [ex0, bm0]; omega
  | .some c r => by
    have := ex0_le_bm0 r; simp only [ex0, bm0]; cases revealed c <;> simp <;> omega

theorem wf_succ {cs : Kids} {n : Nat} (h : Kids.wf cs n = true) (hc : cs ≠ .nil) : ∃ m, n = m + 1 := by
  cases cs with
  | nil => exact absurd rfl hc
  | none r => simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h; exact ⟨n - 1, by omega⟩
  | some c r => simp only [Kids.wf, Bool.and_eq_true, bne_iff_ne, ne_eq] at h; exact ⟨n - 1, by omega⟩

theorem bm0_lt : ∀ (cs : Kids) (n : Nat), Kids.wf cs n = true → bm0 cs < 2 ^ n
  | .nil, n, h => by simp [Kids.wf] at h; subst h; simp [bm0]
  | .none r, n, h => by
    obtain ⟨m, rfl⟩ := wf_succ h (by simp)
    simp only [Kids.wf, Bool.and_eq_true, Nat.add_sub_cancel] at h
    have := bm0_lt r m h.2
    simp only [bm0, Nat.pow_succ]; omega
  | .some c r, n, h => by
    obtain ⟨m, rfl⟩ := wf_succ h (by simp)
    simp only [Kids.wf, Bool.and_eq_true, Nat.add_sub_cancel] at h
    have := bm0_lt r m h.2
    simp only [bm0, Nat.pow_succ]; omega

theorem popc_bm0 : ∀ (cs : Kids) (n : Nat), Kids.wf cs n = true → popc n (bm0 cs) = Kids.count cs
  | .nil, n, h => by simp [Kids.wf] at h; subst h; simp [popc, Kids.count]
  | .none r, n, h => by
    obtain ⟨m, rfl⟩ := wf_succ h (by simp)
    simp only [Kids.wf, Bool.and_eq_true, Nat.add_sub_cancel] at h
    have := popc_bm0 r m h.2
    simp only [bm0, popc, Kids.count]
    rw [show 2 * bm0 r / 2 = bm0 r by omega, this]; omega
  | .some c r, n, h => by
    obtain ⟨m, rfl⟩ := wf_succ h (by simp)
    simp only [Kids.wf, Bool.and_eq_true, Nat.add_sub_cancel] at h
    have := popc_bm0 r m h.2
    simp only [bm0, popc, Kids.count]
    rw [show (1 + 2 * bm0 r) / 2 = bm0 r by omega, this]; omega

theorem popc_ex0 : ∀ (cs : Kids) (n : Nat), Kids.wf cs n = true → popc n (ex0 cs) = (revKids cs).length
  | .nil, n, h => by simp [Kids.wf] at h; subst h; simp [popc, revKids]
  | .none r, n, h => by
    obtain ⟨m, rfl⟩ := wf_succ h (by simp)
    simp only [Kids.wf, Bool.and_eq_true, Nat.add_sub_cancel] at h
    have := popc_ex0 r m h.2
    simp only [ex0, popc, revKids]
    rw [show 2 * ex0 r / 2 = ex0 r by omega, this]; omega
  | .some c r, n, h => by
    obtain ⟨m, rfl⟩ := wf_succ h (by simp)
    simp only [Kids.wf, Bool.and_eq_true, Nat.add_sub_cancel] at h
    have := popc_ex0 r m h.2
    simp only [ex0, popc, revKids]
    cases revealed c
    · simp only [Bool.false_eq_true, ite_false]
      rw [show (0 + 2 * ex0 r) / 2 = ex0 r by omega, this]; omega
    · simp only [ite_true, List.length_cons]
      rw [show (1 + 2 * ex0 r) / 2 = ex0 r by omega, this]; omega

theorem slotOf_length {c : PTrie} (h : c.wf = true) : (slotOf c).length = 32 := by
  cases c with
  | hash x => simpa [slotOf, PTrie.wf] using h
  | _ => simp [slotOf]

theorem kidSlots_length : ∀ (cs : Kids) (n : Nat), Kids.wf cs n = true →
    (kidSlots cs).length = 32 * Kids.count cs
  | .nil, _, _ => by simp [kidSlots, Kids.count]
  | .none r, n, h => by
    simp only [Kids.wf, Bool.and_eq_true] at h
    simp [kidSlots, Kids.count, kidSlots_length r _ h.2]
  | .some c r, n, h => by
    simp only [Kids.wf, Bool.and_eq_true] at h
    simp [kidSlots, Kids.count, kidSlots_length r _ h.2, slotOf_length h.1.2]; omega

theorem chunks32_kidSlots : ∀ (cs : Kids) (n : Nat), Kids.wf cs n = true →
    chunks32 (Kids.count cs) (kidSlots cs) = slotList cs
  | .nil, _, _ => by simp [kidSlots, Kids.count, chunks32, slotList]
  | .none r, n, h => by
    simp only [Kids.wf, Bool.and_eq_true] at h
    simp [kidSlots, Kids.count, slotList, chunks32_kidSlots r _ h.2]
  | .some c r, n, h => by
    simp only [Kids.wf, Bool.and_eq_true] at h
    have hl := slotOf_length h.1.2
    simp only [kidSlots, Kids.count, slotList, Nat.add_comm 1, chunks32]
    rw [List.take_left' hl, List.drop_left' hl, chunks32_kidSlots r _ h.2]

theorem mkKids_bm0 : ∀ (cs : Kids) (n : Nat), Kids.wf cs n = true →
    mkKids n (bm0 cs) (ex0 cs) (slotList cs) (revKids cs) = some cs
  | .nil, n, h => by simp [Kids.wf] at h; subst h; simp [mkKids, bm0, ex0, slotList, revKids]
  | .none r, n, h => by
    obtain ⟨m, rfl⟩ := wf_succ h (by simp)
    simp only [Kids.wf, Bool.and_eq_true, Nat.add_sub_cancel] at h
    have := mkKids_bm0 r m h.2
    simp only [mkKids, bm0, ex0, slotList, revKids]
    rw [show 2 * bm0 r / 2 = bm0 r by omega, show 2 * ex0 r / 2 = ex0 r by omega, this]
    simp only [show ¬ (2 * bm0 r % 2 = 1) by omega, show ¬ (2 * ex0 r % 2 = 1) by omega, ite_false]
    rfl
  | .some c r, n, h => by
    obtain ⟨m, rfl⟩ := wf_succ h (by simp)
    simp only [Kids.wf, Bool.and_eq_true, Nat.add_sub_cancel] at h
    have := mkKids_bm0 r m h.2
    simp only [mkKids, bm0, ex0, slotList, revKids]
    rw [show (1 + 2 * bm0 r) / 2 = bm0 r by omega]
    simp only [show (1 + 2 * bm0 r) % 2 = 1 by omega, ite_true]
    cases c with
    | hash x =>
      simp only [revealed, Bool.false_eq_true, ite_false, slotOf]
      rw [show (0 + 2 * ex0 r) / 2 = ex0 r by omega, this]
      simp only [show ¬ ((0 + 2 * ex0 r) % 2 = 1) by omega, ite_false]
      rfl
    | leaf k s mm =>
      simp only [revealed, ite_true]
      rw [show (1 + 2 * ex0 r) / 2 = ex0 r by omega, this]
      simp only [show (1 + 2 * ex0 r) % 2 = 1 by omega, ite_true]
      rfl
    | ext k c' mm =>
      simp only [revealed, ite_true]
      rw [show (1 + 2 * ex0 r) / 2 = ex0 r by omega, this]
      simp only [show (1 + 2 * ex0 r) % 2 = 1 by omega, ite_true]
      rfl
    | branch v cs' mm =>
      simp only [revealed, ite_true]
      rw [show (1 + 2 * ex0 r) / 2 = ex0 r by omega, this]
      simp only [show (1 + 2 * ex0 r) % 2 = 1 by omega, ite_true]
      rfl

theorem popN_append : ∀ (l stk : List PTrie), popN l.length (l ++ stk) = some (l.reverse, stk)
  | [], stk => rfl
  | x :: l, stk => by
    simp only [List.length_cons, List.cons_append, popN, popN_append l stk, List.reverse_cons]
    rfl

/-! ## Record sequences -/

theorem decRecs_add : ∀ (a b : Nat) (stk : List PTrie) (bs : Bytes) (s : List PTrie) (r : Bytes),
    decRecs a stk bs = some (s, r) → decRecs (a + b) stk bs = decRecs b s r
  | 0, b, stk, bs, s, r, h => by
    simp only [decRecs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; simp
  | a + 1, b, stk, bs, s, r, h => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [decRecs] at h ⊢
    split at h
    · simp at h
    · next stk' bs' _ => exact decRecs_add a b stk' bs' s r h

theorem decRecs_one {stk s : List PTrie} {bs r : Bytes} (h : decRec stk bs = some (s, r)) :
    decRecs 1 stk bs = some (s, r) := by
  simp [decRecs, h]

/-! ## One record -/

theorem dec_leaf_rec (k : List Nat) (s : Slot) (m : Nat) (hw : (PTrie.leaf k s m).wf = true)
    (stk : List PTrie) (rest : Bytes) :
    decRec stk (([kindLeaf s] ++ valPart s ++ preLeaf k s m) ++ rest) =
      some (.leaf k s m :: stk, rest) := by
  simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨⟨⟨hk, hs⟩, hm⟩, hl⟩ := hw
  cases s with
  | val v =>
    have hv : v.length < 4294967296 := by simpa [slotOk] using hs
    simp only [kindLeaf, valPart, preLeaf, refPart, List.append_assoc, List.singleton_append,
      List.cons_append, List.nil_append, decRec]
    simp only [show (1 : UInt8).toNat = 1 from rfl, ite_true, decLeaf, decVal]
    rw [readBorsh_append' _ _ hv]
    simp only [Option.map_some, readU8_cons, show (0 : UInt8).toNat = 0 from rfl]
    simp only [ne_eq, not_true_eq_false, ite_false]
    rw [readU32_append _ _ hl]; simp only
    rw [takeN_append]; simp only
    rw [keyOfHP_hexPrefix k true hk]; simp only
    rw [readU32_append _ _ hv]; simp only
    rw [takeN_append' 32 (zeros 32) _ (zeros_length 32)]; simp only
    rw [readU64_append _ _ hm]
    simp [mkSlot]
  | ref len h =>
    have hv : len < 4294967296 ∧ h.length = 32 := by simpa [slotOk] using hs
    simp only [kindLeaf, valPart, preLeaf, refPart, List.append_assoc, List.singleton_append,
      List.cons_append, List.nil_append, decRec]
    simp only [show (2 : UInt8).toNat = 2 from rfl, ite_true, decLeaf, decVal]
    simp only [show ¬ ((2 : Nat) = 1) by decide, ite_false, Bool.false_eq_true]
    simp only [readU8_cons, show (0 : UInt8).toNat = 0 from rfl]
    simp only [ne_eq, not_true_eq_false, ite_false]
    rw [readU32_append _ _ hl]; simp only
    rw [takeN_append]; simp only
    rw [keyOfHP_hexPrefix k true hk]; simp only
    rw [readU32_append _ _ hv.1]; simp only
    rw [takeN_append' 32 h _ hv.2]; simp only
    rw [readU64_append _ _ hm]
    simp [mkSlot]

def pushT (t : PTrie) (stk : List PTrie) : List PTrie := if revealed t then t :: stk else stk

theorem slotOf_rev {c : PTrie} (h : revealed c = true) : slotOf c = zeros 32 := by
  cases c <;> simp_all [revealed, slotOf]

theorem dec_ext_rec (k : List Nat) (c : PTrie) (m : Nat) (hw : (PTrie.ext k c m).wf = true)
    (stk : List PTrie) (rest : Bytes) :
    decRec (pushT c stk) (([3, if revealed c then 1 else 0] ++ preExt k c m) ++ rest) =
      some (.ext k c m :: stk, rest) := by
  simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨⟨⟨hk, hc⟩, hm⟩, hl⟩ := hw
  have hsl := slotOf_length hc
  have common : ∀ (e : UInt8) (stk' : List PTrie), e.toNat ≤ 1 →
      decRec stk' (([3, e] ++ preExt k c m) ++ rest) =
        (if e.toNat = 1 then
          if slotOf c ≠ zeros 32 then none else
          match stk' with
          | [] => none
          | c :: stk'' => some (.ext k c m :: stk'', rest)
        else some (.ext k (.hash (slotOf c)) m :: stk', rest)) := by
    intro e stk' he
    simp only [preExt, List.append_assoc, List.singleton_append, List.cons_append, List.nil_append,
      decRec, show (3 : UInt8).toNat = 3 from rfl]
    simp only [show ¬ ((3 : Nat) = 1) by decide, show ¬ ((3 : Nat) = 2) by decide, ite_false, ite_true,
      decExt, readU8_cons]
    simp only [show ¬ (e.toNat > 1) by omega, ite_false, show (3 : UInt8).toNat = 3 from rfl,
      ne_eq, not_true_eq_false]
    rw [readU32_append _ _ hl]; simp only
    rw [takeN_append]; simp only
    rw [keyOfHP_hexPrefix k false hk]; simp only
    rw [takeN_append' 32 _ _ hsl]; simp only
    rw [readU64_append _ _ hm]; rfl
  cases hr : revealed c
  · cases c with
    | hash x =>
      simp only [pushT, revealed, Bool.false_eq_true, ite_false]
      rw [common 0 stk (by decide)]
      simp [slotOf]
    | _ => simp [revealed] at hr
  · simp only [pushT, hr, ite_true]
    rw [common 1 (c :: stk) (by decide)]
    have : slotOf c = zeros 32 := by cases c <;> simp_all [slotOf, revealed]
    simp [this]

theorem decVal_false (bs : Bytes) : decVal false bs = some (none, bs) := by simp [decVal]
theorem decVal_true (bs : Bytes) :
    decVal true bs = (readBorshBytes bs).map fun (v, r) => (some v, r) := by simp [decVal]

theorem dec_br_rec (v : Option Slot) (cs : Kids) (m : Nat) (hw : (PTrie.branch v cs m).wf = true)
    (stk : List PTrie) (rest : Bytes) :
    decRec ((revKids cs).reverse ++ stk)
        (([kindBr v] ++ optValPart v ++ u16 (expBits cs 0) ++ preBr v cs m) ++ rest) =
      some (.branch v cs m :: stk, rest) := by
  simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq] at hw
  obtain ⟨⟨hv, hcs⟩, hm⟩ := hw
  have hbm : kidsBitmap cs 0 < 65536 := by
    rw [kidsBitmap_eq]; have := bm0_lt cs 16 hcs; simp at this ⊢; omega
  have hex : expBits cs 0 < 65536 := by
    rw [expBits_eq]; have := bm0_lt cs 16 hcs; have := ex0_le_bm0 cs; simp at this ⊢; omega
  have hpb : popc 16 (kidsBitmap cs 0) = Kids.count cs := by
    rw [kidsBitmap_eq]; simpa using popc_bm0 cs 16 hcs
  have hpe : popc 16 (expBits cs 0) = (revKids cs).length := by
    rw [expBits_eq]; simpa using popc_ex0 cs 16 hcs
  have hsl := kidSlots_length cs 16 hcs
  have hch := chunks32_kidSlots cs 16 hcs
  have hmk : mkKids 16 (kidsBitmap cs 0) (expBits cs 0) (slotList cs) (revKids cs) = some cs := by
    rw [kidsBitmap_eq, expBits_eq]; simpa using mkKids_bm0 cs 16 hcs
  have hpop : popN (revKids cs).length ((revKids cs).reverse ++ stk) = some (revKids cs, stk) := by
    have := popN_append (revKids cs).reverse stk
    simpa using this
  cases v with
  | none =>
    simp only [kindBr, optValPart, preBr, brHead, List.append_assoc, List.singleton_append,
      List.cons_append, List.nil_append, decRec, show (4 : UInt8).toNat = 4 from rfl]
    simp only [show ¬ ((4 : Nat) = 1) by decide, show ¬ ((4 : Nat) = 2) by decide,
      show ¬ ((4 : Nat) = 3) by decide, true_or, ite_false, ite_true, decBranch,
      show decide ((4 : Nat) = 5) = false from rfl, decVal_false]
    rw [readU16_append _ _ hex]; simp only
    simp only [readU8_cons, show (1 : UInt8).toNat = 1 from rfl, ne_eq, not_true_eq_false, ite_true,
      ite_false]
    rw [readU16_append _ _ hbm]; simp only
    rw [hpb, takeN_append' _ _ _ hsl]; simp only
    rw [readU64_append _ _ hm]; simp only
    rw [hpe, hpop]; simp only
    rw [hch, hmk]; rfl
  | some s =>
    cases s with
    | val x =>
      have hx : x.length < 4294967296 := by simpa [slotOk] using hv
      simp only [kindBr, optValPart, valPart, preBr, brHead, refPart, List.append_assoc,
        List.singleton_append, List.cons_append, List.nil_append, decRec,
        show (5 : UInt8).toNat = 5 from rfl]
      simp only [show ¬ ((5 : Nat) = 1) by decide, show ¬ ((5 : Nat) = 2) by decide,
        show ¬ ((5 : Nat) = 3) by decide, show ¬ ((5 : Nat) = 4) by decide, true_or, or_true,
        ite_false, ite_true, decBranch, show decide ((5 : Nat) = 5) = true from rfl, decide_true, decVal_true]
      rw [readBorsh_append' _ _ hx]; simp only [Option.map_some]
      rw [readU16_append _ _ hex]; simp only
      simp only [readU8_cons, show (2 : UInt8).toNat = 2 from rfl, ne_eq, not_true_eq_false,
        ite_true, ite_false, show ¬ ((5 : Nat) = 4) by decide]
      rw [readU32_append _ _ hx]; simp only
      rw [takeN_append' 32 (zeros 32) _ (zeros_length 32)]; simp only [Option.map_some]
      rw [readU16_append _ _ hbm]; simp only
      rw [hpb, takeN_append' _ _ _ hsl]; simp only
      rw [readU64_append _ _ hm]; simp only [mkSlot, ite_true, Option.map_some]
      rw [hpe, hpop]; simp only
      rw [hch, hmk]; rfl
    | ref len h =>
      have hx : len < 4294967296 ∧ h.length = 32 := by simpa [slotOk] using hv
      simp only [kindBr, optValPart, valPart, preBr, brHead, refPart, List.append_assoc,
        List.singleton_append, List.cons_append, List.nil_append, decRec,
        show (6 : UInt8).toNat = 6 from rfl]
      simp only [show ¬ ((6 : Nat) = 1) by decide, show ¬ ((6 : Nat) = 2) by decide,
        show ¬ ((6 : Nat) = 3) by decide, show ¬ ((6 : Nat) = 4) by decide,
        show ¬ ((6 : Nat) = 5) by decide, true_or, or_true,
        ite_false, ite_true, decBranch, show decide ((6 : Nat) = 5) = false from rfl, decide_false, decVal_false]
      rw [readU16_append _ _ hex]; simp only
      simp only [readU8_cons, show (2 : UInt8).toNat = 2 from rfl, ne_eq, not_true_eq_false,
        ite_true, ite_false, show ¬ ((6 : Nat) = 4) by decide]
      rw [readU32_append _ _ hx.1]; simp only
      rw [takeN_append' 32 h _ hx.2]; simp only [Option.map_some]
      rw [readU16_append _ _ hbm]; simp only
      rw [hpb, takeN_append' _ _ _ hsl]; simp only
      rw [readU64_append _ _ hm]; simp only [mkSlot, Option.map_some]
      rw [hpe, hpop]; simp only
      rw [hch, hmk]; rfl

/-! ## Round trip of the trie section -/

mutual
theorem dec_T : ∀ (t : PTrie), t.wf = true → ∀ (stk : List PTrie) (rest : Bytes),
    decRecs (cntT t) stk (encT t ++ rest) = some (pushT t stk, rest)
  | .hash h, _, stk, rest => by simp [cntT, encT, decRecs, pushT, revealed]
  | .leaf k s m, hw, stk, rest => by
    simp only [cntT, encT, pushT, revealed, ite_true]
    exact decRecs_one (dec_leaf_rec k s m hw stk rest)
  | .ext k c m, hw, stk, rest => by
    have hc : c.wf = true := by
      simp only [PTrie.wf, Bool.and_eq_true] at hw; exact hw.1.1.2
    simp only [cntT, encT, pushT, revealed, ite_true, List.append_assoc]
    rw [decRecs_add (cntT c) 1 stk _ (pushT c stk) _ (dec_T c hc stk _)]
    have := dec_ext_rec k c m hw stk rest
    rw [List.append_assoc] at this
    exact decRecs_one this
  | .branch v cs m, hw, stk, rest => by
    have hcs : Kids.wf cs 16 = true := by
      simp only [PTrie.wf, Bool.and_eq_true] at hw; exact hw.1.2
    simp only [cntT, encT, pushT, revealed, ite_true, List.append_assoc]
    rw [decRecs_add (cntKids cs) 1 stk _ _ _ (dec_K cs 16 hcs stk _)]
    have := dec_br_rec v cs m hw stk rest
    simp only [List.append_assoc] at this
    exact decRecs_one this
theorem dec_K : ∀ (cs : Kids) (n : Nat), Kids.wf cs n = true → ∀ (stk : List PTrie) (rest : Bytes),
    decRecs (cntKids cs) stk (encKids cs ++ rest) = some ((revKids cs).reverse ++ stk, rest)
  | .nil, _, _, stk, rest => by simp [cntKids, encKids, decRecs, revKids]
  | .none r, n, h, stk, rest => by
    simp only [Kids.wf, Bool.and_eq_true] at h
    simp only [cntKids, encKids, revKids]
    exact dec_K r (n - 1) h.2 stk rest
  | .some c r, n, h, stk, rest => by
    simp only [Kids.wf, Bool.and_eq_true] at h
    simp only [cntKids, encKids, revKids, List.append_assoc]
    rw [decRecs_add _ _ _ _ _ _ (dec_T c h.1.2 stk _), dec_K r (n - 1) h.2]
    cases hrc : revealed c <;> simp [pushT, hrc]
end

/-! ## Receipts -/

theorem mid_eq (x : Bytes) : u32 0 ++ (u32 0 ++ (u32 1 ++ ([3] ++ x))) = receiptMid ++ x := by
  simp [receiptMid]

theorem valid_len {s : Bytes} (h : AccountId.valid s = true) : s.length < 4294967296 := by
  simp only [AccountId.valid, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

theorem decReceipt_encode (r : Receipt) (hw : r.wf = true) (rest : Bytes) :
    decReceipt (r.encode ++ rest) = some (r, rest) := by
  obtain ⟨pred, recv, rid, signer, ⟨tag, kd⟩, gp, dep⟩ := r
  simp only [Receipt.wf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw
  obtain ⟨⟨⟨⟨⟨⟨hp, hr⟩, hs⟩, hk⟩, hid⟩, hgp⟩, hdep⟩ := hw
  simp only [PublicKey.wf, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hk
  have htag : tag < 256 := by omega
  simp only [Receipt.encode, PublicKey.encode, List.append_assoc]
  unfold decReceipt
  rw [readBorsh_append _ _ (valid_len hp)]; simp only
  rw [readBorsh_append _ _ (valid_len hr)]; simp only
  rw [readHash_append _ _ hid]; simp only
  rw [List.singleton_append, readU8_cons]
  simp only [show (0 : UInt8).toNat = 0 from rfl, ne_eq, not_true_eq_false, ite_false]
  rw [readBorsh_append _ _ (valid_len hs)]; simp only
  rw [readU8_append _ _ htag]; simp only
  have hkd : takeN (if tag = 0 then 32 else 64) (kd ++ (u128 gp ++ (u32 0 ++ (u32 0 ++ (u32 1 ++
      ([3] ++ (u128 dep ++ rest))))))) = some (kd, u128 gp ++ (u32 0 ++ (u32 0 ++ (u32 1 ++
      ([3] ++ (u128 dep ++ rest)))))) := by
    have := takeN_append kd (u128 gp ++ (u32 0 ++ (u32 0 ++ (u32 1 ++ ([3] ++ (u128 dep ++ rest))))))
    rcases hk with ⟨rfl, hl⟩ | ⟨rfl, hl⟩ <;> simpa [hl] using this
  have hnt : ¬ (tag ≠ 0 ∧ tag ≠ 1) := by omega
  simp only [hnt, ite_false, hkd]
  rw [readU128_append _ _ hgp]; simp only
  have hmid : ∀ x, takeN 13 (receiptMid ++ x) = some (receiptMid, x) := fun x => takeN_append receiptMid x
  rw [mid_eq, hmid]
  simp only [ne_eq, not_true_eq_false, ite_false]
  rw [readU128_append _ _ hdep]
  rfl

theorem readMany_receipts (rs : List Receipt) (hw : rs.all Receipt.wf = true) (rest : Bytes) :
    readMany decReceipt rs.length (concatAll (rs.map Receipt.encode) ++ rest) = some (rs, rest) := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hw
    simp only [List.length_cons, List.map_cons, concatAll, List.append_assoc, readMany]
    rw [decReceipt_encode r hw.1]
    simp only
    rw [ih hw.2]

/-! ## Sizes -/

mutual
theorem cntT_le' : ∀ t : PTrie, 11 * cntT t ≤ t.revealedBytes
  | .hash _ => by simp [cntT, PTrie.revealedBytes]
  | .leaf k s _ => by
    have := hexPrefix_length k true
    cases s <;> simp [cntT, PTrie.revealedBytes] <;> omega
  | .ext k c _ => by
    have := cntT_le' c
    simp [cntT, PTrie.revealedBytes]; omega
  | .branch v cs _ => by
    have := cntKids_le' cs
    cases v with
    | none => simp [cntT, PTrie.revealedBytes]; omega
    | some s => cases s <;> simp [cntT, PTrie.revealedBytes] <;> omega
theorem cntKids_le' : ∀ cs : Kids, 11 * cntKids cs ≤ Kids.revealedBytes cs
  | .nil => by simp [cntKids, Kids.revealedBytes]
  | .none r => by have := cntKids_le' r; simp [cntKids, Kids.revealedBytes]; omega
  | .some c r => by
    have := cntKids_le' r; have := cntT_le' c
    simp [cntKids, Kids.revealedBytes]; omega
end

mutual
theorem encT_length_le : ∀ t : PTrie, t.wf = true → (encT t).length ≤ t.revealedBytes + 7 * cntT t
  | .hash _, _ => by simp [encT]
  | .leaf k s m, hw => by
    simp only [PTrie.wf, Bool.and_eq_true] at hw
    have hs := hw.1.1.2
    cases s with
    | val v => simp [encT, kindLeaf, valPart, preLeaf, refPart, PTrie.revealedBytes, cntT]; omega
    | ref len h =>
      have : h.length = 32 := by simp [slotOk] at hs; exact hs.2
      simp [encT, kindLeaf, valPart, preLeaf, refPart, PTrie.revealedBytes, cntT]; omega
  | .ext k c m, hw => by
    simp only [PTrie.wf, Bool.and_eq_true] at hw
    have := encT_length_le c hw.1.1.2
    have := slotOf_length hw.1.1.2
    simp [encT, preExt, PTrie.revealedBytes, cntT]; omega
  | .branch v cs m, hw => by
    simp only [PTrie.wf, Bool.and_eq_true] at hw
    have h1 := encKids_length_le cs 16 hw.1.2
    have h2 := kidSlots_length cs 16 hw.1.2
    cases v with
    | none =>
      simp [encT, kindBr, optValPart, preBr, brHead, PTrie.revealedBytes, cntT]; omega
    | some s =>
      have hv := hw.1.1
      cases s with
      | val x => simp [encT, kindBr, optValPart, valPart, preBr, brHead, refPart, PTrie.revealedBytes, cntT]; omega
      | ref len h =>
        have : h.length = 32 := by simp [slotOk] at hv; exact hv.2
        simp [encT, kindBr, optValPart, valPart, preBr, brHead, refPart, PTrie.revealedBytes, cntT]; omega
theorem encKids_length_le : ∀ (cs : Kids) (n : Nat), Kids.wf cs n = true →
    (encKids cs).length ≤ Kids.revealedBytes cs + 7 * cntKids cs
  | .nil, _, _ => by simp [encKids]
  | .none r, n, h => by
    simp only [Kids.wf, Bool.and_eq_true] at h
    have := encKids_length_le r (n - 1) h.2
    simp [encKids, Kids.revealedBytes, cntKids]; omega
  | .some c r, n, h => by
    simp only [Kids.wf, Bool.and_eq_true] at h
    have h1 := encKids_length_le r (n - 1) h.2
    have h2 := encT_length_le c h.1.2
    simp [encKids, Kids.revealedBytes, cntKids]; omega
end

theorem valid_le64 {s : Bytes} (h : AccountId.valid s = true) : s.length ≤ 64 := by
  simp only [AccountId.valid, Bool.and_eq_true, decide_eq_true_eq] at h
  omega

theorem receipt_encode_length (r : Receipt) (hw : r.wf = true) : r.encode.length ≤ 347 := by
  obtain ⟨pred, recv, rid, signer, ⟨tag, kd⟩, gp, dep⟩ := r
  simp only [Receipt.wf, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hw
  obtain ⟨⟨⟨⟨⟨⟨hp, hr⟩, hs⟩, hk⟩, hid⟩, -⟩, -⟩ := hw
  simp only [PublicKey.wf, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hk
  have := valid_le64 hp; have := valid_le64 hr; have := valid_le64 hs
  have : kd.length ≤ 64 := by omega
  simp [Receipt.encode, PublicKey.encode]; omega

theorem concatAll_length_le (rs : List Receipt) (hw : rs.all Receipt.wf = true) :
    (concatAll (rs.map Receipt.encode)).length ≤ 347 * rs.length := by
  induction rs with
  | nil => simp [concatAll]
  | cons r rs ih =>
    simp only [List.all_cons, Bool.and_eq_true] at hw
    have := receipt_encode_length r hw.1
    simp only [List.map_cons, concatAll, List.length_append, List.length_cons]
    have := ih hw.2
    omega

/-! ## Decoded tries have the length of their encoding -/

theorem decVal_some {hasVal : Bool} {bs bs1 : Bytes} {vo : Option Bytes}
    (h : decVal hasVal bs = some (vo, bs1)) :
    (hasVal = false → vo = none) ∧
    ((vo = none ∧ bs = bs1) ∨ (∃ v, vo = some v ∧ bs = u32 v.length ++ v ++ bs1 ∧ v.length < 4294967296)) := by
  cases hasVal with
  | false =>
    simp only [decVal, Bool.false_eq_true, ite_false, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | true =>
    simp only [decVal, ite_true] at h
    cases hr : readBorshBytes bs with
    | none => simp [hr] at h
    | some p =>
      obtain ⟨v, r⟩ := p
      simp only [hr, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨e, hl⟩ := readBorshBytes_some hr
      refine ⟨by simp, Or.inr ⟨v, rfl, ?_, hl⟩⟩
      simpa [borshBytes] using e

theorem mkSlot_some {vo : Option Bytes} {len : Nat} {h : Bytes} {s : Slot}
    (e : mkSlot vo len h = some s) :
    (∃ v, vo = some v ∧ s = .val v ∧ len = v.length) ∨ (vo = none ∧ s = .ref len h) := by
  cases vo with
  | none => simp only [mkSlot, Option.some.injEq] at e; exact Or.inr ⟨rfl, e.symm⟩
  | some v =>
    simp only [mkSlot] at e
    split at e
    · next hl => simp only [Option.some.injEq] at e; exact Or.inl ⟨v, rfl, e.symm, hl.1⟩
    · simp at e

theorem decLeaf_inv {hasVal : Bool} {stk stk' : List PTrie} {bs bs' : Bytes}
    (h : decLeaf hasVal stk bs = some (stk', bs')) :
    ∃ t, stk' = t :: stk ∧ t.wf = true ∧ revealed t = true ∧
      bs.length + 1 = bs'.length + (encT t).length := by
  unfold decLeaf at h
  split at h; · simp at h
  rename_i vo bs1 h1
  split at h; · simp at h
  rename_i tag bs2 h2
  split at h; · simp at h
  split at h; · simp at h
  rename_i hl bs3 h3
  split at h; · simp at h
  rename_i hp bs4 h4
  split at h; · simp at h
  rename_i key h5
  split at h; · simp at h
  rename_i len bs5 h6
  split at h; · simp at h
  rename_i hh bs6 h7
  split at h; · simp at h
  rename_i mm bs7 h8
  cases hs : mkSlot vo len hh with
  | none => simp [hs] at h
  | some s =>
    simp only [hs, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    obtain ⟨-, hv⟩ := decVal_some h1
    obtain ⟨rfl, -⟩ := readLE_some h2
    obtain ⟨rfl, hhl⟩ := readLE_some h3
    obtain ⟨rfl, hpl⟩ := takeN_some h4
    obtain ⟨hpe, hk⟩ := hexPrefix_keyOfHP h5
    obtain ⟨rfl, hlen⟩ := readLE_some h6
    obtain ⟨rfl, hhh⟩ := takeN_some h7
    obtain ⟨rfl, hmm⟩ := readLE_some h8
    refine ⟨_, rfl, ?_, rfl, ?_⟩
    · simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq, hk, hpe, true_and]
      refine ⟨⟨?_, by simpa using hmm⟩, by simp at hhl; omega⟩
      rcases mkSlot_some hs with ⟨v, rfl, rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases hv with ⟨h0, -⟩ | ⟨v', hv', -, hvl⟩
        · simp at h0
        · simp only [Option.some.injEq] at hv'; subst hv'; simpa [slotOk] using hvl
      · simp only [slotOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
        exact ⟨by simpa using hlen, hhh⟩
    · rcases mkSlot_some hs with ⟨v, rfl, rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rcases hv with ⟨h0, -⟩ | ⟨v', hv', rfl, -⟩
        · simp at h0
        · simp only [Option.some.injEq] at hv'; subst hv'
          simp [encT, kindLeaf, valPart, preLeaf, refPart, hpe, leN_length, hpl, hhh]
          omega
      · rcases hv with ⟨-, rfl⟩ | ⟨v', hv', -, -⟩
        · simp [encT, kindLeaf, valPart, preLeaf, refPart, hpe, leN_length, hpl, hhh]
          omega
        · simp at hv'

/-- Total encoding length of the finished subtrees on the stack. -/
def W : List PTrie → Nat
  | [] => 0
  | t :: s => (encT t).length + W s

/-- Every finished subtree is well formed and revealed. -/
def Ok (s : List PTrie) : Prop := ∀ t ∈ s, t.wf = true ∧ revealed t = true

theorem W_append : ∀ a b : List PTrie, W (a ++ b) = W a + W b
  | [], b => by simp [W]
  | x :: a, b => by simp only [List.cons_append, W, W_append a b]; omega

theorem W_reverse : ∀ a : List PTrie, W a.reverse = W a
  | [] => rfl
  | x :: a => by simp only [List.reverse_cons, W_append, W_reverse a, W]; omega

theorem popN_inv : ∀ (k : Nat) (stk cs s0 : List PTrie), popN k stk = some (cs, s0) →
    stk = cs.reverse ++ s0
  | 0, stk, cs, s0, h => by
    simp only [popN, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h; rfl
  | k + 1, [], cs, s0, h => by simp [popN] at h
  | k + 1, x :: stk, cs, s0, h => by
    simp only [popN] at h
    cases hp : popN k stk with
    | none => simp [hp] at h
    | some p =>
      obtain ⟨cs', s0'⟩ := p
      simp only [hp, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      rw [popN_inv k stk _ _ hp]
      simp

theorem chunks32_inv : ∀ (p : Nat) (bs : Bytes), bs.length = 32 * p →
    (chunks32 p bs).length = p ∧ ∀ x ∈ chunks32 p bs, x.length = 32
  | 0, bs, _ => by simp [chunks32]
  | p + 1, bs, h => by
    have ih := chunks32_inv p (bs.drop 32) (by simp; omega)
    simp only [chunks32, List.length_cons, List.mem_cons, ih.1, true_and]
    rintro x (rfl | hx)
    · simp; omega
    · exact ih.2 x hx

theorem mkKids_inv : ∀ (n bm ex : Nat) (hs : List Bytes) (cs : List PTrie) (kids : Kids),
    mkKids n bm ex hs cs = some kids → (∀ x ∈ hs, x.length = 32) → Ok cs →
    Kids.wf kids n = true ∧ (kidSlots kids).length = 32 * hs.length ∧ (encKids kids).length = W cs
  | 0, bm, ex, [], [], kids, h, _, _ => by
    simp only [mkKids, Option.some.injEq] at h; subst h; simp [Kids.wf, kidSlots, encKids, W]
  | 0, bm, ex, _ :: _, _, kids, h, _, _ => by simp [mkKids] at h
  | 0, bm, ex, [], _ :: _, kids, h, _, _ => by simp [mkKids] at h
  | n + 1, bm, ex, hs, cs, kids, h, hhs, hok => by
    simp only [mkKids] at h
    split at h
    · split at h
      · simp at h
      · rename_i x hs' 
        have hx : x.length = 32 := hhs x (by simp)
        have hhs' : ∀ y ∈ hs', y.length = 32 := fun y hy => hhs y (by simp [hy])
        split at h
        · split at h
          · simp at h
          split at h
          · simp at h
          · rename_i c cs'
            cases hk : mkKids n (bm / 2) (ex / 2) hs' cs' with
            | none => simp [hk] at h
            | some k' =>
              simp only [hk, Option.map_some, Option.some.injEq] at h
              subst h
              have hc := hok c (by simp)
              have ih := mkKids_inv n _ _ hs' cs' k' hk hhs' (fun t ht => hok t (by simp [ht]))
              simp only [Kids.wf, kidSlots, encKids, W, List.length_append, List.length_cons,
                slotOf_length hc.1, hc.1, ih.1, ih.2.1, ih.2.2, Nat.add_sub_cancel]
              simp; omega
        · cases hk : mkKids n (bm / 2) (ex / 2) hs' cs with
          | none => simp [hk] at h
          | some k' =>
            simp only [hk, Option.map_some, Option.some.injEq] at h
            subst h
            have ih := mkKids_inv n _ _ hs' cs k' hk hhs' hok
            simp only [Kids.wf, kidSlots, encKids, W, List.length_append, List.length_cons,
              slotOf, PTrie.wf, hx, ih.1, ih.2.1, ih.2.2, Nat.add_sub_cancel, encT]
            simp; omega
    · split at h
      · simp at h
      · cases hk : mkKids n (bm / 2) (ex / 2) hs cs with
        | none => simp [hk] at h
        | some k' =>
          simp only [hk, Option.map_some, Option.some.injEq] at h
          subst h
          have ih := mkKids_inv n _ _ hs cs k' hk hhs hok
          simp only [Kids.wf, kidSlots, encKids, ih.1, ih.2.1, ih.2.2, Nat.add_sub_cancel]
          simp

theorem decExt_inv {stk stk' : List PTrie} {bs bs' : Bytes} (hok : Ok stk)
    (h : decExt stk bs = some (stk', bs')) :
    ∃ t s0, stk' = t :: s0 ∧ Ok s0 ∧ t.wf = true ∧ revealed t = true ∧
      bs.length + 1 + W stk = bs'.length + (encT t).length + W s0 := by
  unfold decExt at h
  split at h; · simp at h
  rename_i e bs1 h1
  split at h; · simp at h
  rename_i he
  split at h; · simp at h
  rename_i tag bs2 h2
  split at h; · simp at h
  split at h; · simp at h
  rename_i hl bs3 h3
  split at h; · simp at h
  rename_i hp bs4 h4
  split at h; · simp at h
  rename_i key h5
  split at h; · simp at h
  rename_i hh bs5 h6
  split at h; · simp at h
  rename_i mm bs6 h7
  obtain ⟨rfl, -⟩ := readLE_some h1
  obtain ⟨rfl, -⟩ := readLE_some h2
  obtain ⟨rfl, hhl⟩ := readLE_some h3
  obtain ⟨rfl, hpl⟩ := takeN_some h4
  obtain ⟨hpe, hk⟩ := hexPrefix_keyOfHP h5
  obtain ⟨rfl, hhh⟩ := takeN_some h6
  obtain ⟨rfl, hmm⟩ := readLE_some h7
  have hwf : ∀ c, c.wf = true → (PTrie.ext key c mm).wf = true := by
    intro c hc
    simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq, hk, hpe, hc, true_and]
    exact ⟨by simpa using hmm, by simp at hhl; omega⟩
  split at h
  · split at h
    · simp at h
    split at h
    · simp at h
    · rename_i c s0
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      have hc := hok c (by simp)
      refine ⟨_, s0, rfl, fun t ht => hok t (by simp [ht]), hwf c hc.1, rfl, ?_⟩
      simp [encT, preExt, hpe, leN_length, hpl, slotOf_length hc.1, hc.2, W]
      omega
  · simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨_, stk, rfl, hok, hwf _ (by simpa [PTrie.wf] using hhh), rfl, ?_⟩
    simp [encT, preExt, hpe, leN_length, hpl, slotOf, hhh, revealed]
    omega

theorem Ok_split {cs s0 : List PTrie} (h : Ok (cs.reverse ++ s0)) : Ok cs ∧ Ok s0 :=
  ⟨fun t ht => h t (by simp [ht]), fun t ht => h t (by simp [ht])⟩

theorem decBranch_inv {kind : Nat} {stk stk' : List PTrie} {bs bs' : Bytes} (hok : Ok stk)
    (h : decBranch kind stk bs = some (stk', bs')) :
    ∃ t s0, stk' = t :: s0 ∧ Ok s0 ∧ t.wf = true ∧ revealed t = true ∧
      bs.length + 1 + W stk = bs'.length + (encT t).length + W s0 := by
  unfold decBranch at h
  split at h; · simp at h
  rename_i vo bs1 h1
  split at h; · simp at h
  rename_i ex bs2 h2
  split at h; · simp at h
  rename_i tag bs3 h3
  obtain ⟨hvn, hv⟩ := decVal_some h1
  obtain ⟨rfl, -⟩ := readLE_some h2
  obtain ⟨rfl, -⟩ := readLE_some h3
  by_cases k4 : kind = 4
  · subst k4
    have hvo : vo = none := hvn (by decide)
    subst hvo
    simp only [ite_true] at h
    have ht : tag = 1 := Classical.byContradiction fun ht => by simp [ht] at h
    simp only [ht, ne_eq, not_true_eq_false, ite_false] at h
    split at h; · simp at h
    rename_i bm bs5 h5
    split at h; · simp at h
    rename_i slots bs6 h6
    split at h; · simp at h
    rename_i mm bs7 h7
    split at h; · simp at h
    rename_i cs s0 h9
    cases hk : mkKids 16 bm ex (chunks32 (popc 16 bm) slots) cs with
    | none => simp [hk] at h
    | some kids =>
      simp only [hk, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, -⟩ := readLE_some h5
      obtain ⟨rfl, hsl⟩ := takeN_some h6
      obtain ⟨rfl, hmm⟩ := readLE_some h7
      have hstk := popN_inv _ _ _ _ h9
      subst hstk
      have hch := chunks32_inv _ slots hsl
      obtain ⟨hokc, hoks⟩ := Ok_split hok
      obtain ⟨hkw, hks, hke⟩ := mkKids_inv 16 bm ex _ cs kids hk hch.2 hokc
      refine ⟨_, s0, rfl, hoks, ?_, rfl, ?_⟩
      · simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq, hkw, true_and]
        simpa using hmm
      · rcases hv with ⟨-, rfl⟩ | ⟨v, hv, -⟩
        · rw [W_append, W_reverse]
          simp only [encT, kindBr, optValPart, preBr, brHead, List.length_append, hks, hke, hch.1,
            leN_length, u16_length, u64_length, List.length_cons, List.length_nil, ht]
          omega
        · simp at hv
  · simp only [k4, ite_false] at h
    have ht : tag = 2 := Classical.byContradiction fun ht => by simp [ht] at h
    simp only [ht, ne_eq, not_true_eq_false, ite_false] at h
    cases hr : readU32 bs3 with
    | none => simp [hr] at h
    | some p =>
    obtain ⟨len, bs4⟩ := p
    cases ht32 : takeN 32 bs4 with
    | none => simp [hr, ht32] at h
    | some q =>
    obtain ⟨hh, bs5⟩ := q
    simp only [hr, ht32, Option.map_some] at h
    split at h; · simp at h
    rename_i bm bs6 h6
    split at h; · simp at h
    rename_i slots bs7 h7
    split at h; · simp at h
    rename_i mm bs8 h8
    cases hs : mkSlot vo len hh with
    | none => simp [hs] at h
    | some s =>
    simp only [hs, Option.map_some] at h
    split at h; · simp at h
    rename_i cs s0 h9
    cases hk : mkKids 16 bm ex (chunks32 (popc 16 bm) slots) cs with
    | none => simp [hk] at h
    | some kids =>
      simp only [hk, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨rfl, hlen⟩ := readLE_some hr
      obtain ⟨rfl, hhh⟩ := takeN_some ht32
      obtain ⟨rfl, -⟩ := readLE_some h6
      obtain ⟨rfl, hsl⟩ := takeN_some h7
      obtain ⟨rfl, hmm⟩ := readLE_some h8
      have hstk := popN_inv _ _ _ _ h9
      subst hstk
      have hch := chunks32_inv _ slots hsl
      obtain ⟨hokc, hoks⟩ := Ok_split hok
      obtain ⟨hkw, hks, hke⟩ := mkKids_inv 16 bm ex _ cs kids hk hch.2 hokc
      refine ⟨_, s0, rfl, hoks, ?_, rfl, ?_⟩
      · simp only [PTrie.wf, Bool.and_eq_true, decide_eq_true_eq, hkw, and_true]
        refine ⟨?_, by simpa using hmm⟩
        rcases mkSlot_some hs with ⟨v, rfl, rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rcases hv with ⟨h0, -⟩ | ⟨v', hv', -, hvl⟩
          · simp at h0
          · simp only [Option.some.injEq] at hv'; subst hv'; simpa [slotOk] using hvl
        · simp only [slotOk, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
          exact ⟨by simpa using hlen, hhh⟩
      · rw [W_append, W_reverse]
        rcases mkSlot_some hs with ⟨v, rfl, rfl, rfl⟩ | ⟨rfl, rfl⟩
        · rcases hv with ⟨h0, -⟩ | ⟨v', hv', rfl, -⟩
          · simp at h0
          · simp only [Option.some.injEq] at hv'; subst hv'
            simp only [encT, kindBr, optValPart, valPart, preBr, brHead, refPart, List.length_append,
              hks, hke, hch.1, leN_length, u16_length, u32_length, u64_length, zeros_length,
              List.length_cons, List.length_nil, ht, hhh]
            omega
        · rcases hv with ⟨-, rfl⟩ | ⟨v', hv', -, -⟩
          · simp only [encT, kindBr, optValPart, valPart, preBr, brHead, refPart, List.length_append,
              hks, hke, hch.1, leN_length, u16_length, u32_length, u64_length, zeros_length,
              List.length_cons, List.length_nil, ht, hhh]
            omega
          · simp at hv'

theorem decRec_inv {stk stk' : List PTrie} {bs bs' : Bytes} (hok : Ok stk)
    (h : decRec stk bs = some (stk', bs')) :
    Ok stk' ∧ bs.length + W stk = bs'.length + W stk' := by
  cases bs with
  | nil => simp [decRec] at h
  | cons kd bs0 =>
    simp only [decRec] at h
    have fin : ∀ t s0, stk' = t :: s0 → Ok s0 → t.wf = true → revealed t = true →
        bs0.length + 1 + W stk = bs'.length + (encT t).length + W s0 →
        Ok stk' ∧ (kd :: bs0).length + W stk = bs'.length + W stk' := by
      intro t s0 e hs0 hw hr hl
      subst e
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [List.mem_cons] at hx
        rcases hx with rfl | hx
        · exact ⟨hw, hr⟩
        · exact hs0 x hx
      · simp only [List.length_cons, W]; omega
    split at h
    · obtain ⟨t, e, hw, hr, hl⟩ := decLeaf_inv h
      exact fin t stk e hok hw hr (by omega)
    · split at h
      · obtain ⟨t, e, hw, hr, hl⟩ := decLeaf_inv h
        exact fin t stk e hok hw hr (by omega)
      · split at h
        · obtain ⟨t, s0, e, hs0, hw, hr, hl⟩ := decExt_inv hok h
          exact fin t s0 e hs0 hw hr hl
        · split at h
          · obtain ⟨t, s0, e, hs0, hw, hr, hl⟩ := decBranch_inv hok h
            exact fin t s0 e hs0 hw hr hl
          · simp at h

theorem decRecs_inv : ∀ (n : Nat) (stk : List PTrie) (bs : Bytes) (stk' : List PTrie) (bs' : Bytes),
    Ok stk → decRecs n stk bs = some (stk', bs') →
    Ok stk' ∧ bs.length + W stk = bs'.length + W stk'
  | 0, stk, bs, stk', bs', hok, h => by
    simp only [decRecs, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hok, rfl⟩
  | n + 1, stk, bs, stk', bs', hok, h => by
    simp only [decRecs] at h
    split at h
    · simp at h
    · rename_i s1 b1 h1
      obtain ⟨hok1, hl1⟩ := decRec_inv hok h1
      obtain ⟨hok2, hl2⟩ := decRecs_inv n s1 b1 stk' bs' hok1 h
      exact ⟨hok2, by omega⟩

/-! ## Main statements -/

/-- Conditions under which the codec round-trips (all implied by the relation). -/
structure Encodable (w : Witness) : Prop where
  receipts_wf : w.receipts.all Receipt.wf = true
  receipts_len : w.receipts.length < 4294967296
  trie_wf : w.trie.wf = true
  trie_size : w.trie.revealedBytes ≤ 3000000
  trie_revealed : revealed w.trie = true

theorem decodeProof_encodeProof (w : Witness) (h : Encodable w) :
    decodeProof (encodeProof w) = some w := by
  obtain ⟨rs, t⟩ := w
  have hcnt : cntT t < 4294967296 := by
    have h1 := cntT_le' t; have h2 : t.revealedBytes ≤ 3000000 := h.trie_size; omega
  unfold decodeProof encodeProof
  simp only [encodeReceipts, encTrie, List.append_assoc]
  rw [readU32_append _ _ h.receipts_len]; simp only
  rw [readMany_receipts rs h.receipts_wf]; simp only
  unfold decTrie
  rw [readU32_append _ _ hcnt]; simp only
  have := dec_T t h.trie_wf [] []
  rw [List.append_nil] at this
  rw [this]
  simp [pushT, h.trie_revealed]

/-- Every revealed node accounts for at least 11 revealed bytes. -/
theorem cntT_le (t : PTrie) (h : t.wf = true) : 11 * cntT t ≤ t.revealedBytes := by
  have _ := h
  exact cntT_le' t

theorem encTrie_length_le (t : PTrie) (h : t.wf = true) :
    (encTrie t).length ≤ 4 + t.revealedBytes + 7 * cntT t := by
  have := encT_length_le t h
  simp only [encTrie, List.length_append, u32_length]; omega

theorem encodeProof_length_le (w : Witness) (h : Encodable w) :
    (encodeProof w).length ≤ 4 + 347 * w.receipts.length + 4 + w.trie.revealedBytes + 7 * cntT w.trie := by
  have := concatAll_length_le w.receipts h.receipts_wf
  have := encTrie_length_le w.trie h.trie_wf
  simp only [encodeProof, encodeReceipts, List.length_append, u32_length]
  omega

theorem decTrie_some {bs : Bytes} {t : PTrie} (e : decTrie bs = some t) :
    bs.length = (encTrie t).length ∧ t.wf = true ∧ revealed t = true := by
  unfold decTrie at e
  split at e; · simp at e
  rename_i n bs1 h1
  split at e
  · rename_i t' hd
    simp only [Option.some.injEq] at e; subst e
    obtain ⟨rfl, -⟩ := readLE_some h1
    obtain ⟨hok, hl⟩ := decRecs_inv n [] bs1 _ _ (by simp [Ok]) hd
    have := hok t' (by simp)
    refine ⟨?_, this.1, this.2⟩
    simp only [W, List.length_nil] at hl
    simp only [encTrie, List.length_append, leN_length, u32_length]; omega
  · simp at e

theorem decodeProof_some {pb : Bytes} {w : Witness} (e : decodeProof pb = some w) :
    pb.length = (encodeProof w).length ∧ w.trie.wf = true ∧ revealed w.trie = true := by
  unfold decodeProof at e
  split at e; · simp at e
  rename_i n bs h1
  split at e; · simp at e
  rename_i rs bs2 h2
  cases hd : decTrie bs2 with
  | none => simp [hd] at e
  | some t =>
    simp only [hd, Option.map_some, Option.some.injEq] at e
    subst e
    obtain ⟨rfl, -⟩ := readLE_some h1
    obtain ⟨rfl, hlen⟩ := readMany_decReceipt_some h2
    obtain ⟨hl, hw, hr⟩ := decTrie_some hd
    refine ⟨?_, hw, hr⟩
    simp only [encodeProof, encodeReceipts, List.length_append, leN_length, u32_length, hl]
    omega

end ReexecNpai
