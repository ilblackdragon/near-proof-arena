import ReexecNpai.Spec.State
import NpaiIR.Lib.NumSpec

/-!
# Batch proofs, part 1: pure lemmas

* `applyAll` on prefixes; one receipt step (`applyReceipt`) in closed form;
* byte-level helpers (`readMem` slices, `leN`/`leNat` bridges);
* the data segment, receipt fields in memory;
* arena layout: entries are disjoint, ordered intervals of the proof copy;
  `TrieSt` is preserved by scratch writes and updated by a value write.
-/

set_option maxRecDepth 8000
set_option linter.unusedSimpArgs false

namespace ReexecNpai

open NpaiIR ArenaCore.Interp NearSpec NearSpec.TransferV1

/-! ## `applyAll` -/

theorem applyAll_append (ctx : Ctx) : ∀ (st : Acc) (l1 l2 : List Receipt),
    applyAll ctx st (l1 ++ l2) = (applyAll ctx st l1).bind (fun s => applyAll ctx s l2)
  | st, [], l2 => rfl
  | st, r :: l1, l2 => by
    simp only [List.cons_append, applyAll]
    cases applyReceipt ctx st r with
    | none => rfl
    | some s => exact applyAll_append ctx s l1 l2

theorem applyAll_take_succ {ctx : Ctx} {st0 st : Acc} {rs : List Receipt} {j : Nat}
    (h : applyAll ctx st0 (rs.take j) = some st) (hj : j < rs.length) :
    applyAll ctx st0 (rs.take (j + 1)) = applyReceipt ctx st rs[j] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hj, Option.toList_some, applyAll_append, h]
  simp only [Option.bind_some, applyAll]
  cases applyReceipt ctx st rs[j] <;> rfl

theorem applyAll_drop {ctx : Ctx} {st0 st acc : Acc} {rs : List Receipt} {j : Nat}
    (h : applyAll ctx st0 (rs.take j) = some st) (ha : applyAll ctx st0 rs = some acc) :
    applyAll ctx st (rs.drop j) = some acc := by
  rw [← List.take_append_drop j rs, applyAll_append, h] at ha
  simpa using ha

/-! ## One receipt in closed form -/

def acctAmt (raw : List UInt8) : Nat := leNat (raw.take 16)
def acctLck (raw : List UInt8) : Nat := leNat ((raw.drop 16).take 16)
def acctSU (raw : List UInt8) : Nat := leNat (raw.drop 64)
def burnP (ctx : Ctx) (r : Receipt) : Nat := min r.gasPrice ctx.blockGasPrice
def surplusOf (ctx : Ctx) (r : Receipt) : Nat := Params.G * (r.gasPrice - burnP ctx r)

/-- The conditions under which `applyReceipt` succeeds (given the account value `raw`). -/
structure StepOk (ctx : Ctx) (tok : Nat) (r : Receipt) (raw : List UInt8) : Prop where
  len : raw.length = 72
  c1 : acctAmt raw + r.deposit < Params.u128Max
  c2 : acctAmt raw + r.deposit + acctLck raw < Params.two128
  c3 : Params.storageAmountPerByte * acctSU raw ≤ acctAmt raw + r.deposit + acctLck raw ∨ acctSU raw ≤ 770
  c4 : Params.G * burnP ctx r < Params.two128
  c5 : surplusOf ctx r < Params.two128
  c6 : tok + Params.G * burnP ctx r < Params.two128

def newVal (raw : List UInt8) (amt : Nat) : List UInt8 := u128 amt ++ raw.drop 16

def refundOf (ctx : Ctx) (r : Receipt) : List Receipt :=
  if surplusOf ctx r = 0 then [] else [gasRefundReceipt r ctx.blockHeight (surplusOf ctx r)]

def outcomeOf (ctx : Ctx) (r : Receipt) : NearSpec.Outcome :=
  { id := r.receiptId, receiptIds := (refundOf ctx r).map Receipt.receiptId, gasBurnt := Params.G,
    tokensBurnt := Params.G * burnP ctx r, executorId := r.receiverId }

def stepAcc (ctx : Ctx) (st : Acc) (r : Receipt) (t' : PTrie) : Acc :=
  { trie := t', outcomes := st.outcomes ++ [outcomeOf ctx r], refunds := st.refunds ++ refundOf ctx r,
    gasBurnt := st.gasBurnt + Params.G, tokensBurnt := st.tokensBurnt + Params.G * burnP ctx r }

theorem u128_leNat {l : List UInt8} (h : l.length = 16) : u128 (leNat l) = l := by
  have := leN_leNat l; rw [h] at this; exact this

theorem u64_leNat {l : List UInt8} (h : l.length = 8) : u64 (leNat l) = l := by
  have := leN_leNat l; rw [h] at this; exact this

theorem encode_upd (raw : List UInt8) (h : raw.length = 72) (amt : Nat) :
    Account.encode ⟨amt, leNat ((raw.drop 16).take 16), (raw.drop 32).take 32, leNat (raw.drop 64)⟩ =
      newVal raw amt := by
  simp only [Account.encode, newVal]
  rw [u128_leNat (by simp; omega), u64_leNat (by simp; omega)]
  simp only [List.append_assoc]
  congr 1
  have e1 : (raw.drop 16).take 16 ++ raw.drop 32 = raw.drop 16 := by
    rw [show raw.drop 32 = (raw.drop 16).drop 16 by simp]; exact List.take_append_drop _ _
  have e2 : (raw.drop 32).take 32 ++ raw.drop 64 = raw.drop 32 := by
    rw [show raw.drop 64 = (raw.drop 32).drop 32 by simp]; exact List.take_append_drop _ _
  rw [e2, e1]

theorem u128Max_lt : Params.u128Max < Params.two128 := by decide

theorem applyReceipt_some {ctx : Ctx} {st : Acc} {r : Receipt} {raw : List UInt8} {t' : PTrie}
    (hg : st.trie.get (accountKeyPath r.receiverId) = some raw) (hok : StepOk ctx st.tokensBurnt r raw)
    (hs : st.trie.set (accountKeyPath r.receiverId) (newVal raw (acctAmt raw + r.deposit)) = some t') :
    applyReceipt ctx st r = some (stepAcc ctx st r t') := by
  obtain ⟨hl, c1, c2, c3, c4, c5, c6⟩ := hok
  have hne : leNat (raw.take 16) ≠ Params.u128Max := by
    intro e; simp only [acctAmt] at c1; omega
  simp only [applyReceipt, hg, Account.decode, hl, ↓reduceIte, hne]
  simp only [acctAmt, acctLck, acctSU, burnP, surplusOf] at c1 c2 c3 c4 c5 c6 hs
  have n3 : ¬ ((!(decide (leNat (List.take 16 raw) + r.deposit + leNat (List.take 16 (List.drop 16 raw)) ≥
      Params.storageAmountPerByte * leNat (List.drop 64 raw)) ||
      decide (leNat (List.drop 64 raw) ≤ Params.zeroBalanceStorageLimit))) = true) := by
    rcases c3 with c3 | c3
    · simp [show leNat (List.take 16 raw) + r.deposit + leNat (List.take 16 (List.drop 16 raw)) ≥
        Params.storageAmountPerByte * leNat (List.drop 64 raw) from c3]
    · simp [Params.zeroBalanceStorageLimit, c3]
  rw [if_neg (by omega), if_neg (by omega), if_neg n3,
    if_neg (by simp; omega), if_neg (by omega), encode_upd raw hl, hs]
  rfl

theorem applyReceipt_inv {ctx : Ctx} {st st' : Acc} {r : Receipt} {raw : List UInt8}
    (hg : st.trie.get (accountKeyPath r.receiverId) = some raw) (h : applyReceipt ctx st r = some st') :
    StepOk ctx st.tokensBurnt r raw ∧ ∃ t', st.trie.set (accountKeyPath r.receiverId)
      (newVal raw (acctAmt raw + r.deposit)) = some t' ∧ st' = stepAcc ctx st r t' := by
  simp only [applyReceipt, hg, Account.decode] at h
  by_cases hl : raw.length = 72
  case neg => simp [hl] at h
  simp only [hl, ↓reduceIte] at h
  by_cases hne : leNat (raw.take 16) = Params.u128Max
  · simp [hne] at h
  simp only [hne, ↓reduceIte] at h
  split at h
  · cases h
  rename_i n1
  split at h
  · cases h
  rename_i n2
  split at h
  · cases h
  rename_i n3
  split at h
  · cases h
  rename_i n4
  split at h
  · cases h
  rename_i n6
  rw [encode_upd raw hl] at h
  split at h
  · cases h
  rename_i t' hs
  cases h
  simp only [Bool.not_eq_true', Bool.or_eq_false_iff, decide_eq_false_iff_not, not_and, Decidable.not_not,
    Bool.or_eq_true, decide_eq_true_eq, not_or] at n3 n4
  refine ⟨⟨hl, ?_, ?_, ?_, ?_, ?_, ?_⟩, t', hs, rfl⟩ <;>
    simp only [acctAmt, acctLck, acctSU, burnP, surplusOf, Params.zeroBalanceStorageLimit] at * <;> omega

/-! ## Bytes -/

theorem leN_eq : ∀ (n x : Nat), ArenaCore.Bytes.leN n x = NearSpec.leN n x
  | 0, _ => rfl
  | n + 1, x => by simp only [ArenaCore.Bytes.leN, NearSpec.leN, leN_eq n]

theorem leToNat_eq : ∀ (l : List UInt8), ArenaCore.Bytes.leToNat l = leNat l
  | [] => rfl
  | x :: xs => by simp only [ArenaCore.Bytes.leToNat, leNat, leToNat_eq xs]

theorem u32_len (x : Nat) : (u32 x).length = 4 := NearSpec.leN_length 4 x
theorem u64_len (x : Nat) : (u64 x).length = 8 := NearSpec.leN_length 8 x
theorem u128_len (x : Nat) : (u128 x).length = 16 := NearSpec.leN_length 16 x

theorem leToNat_u32 {x : Nat} (h : x < 4294967296) : ArenaCore.Bytes.leToNat (u32 x) = x := by
  rw [leToNat_eq]; exact NearSpec.leNat_leN 4 x (by simpa using h)

theorem readMem_sub {M0 : Nat → UInt8} {a L : Nat} {l : List UInt8} (h : readMem M0 a L = l) (o n : Nat)
    (hn : o + n ≤ L) : readMem M0 (a + o) n = (l.drop o).take n := by
  subst h
  apply List.ext_getElem (by simp; omega)
  intro i h1 h2
  simp [readMem, Nat.add_assoc]

theorem rm_split {M0 : Nat → UInt8} {a : Nat} {l1 l2 : List UInt8}
    (h : readMem M0 a (l1 ++ l2).length = l1 ++ l2) :
    readMem M0 a l1.length = l1 ∧ readMem M0 (a + l1.length) l2.length = l2 := by
  rw [List.length_append, readMem_add] at h
  exact List.append_inj h (by simp)

theorem rm_split' {M0 : Nat → UInt8} {a n : Nat} {l1 l2 : List UInt8}
    (h : readMem M0 a n = l1 ++ l2) (hn : n = l1.length + l2.length) :
    readMem M0 a l1.length = l1 ∧ readMem M0 (a + l1.length) l2.length = l2 := by
  subst hn; exact rm_split (by simpa using h)

/-! ## Data segment -/

theorem data_sub {M0 : Nat → UInt8} (h : readMem M0 0 168 = dataSeg) (o n : Nat) (hn : o + n ≤ 168) :
    readMem M0 o n = (dataSeg.drop o).take n := by
  have := readMem_sub h o n hn; simpa using this

theorem data_ff {M0 : Nat → UInt8} (h : readMem M0 0 168 = dataSeg) :
    readMem M0 104 16 = List.replicate 16 255 := by rw [data_sub h 104 16 (by decide)]; rfl

theorem data_g {M0 : Nat → UInt8} (h : readMem M0 0 168 = dataSeg) :
    ArenaCore.Bytes.leToNat (readMem M0 120 8) = Params.G := by rw [data_sub h 120 8 (by decide)]; rfl

theorem data_p519 {M0 : Nat → UInt8} (h : readMem M0 0 168 = dataSeg) :
    ArenaCore.Bytes.leToNat (readMem M0 128 8) = 19073486328125 := by rw [data_sub h 128 8 (by decide)]; rfl

theorem data_zero {M0 : Nat → UInt8} (h : readMem M0 0 168 = dataSeg) (n : Nat) (hn : n ≤ 32) :
    readMem M0 136 n = List.replicate n 0 := by
  rw [data_sub h 136 n (by omega)]
  have e : dataSeg.drop 136 = List.replicate 32 0 := by rfl
  rw [e, List.take_replicate, Nat.min_eq_left hn]

theorem data_sys {M0 : Nat → UInt8} (h : readMem M0 0 168 = dataSeg) :
    readMem M0 80 6 = AccountId.system := by rw [data_sub h 80 6 (by decide)]; rfl

theorem data_mid {M0 : Nat → UInt8} (h : readMem M0 0 168 = dataSeg) :
    readMem M0 88 13 = receiptMid := by rw [data_sub h 88 13 (by decide)]; rfl

/-! ## Receipt fields in memory -/

def pRecv (r : Receipt) (A : Nat) : Nat := A + 4 + r.predecessorId.length + 4
def pRid (r : Receipt) (A : Nat) : Nat := pRecv r A + r.receiverId.length
def pSig (r : Receipt) (A : Nat) : Nat := pRid r A + 37
def pPk (r : Receipt) (A : Nat) : Nat := pSig r A + r.signerId.length
def pGp (r : Receipt) (A : Nat) : Nat := pPk r A + 1 + r.signerPk.data.length

theorem rtBytes_eq (r : Receipt) (A : Nat) : rtBytes r A = u32 (A + 4) ++ (u32 r.predecessorId.length ++
    (u32 (pRecv r A) ++ (u32 r.receiverId.length ++ (u32 (pRid r A) ++ (u32 (pSig r A) ++
    (u32 r.signerId.length ++ (u32 (pPk r A) ++ (u32 (pGp r A) ++ u32 (pGp r A + 29))))))))) := by
  simp only [rtBytes, pRecv, pRid, pSig, pPk, pGp, List.append_assoc]

structure RcptMem (M0 : Nat → UInt8) (r : Receipt) (A : Nat) : Prop where
  recv : readMem M0 (pRecv r A) r.receiverId.length = r.receiverId
  rid : readMem M0 (pRid r A) 32 = r.receiptId
  sig : readMem M0 (pSig r A) r.signerId.length = r.signerId
  pk : readMem M0 (pPk r A) (1 + r.signerPk.data.length) = r.signerPk.encode
  gp : readMem M0 (pGp r A) 16 = u128 r.gasPrice
  dep : readMem M0 (pGp r A + 29) 16 = u128 r.deposit

theorem rcptMem_of {M0 : Nat → UInt8} {r : Receipt} {A : Nat} (hrid : r.receiptId.length = 32)
    (h : readMem M0 A r.encode.length = r.encode) : RcptMem M0 r A := by
  simp only [Receipt.encode, borshBytes, List.append_assoc] at h
  obtain ⟨-, h⟩ := rm_split h
  obtain ⟨-, h⟩ := rm_split h
  obtain ⟨-, h⟩ := rm_split h
  obtain ⟨hrecv, h⟩ := rm_split h
  obtain ⟨hrid', h⟩ := rm_split h
  obtain ⟨-, h⟩ := rm_split h
  obtain ⟨-, h⟩ := rm_split h
  obtain ⟨hsig, h⟩ := rm_split h
  obtain ⟨hpk, h⟩ := rm_split h
  obtain ⟨hgp, h⟩ := rm_split h
  obtain ⟨-, h⟩ := rm_split h
  obtain ⟨-, h⟩ := rm_split h
  obtain ⟨-, h⟩ := rm_split h
  obtain ⟨-, hdep⟩ := rm_split h
  have hpl : r.signerPk.encode.length = 1 + r.signerPk.data.length := by
    simp [PublicKey.encode, u8, NearSpec.leN_length]
  simp only [u32_len, u128_len, hrid, hpl, List.length_cons, List.length_nil] at hrecv hrid' hsig hpk hgp hdep
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [pRecv] using hrecv
  · simpa only [pRid, pRecv] using hrid'
  · have : pSig r A = A + 4 + r.predecessorId.length + 4 + r.receiverId.length + 32 + 1 + 4 := by
      simp only [pSig, pRid, pRecv] <;> omega
    rw [this]; exact hsig
  · have : pPk r A = A + 4 + r.predecessorId.length + 4 + r.receiverId.length + 32 + 1 + 4 +
        r.signerId.length := by simp only [pPk, pSig, pRid, pRecv] <;> omega
    rw [this]; exact hpk
  · have : pGp r A = A + 4 + r.predecessorId.length + 4 + r.receiverId.length + 32 + 1 + 4 +
        r.signerId.length + (1 + r.signerPk.data.length) := by simp only [pGp, pPk, pSig, pRid, pRecv] <;> omega
    rw [this]; exact hgp
  · have : pGp r A + 29 = A + 4 + r.predecessorId.length + 4 + r.receiverId.length + 32 + 1 + 4 +
        r.signerId.length + (1 + r.signerPk.data.length) + 16 + 4 + 4 + 4 + 1 := by
      simp only [pGp, pPk, pSig, pRid, pRecv] <;> omega
    rw [this]; exact hdep

/-- Receipt-table entry fields as the program reads them. -/
structure RtMem (M0 : Nat → UInt8) (E : Nat) (r : Receipt) (A : Nat) : Prop where
  f8 : ArenaCore.Bytes.leToNat (readMem M0 (E + 8) 4) = pRecv r A
  f12 : ArenaCore.Bytes.leToNat (readMem M0 (E + 12) 4) = r.receiverId.length
  f16 : ArenaCore.Bytes.leToNat (readMem M0 (E + 16) 4) = pRid r A
  f20 : ArenaCore.Bytes.leToNat (readMem M0 (E + 20) 4) = pSig r A
  f24 : ArenaCore.Bytes.leToNat (readMem M0 (E + 24) 4) = r.signerId.length
  f28 : ArenaCore.Bytes.leToNat (readMem M0 (E + 28) 4) = pPk r A
  f32 : ArenaCore.Bytes.leToNat (readMem M0 (E + 32) 4) = pGp r A
  f36 : ArenaCore.Bytes.leToNat (readMem M0 (E + 36) 4) = pGp r A + 29

theorem rtMem_of {M0 : Nat → UInt8} {E A : Nat} {r : Receipt} (h : readMem M0 E 40 = rtBytes r A)
    (hb : pGp r A + 29 < 4294967296) : RtMem M0 E r A := by
  rw [rtBytes_eq] at h
  obtain ⟨-, h⟩ := rm_split' h (by simp)
  obtain ⟨-, h⟩ := rm_split' h (by simp)
  obtain ⟨h8, h⟩ := rm_split' h (by simp)
  obtain ⟨h12, h⟩ := rm_split' h (by simp)
  obtain ⟨h16, h⟩ := rm_split' h (by simp)
  obtain ⟨h20, h⟩ := rm_split' h (by simp)
  obtain ⟨h24, h⟩ := rm_split' h (by simp)
  obtain ⟨h28, h⟩ := rm_split' h (by simp)
  obtain ⟨h32, h36⟩ := rm_split' h (by simp)
  simp only [u32_len] at h8 h12 h16 h20 h24 h28 h32 h36
  have e1 : r.receiverId.length < 4294967296 := by simp only [pGp, pPk, pSig, pRid, pRecv] at hb; omega
  have e2 : r.signerId.length < 4294967296 := by simp only [pGp, pPk, pSig, pRid, pRecv] at hb; omega
  have e3 : pRecv r A < 4294967296 := by simp only [pGp, pPk, pSig, pRid] at hb; omega
  have e4 : pRid r A < 4294967296 := by simp only [pGp, pPk, pSig] at hb; omega
  have e5 : pSig r A < 4294967296 := by simp only [pGp, pPk] at hb; omega
  have e6 : pPk r A < 4294967296 := by simp only [pGp] at hb; omega
  have e7 : pGp r A < 4294967296 := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show E + 8 = E + 4 + 4 by omega, h8, leToNat_u32 e3]
  · rw [show E + 12 = E + 4 + 4 + 4 by omega, h12, leToNat_u32 e1]
  · rw [show E + 16 = E + 4 + 4 + 4 + 4 by omega, h16, leToNat_u32 e4]
  · rw [show E + 20 = E + 4 + 4 + 4 + 4 + 4 by omega, h20, leToNat_u32 e5]
  · rw [show E + 24 = E + 4 + 4 + 4 + 4 + 4 + 4 by omega, h24, leToNat_u32 e2]
  · rw [show E + 28 = E + 4 + 4 + 4 + 4 + 4 + 4 + 4 by omega, h28, leToNat_u32 e6]
  · rw [show E + 32 = E + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 by omega, h32, leToNat_u32 e7]
  · rw [show E + 36 = E + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 + 4 by omega, h36, leToNat_u32 hb]

theorem concatAll_append : ∀ (l1 l2 : List (List UInt8)), concatAll (l1 ++ l2) = concatAll l1 ++ concatAll l2
  | [], _ => rfl
  | a :: l1, l2 => by simp [concatAll, concatAll_append l1 l2]

/-- Receipt `i` sits at `PF + rOff rs i` in the intact receipts region. -/
theorem rcpt_at {cb pb : List UInt8} {rs : List Receipt} {R : Nat} {m : M} (h : RcptsMem cb pb rs R m)
    {i : Nat} (hi : i < rs.length) :
    readMem m.mem (PF + rOff rs i) rs[i].encode.length = rs[i].encode ∧
      rOff rs i + rs[i].encode.length ≤ R := by
  obtain ⟨hcat, -⟩ := readMany_decReceipt_some h.ok.dec
  have hs : rs = rs.take i ++ rs[i] :: rs.drop (i + 1) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  rw [hs, List.map_append, concatAll_append, List.map_cons, concatAll] at hcat
  have hro : rOff rs i = 4 + (concatAll ((rs.take i).map Receipt.encode)).length := rfl
  rw [hro]
  generalize concatAll ((rs.take i).map Receipt.encode) = C1 at hcat
  generalize concatAll ((rs.drop (i + 1)).map Receipt.encode) = C2 at hcat
  generalize rs[i].encode = E at hcat ⊢
  have hl := congrArg List.length hcat
  simp only [List.length_drop, List.length_append] at hl
  have h4 := h.ok.n4
  have hR := h.ok.Rle
  refine ⟨?_, by omega⟩
  rw [readMem_sub h.rcpts (4 + C1.length) E.length (by omega), List.drop_take]
  have : pb.drop (4 + C1.length) = E ++ (C2 ++ pb.drop R) := by
    rw [← List.drop_drop, hcat, List.append_assoc, List.drop_left, List.append_assoc]
  rw [this, List.take_take, List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]

/-! ## Arena layout -/

theorem preImg_ne_nil (nf : NF) (vlen : Nat) (z : List UInt8) (zs : List (List UInt8)) :
    preImg nf vlen z zs ≠ [] := by
  cases nf with
  | leaf k ref mm => simp [preImg]
  | ext k h mm => simp [preImg]
  | branch v ks mm =>
    rcases v with _ | _ | ⟨len, h⟩ <;> simp [preImg]

structure EntOk (pb : List UInt8) (e : Ent) : Prop where
  rst : PF ≤ e.rst
  rp : e.rst < e.pre
  pend : e.pre + e.preLen ≤ PF + pb.length
  plen : 1 ≤ e.preLen
  hv : hasVal e.nf = true → e.val = e.rst + 5 ∧ e.val + vlenAt pb e + 
    (match e.nf with | .branch _ _ _ => 2 | _ => 0) = e.pre

theorem entOk {pb : List UInt8} {A : List Ent} {K : List Nat} {start : Nat} (hw : ArenaWF pb A K start)
    {j : Nat} (hj : j < A.length) : EntOk pb A[j] := by
  obtain ⟨e, he, -, h1, h2, h3, ⟨z, zs, -, -, -, hp⟩, hv, -⟩ := hw.nodes j hj
  rw [List.getElem?_eq_getElem hj] at he
  cases he
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · rcases Nat.eq_zero_or_pos A[j].preLen with h0 | h0
    · rw [h0] at hp; simp [pseg] at hp; exact absurd hp (preImg_ne_nil _ _ _ _)
    · exact h0
  · intro hh
    rw [if_pos hh] at hv
    exact ⟨hv.1, hv.2.2.symm⟩

theorem getD_eq_get {A : List Ent} {j : Nat} (h : j < A.length) : A.getD j default = A[j] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem arena_mono {pb : List UInt8} {A : List Ent} {K : List Nat} {start : Nat} (hw : ArenaWF pb A K start) :
    ∀ (k j : Nat) (hjk : j < k) (hk : k < A.length),
      A[j].pre + A[j].preLen ≤ A[k].rst
  | 0, j, hjk, _ => absurd hjk (Nat.not_lt_zero _)
  | k + 1, j, hjk, hk => by
    have hc := hw.contig k hk
    rw [getD_eq_get (by omega), getD_eq_get hk] at hc
    rcases Nat.lt_or_ge j k with h | h
    · have := arena_mono hw k j h (by omega)
      have e := entOk hw (j := k) (by omega)
      have := e.rp
      omega
    · have : j = k := by omega
      subst this; omega

theorem rst_ge {pb : List UInt8} {A : List Ent} {K : List Nat} {R : Nat} (hw : ArenaWF pb A K (PF + R + 4))
    {j : Nat} (hj : j < A.length) : PF + R + 4 ≤ A[j].rst := by
  have hf := hw.first
  rw [getD_eq_get (by omega)] at hf
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h; omega
  · have := arena_mono hw j 0 h hj
    have := (entOk hw (j := 0) (by omega)).rp
    omega

/-! ## Scratch writes and the trie state -/

/-- Addresses the batch may overwrite (scratch, accumulator cells, outcome leaves, refund buffer). -/
def Scr (a : Nat) : Prop :=
  (512 ≤ a ∧ a < 2560) ∨ (3088 ≤ a ∧ a < 3120) ∨ (3124 ≤ a ∧ a < 3584) ∨ (19968 ≤ a ∧ a < 117000)

theorem rm_eq {m m' : M} {p n : Nat} (hm : ∀ a, p ≤ a → a < p + n → m'.mem a = m.mem a) :
    readMem m'.mem p n = readMem m.mem p n := readMem_congr (fun i hi => hm _ (by omega) (by omega))

theorem rcptsMem_mod {cb pb : List UInt8} {rs : List Receipt} {R : Nat} {m m' : M}
    (h : RcptsMem cb pb rs R m) (h14 : m'.regs 14 = m.regs 14) (h15 : m'.regs 15 = m.regs 15)
    (hm : ∀ a, (a < 117000 ∧ ¬ Scr a) ∨ (PF ≤ a ∧ a < PF + R) → m'.mem a = m.mem a) :
    RcptsMem cb pb rs R m' := by
  have hn := h.ok.n_max
  simp only [Params.maxBatch] at hn
  have k1 : m'.regs 15 = 1 := by rw [h15]; exact h.k1
  have k8 : m'.regs 14 = 8 := by rw [h14]; exact h.k8
  refine ⟨⟨⟨k1, k8, ?_⟩, ?_, h.shape⟩, h.ok, ?_, h.plen, ?_, ?_, ?_, ?_⟩
  · rw [rm_eq (fun a h1 h2 => hm a (.inl ⟨by omega, by simp only [Scr]; omega⟩))]; exact h.data
  · rw [rm_eq (fun a h1 h2 => hm a (.inl ⟨by simp only [CLM] at h1 h2; omega, by simp only [Scr, CLM] at *; omega⟩))]
    exact h.claim
  · rw [rm_eq (fun a h1 h2 => hm a (.inr ⟨h1, h2⟩))]; exact h.rcpts
  · simp only [rd32]; rw [rm_eq (fun a h1 h2 => hm a (.inl ⟨by simp only [C_PEND] at *; omega,
      by simp only [Scr, C_PEND] at *; omega⟩))]; exact h.pend
  · simp only [rd32]; rw [rm_eq (fun a h1 h2 => hm a (.inl ⟨by simp only [C_N] at *; omega,
      by simp only [Scr, C_N] at *; omega⟩))]; exact h.nC
  · simp only [rd32]; rw [rm_eq (fun a h1 h2 => hm a (.inl ⟨by simp only [C_REND] at *; omega,
      by simp only [Scr, C_REND] at *; omega⟩))]; exact h.rend
  · intro i hi
    rw [rm_eq (fun a h1 h2 => hm a (.inl ⟨by simp only [RT] at *; omega,
      by simp only [Scr, RT] at *; omega⟩))]; exact h.rt i hi

/-- General modification of the trie memory: the written set `W` avoids the
arena, child list and node count, and inside entry spans it only hits value regions,
whose new contents are `vals'`. -/
theorem trieMem_gen {pb : List UInt8} {A : List Ent} {K : List Nat} {start : Nat} {vals vals' : Nat → List UInt8}
    {m m' : M} (h : TrieMem pb A K vals m) (hw : ArenaWF pb A K start) (W : Nat → Prop)
    (hm : ∀ a, ¬ W a → m'.mem a = m.mem a) (hlow : ∀ a, W a → Scr a ∨ PF ≤ a)
    (hreg : ∀ j (hj : j < A.length) a, W a → A[j].rst ≤ a + 1 → a < A[j].pre + A[j].preLen →
      hasVal A[j].nf = true ∧ A[j].val ≤ a ∧ a < A[j].val + vlenAt pb A[j])
    (hv : ∀ j (hj : j < A.length), hasVal A[j].nf = true →
      readMem m'.mem A[j].val (vlenAt pb A[j]) = vals' j ∧ (vals' j).length = vlenAt pb A[j]) :
    TrieMem pb A K vals' m' := by
  have hlen := hw.len_le
  have hkl := h.klen
  simp only [NCAP] at hlen hkl
  have nW : ∀ a, a < PF → ¬ Scr a → m'.mem a = m.mem a := fun a h1 h2 => hm a (fun hW => by
    rcases hlow a hW with h3 | h3
    · exact h2 h3
    · exact absurd h3 (by omega))
  refine ⟨?_, ?_, h.krange, h.klen, ?_, hv, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨e1, e2, e3, e4, e5, e6⟩ := h.amem j hj
    simp only [rd32] at e1 e2 e3 e4 e5 e6
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp only [rd32] <;>
      (rw [rm_eq (fun a h1 h2 => nW a (by simp only [PF, AR] at *; omega) (by simp only [Scr, AR] at *; omega))];
       assumption)
  · intro i hi
    simp only [rd32]
    rw [rm_eq (fun a h1 h2 => nW a (by simp only [PF, KL] at *; omega) (by simp only [Scr, KL] at *; omega))]
    exact h.kmem i hi
  · simp only [rd32]
    rw [rm_eq (fun a h1 h2 => nW a (by simp only [PF, C_NODES] at *; omega)
      (by simp only [Scr, C_NODES] at *; omega))]
    exact h.nodes
  · intro j hj hh
    have eo := entOk hw hj
    obtain ⟨e1, e2⟩ := eo.hv hh
    rw [rm_eq (fun a h1 h2 => hm a (fun hW => by
      have := hreg j hj a hW (by omega) (by have := eo.plen; split at e2 <;> omega)
      omega))]
    exact h.lmem j hj hh
  · intro j hj
    have eo := entOk hw hj
    obtain ⟨z, zs, h1, h2, h3, h4⟩ := h.pmem j hj
    refine ⟨z, zs, h1, h2, h3, ?_⟩
    rw [rm_eq (fun a h5 h6 => hm a (fun hW => by
      have := hreg j hj a hW (by have := eo.rp; omega) h6
      have := eo.hv this.1
      split at this <;> omega))]
    exact h4
  · intro j hj
    have eo := entOk hw hj
    have hh := h.hmem j hj
    split
    · rename_i k hx mm hn
      rw [hn] at hh
      simp only at hh
      rw [rm_eq (fun a h5 h6 => hm a (fun hW => by
        have := hreg j hj a hW (by have := eo.rp; omega) (by have := eo.plen; have := eo.rp; omega)
        rw [hn] at this; simp [hasVal] at this))]
      exact hh
    · rename_i v ks mm hn
      rw [hn] at hh
      simp only at hh
      rw [rm_eq (fun a h5 h6 => hm a (fun hW => by
        have := hreg j hj a hW (by have := eo.rp; omega) (by have := eo.plen; have := eo.rp; omega)
        have := eo.hv this.1
        rw [hn] at this
        simp only at this
        omega))]
      exact hh
    · trivial

theorem trieSt_frame {cb pb : List UInt8} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat}
    {vals : Nat → List UInt8} {m m' : M} (h : TrieSt cb pb rs R A K vals m)
    (h14 : m'.regs 14 = m.regs 14) (h15 : m'.regs 15 = m.regs 15) (hm : ∀ a, ¬ Scr a → m'.mem a = m.mem a) :
    TrieSt cb pb rs R A K vals m' := by
  have hw := h.tok.wf
  refine ⟨rcptsMem_mod h.toRcptsMem h14 h15 (fun a ha => hm a (by
      rcases ha with ha | ha
      · exact ha.2
      · simp only [Scr, PF] at *; omega)), h.tok, ?_⟩
  refine trieMem_gen h.tmem hw Scr hm (fun a ha => .inl ha) ?_ ?_
  · intro j hj a ha h1 h2
    have := (entOk hw hj).rst
    simp only [Scr, PF] at *; omega
  · intro j hj hh
    have eo := entOk hw hj
    obtain ⟨e1, e2⟩ := eo.hv hh
    rw [rm_eq (fun a h1 h2 => hm a (by have := eo.rst; simp only [Scr, PF] at *; omega))]
    exact h.tmem.vmem j hj hh

theorem trieSt_upd {cb pb : List UInt8} {rs : List Receipt} {R : Nat} {A : List Ent} {K : List Nat}
    {vals : Nat → List UInt8} {m m' : M} (h : TrieSt cb pb rs R A K vals m) {f : Nat} (hf : f < A.length)
    (hhv : hasVal A[f].nf = true) (h72 : vlenAt pb A[f] = 72)
    (h14 : m'.regs 14 = m.regs 14) (h15 : m'.regs 15 = m.regs 15)
    (hm : ∀ a, ¬ Scr a → ¬ (A[f].val ≤ a ∧ a < A[f].val + 16) → m'.mem a = m.mem a) {nv : List UInt8}
    (hnv : readMem m'.mem A[f].val 72 = nv) :
    TrieSt cb pb rs R A K (updVals vals f nv) m' := by
  have hw := h.tok.wf
  have eof := entOk hw hf
  obtain ⟨ev, ep⟩ := eof.hv hhv
  rw [h72] at ep
  have hrf := rst_ge hw hf
  have hdisj : ∀ j (hj : j < A.length), j ≠ f → ∀ a, A[j].rst ≤ a + 1 → a < A[j].pre + A[j].preLen →
      a < A[f].val ∨ A[f].val + 72 ≤ a := by
    intro j hj hne a h1 h2
    rcases Nat.lt_or_ge j f with hl | hl
    · have := arena_mono hw f j hl hf; omega
    · have := arena_mono hw j f (by omega) hj
      have := eof.plen
      split at ep <;> omega
  refine ⟨rcptsMem_mod h.toRcptsMem h14 h15 (fun a ha => hm a (by
      rcases ha with ha | ha
      · exact ha.2
      · simp only [Scr, PF] at *; omega) (by rcases ha with ha | ha <;> simp only [PF] at * <;> omega)),
    h.tok, ?_⟩
  refine trieMem_gen h.tmem hw (fun a => Scr a ∨ (A[f].val ≤ a ∧ a < A[f].val + 16))
    (fun a ha => hm a (fun h' => ha (.inl h')) (fun h' => ha (.inr h'))) ?_ ?_ ?_
  · intro a ha
    rcases ha with ha | ha
    · exact .inl ha
    · exact .inr (by have := eof.rst; omega)
  · intro j hj a ha h1 h2
    rcases ha with ha | ha
    · have := (entOk hw hj).rst
      simp only [Scr, PF] at *; omega
    · by_cases hjf : j = f
      · subst hjf; exact ⟨hhv, ha.1, by omega⟩
      · have := hdisj j hj hjf a h1 h2; omega
  · intro j hj hh
    by_cases hjf : j = f
    · subst hjf
      simp only [updVals, ↓reduceIte, h72]
      exact ⟨hnv, by rw [← hnv]; simp⟩
    · have eo := entOk hw hj
      obtain ⟨e1, e2⟩ := eo.hv hh
      simp only [updVals, hjf, ↓reduceIte]
      rw [rm_eq (fun a h1 h2 => hm a (by have := eo.rst; simp only [Scr, PF] at *; omega) (by
        have := hdisj j hj hjf a (by omega) (by split at e2 <;> omega)
        omega))]
      exact h.tmem.vmem j hj hh

/-! ## Macro rules in continuation form -/

section
variable {inp : Inputs}

theorem wp_addLE {m : M} {Q : M → Prop} {n : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (hn : m.regs 4 = n) (hc0 : m.regs 5 ≤ 1) (hba : m.regs 1 + n ≤ 13844304) (hbb : m.regs 2 + n ≤ 13844304)
    (hbd : m.regs 3 + n ≤ 13844304) (hal : Alias (m.regs 3) (m.regs 1) n) (hbl : Alias (m.regs 3) (m.regs 2) n)
    (h : ∀ m', m'.mem = writeMem m.mem (m.regs 3) n
        (ArenaCore.Bytes.leN n (sumPref m.mem (m.regs 1) (m.regs 2) (m.regs 5) n)) →
      m'.regs 5 = sumPref m.mem (m.regs 1) (m.regs 2) (m.regs 5) n / 256 ^ n →
      Frame [1, 2, 3, 4, 5, 6, 7] m m' → Q m') :
    wp P inp addLE m Q :=
  wp_of_spec (addLE_spec ⟨hk1, hk8⟩ hn hc0 (by simpa using hba) (by simpa using hbb) (by simpa using hbd)
    (by simp) hal hbl) (fun m' _ ⟨h1, h2, h3, _⟩ => h m' h1 h2 h3)

theorem twp_addLE {m : M} {Q : M → Nat → Prop} {n : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (hn : m.regs 4 = n) (hc0 : m.regs 5 ≤ 1) (hba : m.regs 1 + n ≤ 13844304) (hbb : m.regs 2 + n ≤ 13844304)
    (hbd : m.regs 3 + n ≤ 13844304) (hal : Alias (m.regs 3) (m.regs 1) n) (hbl : Alias (m.regs 3) (m.regs 2) n)
    (h : ∀ m' c, m'.mem = writeMem m.mem (m.regs 3) n
        (ArenaCore.Bytes.leN n (sumPref m.mem (m.regs 1) (m.regs 2) (m.regs 5) n)) →
      m'.regs 5 = sumPref m.mem (m.regs 1) (m.regs 2) (m.regs 5) n / 256 ^ n →
      Frame [1, 2, 3, 4, 5, 6, 7] m m' → c ≤ 12 * n + 1 → Q m' c) :
    twp P inp addLE m Q :=
  twp_of_spec (addLE_spec ⟨hk1, hk8⟩ hn hc0 (by simpa using hba) (by simpa using hbb) (by simpa using hbd)
    (by simp) hal hbl) (fun m' c ⟨h1, h2, h3, h4⟩ => h m' c h1 h2 h3 h4)

theorem wp_subLE {m : M} {Q : M → Prop} {n : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (hn : m.regs 4 = n) (hc0 : m.regs 5 ≤ 1) (hba : m.regs 1 + n ≤ 13844304) (hbb : m.regs 2 + n ≤ 13844304)
    (hbd : m.regs 3 + n ≤ 13844304) (hal : Alias (m.regs 3) (m.regs 1) n) (hbl : Alias (m.regs 3) (m.regs 2) n)
    (h : ∀ m', m'.mem = writeMem m.mem (m.regs 3) n (ArenaCore.Bytes.leN n
        ((ArenaCore.Bytes.leToNat (readMem m.mem (m.regs 1) n) + 256 ^ n -
          ArenaCore.Bytes.leToNat (readMem m.mem (m.regs 2) n) - m.regs 5) % 256 ^ n)) →
      m'.regs 5 = (if ArenaCore.Bytes.leToNat (readMem m.mem (m.regs 1) n) <
          ArenaCore.Bytes.leToNat (readMem m.mem (m.regs 2) n) + m.regs 5 then 1 else 0) →
      Frame [1, 2, 3, 4, 5, 6, 7] m m' → Q m') :
    wp P inp subLE m Q :=
  wp_of_spec (subLE_spec ⟨hk1, hk8⟩ hn hc0 (by simpa using hba) (by simpa using hbb) (by simpa using hbd)
    (by simp) hal hbl) (fun m' _ ⟨h1, h2, _, _, _, _, h3, _⟩ => h m' h1 h2 h3)

theorem twp_subLE {m : M} {Q : M → Nat → Prop} {n : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (hn : m.regs 4 = n) (hc0 : m.regs 5 ≤ 1) (hba : m.regs 1 + n ≤ 13844304) (hbb : m.regs 2 + n ≤ 13844304)
    (hbd : m.regs 3 + n ≤ 13844304) (hal : Alias (m.regs 3) (m.regs 1) n) (hbl : Alias (m.regs 3) (m.regs 2) n)
    (h : ∀ m' c, m'.mem = writeMem m.mem (m.regs 3) n (ArenaCore.Bytes.leN n
        ((ArenaCore.Bytes.leToNat (readMem m.mem (m.regs 1) n) + 256 ^ n -
          ArenaCore.Bytes.leToNat (readMem m.mem (m.regs 2) n) - m.regs 5) % 256 ^ n)) →
      m'.regs 5 = (if ArenaCore.Bytes.leToNat (readMem m.mem (m.regs 1) n) <
          ArenaCore.Bytes.leToNat (readMem m.mem (m.regs 2) n) + m.regs 5 then 1 else 0) →
      Frame [1, 2, 3, 4, 5, 6, 7] m m' → c ≤ 14 * n + 1 → Q m' c) :
    twp P inp subLE m Q :=
  twp_of_spec (subLE_spec ⟨hk1, hk8⟩ hn hc0 (by simpa using hba) (by simpa using hbb) (by simpa using hbd)
    (by simp) hal hbl) (fun m' c ⟨h1, h2, _, _, _, _, h3, h4⟩ => h m' c h1 h2 h3 h4)

theorem wp_mulLE {m : M} {Q : M → Prop} {n : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (hn : m.regs 4 = n) (hK : m.regs 2 < 281474976710656) (hc0 : m.regs 5 < 281474976710656)
    (hba : m.regs 1 + n ≤ 13844304) (hbd : m.regs 3 + n ≤ 13844304) (hal : Alias (m.regs 3) (m.regs 1) n)
    (h : ∀ m', m'.mem = writeMem m.mem (m.regs 3) n (ArenaCore.Bytes.leN n
        (ArenaCore.Bytes.leToNat (readMem m.mem (m.regs 1) n) * m.regs 2 + m.regs 5)) →
      m'.regs 5 = (ArenaCore.Bytes.leToNat (readMem m.mem (m.regs 1) n) * m.regs 2 + m.regs 5) / 256 ^ n →
      m'.regs 3 = m.regs 3 + n → Frame [1, 3, 4, 5, 6] m m' → Q m') :
    wp P inp mulLE m Q :=
  wp_of_spec (mulLE_spec ⟨hk1, hk8⟩ hn hK hc0 (by simpa using hba) (by simpa using hbd) (by simp) hal)
    (fun m' _ ⟨h1, h2, _, h3, _, _, h4, _⟩ => h m' h1 h2 h3 h4)

theorem twp_mulLE {m : M} {Q : M → Nat → Prop} {n : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (hn : m.regs 4 = n) (hK : m.regs 2 < 281474976710656) (hc0 : m.regs 5 < 281474976710656)
    (hba : m.regs 1 + n ≤ 13844304) (hbd : m.regs 3 + n ≤ 13844304) (hal : Alias (m.regs 3) (m.regs 1) n)
    (h : ∀ m' c, m'.mem = writeMem m.mem (m.regs 3) n (ArenaCore.Bytes.leN n
        (ArenaCore.Bytes.leToNat (readMem m.mem (m.regs 1) n) * m.regs 2 + m.regs 5)) →
      m'.regs 5 = (ArenaCore.Bytes.leToNat (readMem m.mem (m.regs 1) n) * m.regs 2 + m.regs 5) / 256 ^ n →
      m'.regs 3 = m.regs 3 + n → Frame [1, 3, 4, 5, 6] m m' → c ≤ 10 * n + 1 → Q m' c) :
    twp P inp mulLE m Q :=
  twp_of_spec (mulLE_spec ⟨hk1, hk8⟩ hn hK hc0 (by simpa using hba) (by simpa using hbd) (by simp) hal)
    (fun m' c ⟨h1, h2, _, h3, _, _, h4, h5⟩ => h m' c h1 h2 h3 h4 h5)

/-- `stLE 3 5 n 11 12 13`. -/
theorem wp_stLE {m : M} {Q : M → Prop} {n : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (hb : m.regs 3 + n ≤ 13844304) (hv : m.regs 5 < 18446744073709551616)
    (h : ∀ m', m'.mem = writeMem m.mem (m.regs 3) n (ArenaCore.Bytes.leN n (m.regs 5)) →
      Frame [11, 12, 13] m m' → Q m') :
    wp P inp (stLE 3 5 n 11 12 13) m Q :=
  wp_of_spec (stLE_spec (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ⟨hk1, hk8⟩ (by simpa using hb) (by simp) hv) (fun m' _ ⟨h1, h2, _⟩ => h m' h1 h2)

theorem twp_stLE {m : M} {Q : M → Nat → Prop} {n : Nat} (hk1 : m.regs 15 = 1) (hk8 : m.regs 14 = 8)
    (hb : m.regs 3 + n ≤ 13844304) (hv : m.regs 5 < 18446744073709551616)
    (h : ∀ m' c, m'.mem = writeMem m.mem (m.regs 3) n (ArenaCore.Bytes.leN n (m.regs 5)) →
      Frame [11, 12, 13] m m' → c ≤ 6 * n + 4 → Q m' c) :
    twp P inp (stLE 3 5 n 11 12 13) m Q :=
  twp_of_spec (stLE_spec (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) ⟨hk1, hk8⟩ (by simpa using hb) (by simp) hv) (fun m' c ⟨h1, h2, h3⟩ => h m' c h1 h2 h3)

/-- `memcpy 1 2 3 4`. -/
theorem wp_memcpy {m : M} {Q : M → Prop} {n : Nat} (hk1 : m.regs 15 = 1) (hn : m.regs 3 = n)
    (hbd : m.regs 1 + n ≤ 13844304) (hbs : m.regs 2 + n ≤ 13844304)
    (hov : m.regs 1 ≤ m.regs 2 ∨ m.regs 2 + n ≤ m.regs 1)
    (h : ∀ m', m'.mem = writeMem m.mem (m.regs 1) n (readMem m.mem (m.regs 2) n) →
      m'.regs 1 = m.regs 1 + n → Frame [1, 2, 3, 4] m m' → Q m') :
    wp P inp (memcpy 1 2 3 4) m Q :=
  wp_of_spec (memcpy_spec (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hk1 hn (by simpa using hbd) (by simpa using hbs) (by simp) hov) (fun m' _ ⟨h1, h2, _, _, h3, _⟩ => h m' h1 h2 h3)

theorem twp_memcpy {m : M} {Q : M → Nat → Prop} {n : Nat} (hk1 : m.regs 15 = 1) (hn : m.regs 3 = n)
    (hbd : m.regs 1 + n ≤ 13844304) (hbs : m.regs 2 + n ≤ 13844304)
    (hov : m.regs 1 ≤ m.regs 2 ∨ m.regs 2 + n ≤ m.regs 1)
    (h : ∀ m' c, m'.mem = writeMem m.mem (m.regs 1) n (readMem m.mem (m.regs 2) n) →
      m'.regs 1 = m.regs 1 + n → Frame [1, 2, 3, 4] m m' → c ≤ 7 * n + 1 → Q m' c) :
    twp P inp (memcpy 1 2 3 4) m Q :=
  twp_of_spec (memcpy_spec (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    hk1 hn (by simpa using hbd) (by simpa using hbs) (by simp) hov)
    (fun m' c ⟨h1, h2, _, _, h3, h4⟩ => h m' c h1 h2 h3 h4)

end

/-! ## Little-endian arrays in memory -/

theorem leN_add : ∀ (a b X : Nat),
    ArenaCore.Bytes.leN (a + b) X = ArenaCore.Bytes.leN a X ++ ArenaCore.Bytes.leN b (X / 256 ^ a)
  | 0, b, X => by simp [ArenaCore.Bytes.leN]
  | a + 1, b, X => by
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [ArenaCore.Bytes.leN, leN_add a b (X / 256), List.cons_append, Nat.div_div_eq_div_mul,
      Nat.pow_succ, Nat.mul_comm (256 ^ a) 256]

theorem writeMem_append (M0 : Nat → UInt8) (d a b : Nat) (L1 L2 : List UInt8) (h1 : L1.length = a) :
    writeMem (writeMem M0 d a L1) (d + a) b L2 = writeMem M0 d (a + b) (L1 ++ L2) := by
  funext j
  simp only [writeMem]
  by_cases hA : d + a ≤ j ∧ j < d + a + b
  · rw [if_pos hA, if_pos ⟨by omega, by omega⟩]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega), h1]
    congr 2; omega
  · rw [if_neg hA]
    by_cases hB : d ≤ j ∧ j < d + a
    · rw [if_pos hB, if_pos ⟨hB.1, by omega⟩]
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    · rw [if_neg hB, if_neg (by omega)]

theorem writeMem_leN_split (M0 : Nat → UInt8) (d a b X : Nat) :
    writeMem (writeMem M0 d a (ArenaCore.Bytes.leN a X)) (d + a) b (ArenaCore.Bytes.leN b (X / 256 ^ a)) =
      writeMem M0 d (a + b) (ArenaCore.Bytes.leN (a + b) X) := by
  rw [writeMem_append _ _ _ _ _ _ (ArenaCore.Bytes.leN_length _ _), leN_add]

theorem rm_wm_self (M0 : Nat → UInt8) (d n : Nat) (L : List UInt8) (h : L.length = n) :
    readMem (writeMem M0 d n L) d n = L := by
  rw [readMem_writeMem_self _ _ _ _ (by omega), List.take_of_length_le (by omega)]

theorem rm_wm_in (M0 : Nat → UInt8) (d n : Nat) (L : List UInt8) (h : L.length = n) (o k : Nat)
    (hk : o + k ≤ n) : readMem (writeMem M0 d n L) (d + o) k = (L.drop o).take k := by
  rw [readMem_writeMem_sub _ _ _ _ _ _ (by omega) (by omega) (by omega)]
  congr 2; omega

theorem rm_wm_out (M0 : Nat → UInt8) (d n : Nat) (L : List UInt8) (a k : Nat) (h : a + k ≤ d ∨ d + n ≤ a) :
    readMem (writeMem M0 d n L) a k = readMem M0 a k := readMem_writeMem_disjoint _ _ _ _ _ _ h

theorem leN_take (n k X : Nat) (h : k ≤ n) :
    (ArenaCore.Bytes.leN n X).take k = ArenaCore.Bytes.leN k X := by
  have := leN_add k (n - k) X
  rw [show k + (n - k) = n by omega] at this
  rw [this, List.take_left' (ArenaCore.Bytes.leN_length _ _)]

theorem leToNat_leN' {w x : Nat} (h : x < 256 ^ w) : ArenaCore.Bytes.leToNat (ArenaCore.Bytes.leN w x) = x :=
  leToNat_leN w x h

theorem leN_inj {n x y : Nat} (hx : x < 256 ^ n) (hy : y < 256 ^ n)
    (h : ArenaCore.Bytes.leN n x = ArenaCore.Bytes.leN n y) : x = y := by
  rw [← leToNat_leN' hx, ← leToNat_leN' hy, h]

theorem leToNat_lt' (M0 : Nat → UInt8) (a n : Nat) : ArenaCore.Bytes.leToNat (readMem M0 a n) < 256 ^ n :=
  leToNat_readMem_lt M0 a n

theorem and10' (a b : Prop) [Decidable a] [Decidable b] :
    BinOp.and.eval (if a then 1 else 0) (if b then 1 else 0) = if a ∧ b then 1 else 0 := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb] <;> rfl

end ReexecNpai
