import M5T1.MsgRowSpan
import ZkFormal.Sha.Sound

/-!
# M5T1.MsgRowDg — a `DG` row's digest is SHA-256 of its `MSG` message (F-2)

**`dg_digest`**: on a `Holds (fullAir tape xtape)` trace (with `SchtFixed`, public tapes that send
nothing on `SCH`, `RNG`, `SHA_BYTES`, `SHA_DIGEST`, `MLEN`, and `MIdBound`), an active `DG` row
(`act = 1`) of message id `128·qf + 96 + mt` and length `len` has a message span `r0..r1` of `MSG`
with the same id, `r1 + 1 − r0 = len` bytes, hashed (`hsh = 1`), and its 32 digest columns are
`sha256` of the span's bytes.

Chain: `DG`'s `SHA_DIGEST` receive is the SHA table's digest send (`sha_digest_contract_closed`,
lane L5: a digest row of the SHA table, its message `m`, `dg = sha256 m`, and every byte `m[i]` is
received on `SHA_BYTES` as `(id, i, m[i])`); each such receive is an `MSG` row's send, which lies in
a message span (`span_of`) of that id; by `span_start_unique` (the ids are distinct under
`MIdBound`) it is one span, and `j` is the position in it, so the bytes are the span's. `DG`'s
`MLEN` receive is the span's end row's send `(id, j + 1)`, so `|m| = len` = the span's length
(`|m| ≤ 64 · 2^22 < p`).

**Finding (id wrap).** `MSG`'s `dm` constraint makes consecutive message ids increase by
`1 + dm`, `dm < 2^24`, only **modulo `p`**: with about `p / 2^24 ≈ 120` messages the ids can come
back to a value already used, and two messages with the same id would let the SHA table hash a mix
of their bytes (its byte receives can be matched by either). `MIdBound` (every active row's id
`< 2^30`, e.g. families `mf < 2^23 − 1`) excludes the wrap; it must come from the demands (`MBEG`
from `RX`) or a range check on `mf`.
-/

namespace M5T1.MsgRow

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound M5T1 M5T1.Bus ZkFormal.Sha.View

/-! ## Senders -/

theorem noSend_digest : ∀ t, t ≠ 0 → NoSend (m5t1Air.tables.getD t default) B_SHA_DIGEST = true := by
  intro t hne
  obtain _ | _ | _ | _ | _ | _ | _ | _ | _ | t := t
  all_goals first | decide +kernel | exact absurd rfl hne | exact getD_big (by omega)

theorem noSend_bytes : ∀ t, t ≠ 3 → NoSend (m5t1Air.tables.getD t default) B_SHA_BYTES = true := by
  intro t hne
  obtain _ | _ | _ | _ | _ | _ | _ | _ | _ | t := t
  all_goals first | decide +kernel | exact absurd rfl hne | exact getD_big (by omega)

theorem noSend_mlen : ∀ t, t ≠ 3 → NoSend (m5t1Air.tables.getD t default) B_MLEN = true := by
  intro t hne
  obtain _ | _ | _ | _ | _ | _ | _ | _ | _ | t := t
  all_goals first | decide +kernel | exact absurd rfl hne | exact getD_big (by omega)

/-- Every interaction of `is` sending on `b` is `X`. -/
def OnlySend (is : List Interaction) (b : Nat) (X : Interaction) : Bool :=
  is.all fun i => !(i.bus == b && i.send) || decide (i = X)

theorem onlySend_spec {is : List Interaction} {b : Nat} {X : Interaction} (h : OnlySend is b X = true)
    {i : Interaction} (hi : i ∈ is) (hb : i.bus = b) (hs : i.send = true) : i = X := by
  have := List.all_eq_true.1 h i hi
  simp only [hb, hs, beq_self_eq_true, Bool.and_self, Bool.not_true, Bool.false_or,
    decide_eq_true_eq] at this
  exact this

def mlenI : Interaction := snd B_MLEN (Msg.c "endm") [Msg.mId, Msg.c "j" + 1]
def bytesI : Interaction := snd B_SHA_BYTES (Msg.c "hsh") [Msg.mId, Msg.c "j", Msg.c "b"]

theorem only_mlen : OnlySend Msg.interactions B_MLEN mlenI = true := by decide +kernel
theorem only_bytes : OnlySend Msg.interactions B_SHA_BYTES bytesI = true := by decide +kernel

theorem sha_digest_i {i : Interaction}
    (hi : i ∈ ZkFormal.Sha.Table.interactions B_SHA_BYTES B_SHA_DIGEST) (hs : i.send = true) :
    i = (ZkFormal.Sha.Table.interactions B_SHA_BYTES B_SHA_DIGEST)[16]! := by
  simp only [ZkFormal.Sha.Table.interactions, List.mem_append, List.mem_map, List.mem_range,
    List.mem_singleton] at hi
  rcases hi with ⟨q, -, rfl⟩ | rfl
  · cases hs
  · rfl

theorem sha_bytes_i (q : Nat) (hq : q < 16) :
    (ZkFormal.Sha.Table.interactions B_SHA_BYTES B_SHA_DIGEST)[q]! ∈
      ZkFormal.Sha.Table.interactions B_SHA_BYTES B_SHA_DIGEST ∧
    ((ZkFormal.Sha.Table.interactions B_SHA_BYTES B_SHA_DIGEST)[q]!).bus = B_SHA_BYTES ∧
    ((ZkFormal.Sha.Table.interactions B_SHA_BYTES B_SHA_DIGEST)[q]!).send = false ∧
    ((ZkFormal.Sha.Table.interactions B_SHA_BYTES B_SHA_DIGEST)[q]!).mult =
      [Expr.col (ZkFormal.Sha.Layout.colF q) false] := by
  have hl : q < (ZkFormal.Sha.Table.interactions B_SHA_BYTES B_SHA_DIGEST).length := by
    simp [ZkFormal.Sha.Table.interactions]; omega
  have he : (ZkFormal.Sha.Table.interactions B_SHA_BYTES B_SHA_DIGEST)[q]! =
      (ZkFormal.Sha.Table.interactions B_SHA_BYTES B_SHA_DIGEST)[q] := by
    simp [getElem!_def, List.getElem?_eq_getElem hl]
  rw [he]
  refine ⟨List.getElem_mem hl, ?_⟩
  simp [ZkFormal.Sha.Table.interactions, List.getElem_append, hq, ZkFormal.Sha.Table.E.c]

theorem multNat_pos {i : Interaction} {b : Expr} (hm : i.mult = [b]) {tr : Trace Fp} {t r : Nat}
    {pub : List Fp} (h : 0 < i.multNat tr t r pub) : b.eval tr t r pub = 1 := by
  unfold Interaction.multNat at h
  rw [hm] at h
  simp only [Interaction.multNat.go] at h
  by_cases hb : b.eval tr t r pub = 1
  · exact hb
  · simp [hb] at h

/-! ## The SHA message length -/

theorem chainStarts_len (tr : Trace Fp) (t : Nat) : ∀ f d, (chainStarts tr t f d).length ≤ f := by
  intro f
  induction f with
  | zero => intro d; simp [chainStarts]
  | succ f ih =>
    intro d
    simp only [chainStarts]
    split
    · simp only [List.length_append, List.length_singleton]; have := ih (d - 17); omega
    · simp

theorem flatMap_len {α β : Type} (l : List α) (f : α → List β) (k : Nat) (h : ∀ a ∈ l, (f a).length ≤ k) :
    (l.flatMap f).length ≤ k * l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.flatMap_cons, List.length_append, List.length_cons, Nat.mul_succ]
    have := h a (List.mem_cons_self ..)
    have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    omega

theorem digests_len {tr : Trace Fp} {t : Nat} {m dg : ArenaCore.Bytes} (h : (m, dg) ∈ digests tr t) :
    m.length ≤ 64 * tr.height t := by
  simp only [digests, List.mem_map, List.mem_filter] at h
  obtain ⟨d, -, hd⟩ := h
  simp only [Prod.mk.injEq] at hd
  rw [← hd.1, List.length_map]
  unfold msgOf chainOf
  refine Nat.le_trans (flatMap_len _ _ 64 fun s _ => ?_) (Nat.mul_le_mul_left _ (chainStarts_len _ _ _ _))
  unfold blockData
  exact Nat.le_trans (List.length_filterMap_le _ _) (by simp)

/-! ## `dg_digest` -/

section
variable {tape xtape : List (Nat × Bool × List Nat)} {tr : Trace Fp} {pub : List Fp}

theorem dg_lt : 4 < (fullAir tape xtape).tables.length := by rw [fullAir_len]; decide
theorem sha_lt : 0 < (fullAir tape xtape).tables.length := by rw [fullAir_len]; decide

theorem toNat_ofNat' (n : Nat) : (Fp.ofNat n).toNat = n % 2013265921 := Fp.toNat_ofNat n

/-- Schema fact: padding entries are not hashed. -/
def padNoHash : Bool := schema.all fun g => g.kind != K_PAD || !(mflags g.mt).1
theorem padNoHash_true : padNoHash = true := by decide +kernel

theorem act_of_hsh (RH : RowHyps tr pub) {x : Nat} (hx : x < tr.height 3) (h : V tr pub x "hsh" = 1) :
    V tr pub x "act" = 1 := by
  obtain ⟨g, hg, hd⟩ := RH.desc x hx
  have := List.all_eq_true.1 padNoHash_true g hg
  rw [hd.act]
  rw [hd.hsh] at h
  have h1 := b2n_eq_one h
  rw [h1] at this
  simp only [Bool.not_true, Bool.or_false, bne_iff_ne, ne_eq] at this
  simp [b2n, this]

/-- **A `DG` row's digest is SHA-256 of its message.** -/
theorem dg_digest (H : Holds (fullAir tape xtape) pub tr) (hS : SchtFixed tr)
    (hs1 : NoSendOn B_SCH tape) (hs2 : NoSendOn B_SCH xtape) (hr1 : NoRng tape) (hr2 : NoRng xtape)
    (hb1 : NoSendOn B_SHA_BYTES tape) (hb2 : NoSendOn B_SHA_BYTES xtape)
    (hd1 : NoSendOn B_SHA_DIGEST tape) (hd2 : NoSendOn B_SHA_DIGEST xtape)
    (hl1 : NoSendOn B_MLEN tape) (hl2 : NoSendOn B_MLEN xtape) (hB : MIdBound tr pub)
    {r : Nat} (hr : r < tr.height 4) (hact : ev tr 4 r pub (Dg.c "act") = 1) :
    ∃ r0 r1, IsSpan tr pub r0 r1 ∧ MI tr pub r0 = ev tr 4 r pub Dg.mId ∧
      r1 + 1 - r0 = ev tr 4 r pub (Dg.c "len") ∧ V tr pub r0 "hsh" = 1 ∧
      (List.range 32).map (fun k => ev tr 4 r pub (Dg.c "d" k)) =
        (ArenaCore.sha256 ((rowBytes tr pub r0 (r1 + 1 - r0)).map UInt8.ofNat)).map UInt8.toNat := by
  have RH := rowHyps_of H hS hs1 hs2 hr1 hr2
  have hHt := msg_height H
  have hg : (Dg.c "act").eval tr 4 r pub = 1 := eval_of_ev (e := Dg.c "act") hact (by decide)
  -- the digest: a SHA digest row
  have hiD : rcv B_SHA_DIGEST (Dg.c "act") ([Dg.mId, Dg.c "len"] ++ (List.range 32).map fun k => Dg.c "d" k) ∈
      ((fullAir tape xtape).tables[4]'dg_lt).interactions :=
    List.mem_append_left _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))
  obtain ⟨t', d, ht', hd, i', hi', hb', hs', hmv, hm'⟩ :=
    recv_sender H dg_lt hr hiD rfl (by rw [multNat_one hg]; decide)
  have h0 := sender_idx noSend_digest hd1 hd2 ht' hi' hb' hs'
  subst h0
  have hi16 := sha_digest_i hi' hs'
  subst hi16
  have hdm : tr.cell 0 d ZkFormal.Sha.Layout.colDmult = 1 :=
    multNat_pos (b := Expr.col ZkFormal.Sha.Layout.colDmult false) rfl hm'
  have hL := ZkFormal.Sha.shaLocal_of_holds H (t := 0) sha_lt rfl
  obtain ⟨m, dg, hmem, hdg, hmsg, hbytes⟩ :=
    ZkFormal.Sha.sha_digest_contract_closed hL B_SHA_BYTES B_SHA_DIGEST hd hdm
  rw [hmsg] at hmv
  simp only [Interaction.msgVal, rcv, List.map_append, List.map_cons, List.map_nil, List.map_map,
    List.cons_append, List.nil_append, List.cons.injEq] at hmv
  obtain ⟨hId, hLen, hDg⟩ := hmv
  -- `|m| < p`
  have hSh : tr.height 0 ≤ 2 ^ 22 := by
    have h := (H.logBound 0 sha_lt).2
    have h8 : ((fullAir tape xtape).tables[0]'sha_lt).maxLog = 22 := rfl
    rw [h8] at h
    exact Nat.pow_le_pow_right (by decide) h
  have hmlen : m.length ≤ 2 ^ 28 := by
    have := digests_len hmem; omega
  -- the length: an `MSG` end row
  have hiL : rcv B_MLEN (Dg.c "act") [Dg.mId, Dg.c "len"] ∈ ((fullAir tape xtape).tables[4]'dg_lt).interactions :=
    List.mem_append_left _ (List.mem_cons_self ..)
  obtain ⟨t2, y, ht2, hy, i2, hi2, hb2', hs2', hmv2, hm2⟩ :=
    recv_sender H dg_lt hr hiL rfl (by rw [multNat_one hg]; decide)
  have h3 := sender_idx noSend_mlen hl1 hl2 ht2 hi2 hb2' hs2'
  subst h3
  have hi2' := onlySend_spec only_mlen hi2 hb2' hs2'
  subst hi2'
  have hey : V tr pub y "endm" = 1 := by
    have := multNat_pos (b := Msg.c "endm") rfl hm2
    show ((Msg.c "endm").eval tr 3 y pub).toNat = 1
    rw [this]; rfl
  simp only [Interaction.msgVal, mlenI, snd, rcv, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmv2
  obtain ⟨hIdY, hLenY⟩ := hmv2
  have hAy := c7 H hy hey
  obtain ⟨r0, r1, hsp, hy0, hy1⟩ := span_of H RH hy hAy
  have hyr1 : y = r1 := by
    by_cases h : y < r1
    · have := hsp.mid y hy0 h; rw [hey] at this; exact absurd this (by decide)
    · omega
  subst hyr1
  have hl := hsp.lt
  have hle := hsp.le
  have hjy : V tr pub y "j" = y - r0 := by
    have := j_span H hsp (y - r0) (by omega); rwa [Nat.add_sub_cancel' hle] at this
  -- the numbers
  have hlenN : ev tr 4 r pub (Dg.c "len") = y - r0 + 1 := by
    have := congrArg Fp.toNat hLenY
    change ev tr 3 y pub (Msg.c "j" + 1) = ev tr 4 r pub (Dg.c "len") at this
    rw [ev_hadd, ev_one'] at this
    have h' : (V tr pub y "j" + 1) % 2013265921 = y - r0 + 1 := by rw [hjy]; exact Nat.mod_eq_of_lt (by omega)
    unfold V at h'; omega
  have hmL : m.length = y - r0 + 1 := by
    have := congrArg Fp.toNat hLen
    rw [toNat_ofNat'] at this
    change m.length % 2013265921 = ev tr 4 r pub (Dg.c "len") at this
    rw [Nat.mod_eq_of_lt (by omega)] at this; omega
  have hMIy : MI tr pub y = ev tr 4 r pub Dg.mId := congrArg Fp.toNat hIdY
  have hMI0 : MI tr pub r0 = ev tr 4 r pub Dg.mId := by rw [← mId_span' H hsp hle (Nat.le_refl _)]; exact hMIy
  have hIdd : (tr.cell 0 d ZkFormal.Sha.Layout.colId).toNat = MI tr pub r0 := by
    rw [hMI0]; exact congrArg Fp.toNat hId
  -- the bytes
  have hbyte : ∀ i, i < m.length → V tr pub (r0 + i) "b" = (m[i]!).toNat ∧ V tr pub (r0 + i) "hsh" = 1 := by
    intro i hi
    obtain ⟨r', hr', q, hq, hfq, hmq⟩ := hbytes i hi
    obtain ⟨hmemq, hbq, hsq, hmultq⟩ := sha_bytes_i q hq
    have hmq1 : 0 < ((ZkFormal.Sha.Table.interactions B_SHA_BYTES B_SHA_DIGEST)[q]!).multNat tr 0 r' pub := by
      unfold Interaction.multNat; rw [hmultq]
      simp only [Interaction.multNat.go]
      have : (Expr.col (ZkFormal.Sha.Layout.colF q) false).eval tr 0 r' pub = 1 := hfq
      rw [if_pos this]; decide
    obtain ⟨t3, x, ht3, hx, i3, hi3, hb3, hs3, hmv3, hm3⟩ := recv_sender H sha_lt hr' hmemq hsq hmq1
    have h4 := sender_idx noSend_bytes hb1 hb2 ht3 hi3 (hb3.trans hbq) hs3
    subst h4
    have hi3' := onlySend_spec only_bytes hi3 (hb3.trans hbq) hs3
    subst hi3'
    rw [hmq] at hmv3
    simp only [Interaction.msgVal, bytesI, snd, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hmv3
    obtain ⟨hIx, hjx, hbx⟩ := hmv3
    have hhx : V tr pub x "hsh" = 1 := by
      have := multNat_pos (b := Msg.c "hsh") rfl hm3
      show ((Msg.c "hsh").eval tr 3 x pub).toNat = 1
      rw [this]; rfl
    have hAx := act_of_hsh RH hx hhx
    obtain ⟨a0, a1, hspa, hx0, hx1⟩ := span_of H RH hx hAx
    have hMIx : MI tr pub x = MI tr pub r0 := by
      rw [← hIdd]; exact congrArg Fp.toNat hIx
    have hMIa : MI tr pub a0 = MI tr pub r0 := by rw [← mId_span' H hspa hx0 hx1]; exact hMIx
    obtain ⟨rfl, rfl⟩ := span_start_unique H hB RH hr1 hr2 hspa hsp hMIa
    have hjx' : V tr pub x "j" = x - a0 := by
      have := j_span H hspa (x - a0) (by omega); rwa [Nat.add_sub_cancel' hx0] at this
    have hi' : x - a0 = i := by
      have := congrArg Fp.toNat hjx
      rw [toNat_ofNat'] at this
      change V tr pub x "j" = i % 2013265921 at this
      rw [hjx', Nat.mod_eq_of_lt (by omega)] at this; exact this
    have hxe : a0 + i = x := by omega
    rw [hxe]
    refine ⟨?_, hhx⟩
    have := congrArg Fp.toNat hbx
    rw [toNat_ofNat'] at this
    change V tr pub x "b" = (m[i]!).toNat % 2013265921 at this
    rw [this]; exact Nat.mod_eq_of_lt (Nat.lt_trans (UInt8.toNat_lt _) (by decide))
  have hrb : (rowBytes tr pub r0 (y + 1 - r0)).map UInt8.ofNat = m := by
    apply List.ext_getElem
    · simp [rowBytes_length]; omega
    · intro i h1 h2
      simp only [rowBytes, List.getElem_map, List.getElem_range]
      rw [(hbyte i h2).1]
      have : m[i]! = m[i] := by simp [getElem!_def, List.getElem?_eq_getElem h2]
      rw [this]; simp
  refine ⟨r0, y, hsp, hMI0, by rw [hlenN]; omega, by have := (hbyte 0 (by omega)).2; simpa using this, ?_⟩
  rw [hrb, ← hdg]
  have := congrArg (List.map Fp.toNat) hDg
  simp only [List.map_map] at this
  have e1 : (Fp.toNat ∘ fun x : UInt8 => Fp.ofNat x.toNat) = UInt8.toNat := by
    funext x; simp only [Function.comp, toNat_ofNat']
    exact Nat.mod_eq_of_lt (Nat.lt_trans (UInt8.toNat_lt _) (by decide))
  rw [e1] at this
  rw [this]; rfl
end

#print axioms dg_digest

end M5T1.MsgRow
