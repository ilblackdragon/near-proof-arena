import ZkFormal.V3.EncodeWitness
import ZkFormal.NearV3.Rcpt.Candidates.ParserConsumption

namespace ZkFormal.NearV3.Assembly
open NearSpec NearSpecV3 Sched
open Rcpt.Candidates

/-- Successful byte-vector decoding accounts for its complete canonical encoding. -/
theorem pBytes_size {w : String} {bs a rest : Bytes}
    (h : pBytes w bs = .ok (a, rest)) :
    (borshBytes a).length + rest.length = bs.length := by
  rw [(ReexecV3D0.pBytes_inv h).1, List.length_append]

theorem pAccountId_size {w : String} {bs a rest : Bytes}
    (h : pAccountId w bs = .ok (a, rest)) :
    (borshBytes a).length + rest.length = bs.length := by
  unfold pAccountId at h
  obtain ⟨⟨a', r⟩, hp, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · cases h; exact pBytes_size hp
  · cases h

theorem pTake_size {n : Nat} {w : String} {bs a rest : Bytes}
    (h : pTake n w bs = .ok (a, rest)) :
    a.length = n ∧ bs.length = n + rest.length := by
  constructor
  · unfold pTake NearSpecV3.lift takeT at h
    split at h
    · rename_i v hv
      cases h
      obtain ⟨pre, h1, h2, h3⟩ := ReexecV3D0.takeAcc_split hv
      simp at h3
      subst h3
      exact h2
    · cases h
  · exact pTake_consumption h

theorem pPublicKey_size {w : String} {bs rest : Bytes} {a : PublicKey}
    (h : pPublicKey w bs = .ok (a, rest)) :
    a.encode.length + rest.length = bs.length := by
  unfold pPublicKey at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    cases h
    simp only [PublicKey.encode, List.length_append, u8, leN, List.length_cons,
      List.length_nil]
    have ht := @pTake_size
    have hu := @pU8_consumption
    grind only

theorem pHash_size {w : String} {bs a rest : Bytes}
    (h : pHash w bs = .ok (a, rest)) :
    a.length = 32 ∧ bs.length = 32 + rest.length := by
  constructor
  · unfold pHash NearSpecV3.lift at h
    split at h
    · rename_i v hv
      cases h
      exact (ReexecV3D0.takeN_split hv).2
    · cases h
  · exact pHash_consumption h

/-- D0 receipt parsing consumes exactly the canonical receipt encoding length. -/
theorem pReceipt_size {bs rest : Bytes} {a : Receipt}
    (h : pReceipt bs = .ok (a, rest)) :
    a.encode.length + rest.length = bs.length := by
  unfold pReceipt at h
  repeat' (first
    | (obtain ⟨_, _, h⟩ := bind_ok h)
    | (split at h)
    | (dsimp only at h))
  all_goals try (cases h; done)
  all_goals try (exfalso; exact throw_ne (by assumption))
  all_goals
    cases h
    simp only [Receipt.encode, List.length_append, List.length_cons, List.length_nil,
      u128, u32, leN]
    have ha := @pAccountId_size
    have hp := @pPublicKey_size
    have hh := @pHash_size
    have hu := @pLE_consumption
    simp only [pU8, pU32, pU128, readU8, readU32, readU128] at *
    grind only

theorem pMany_size {α : Type} (p : NearSpecV3.P α) (enc : α → Bytes)
    (hp : ∀ bs a rest, p bs = .ok (a, rest) → (enc a).length + rest.length = bs.length) :
    ∀ n bs xs rest, pMany p n bs = .ok (xs, rest) →
      (concatAll (xs.map enc)).length + rest.length = bs.length := by
  intro n
  induction n with
  | zero => intro bs xs rest h; cases h; simp [concatAll]
  | succ n ih =>
    intro bs xs rest h
    unfold pMany at h
    obtain ⟨⟨a, tail⟩, ha, h⟩ := bind_ok h
    obtain ⟨⟨ys, last⟩, hy, h⟩ := bind_ok h
    cases h
    have h1 := hp _ _ _ ha
    have h2 := ih _ _ _ hy
    simp only [List.map_cons, concatAll, List.length_append] at *
    omega

theorem pVec_size {α : Type} (p : NearSpecV3.P α) (enc : α → Bytes)
    (hp : ∀ bs a rest, p bs = .ok (a, rest) → (enc a).length + rest.length = bs.length)
    {w : String} {bs rest : Bytes} {xs : List α} (h : pVec w p bs = .ok (xs, rest)) :
    (encList enc xs).length + rest.length = bs.length := by
  unfold pVec at h
  obtain ⟨⟨n, tail⟩, hn, h⟩ := bind_ok h
  have h1 := pMany_size p enc hp n _ _ _ h
  have h2 := pLE_consumption hn
  simp only [encList, List.length_append, u32, leN, List.length_cons, List.length_nil]
  omega

theorem pPathItem_size {bs rest : Bytes} {a : Bytes × Nat}
    (h : pPathItem bs = .ok (a, rest)) :
    (V3.encodePathItem a).length + rest.length = bs.length := by
  unfold pPathItem at h
  obtain ⟨⟨hash, tail⟩, hh, h⟩ := bind_ok h
  obtain ⟨⟨d, last⟩, hd, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · obtain ⟨_, he, _⟩ := bind_ok h; cases he
  · cases h
    have h1 := pHash_size hh
    have h2 := pU8_consumption hd
    simp only [V3.encodePathItem, List.length_append, u8, leN, List.length_cons,
      List.length_nil]
    omega

theorem pEntry_size {bs rest : Bytes} {a : ProofEntry}
    (h : pEntry bs = .ok (a, rest)) :
    (V3.encodeEntry a).length + rest.length = bs.length := by
  unfold pEntry at h
  obtain ⟨⟨key, r1⟩, hk, h⟩ := bind_ok h
  obtain ⟨⟨rs, r2⟩, hrs, h⟩ := bind_ok h
  obtain ⟨⟨f, r3⟩, hf, h⟩ := bind_ok h
  obtain ⟨⟨t, r4⟩, ht, h⟩ := bind_ok h
  obtain ⟨⟨path, r5⟩, hp, h⟩ := bind_ok h
  cases h
  have h1 := pHash_size hk
  have h2 := pVec_size _ Receipt.encode (fun _ _ _ => pReceipt_size) hrs
  have h3 := pLE_consumption hf
  have h4 := pLE_consumption ht
  have h5 := pVec_size _ V3.encodePathItem (fun _ _ _ => pPathItem_size) hp
  simp only [V3.encodeEntry, List.length_append, u64, leN, List.length_cons, List.length_nil]
  omega

theorem pTransition_size {bs rest : Bytes} {a : Transition}
    (h : pTransition bs = .ok (a, rest)) :
    (V3.encodeTransition a).length + rest.length = bs.length := by
  rw [(ReexecV3D0.pTransition_inv h).1, List.length_append]
  rfl

/-- Canonical headers replace a parsed signature by the shortest accepted signature. -/
theorem pChunkHeader_size {bs rest ib : Bytes} {ci : ChunkInner}
    (h : pChunkHeader bs = .ok ((ib, ci), rest)) :
    1 + ib.length + 8 + 65 + rest.length ≤ bs.length := by
  unfold pChunkHeader at h
  obtain ⟨⟨tg, m1⟩, g1, h⟩ := bind_ok h
  dsimp only at h
  split at h
  · cases h
  obtain ⟨⟨ci', m2⟩, g2, h⟩ := bind_ok h
  dsimp only at h
  obtain ⟨⟨hv, m3⟩, g3, h⟩ := bind_ok h
  dsimp only at h
  obtain ⟨⟨sg, m4⟩, g4, h⟩ := bind_ok h
  simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨⟨hib, hci⟩, hr⟩ := h
  subst m4
  obtain ⟨I, eI, _⟩ := ReexecV3D0.cfk ReexecV3D0.cf_pChunkInner g2
  have hi : I = ib := by rw [← hib, eI, ReexecV3D0.consumed_app]
  have h1 := pU8_consumption g1
  have h3 := pLE_consumption g3
  obtain ⟨S, eS, hS⟩ := ReexecV3D0.pSignature_split g4
  have h2 := congrArg List.length eI
  have h4 := congrArg List.length eS
  simp only [List.length_append, hi] at h2 h4
  omega

/-- Canonical re-encoding never enlarges an actually decoded witness. No round-trip,
canonical-input, signature-shape, or additional size premise is required. -/
theorem decodeStateWitness_encodeSW_size {sw : Bytes} {s : StateWitness}
    (hs : decodeStateWitness sw = .ok s) : (V3.encodeSW s).length ≤ sw.length := by
  unfold decodeStateWitness at hs
  dsimp only at hs
  split at hs
  · cases hs
  rename_i hmax
  obtain ⟨⟨t, b1⟩, h1, hs⟩ := bind_ok hs
  dsimp only at hs
  split at hs
  · cases hs
  rename_i ht
  have ht1 : t = 1 := by simpa using ht
  subst ht1
  obtain ⟨⟨eid, b2⟩, h2, hs⟩ := bind_ok hs
  dsimp only at hs
  obtain ⟨⟨⟨ib, ci⟩, b3⟩, h3, hs⟩ := bind_ok hs
  dsimp only at hs
  obtain ⟨⟨main, b4⟩, h4, hs⟩ := bind_ok hs
  dsimp only at hs
  obtain ⟨⟨entries, b5⟩, h5, hs⟩ := bind_ok hs
  dsimp only at hs
  obtain ⟨⟨arh, b6⟩, h6, hs⟩ := bind_ok hs
  dsimp only at hs
  obtain ⟨⟨ntx, b7⟩, h7, hs⟩ := bind_ok hs
  dsimp only at hs
  split at hs
  · cases hs
  rename_i hntx
  have hntx0 : ntx = 0 := by simpa using hntx
  subst hntx0
  obtain ⟨⟨impl, b8⟩, h8, hs⟩ := bind_ok hs
  dsimp only at hs
  obtain ⟨⟨nnew, b9⟩, h9, hs⟩ := bind_ok hs
  dsimp only at hs
  split at hs
  · cases hs
  rename_i hnn
  have hnn0 : nnew = 0 := by simpa using hnn
  subst hnn0
  split at hs
  · cases hs
  rename_i hemp
  have hb9 : b9 = [] := by simpa using hemp
  subst hb9
  simp only [pure, Except.pure, Except.ok.injEq] at hs
  subst hs
  have z1 := pU8_consumption h1
  have z2 := pHash_size h2
  have z3 := pChunkHeader_size h3
  have z4 := pTransition_size h4
  have z5 := pVec_size _ V3.encodeEntry (fun _ _ _ => pEntry_size) h5
  have z6 := pHash_size h6
  have z7 := pLE_consumption h7
  have z8 := pVec_size _ V3.encodeTransition (fun _ _ _ => pTransition_size) h8
  have z9 := pLE_consumption h9
  simp only [V3.encodeSW, List.length_append, u8, u32, leN,
    ReexecV3D0.zeros8, ReexecV3D0.sig0, List.length_cons, List.length_nil,
    List.length_replicate]
  simp only [List.length_nil] at z9
  omega

end ZkFormal.NearV3.Assembly
