import ZkFormal.Near.Link.Statements

/-!
# ZkFormal.Near.Link.Bus — generic bus facts

* `ofNat_inj`, `toFp_inj` — `Fp.ofNat` is injective below `P`;
* `cnt_pos` — a positive count means a message with that image is in the list;
* `LinkHyp.balance` — on buses without SHA traffic, sends and receives have equal
  counts, so every received message has a sent preimage and vice versa;
* `nearSends_*` / `nearRecvs_*` — the NEAR traffic of each bus.
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

set_option linter.unusedSimpArgs false

namespace Link

theorem ofNat_inj {x y : Nat} (hx : x < P) (hy : y < P) (h : Fp.ofNat x = Fp.ofNat y) : x = y := by
  have := congrArg Fp.toNat h
  rwa [Fp.toNat_ofNat, Fp.toNat_ofNat, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at this

theorem ofNat_eq_iff {x y : Nat} : Fp.ofNat x = Fp.ofNat y ↔ x % P = y % P := by
  constructor
  · intro h; have := congrArg Fp.toNat h; rwa [Fp.toNat_ofNat, Fp.toNat_ofNat] at this
  · intro h; apply Fp.ext; rw [Fp.toNat_ofNat, Fp.toNat_ofNat, h]

/-- All components are canonical. -/
def Canon (m : Msg) : Prop := ∀ x ∈ m, x < P

theorem toFp_inj : ∀ {a b : Msg}, Canon a → Canon b → a.toFp = b.toFp → a = b
  | [], [], _, _, _ => rfl
  | [], _ :: _, _, _, h => by simp [Msg.toFp] at h
  | _ :: _, [], _, _, h => by simp [Msg.toFp] at h
  | x :: a, y :: b, ha, hb, h => by
    simp only [Msg.toFp, List.map_cons, List.cons.injEq] at h
    have hxy := ofNat_inj (ha x (by simp)) (hb y (by simp)) h.1
    have := toFp_inj (a := a) (b := b) (fun z hz => ha z (by simp [hz]))
      (fun z hz => hb z (by simp [hz])) h.2
    rw [hxy, this]

theorem cnt_pos {l : List Msg} {m : List Fp} : 0 < cnt l m ↔ ∃ x ∈ l, x.toFp = m := by
  unfold cnt; rw [List.count_pos_iff, List.mem_map]

theorem cnt_pos_of_mem {l : List Msg} {x : Msg} (h : x ∈ l) : 0 < cnt l x.toFp :=
  cnt_pos.mpr ⟨x, h, rfl⟩

theorem toFp_length (m : Msg) : m.toFp.length = m.length := List.length_map _

section Hyp
variable {c : WfClaim} {vs : List NodeS} {ws : List WalkV} {rs : RcptVs} {as : List AcctV}
  {mv : MrkV} {ids : List (Nat × List Nat)} {shaS shaR : Nat → List Fp → Nat}
  (h : LinkHyp c vs ws rs as mv ids shaS shaR)
include h

/-- Balance on a bus without SHA traffic. -/
theorem balance {b : Nat} (h1 : b ≠ B_BYTES) (h2 : b ≠ B_DIGEST) (m : List Fp) :
    cnt (nearSends (publicOf c) vs ws rs as mv ids b) m =
      cnt (nearRecvs (publicOf c) vs ws rs as mv ids b) m := by
  have := h.bal b m
  rw [h.sha.sends_only_digest b m h2, h.sha.recvs_only_bytes b m h1] at this
  omega

theorem recv_sent {b : Nat} (h1 : b ≠ B_BYTES) (h2 : b ≠ B_DIGEST) {x : Msg}
    (hx : x ∈ nearRecvs (publicOf c) vs ws rs as mv ids b) :
    ∃ y ∈ nearSends (publicOf c) vs ws rs as mv ids b, y.toFp = x.toFp := by
  have := cnt_pos_of_mem hx
  rw [← balance h h1 h2] at this
  exact cnt_pos.mp this

theorem sent_recv {b : Nat} (h1 : b ≠ B_BYTES) (h2 : b ≠ B_DIGEST) {x : Msg}
    (hx : x ∈ nearSends (publicOf c) vs ws rs as mv ids b) :
    ∃ y ∈ nearRecvs (publicOf c) vs ws rs as mv ids b, y.toFp = x.toFp := by
  have := cnt_pos_of_mem hx
  rw [balance h h1 h2] at this
  exact cnt_pos.mp this

/-- The images of sends and receives are permutations of each other. -/
theorem perm {b : Nat} (h1 : b ≠ B_BYTES) (h2 : b ≠ B_DIGEST) :
    ((nearSends (publicOf c) vs ws rs as mv ids b).map Msg.toFp).Perm
      ((nearRecvs (publicOf c) vs ws rs as mv ids b).map Msg.toFp) :=
  List.perm_iff_count.mpr (balance h h1 h2)

end Hyp

/-! ## Traffic per bus -/

section Traffic
variable (pub : List Fp) (vs : List NodeS) (ws : List WalkV) (rs : RcptVs) (as : List AcctV)
  (mv : MrkV) (ids : List (Nat × List Nat))

theorem nearSends_bytes : nearSends pub vs ws rs as mv ids B_BYTES =
    nodeSends vs B_BYTES ++ rcptSends pub rs B_BYTES ++ acctSends as B_BYTES ++
      mrkSends pub mv B_BYTES := by
  simp [nearSends, nodeTraffic, walkTraffic, rcptTraffic, acctTraffic, mrkTraffic, sortTraffic,
    walkSends, B_BYTES, B_EDGE, B_FINAL]

theorem nearRecvs_digest : nearRecvs pub vs ws rs as mv ids B_DIGEST =
    nodeRecvs vs pub B_DIGEST ++ rcptRecvs pub rs B_DIGEST ++ mrkRecvs pub mv B_DIGEST := by
  simp [nearRecvs, nodeTraffic, walkTraffic, rcptTraffic, acctTraffic, mrkTraffic, sortTraffic,
    walkRecvs, acctRecvs, B_DIGEST, B_EDGE, B_KEYNIB, B_MEM, B_RIDS]

theorem nearSends_digest : nearSends pub vs ws rs as mv ids B_DIGEST = [] := by
  simp [nearSends, nodeTraffic, walkTraffic, rcptTraffic, acctTraffic, mrkTraffic, sortTraffic,
    nodeSends, walkSends, rcptSends, acctSends, mrkSends, B_DIGEST, B_BYTES, B_PARENT, B_EDGE,
    B_FINAL, B_KEYNIB, B_MEM, B_RIDS, B_MPOS, B_VSLOT]

theorem nearRecvs_bytes : nearRecvs pub vs ws rs as mv ids B_BYTES = [] := by
  simp [nearRecvs, nodeTraffic, walkTraffic, rcptTraffic, acctTraffic, mrkTraffic, sortTraffic,
    nodeRecvs, walkRecvs, rcptRecvs, acctRecvs, mrkRecvs, B_DIGEST, B_BYTES, B_PARENT, B_EDGE,
    B_FINAL, B_KEYNIB, B_MEM, B_RIDS, B_MPOS, B_VSLOT]

theorem nearSends_parent : nearSends pub vs ws rs as mv ids B_PARENT = nodeSends vs B_PARENT := by
  simp [nearSends, nodeTraffic, walkTraffic, rcptTraffic, acctTraffic, mrkTraffic, sortTraffic,
    walkSends, rcptSends, acctSends, mrkSends, B_BYTES, B_PARENT, B_EDGE, B_FINAL, B_KEYNIB,
    B_MEM, B_RIDS, B_MPOS, B_VSLOT]

theorem nearRecvs_parent : nearRecvs pub vs ws rs as mv ids B_PARENT = nodeRecvs vs pub B_PARENT := by
  simp [nearRecvs, nodeTraffic, walkTraffic, rcptTraffic, acctTraffic, mrkTraffic, sortTraffic,
    walkRecvs, rcptRecvs, acctRecvs, mrkRecvs, B_DIGEST, B_PARENT, B_EDGE, B_FINAL, B_KEYNIB,
    B_MEM, B_RIDS, B_MPOS, B_VSLOT]

theorem nearSends_vslot : nearSends pub vs ws rs as mv ids B_VSLOT = acctSends as B_VSLOT := by
  simp [nearSends, nodeTraffic, walkTraffic, rcptTraffic, acctTraffic, mrkTraffic, sortTraffic,
    nodeSends, walkSends, rcptSends, mrkSends, B_BYTES, B_PARENT, B_EDGE, B_FINAL, B_KEYNIB,
    B_MEM, B_RIDS, B_MPOS, B_VSLOT]

theorem nearRecvs_vslot : nearRecvs pub vs ws rs as mv ids B_VSLOT = nodeRecvs vs pub B_VSLOT := by
  simp [nearRecvs, nodeTraffic, walkTraffic, rcptTraffic, acctTraffic, mrkTraffic, sortTraffic,
    walkRecvs, rcptRecvs, acctRecvs, mrkRecvs, B_DIGEST, B_PARENT, B_EDGE, B_FINAL, B_KEYNIB,
    B_MEM, B_RIDS, B_MPOS, B_VSLOT]

theorem nearSends_edge : nearSends pub vs ws rs as mv ids B_EDGE =
    nodeSends vs B_EDGE ++ walkSends ws B_EDGE := by
  simp [nearSends, nodeTraffic, walkTraffic, rcptTraffic, acctTraffic, mrkTraffic, sortTraffic,
    rcptSends, acctSends, mrkSends, B_BYTES, B_PARENT, B_EDGE, B_FINAL, B_KEYNIB,
    B_MEM, B_RIDS, B_MPOS, B_VSLOT]

theorem nearRecvs_edge : nearRecvs pub vs ws rs as mv ids B_EDGE =
    nodeRecvs vs pub B_EDGE ++ walkRecvs ws B_EDGE := by
  simp [nearRecvs, nodeTraffic, walkTraffic, rcptTraffic, acctTraffic, mrkTraffic, sortTraffic,
    rcptRecvs, acctRecvs, mrkRecvs, B_DIGEST, B_PARENT, B_EDGE, B_FINAL, B_KEYNIB,
    B_MEM, B_RIDS, B_MPOS, B_VSLOT]

theorem nearSends_keynib : nearSends pub vs ws rs as mv ids B_KEYNIB = rcptSends pub rs B_KEYNIB := by
  simp [nearSends, nodeTraffic, walkTraffic, rcptTraffic, acctTraffic, mrkTraffic, sortTraffic,
    nodeSends, walkSends, acctSends, mrkSends, B_BYTES, B_PARENT, B_EDGE, B_FINAL, B_KEYNIB,
    B_MEM, B_RIDS, B_MPOS, B_VSLOT]

theorem nearRecvs_keynib : nearRecvs pub vs ws rs as mv ids B_KEYNIB = walkRecvs ws B_KEYNIB := by
  simp [nearRecvs, nodeTraffic, walkTraffic, rcptTraffic, acctTraffic, mrkTraffic, sortTraffic,
    nodeRecvs, rcptRecvs, acctRecvs, mrkRecvs, B_DIGEST, B_PARENT, B_EDGE, B_FINAL, B_KEYNIB,
    B_MEM, B_RIDS, B_MPOS, B_VSLOT]

theorem nearSends_final : nearSends pub vs ws rs as mv ids B_FINAL = walkSends ws B_FINAL := by
  simp [nearSends, nodeTraffic, walkTraffic, rcptTraffic, acctTraffic, mrkTraffic, sortTraffic,
    nodeSends, rcptSends, acctSends, mrkSends, B_BYTES, B_PARENT, B_EDGE, B_FINAL, B_KEYNIB,
    B_MEM, B_RIDS, B_MPOS, B_VSLOT]

theorem nearRecvs_final : nearRecvs pub vs ws rs as mv ids B_FINAL = rcptRecvs pub rs B_FINAL := by
  simp [nearRecvs, nodeTraffic, walkTraffic, rcptTraffic, acctTraffic, mrkTraffic, sortTraffic,
    nodeRecvs, walkRecvs, acctRecvs, mrkRecvs, B_DIGEST, B_PARENT, B_EDGE, B_FINAL, B_KEYNIB,
    B_MEM, B_RIDS, B_MPOS, B_VSLOT]

theorem nearSends_mem : nearSends pub vs ws rs as mv ids B_MEM =
    rcptSends pub rs B_MEM ++ acctSends as B_MEM := by
  simp [nearSends, nodeTraffic, walkTraffic, rcptTraffic, acctTraffic, mrkTraffic, sortTraffic,
    nodeSends, walkSends, mrkSends, B_BYTES, B_PARENT, B_EDGE, B_FINAL, B_KEYNIB,
    B_MEM, B_RIDS, B_MPOS, B_VSLOT]

theorem nearRecvs_mem : nearRecvs pub vs ws rs as mv ids B_MEM =
    rcptRecvs pub rs B_MEM ++ acctRecvs as B_MEM := by
  simp [nearRecvs, nodeTraffic, walkTraffic, rcptTraffic, acctTraffic, mrkTraffic, sortTraffic,
    nodeRecvs, walkRecvs, mrkRecvs, B_DIGEST, B_PARENT, B_EDGE, B_FINAL, B_KEYNIB,
    B_MEM, B_RIDS, B_MPOS, B_VSLOT]

theorem nearSends_rids : nearSends pub vs ws rs as mv ids B_RIDS = rcptSends pub rs B_RIDS := by
  simp [nearSends, nodeTraffic, walkTraffic, rcptTraffic, acctTraffic, mrkTraffic, sortTraffic,
    nodeSends, walkSends, acctSends, mrkSends, B_BYTES, B_PARENT, B_EDGE, B_FINAL, B_KEYNIB,
    B_MEM, B_RIDS, B_MPOS, B_VSLOT]

theorem nearRecvs_rids : nearRecvs pub vs ws rs as mv ids B_RIDS = (sortTraffic ids).recvs B_RIDS := by
  simp [nearRecvs, nodeTraffic, walkTraffic, rcptTraffic, acctTraffic, mrkTraffic,
    nodeRecvs, walkRecvs, rcptRecvs, acctRecvs, mrkRecvs, B_DIGEST, B_PARENT, B_EDGE, B_FINAL,
    B_KEYNIB, B_MEM, B_RIDS, B_MPOS, B_VSLOT]

theorem nearSends_mpos : nearSends pub vs ws rs as mv ids B_MPOS =
    rcptSends pub rs B_MPOS ++ mrkSends pub mv B_MPOS := by
  simp [nearSends, nodeTraffic, walkTraffic, rcptTraffic, acctTraffic, mrkTraffic, sortTraffic,
    nodeSends, walkSends, acctSends, B_BYTES, B_PARENT, B_EDGE, B_FINAL, B_KEYNIB,
    B_MEM, B_RIDS, B_MPOS, B_VSLOT]

theorem nearRecvs_mpos : nearRecvs pub vs ws rs as mv ids B_MPOS = mrkRecvs pub mv B_MPOS := by
  simp [nearRecvs, nodeTraffic, walkTraffic, rcptTraffic, acctTraffic, mrkTraffic, sortTraffic,
    nodeRecvs, walkRecvs, rcptRecvs, acctRecvs, B_DIGEST, B_PARENT, B_EDGE, B_FINAL, B_KEYNIB,
    B_MEM, B_RIDS, B_MPOS, B_VSLOT]

end Traffic

end Link

end ZkFormal.Near
