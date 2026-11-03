import StateM5a.RowFacts

/-!
# StateM5a.VerBus — the `VER` bus of the AIR: who publishes, what is read

Field level, for the decoded version store (`VerStore`):

* `ver_senders`: every message sent on `VER` is a `BR` or an `SN` row's publication (no other
  table of the Lean AIR sends on `VER`; the extra tables do not, a premise);
* `br_ver_snd`: a `BR` row publishes part `p < 17` of its old record (bits `vm`, ref flag `0`,
  ref `ho`) or of its new record (bits `vmn`, ref flag `nref`, ref `hn`); `sn_ver_tag`: an `SN`
  publication carries the tag `VT_SN`;
* `br_ver_rcv`: a `BR` row with `gold − gsha = 1` receives part `p` of its old record (ref flag
  `oref`, ref `ho`), so that message was sent by a publisher.
-/

namespace StateM5a.VerBus

open ZkFormal.Air ZkFormal.Algebra ZkFormal.Sha.Sound StateM5a.Bus StateM5a.DecodeBus StateM5a.Traffic
open StateM5a.DecodeWalk StateM5a.DecodeM5a StateM5a.KeyDecode

set_option maxRecDepth 100000

/-- `BR` old / new record parts and reader parts (`Br.rec` with the row's arguments). -/
def brOldParts : List (List Expr) :=
  Br.rec 0 (pack2 fun b => Br.c "ho" b) (fun i => Br.c "f" i) (fun i => Br.c "isn" i) Br.ch (Br.c "hasv")
    (fun t => Br.c "vl" t) (fun t => Br.c "vh" t) Br.M
def brNewParts : List (List Expr) :=
  Br.rec (Br.c "nref") (pack2 fun b => Br.c "hn" b) (fun i => Br.c "nf" i) Br.nisn Br.newch (Br.c "nhv")
    (fun t => Br.c "nvl" t) (fun t => Br.c "nvh" t) Br.NM
def brRcvParts : List (List Expr) :=
  Br.rec (Br.c "oref") (pack2 fun b => Br.c "ho" b) (fun i => Br.c "f" i) (fun i => Br.c "isn" i) Br.ch
    (Br.c "hasv") (fun t => Br.c "vl" t) (fun t => Br.c "vh" t) Br.M

theorem br_ver_filter : Br.interactions.filter (fun i => decide (i.bus = B_VER ∧ i.send = true)) =
    brOldParts.map (fun m => sndBits B_VER (Br.bitsOf "vm") m) ++
      brNewParts.map (fun m => sndBits B_VER (Br.bitsOf "vmn") m) := by
  simp only [brOldParts, brNewParts, Br.rec]; filt
  all_goals (repeat rw [List.filter_eq_self.2 (fun _ _ => rfl)])

theorem br_ver_rfilter : Br.interactions.filter (fun i => decide (i.bus = B_VER ∧ i.send = false)) =
    brRcvParts.map (fun m => rcv B_VER (Br.gold - Br.c "gsha") m) := by
  simp only [brRcvParts, Br.rec]; filt
  all_goals (repeat rw [List.filter_eq_self.2 (fun _ _ => rfl)])

theorem sn_ver_head : ∀ i ∈ Sn.interactions, i.bus = B_VER → i.send = true → i.msg.head? = some (K VT_SN) := by
  intro i hi hb hs
  have : i ∈ Sn.interactions.filter (fun i => decide (i.bus = B_VER ∧ i.send = true)) :=
    List.mem_filter.2 ⟨hi, by simp [hb, hs]⟩
  have e : Sn.interactions.filter (fun i => decide (i.bus = B_VER ∧ i.send = true)) =
      (Sn.rec 0 (pack2 fun b => Sn.c "ho" b) (Sn.c "xf") (fun t => Sn.c "x" t) Sn.M).map
        (fun m => sndBits B_VER (Sn.bitsOf "vm") m) ++
      (Sn.rec (Sn.c "nref") (pack2 fun b => Sn.c "hn" b) (Sn.c "nxf") (fun t => Sn.c "nx" t) Sn.NM).map
        (fun m => sndBits B_VER (Sn.bitsOf "vmn") m) := by filt
  rw [e] at this
  simp only [List.mem_append, List.mem_map, Sn.rec, List.mem_cons, List.mem_nil_iff, or_false] at this
  rcases this with ⟨m, hm, rfl⟩ | ⟨m, hm, rfl⟩ <;> rcases hm with rfl | rfl | rfl <;> rfl

/-- The other tables of the Lean AIR do not send on `VER`. -/
theorem ver_nosend (D : Nat) : ∀ t, t < 12 → t ≠ 2 → t ≠ 3 →
    sendsOn ((m5aAir D).tables[t]!).interactions B_VER = false := by
  intro t ht h2 h3
  rcases (by omega : t = 0 ∨ t = 1 ∨ t = 4 ∨ t = 5 ∨ t = 6 ∨ t = 7 ∨ t = 8 ∨ t = 9 ∨ t = 10 ∨ t = 11) with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · show sendsOn shaTable.interactions B_VER = false; decide
  · show sendsOn Key.table.interactions B_VER = false; decide
  · show sendsOn Kcmp.table.interactions B_VER = false; decide
  · show sendsOn Wsb.interactions B_VER = false; decide
  · show sendsOn Wsn.interactions B_VER = false; decide
  · show sendsOn Wsa.table.interactions B_VER = false; decide
  · show sendsOn Snc.table.interactions B_VER = false; decide
  · show sendsOn Rng.table.interactions B_VER = false; decide
  · show sendsOn Wsl.table.interactions B_VER = false; decide
  · show sendsOn Wsp.interactions B_VER = false; decide

end StateM5a.VerBus
