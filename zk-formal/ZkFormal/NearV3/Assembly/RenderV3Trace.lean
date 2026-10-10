import ZkFormal.NearV3.Assembly.RenderV3Assemble
import ZkFormal.Near.Extract.BusCount

/-!
# ZkFormal.NearV3.Assembly.RenderV3Trace — assembling a full trace from per-table traces

`HoldsP nearAirV3` is a conjunction of per-table obligations (`TableLocal`,
`TableTraffic`) that read only table `t`'s `log` and `cell`, so a full trace can
be built as a disjoint union of one trace per table: `traceSum ts` reads `ts[t]`
for table `t`.  `tableLocal_traceSum` / `tableTraffic_traceSum` show the per-table
obligations are invariant under this reindexing.
-/

namespace ZkFormal.NearV3.Assembly

open ZkFormal.Air ZkFormal.Algebra ZkFormal.V2

/-- The zero trace (all height 1, all cells 0), the default for absent tables. -/
def zeroTrace : Trace Fp := ⟨fun _ => 1, fun _ _ _ => 0⟩

/-- A full trace assembled from per-table traces: table `t` is `ts.getD t zeroTrace`. -/
def traceSum (ts : List (Trace Fp)) : Trace Fp :=
  ⟨fun t => (ts.getD t zeroTrace).log t, fun t r c => (ts.getD t zeroTrace).cell t r c⟩

/-- Two traces agree at table `t`. -/
def AgreeAt (tr1 tr2 : Trace Fp) (t : Nat) : Prop :=
  tr1.log t = tr2.log t ∧ ∀ r c, tr1.cell t r c = tr2.cell t r c

theorem flatMap_congr {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, f a = g a) : l.flatMap f = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    simp only [List.flatMap_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]

theorem AgreeAt.height {tr1 tr2 : Trace Fp} {t : Nat} (h : AgreeAt tr1 tr2 t) :
    tr1.height t = tr2.height t := by
  unfold Trace.height; rw [h.1]

theorem AgreeAt.eval {tr1 tr2 : Trace Fp} {t : Nat} (h : AgreeAt tr1 tr2 t)
    (e : Expr) (r : Nat) (pub : List Fp) : e.eval tr1 t r pub = e.eval tr2 t r pub := by
  have hh := h.height
  unfold Expr.eval Expr.evalWith rowEnv
  simp only [hh, h.2]

theorem AgreeAt.msgVal {tr1 tr2 : Trace Fp} {t : Nat} (h : AgreeAt tr1 tr2 t)
    (i : Interaction) (r : Nat) (pub : List Fp) :
    i.msgVal tr1 t r pub = i.msgVal tr2 t r pub := by
  unfold Interaction.msgVal
  apply List.map_congr_left; intro e _; exact h.eval e r pub

theorem AgreeAt.multNat {tr1 tr2 : Trace Fp} {t : Nat} (h : AgreeAt tr1 tr2 t)
    (i : Interaction) (r : Nat) (pub : List Fp) :
    i.multNat tr1 t r pub = i.multNat tr2 t r pub := by
  unfold Interaction.multNat
  have H : ∀ (l : List Expr) (k : Nat),
      Interaction.multNat.go tr1 t r pub l k = Interaction.multNat.go tr2 t r pub l k := by
    intro l; induction l with
    | nil => intro k; rfl
    | cons e es ih => intro k; simp only [Interaction.multNat.go]; rw [h.eval e r pub, ih (k+1)]
  exact H i.mult 0

/-- `rowTraffic` is invariant under agreement at table `t`. -/
theorem AgreeAt.rowTraffic {tr1 tr2 : Trace Fp} {t : Nat} (h : AgreeAt tr1 tr2 t)
    (is : List Interaction) (r : Nat) (pub : List Fp) (b : Nat) (s : Bool) :
    ZkFormal.Near.rowTraffic is tr1 t r pub b s = ZkFormal.Near.rowTraffic is tr2 t r pub b s := by
  unfold ZkFormal.Near.rowTraffic
  apply flatMap_congr
  intro i _
  by_cases hb : (i.bus = b ∧ i.send = s)
  · rw [if_pos hb, if_pos hb, h.multNat i r pub, h.msgVal i r pub]
  · rw [if_neg hb, if_neg hb]

theorem AgreeAt.tableBusCount {tr1 tr2 : Trace Fp} {t : Nat} (h : AgreeAt tr1 tr2 t)
    (is : List Interaction) (pub : List Fp) (b : Nat) (s : Bool) (m : List Fp) :
    ZkFormal.Air.tableBusCount is tr1 t pub b s m =
      ZkFormal.Air.tableBusCount is tr2 t pub b s m := by
  rw [ZkFormal.Near.tableBusCount_eq, ZkFormal.Near.tableBusCount_eq, h.height]
  congr 1
  apply flatMap_congr
  intro r _
  exact h.rowTraffic is r pub b s

/-- `TableLocal` is invariant under agreement at table `t`. -/
theorem tableLocal_agree {tr1 tr2 : Trace Fp} {t : Nat} {T : ZkFormal.Air.Table} {pub : List Fp}
    (h : AgreeAt tr1 tr2 t) : ZkFormal.Near.TableLocal T tr1 t pub ↔
      ZkFormal.Near.TableLocal T tr2 t pub := by
  have hh := h.height
  constructor <;> intro hl <;> refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← h.1]; exact hl.log_ge
  · rw [← h.1]; exact hl.log_le
  · intro r hr e he; rw [← h.eval e r pub]
    exact hl.constr r (by rw [hh]; exact hr) e he
  · intro r hr i hi bb hb; rw [← h.eval bb r pub]
    exact hl.bits r (by rw [hh]; exact hr) i hi bb hb
  · rw [h.1]; exact hl.log_ge
  · rw [h.1]; exact hl.log_le
  · intro r hr e he; rw [h.eval e r pub]
    exact hl.constr r (by rw [← hh]; exact hr) e he
  · intro r hr i hi bb hb; rw [h.eval bb r pub]
    exact hl.bits r (by rw [← hh]; exact hr) i hi bb hb

/-- Table `t` of `traceSum ts` agrees with `ts[t]`. -/
theorem agreeAt_traceSum (ts : List (Trace Fp)) {t : Nat} (ht : t < ts.length) :
    AgreeAt (traceSum ts) (ts[t]) t := by
  have hd : ts.getD t zeroTrace = ts[t] := by
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ht, Option.getD_some]
  constructor
  · simp only [traceSum]; rw [hd]
  · intro r c; simp only [traceSum]; rw [hd]

/-- **`TableLocal` of a `traceSum` reduces to the per-table trace.** -/
theorem tableLocal_traceSum {ts : List (Trace Fp)} {t : Nat} {T : ZkFormal.Air.Table} {pub : List Fp}
    (ht : t < ts.length) :
    ZkFormal.Near.TableLocal T (traceSum ts) t pub ↔ ZkFormal.Near.TableLocal T (ts[t]) t pub :=
  tableLocal_agree (agreeAt_traceSum ts ht)

/-- **`TableTraffic` of a `traceSum` reduces to the per-table trace.** -/
theorem tableTraffic_traceSum {ts : List (Trace Fp)} {t : Nat} {is : List Interaction} {pub : List Fp}
    {tf : ZkFormal.Near.Traffic} (ht : t < ts.length) :
    ZkFormal.Near.TableTraffic is (traceSum ts) t pub tf ↔
      ZkFormal.Near.TableTraffic is (ts[t]) t pub tf := by
  have h := agreeAt_traceSum ts ht
  constructor <;> intro hh b m
  · rw [← h.tableBusCount is pub b true m, ← h.tableBusCount is pub b false m]; exact hh b m
  · rw [h.tableBusCount is pub b true m, h.tableBusCount is pub b false m]; exact hh b m

end ZkFormal.NearV3.Assembly
