import ZkFormal.NearV3.Render.Ups.CompactExtract.Plan
import ZkFormal.NearV3.Render.Ups.CompactExtract.TableTraffic
namespace ZkFormal.NearV3.Render.UpsRelay.Extract
open ZkFormal.Air ZkFormal.Algebra ZkFormal.Near UpsV3 UpsRows

/-- The compact physical table gives the same semantic part-plan structure used
by the existing upsert proof, with exact bus traffic and no synthetic value rows. -/
theorem physical_plan {tr : Trace Fp} {pub : List Fp} {t : Nat}
    (hL : TableLocal compactTable tr t pub) :
    ∃ v, Wf v ∧ TableTraffic compactInteractions tr t pub (upsTraffic v) ∧
      ∀s∈v, ∃ ps fls ws ci ti di si kd sdx,
        UpsLayout s ps fls ws ∧ UpsPlan s ps ci ti di si kd sdx := by
  obtain ⟨v,hw,ht⟩:=physical_view_traffic hL
  refine ⟨v,hw,ht,?_⟩
  intro s hs
  obtain ⟨ps,fls,ws,hl⟩:=ups_layout hw s hs
  obtain ⟨ci,ti,di,si,kd,sdx,hp⟩:=ups_plan hw hs hl
  exact ⟨ps,fls,ws,ci,ti,di,si,kd,sdx,hl,hp⟩
end ZkFormal.NearV3.Render.UpsRelay.Extract
