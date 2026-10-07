import ZkFormal.NearV3.Qv.Candidates.Records

namespace ZkFormal.NearV3.Qv.Candidates.ValueGen
open NearSpec

/-- Endpoint markers describe positions within a record, independently of mode. -/
theorem Record.markers (v : Record) (hv : v.Valid) (r : Nat) (hr : r<v.size) :
    let cells := v.rows.getD r []
    cells.getD ValueTable.act 0 = 1 ∧
    cells.getD ValueTable.vf 0 = (decide (r=0)).toNat ∧
    cells.getD ValueTable.vl 0 = (decide (r+1=v.size)).toNat ∧
    cells.getD ValueTable.cont 0 = (decide (r+1≠v.size)).toNat := by
  cases v with
  | mk vid tau users p =>
    cases p with
    | empty index =>
      change r<16 at hr
      change index.length=8 at hv
      simp only [Record.rows,Record.size]
      rw [emptyRows_get vid tau users index hv hr]
      simp [ValueTable.act,ValueTable.vf,ValueTable.vl,ValueTable.cont]
    | buffer es =>
      change r<4+24*es.length at hr
      simp only [Record.rows,Record.size]
      rw [bufferRows_get vid tau users es hv.1 r]
      by_cases h4 : r<4
      · simp [bufferRowAt,h4,ValueTable.act,ValueTable.vf,ValueTable.vl,ValueTable.cont]
        by_cases he : r+1=4+24*es.length <;> simp [he]
      · have hd : 4+24*((r-4)/24)+(r-4)%24=r := by omega
        simp [bufferRowAt,h4,hr,hd,ValueTable.act,ValueTable.vf,ValueTable.vl,ValueTable.cont]
        by_cases he : r+1=4+24*es.length <;> simp [he]
    | raw bytes =>
      simp only [Record.rows,Record.size]
      rw [rawRows_get]
      by_cases hz : bytes.length=0
      · have h0 : r=0 := by change r<max 1 bytes.length at hr; omega
        simp [hz,h0,ValueTable.act,ValueTable.vf,ValueTable.vl,ValueTable.cont]
      · have hp : 1≤bytes.length := by omega
        have hlt : r<bytes.length := by change r<max 1 bytes.length at hr; omega
        simp [hz,hlt,Nat.max_eq_right hp,ValueTable.act,ValueTable.vf,ValueTable.vl,ValueTable.cont]

end ZkFormal.NearV3.Qv.Candidates.ValueGen
