import ZkFormal.Near.Extract.Statements
import ZkFormal.Near.Statements

/-!
# ZkFormal.Near.Extract.Compose — `ExtractStmt` from the per-table views,
the SHA contract and linking
-/

namespace ZkFormal.Near

open ZkFormal.Air ZkFormal.Algebra NearSpec NearSpec.TransferV1

theorem nearAir_tables : nearAir.tables =
    [Sha.Table.table B_BYTES B_DIGEST, Node.table, WalkTab.table, Rcpt.table, Acct.table, Mrk.table,
     Sort.table] := rfl

/-- `Holds` gives the local legality of every table. -/
theorem tableLocal_of_holds {pub : List Fp} {tr : Trace Fp} (h : Holds nearAir pub tr)
    {t : Nat} {T : Table} (ht : nearAir.tables[t]? = some T) : TableLocal T tr t pub := by
  have hlt : t < nearAir.tables.length := by
    rcases Nat.lt_or_ge t nearAir.tables.length with hl | hl
    · exact hl
    · rw [List.getElem?_eq_none hl] at ht; cases ht
  have hT : nearAir.tables[t] = T := by
    rw [List.getElem?_eq_getElem hlt] at ht; exact Option.some.inj ht
  obtain ⟨h1, h2⟩ := h.logBound t hlt
  refine ⟨h1, hT ▸ h2, ?_, ?_⟩
  · intro r hr e he; exact h.constr t hlt r hr e (hT ▸ he)
  · intro r hr i hi b hb; exact h.bits t hlt r hr i (hT ▸ hi) b hb

theorem shaLocal_of_holds' {pub : List Fp} {tr : Trace Fp} (h : Holds nearAir pub tr) :
    Sha.ShaLocal tr T_SHA pub := by
  have := tableLocal_of_holds h (t := T_SHA) (T := Sha.Table.table B_BYTES B_DIGEST) rfl
  exact ⟨this.log_ge, this.log_le, this.constr⟩

/-- Total bus count = sum over the seven tables. -/
theorem busCount_near (tr : Trace Fp) (pub : List Fp) (b : Nat) (s : Bool) (m : List Fp) :
    busCount nearAir tr pub b s m =
      tableBusCount (Sha.Table.interactions B_BYTES B_DIGEST) tr T_SHA pub b s m +
      (tableBusCount Node.interactions tr T_NODE pub b s m +
      (tableBusCount WalkTab.interactions tr T_WALK pub b s m +
      (tableBusCount Rcpt.interactions tr T_RCPT pub b s m +
      (tableBusCount Acct.interactions tr T_ACCT pub b s m +
      (tableBusCount Mrk.interactions tr T_MRK pub b s m +
      (tableBusCount Sort.interactions tr T_SORT pub b s m + 0)))))) := rfl

theorem extract_of_views (hN : NodeViewStmt) (hW : WalkViewStmt) (hR : RcptViewStmt)
    (hA : AcctViewStmt) (hM : MrkViewStmt) (hS : SortViewStmt) (hSha : ShaFactsStmt)
    (hL : LinkStmt) : ExtractStmt := by
  intro c tr h
  obtain ⟨vs, hvs, tN⟩ := hN tr _ (tableLocal_of_holds h (t := T_NODE) rfl)
  obtain ⟨ws, hws, tW⟩ := hW tr _ (tableLocal_of_holds h (t := T_WALK) rfl)
  obtain ⟨rs, hrs, tR⟩ := hR tr _ (tableLocal_of_holds h (t := T_RCPT) rfl)
  obtain ⟨as, has, tA⟩ := hA tr _ (tableLocal_of_holds h (t := T_ACCT) rfl)
  obtain ⟨mv, hmv, tM⟩ := hM tr _ (tableLocal_of_holds h (t := T_MRK) rfl)
  obtain ⟨ids, hids, tS⟩ := hS tr _ (tableLocal_of_holds h (t := T_SORT) rfl)
  refine hL c vs ws rs as mv ids (shaCounts tr (publicOf c) true) (shaCounts tr (publicOf c) false)
    hvs hws hrs has hmv hids (hSha tr _ (shaLocal_of_holds' h)) ?_
  intro b m
  have hb := h.balance b m
  rw [busCount_near, busCount_near] at hb
  rw [(tN b m).1, (tW b m).1, (tR b m).1, (tA b m).1, (tM b m).1, (tS b m).1,
    (tN b m).2, (tW b m).2, (tR b m).2, (tA b m).2, (tM b m).2, (tS b m).2] at hb
  simp only [cnt, shaCounts]
  omega

end ZkFormal.Near
