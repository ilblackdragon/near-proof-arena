import ZkFormal.NearV3.Candidates.CurrentFamily

namespace ZkFormal.NearV3.Candidates.CurrentFamily
set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

/-- Syntactic well-formedness only: capacity, balance and admission are separate. -/
theorem tables_wf : tables.all (ZkFormal.Air.Table.wf air 8)=true := by decide +kernel

/-- These table positions have no BYTES sends at all. This is not a claim about
kind exclusion for the remaining actual BYTES-producing tables. -/
def noBytesPositions : List Nat :=
  [0,1,2,3,5,7,8,10,11,12,14,15,16,17,20,21,26,28,29]

theorem noBytesSend : noBytesPositions.all (fun j =>
    tables[j]!.interactions.all (fun i => !(i.bus=ZkFormal.Near.B_BYTES && i.send)))=true := by
  decide +kernel
/-- Exact shapes extracted from the concrete candidate tables. -/
theorem shapes_two : shapes 2 =
  [⟨544,9,5,9,22⟩,
    ⟨544,9,5,9,22⟩,
    ⟨544,9,5,9,22⟩,
    ⟨544,9,5,9,22⟩,
    ⟨187,11,6,11,22⟩,
    ⟨73,4,5,4,11⟩,
    ⟨16,4,5,4,22⟩,
    ⟨56,4,5,4,21⟩,
    ⟨53,2,4,2,22⟩,
    ⟨200,8,5,8,22⟩,
    ⟨272,2,5,2,21⟩,
    ⟨137,2,3,2,20⟩,
    ⟨77,4,6,4,20⟩,
    ⟨91,8,5,8,22⟩,
    ⟨119,6,5,6,22⟩,
    ⟨64,6,5,6,22⟩,
    ⟨18,3,5,3,22⟩,
    ⟨33,1,3,1,22⟩,
    ⟨263,9,5,9,22⟩,
    ⟨16,7,5,7,17⟩,
    ⟨7,2,5,2,16⟩,
    ⟨6,2,5,2,13⟩,
    ⟨57,4,7,4,22⟩,
    ⟨57,4,7,4,22⟩,
    ⟨57,4,7,4,22⟩,
    ⟨57,3,5,3,22⟩,
    ⟨33,1,3,1,2⟩,
    ⟨58,3,5,3,19⟩,
    ⟨49,1,3,1,18⟩,
    ⟨52,7,6,7,22⟩] := by decide +kernel

end ZkFormal.NearV3.Candidates.CurrentFamily
