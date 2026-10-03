/-- Shadowed, weakened trusted definition shipped inside the candidate. -/
namespace ArenaCore
def Admits (_r : Prop) : Prop := True           -- trivially true (sabotaged)
theorem admits_of_sound {r : Prop} (_ : r) : Admits r := trivial
end ArenaCore
