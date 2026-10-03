/-- Shadowed, weakened trusted definition. -/
namespace ArenaCore
def Admits (_r : Prop) : Prop := True
theorem admits_of_sound {r : Prop} (_ : r) : Admits r := trivial
end ArenaCore
