import MoserWorm.LowerBound.Certificate.Basic

/-! The outward root box and paths through its binary subdivisions. -/

namespace MoserWorm.LowerBound.Certificate

def root : PlacementBox :=
  let x := (DIval.ratio 603894 1000000).hi
  let y := (DIval.ratio 478 1000).hi
  #v[⟨0, (DIval.piI.mul (DIval.ratio 1 3)).hi⟩,
     ⟨0, (DIval.piI.mul (DIval.ofInt 2)).hi⟩, ⟨0, DIval.piI.hi⟩,
     ⟨-x, x⟩, ⟨-y, y⟩, ⟨-x, x⟩, ⟨-y, y⟩, ⟨-x, x⟩, ⟨-y, y⟩]

def followPath : PlacementBox → List (Fin 9 × Bool) → PlacementBox
  | box, [] => box
  | box, (axis, right) :: path =>
      followPath (if right then box.right axis else box.left axis) path

end MoserWorm.LowerBound.Certificate
