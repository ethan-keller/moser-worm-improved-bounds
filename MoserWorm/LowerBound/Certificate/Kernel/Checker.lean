import MoserWorm.LowerBound.Certificate.Kernel.Collect

/-! Kernel replay with proved, exactly equal centering and collection shortcuts. -/

namespace MoserWorm.LowerBound.Certificate.Kernel

def fanPositive (variables : Coordinate → DIval) (a b c : IVertex) : Bool :=
  decide (0 < (directFanBound variables a b c).lo) ||
  decide (0 < (bound (fanPolynomial a b c) variables).lo)

def fanValid (variables : Coordinate → DIval) (points : List IVertex) : Bool :=
  let pointAt := fun i => points.getD i (.fixed (DIval.ofInt 0, DIval.ofInt 0))
  decide (3 ≤ points.length) &&
  (List.range (points.length - 2)).all (fun j =>
    fanPositive variables (pointAt 0) (pointAt 1) (pointAt (j + 2))) &&
  (List.range (points.length - 3)).all (fun j =>
    fanPositive variables (pointAt 0) (pointAt (j + 2)) (pointAt (j + 3)))

def polygonValid (variables : Coordinate → DIval) (points : List IVertex) : Bool :=
  if points.length = 3 ∨ points.length = 4 ∨ points.length = 5 then true
  else fanValid variables points

/-- Collect the area polynomial first, retaining the original bound as fallback. -/
def areaValid (variables : Coordinate → DIval) (p : IPoly Coordinate) : Bool :=
  decide (239 * dfxOne ≤ 1000 * (bound
    (collect (sortSupports (fun i j => coordinateCode i ≤ coordinateCode j) p)) variables).lo) ||
  decide (239 * dfxOne ≤ 1000 * (bound p variables).lo)

def checkLeaf (box : PlacementBox) (leaf : Leaf) : Bool :=
  let points := rotatedVertices box
  let variables := liftedBox box
  box.valid && anglesValid box &&
  decide ((leaf.map (·.weight)).sum ≤ dfxOne) &&
  leaf.all (fun fan => decide (0 ≤ fan.weight ∧ fan.labels.Nodup) &&
    polygonValid variables (selectedPoints points fan.labels)) &&
  (let p := IPoly.sum (leaf.map fun fan =>
    (shoelacePolynomial (selectedPoints points fan.labels)).scale (DIval.pt fan.weight))
   areaValid variables p)

theorem fanPositive_eq (variables : Coordinate → DIval) (a b c : IVertex) :
    fanPositive variables a b c = Certificate.fanPositive variables a b c := by
  simp only [fanPositive, Certificate.fanPositive, bound_eq]

theorem fanValid_eq (variables : Coordinate → DIval) (points : List IVertex) :
    fanValid variables points = Certificate.fanValid variables points := by
  simp only [fanValid, Certificate.fanValid, fanPositive_eq]

theorem polygonValid_eq (variables : Coordinate → DIval) (points : List IVertex) :
    polygonValid variables points = Certificate.polygonValid variables points := by
  simp only [polygonValid, Certificate.polygonValid, fanValid_eq]

theorem areaValid_eq (variables : Coordinate → DIval) (p : IPoly Coordinate) :
    areaValid variables p = Certificate.areaValid variables p := by
  simp only [areaValid, Certificate.areaValid, bound_eq]

theorem checkLeaf_eq (box : PlacementBox) (leaf : Leaf) :
    checkLeaf box leaf = Certificate.checkLeaf box leaf := by
  simp only [checkLeaf, Certificate.checkLeaf, polygonValid_eq, areaValid_eq]

/-- Feed this fact directly into the existing real soundness theorem. -/
theorem accepted {box : PlacementBox} {leaf : Leaf} (h : checkLeaf box leaf = true) :
    Certificate.checkLeaf box leaf = true := by
  rwa [checkLeaf_eq] at h

/-- The exporter can keep its existing tree acceptance theorem statements. -/
theorem checkTree_eq (box : PlacementBox) (tree : BoxTree 9 Leaf) :
    BoxTree.check checkLeaf box tree = BoxTree.check Certificate.checkLeaf box tree := by
  have h : checkLeaf = Certificate.checkLeaf :=
    funext fun b => funext fun leaf => checkLeaf_eq b leaf
  rw [h]

theorem treeAccepted {box : PlacementBox} {tree : BoxTree 9 Leaf}
    (h : BoxTree.check checkLeaf box tree = true) :
    BoxTree.check Certificate.checkLeaf box tree = true := by
  rwa [checkTree_eq] at h

end MoserWorm.LowerBound.Certificate.Kernel
