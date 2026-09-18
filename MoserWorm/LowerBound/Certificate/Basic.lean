import MoserWorm.LowerBound.Certificate.Model
import MoserWorm.Common.Box.Basic
import MoserWorm.Common.Interval.RationalBasic

/-! The executable lower certificate: reduced determinants on lifted rotation boxes. -/

namespace MoserWorm.LowerBound.Certificate

abbrev BodyId := Fin 3
abbrev Coordinate := BodyId × Fin 4
abbrev Label := Fin 13
abbrev PlacementBox := DyadicBox 9

inductive IVertex where
  | fixed (point : DIval × DIval)
  | moving (body : BodyId) (point : DIval × DIval)
  deriving Repr, DecidableEq

def determinant (a b : DIval × DIval) : DIval :=
  (a.1.mul b.2).sub (a.2.mul b.1)

def rotatePoint (s c : DIval) (v : DIval × DIval) : DIval × DIval :=
  ((c.mul v.1).sub (s.mul v.2), (s.mul v.1).add (c.mul v.2))

def bodyT : List (DIval × DIval) :=
  let r := (DIval.ofInt 3).sqrtI
  [(DIval.ratio (-1) 4, (r.mul (DIval.ratio 1 12)).neg),
   (DIval.ratio 1 4, (r.mul (DIval.ratio 1 12)).neg),
   (DIval.ofInt 0, r.mul (DIval.ratio 1 6))]

def bodyU : List (DIval × DIval) :=
  let (s, c) := DIval.sincosIv (DIval.piI.mul (DIval.ratio 11 24))
  let (s₂, c₂) := DIval.sincosIv (DIval.piI.mul (DIval.ratio 11 12))
  let k := DIval.ratio 1 12
  let two := DIval.ofInt 2
  let three := DIval.ofInt 3
  let one := DIval.ofInt 1
  [(((three.add (two.mul c)).add c₂).neg.mul k,
     ((two.mul s).add s₂).neg.mul k),
   (((one.sub (two.mul c)).sub c₂).mul k,
     ((two.mul s).add s₂).neg.mul k),
   (((one.add (two.mul c)).sub c₂).mul k,
     ((two.mul s).sub s₂).mul k),
   (((one.add (two.mul c)).add (three.mul c₂)).mul k,
     ((two.mul s).add (three.mul s₂)).mul k)]

def bodyC : List (DIval × DIval) :=
  let y := (DIval.ofInt 8745).sqrtI.mul (DIval.ratio 1 1024)
  [(DIval.ratio (-7) 16, DIval.ofInt 0),
   (DIval.ratio 49 128, y.neg),
   (DIval.ratio 7 16, DIval.ofInt 0),
   (DIval.ratio (-49) 128, y)]

def bodyVertices : BodyId → List (DIval × DIval) :=
  fun i => if i = 0 then bodyT else if i = 1 then bodyU else bodyC

def angleInterval (box : PlacementBox) (i : BodyId) : DIval :=
  box[i.val]

def translationInterval (box : PlacementBox) (i : BodyId) (y : Bool) : DIval :=
  box[3 + 2 * i.val + if y then 1 else 0]'(by have := i.isLt; split <;> omega)

def angleRadius (box : PlacementBox) (i : BodyId) : Int :=
  let a := angleInterval box i
  let mid := DyadicBox.midpoint a
  max (a.hi - mid) (mid - a.lo)

def rotatedVertices (box : PlacementBox) : List IVertex :=
  [.fixed (DIval.ratio (-1) 2, DIval.ofInt 0),
   .fixed (DIval.ratio 1 2, DIval.ofInt 0)] ++
  ([0, 1, 2] : List BodyId).flatMap fun i =>
    let (s, c) := DIval.sincos (DyadicBox.midpoint (angleInterval box i))
    (bodyVertices i).map fun v => .moving i (rotatePoint s c v)

def liftedBox (box : PlacementBox) : Coordinate → DIval :=
  fun (i, k) =>
    let (s, c) := DIval.sincos (angleRadius box i)
    if k = 0 then translationInterval box i false
    else if k = 1 then translationInterval box i true
    else if k = 2 then ⟨c.lo, dfxOne⟩
    else ⟨-s.hi, s.hi⟩

def anglesValid (box : PlacementBox) : Bool :=
  ([0, 1, 2] : List BodyId).all fun i =>
    let mid := DyadicBox.midpoint (angleInterval box i)
    let radius := angleRadius box i
    decide (-64 * dfxOne ≤ mid ∧ mid ≤ 64 * dfxOne ∧
      0 ≤ radius ∧ radius ≤ DIval.pi2Lo)

def xPolynomial (i : BodyId) (v : DIval × DIval) : IPoly Coordinate :=
  (IPoly.coord (i, 0)).add
    (((IPoly.coord (i, 2)).scale v.1).add ((IPoly.coord (i, 3)).scale v.2.neg))

def yPolynomial (i : BodyId) (v : DIval × DIval) : IPoly Coordinate :=
  (IPoly.coord (i, 1)).add
    (((IPoly.coord (i, 2)).scale v.2).add ((IPoly.coord (i, 3)).scale v.1))

def bilinear (a : DIval) (i j : Coordinate) : IPoly Coordinate := [([i, j], a)]

def sameBodyPolynomial (i : BodyId) (v w : DIval × DIval) : IPoly Coordinate :=
  (IPoly.constant (determinant v w)).add
    ((bilinear (w.2.sub v.2) (i, 0) (i, 2)).add
      ((bilinear (w.1.sub v.1) (i, 0) (i, 3)).add
        ((bilinear (v.1.sub w.1) (i, 1) (i, 2)).add
          (bilinear (w.2.sub v.2) (i, 1) (i, 3)))))

def edgePolynomial : IVertex → IVertex → IPoly Coordinate
  | .fixed v, .fixed w => IPoly.constant (determinant v w)
  | .fixed v, .moving j w =>
      ((yPolynomial j w).scale v.1).add ((xPolynomial j w).scale v.2.neg)
  | .moving i v, .fixed w =>
      ((xPolynomial i v).scale w.2).add ((yPolynomial i v).scale w.1.neg)
  | .moving i v, .moving j w =>
      if i = j then sameBodyPolynomial i v w
      else ((xPolynomial i v).mul (yPolynomial j w)).add
        (((yPolynomial i v).mul (xPolynomial j w)).scale (DIval.ofInt (-1)))

def fanPolynomial (a b c : IVertex) : IPoly Coordinate :=
  (edgePolynomial a b).add ((edgePolynomial b c).add (edgePolynomial c a))

def shoelacePolynomial (points : List IVertex) : IPoly Coordinate :=
  let pointAt := fun i => points.getD i (.fixed (DIval.ofInt 0, DIval.ofInt 0))
  (IPoly.sum ((List.range points.length).map fun i =>
    edgePolynomial (pointAt i) (pointAt ((i + 1) % points.length)))).scale (DIval.ratio 1 2)

def coordinateCode (i : Coordinate) : Nat := 4 * i.1.val + i.2.val

def centeredPolynomial (p : IPoly Coordinate) (box : Coordinate → DIval) :
    IPoly Coordinate :=
  p.flatMap fun (s, a) =>
    let affine : Coordinate → IPoly Coordinate := fun i =>
      let mid := DyadicBox.midpoint (box i)
      let radius := max ((box i).hi - mid) (mid - (box i).lo)
      [( [], DIval.pt mid), ([i], DIval.pt radius)]
    (s.foldr (fun i q => (affine i).mul q) (IPoly.constant (DIval.ofInt 1))).scale a

/-- Linear-time enclosure on the unit box; equal monomials are collected first. -/
def unitRange : IPoly Coordinate → DIval
  | [] => DIval.ofInt 0
  | (s, a) :: p =>
      let size : Int := max a.lo.natAbs a.hi.natAbs
      (if s.isEmpty then a else (⟨-size, size⟩ : DIval)).add (unitRange p)

def centeredBound (p : IPoly Coordinate) (box : Coordinate → DIval) : DIval :=
  unitRange (collect (sortSupports
    (fun i j => coordinateCode i ≤ coordinateCode j) (centeredPolynomial p box)))

/-- Direct coordinate enclosure in the lifted rotation box. -/
def directPosition (variables : Coordinate → DIval) : IVertex → DIval × DIval
  | .fixed v => v
  | .moving i v =>
      let z := rotatePoint (variables (i, 3)) (variables (i, 2)) v
      ((variables (i, 0)).add z.1, (variables (i, 1)).add z.2)

/-- Differences on one body cancel its translation before interval arithmetic. -/
def directDifference (variables : Coordinate → DIval) (a b : IVertex) : DIval × DIval :=
  match a, b with
  | .moving i v, .moving j w =>
      if i = j then
        rotatePoint (variables (i, 3)) (variables (i, 2)) (v.1.sub w.1, v.2.sub w.2)
      else
        let v := directPosition variables a
        let w := directPosition variables b
        (v.1.sub w.1, v.2.sub w.2)
  | _, _ =>
      let v := directPosition variables a
      let w := directPosition variables b
      (v.1.sub w.1, v.2.sub w.2)

def directFanBound (variables : Coordinate → DIval) (a b c : IVertex) : DIval :=
  determinant (directDifference variables b a) (directDifference variables c a)

/-- Try the inexpensive determinant enclosure before the coefficient bound. -/
def fanPositive (variables : Coordinate → DIval) (a b c : IVertex) : Bool :=
  decide (0 < (directFanBound variables a b c).lo) ||
  decide (0 < (centeredBound (fanPolynomial a b c) variables).lo)

def fanValid (variables : Coordinate → DIval) (points : List IVertex) : Bool :=
  let pointAt := fun i => points.getD i (.fixed (DIval.ofInt 0, DIval.ofInt 0))
  decide (3 ≤ points.length) &&
  (List.range (points.length - 2)).all (fun j =>
    fanPositive variables (pointAt 0) (pointAt 1) (pointAt (j + 2))) &&
  (List.range (points.length - 3)).all (fun j =>
    fanPositive variables (pointAt 0) (pointAt (j + 2)) (pointAt (j + 3)))

/-- Lists of three to five points use unconditional signed-area bounds. -/
def polygonValid (variables : Coordinate → DIval) (points : List IVertex) : Bool :=
  if points.length = 3 ∨ points.length = 4 ∨ points.length = 5 then true
  else fanValid variables points

structure WeightedFan where
  weight : Int
  labels : List Label
  deriving Repr

abbrev Leaf := List WeightedFan

def selectedPoints (points : List IVertex) (labels : List Label) : List IVertex :=
  labels.map fun i => points.getD i.val (.fixed (DIval.ofInt 0, DIval.ofInt 0))

/-- Collect the area polynomial first, retaining the original bound as fallback. -/
def areaValid (variables : Coordinate → DIval) (p : IPoly Coordinate) : Bool :=
  decide (239 * dfxOne ≤ 1000 * (centeredBound
    (collect (sortSupports (fun i j => coordinateCode i ≤ coordinateCode j) p)) variables).lo) ||
  decide (239 * dfxOne ≤ 1000 * (centeredBound p variables).lo)

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

end MoserWorm.LowerBound.Certificate
