import MoserWorm.LowerBound.Certificate.Kernel.Checker

namespace MoserWorm.LowerBound.Certificate.Chord

abbrev Triple := Label × Label × Label

def leftArc (labels : List Label) (i j : Nat) : List Label :=
  (labels.drop i).take (j - i + 1)

def rightArc (labels : List Label) (i j : Nat) : List Label :=
  labels.drop j ++ labels.take (i + 1)

def sideTests (labels : List Label) (i j : Nat) (positiveRight : Bool) : List Triple :=
  let a := labels.getD i 0
  let b := labels.getD j 0
  -- Removing the endpoint labels also handles arbitrary repeated input labels.
  -- On the externally checked `Nodup` lists these are exactly the open arcs.
  let l := (leftArc labels i j).filter (fun k => k != a && k != b)
  let r := (rightArc labels i j).filter (fun k => k != a && k != b)
  if positiveRight then
    l.map (fun k => (a, k, b)) ++ r.map (fun k => (a, b, k))
  else
    l.map (fun k => (a, b, k)) ++ r.map (fun k => (a, k, b))

/-- A strictly signed side can prove nondegeneracy even when coordinate
intervals overlap zero. The witness specifies which side test to evaluate. -/
inductive NonzeroWitness where
  | coordinate
  | side (label : Label) (reversed : Bool)
  deriving Repr

inductive Witness where
  | terminal
  | rotate (offset : Nat) (child : Witness)
  | cut (i j : Nat) (positiveRight : Bool) (nonzero : NonzeroWitness)
      (left right : Witness)
  deriving Repr

def excludesZero (a : DIval) : Bool := decide (0 < a.lo) || decide (a.hi < 0)

def nonzeroCheck (box : Coordinate → DIval) (v : Label → IVertex)
    (a b : Label) : NonzeroWitness → Bool
  | .coordinate =>
      let d := directDifference box (v b) (v a)
      excludesZero d.1 || excludesZero d.2
  | .side k false => Kernel.fanPositive box (v a) (v b) (v k)
  | .side k true => Kernel.fanPositive box (v a) (v k) (v b)

def fanNonnegative (box : Coordinate → DIval) (a b c : IVertex) : Bool :=
  decide (0 ≤ (directFanBound box a b c).lo) ||
  decide (0 ≤ (Kernel.bound (fanPolynomial a b c) box).lo)

def check (box : Coordinate → DIval) (v : Label → IVertex) :
    List Label → Witness → Bool
  | labels, .terminal => Kernel.polygonValid box (labels.map v)
  | labels, .rotate offset child =>
      decide (offset < labels.length) && check box v (labels.drop offset ++ labels.take offset) child
  | labels, .cut i j side nz l r =>
      decide (i < j ∧ j < labels.length ∧ 2 ≤ j - i ∧ j - i ≤ labels.length - 2) &&
      nonzeroCheck box v (labels.getD i 0) (labels.getD j 0) nz &&
      (sideTests labels i j side).all (fun t =>
        fanNonnegative box (v t.1) (v t.2.1) (v t.2.2)) &&
      check box v (leftArc labels i j) l &&
      check box v (rightArc labels i j) r

/-- The area expression is exactly the production expression on the original
labels and weights. Cut annotations never replace it by block areas. -/
def originalAreaPolynomial (v : Label → IVertex) (leaf : Leaf) : IPoly Coordinate :=
  IPoly.sum (leaf.map fun f => (shoelacePolynomial (f.labels.map v)).scale (DIval.pt f.weight))

structure AnnotatedFan where
  fan : WeightedFan
  witness : Witness
  deriving Repr

abbrev AnnotatedLeaf := List AnnotatedFan

def plainLeaf (leaf : AnnotatedLeaf) : Leaf := leaf.map AnnotatedFan.fan

def intervalLabels (box : PlacementBox) (k : Label) : IVertex :=
  (rotatedVertices box).getD k.val (.fixed (DIval.ofInt 0, DIval.ofInt 0))

def checkAnnotatedLeaf (box : PlacementBox) (leaf : AnnotatedLeaf) : Bool :=
  let vars := liftedBox box
  box.valid && anglesValid box &&
  decide (((plainLeaf leaf).map WeightedFan.weight).sum ≤ dfxOne) &&
  leaf.all (fun f => decide (0 ≤ f.fan.weight ∧ f.fan.labels.Nodup) &&
    check vars (intervalLabels box) f.fan.labels f.witness) &&
  Kernel.areaValid vars (originalAreaPolynomial (intervalLabels box) (plainLeaf leaf))

/-- Annotated leaves use the existing generic subdivision tree. -/
abbrev AnnotatedTree := BoxTree 9 AnnotatedLeaf

end MoserWorm.LowerBound.Certificate.Chord
