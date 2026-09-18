import MoserWorm.LowerBound.Certificate.Basic

/-! Exact shortcuts for the constant, linear, and quadratic centering cases. -/

namespace MoserWorm.LowerBound.Certificate.Kernel

/-- A point product needs one endpoint product and no minimum/maximum tests. -/
def pointProduct (x y : Int) : DIval :=
  let p := x * y
  ⟨p.fdiv dfxOne, -((-p).fdiv dfxOne)⟩

theorem pointProduct_eq (x y : Int) :
    pointProduct x y = (DIval.pt x).mul (DIval.pt y) := by
  simp [pointProduct, DIval.mul, DIval.pt]

theorem point_mul_one (x : Int) :
    (DIval.pt x).mul (DIval.ofInt 1) = DIval.pt x := by
  simp [DIval.mul, DIval.pt, DIval.ofInt, ← Int.neg_mul,
    Int.mul_fdiv_cancel, show (dfxOne : Int) ≠ 0 by decide]

/-- Preserve the original rounding order; higher degrees use the reference code. -/
def centerTerm (box : Coordinate → DIval) (s : List Coordinate) (a : DIval) :
    IPoly Coordinate :=
  let mid := fun i => DyadicBox.midpoint (box i)
  let rad := fun i => max ((box i).hi - mid i) (mid i - (box i).lo)
  match s with
  | [] => [([], a.mul (DIval.ofInt 1))]
  | [i] => [([], a.mul (DIval.pt (mid i))), ([i], a.mul (DIval.pt (rad i)))]
  | [i, j] =>
    [([], a.mul (pointProduct (mid i) (mid j))),
     ([j], a.mul (pointProduct (mid i) (rad j))),
     ([i], a.mul (pointProduct (rad i) (mid j))),
     ([i, j], a.mul (pointProduct (rad i) (rad j)))]
  | _ => centeredPolynomial [(s, a)] box

def center (p : IPoly Coordinate) (box : Coordinate → DIval) : IPoly Coordinate :=
  p.flatMap fun (s, a) => centerTerm box s a

theorem centerTerm_eq (box : Coordinate → DIval) (s : List Coordinate) (a : DIval) :
    centerTerm box s a = centeredPolynomial [(s, a)] box := by
  rcases s with _ | ⟨i, s⟩
  · rfl
  rcases s with _ | ⟨j, s⟩
  · simp [centerTerm, centeredPolynomial, IPoly.mul, IPoly.constant, IPoly.scale,
      point_mul_one]
  rcases s with _ | ⟨k, s⟩
  · simp [centerTerm, centeredPolynomial, IPoly.mul, IPoly.constant, IPoly.scale,
      point_mul_one, pointProduct_eq]
  · rfl

theorem center_eq (p : IPoly Coordinate) (box : Coordinate → DIval) :
    center p box = centeredPolynomial p box := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rcases t with ⟨s, a⟩
    change centerTerm box s a ++ center p box = _
    rw [centerTerm_eq, ih]
    simp only [centeredPolynomial, List.flatMap_cons, List.flatMap_nil, List.append_nil]

end MoserWorm.LowerBound.Certificate.Kernel
