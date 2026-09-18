import MoserWorm.Common.Multiaffine
import MoserWorm.Common.Area
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases

/-! The algebra behind the lower certificate. Same-body edges are reduced
using the unit-circle identity before the rotation variables are separated. -/

namespace MoserWorm.LowerBound.Corner

open Multiaffine
open Multiaffine.Polynomial

variable {B R : Type*} [DecidableEq B]

/-- Four scalar coordinates per movable body: `tx`, `ty`, `c`, `s`. -/
abbrev Coordinate (B : Type*) := B × Fin 4

abbrev Poly (B R : Type*) := Multiaffine.Polynomial (Coordinate B) R

/-- Local coordinates already include the box's midpoint rotation. -/
inductive Vertex (B R : Type*) where
  | fixed (v : R × R)
  | moving (body : B) (v : R × R)

def det [CommRing R] (v w : R × R) : R :=
  v.1 * w.2 - v.2 * w.1

def rotate [CommRing R] (c s : R) (v : R × R) : R × R :=
  (c * v.1 - s * v.2, s * v.1 + c * v.2)

def place [CommRing R] (t : R × R) (c s : R) (v : R × R) : R × R :=
  t + rotate c s v

def position [CommRing R] (x : Coordinate B → R) : Vertex B R → R × R
  | .fixed v => v
  | .moving i v => place (x (i, 0), x (i, 1)) (x (i, 2)) (x (i, 3)) v

omit [DecidableEq B] in
theorem det_rotate [CommRing R] (c s : R) (v w : R × R) :
    det (rotate c s v) (rotate c s w) = (c ^ 2 + s ^ 2) * det v w := by
  simp only [det, rotate]
  ring

omit [DecidableEq B] in
theorem det_same_owner [CommRing R] (t : R × R) (c s : R) (v w : R × R) :
    det (place t c s v) (place t c s w) =
      det t (rotate c s (w - v)) + (c ^ 2 + s ^ 2) * det v w := by
  simp only [det, place, rotate, Prod.fst_add, Prod.snd_add, Prod.fst_sub, Prod.snd_sub]
  ring

omit [DecidableEq B] in
theorem det_same_owner_unit [CommRing R] (t : R × R) {c s : R}
    (h : c ^ 2 + s ^ 2 = 1) (v w : R × R) :
    det (place t c s v) (place t c s w) = det t (rotate c s (w - v)) + det v w := by
  rw [det_same_owner, h, one_mul]

omit [DecidableEq B] in
theorem det_same_owner_rotation (t : ℝ × ℝ) (θ : ℝ) (v w : ℝ × ℝ) :
    det (place t (Real.cos θ) (Real.sin θ) v)
      (place t (Real.cos θ) (Real.sin θ) w) =
      det t (rotate (Real.cos θ) (Real.sin θ) (w - v)) + det v w :=
  det_same_owner_unit t (Real.cos_sq_add_sin_sq θ) v w

/-- A quadratic term with distinct variable indices has its usual evaluation. -/
def bilinear [CommRing R] (a : R) (i j : Coordinate B) : Poly B R :=
  [({i, j}, a)]

theorem eval_bilinear [CommRing R] (a : R) {i j : Coordinate B} (h : i ≠ j)
    (x : Coordinate B → R) :
    (bilinear a i j).eval x = a * x i * x j := by
  simp [bilinear, Multiaffine.Polynomial.eval, h, mul_assoc]

def xPoly [CommRing R] (i : B) (v : R × R) : Poly B R :=
  (coord (i, 0)).add (((coord (i, 2)).scale v.1).add ((coord (i, 3)).scale (-v.2)))

def yPoly [CommRing R] (i : B) (v : R × R) : Poly B R :=
  (coord (i, 1)).add (((coord (i, 2)).scale v.2).add ((coord (i, 3)).scale v.1))

omit [DecidableEq B] in
@[simp] theorem eval_xPoly [CommRing R] (i : B) (v : R × R) (x : Coordinate B → R) :
    (xPoly i v).eval x = (position x (.moving i v)).1 := by
  simp [xPoly, position, place, rotate]
  ring

omit [DecidableEq B] in
@[simp] theorem eval_yPoly [CommRing R] (i : B) (v : R × R) (x : Coordinate B → R) :
    (yPoly i v).eval x = (position x (.moving i v)).2 := by
  simp [yPoly, position, place, rotate]
  ring

omit [DecidableEq B] in
theorem supportedOn_xPoly [CommRing R] (i : B) (v : R × R) :
    (xPoly i v).SupportedOn {j | j.1 = i} := by
  apply supportedOn_add
  · exact supportedOn_coord rfl
  · apply supportedOn_add
    · exact supportedOn_scale _ (supportedOn_coord rfl)
    · exact supportedOn_scale _ (supportedOn_coord rfl)

omit [DecidableEq B] in
theorem supportedOn_yPoly [CommRing R] (i : B) (v : R × R) :
    (yPoly i v).SupportedOn {j | j.1 = i} := by
  apply supportedOn_add
  · exact supportedOn_coord rfl
  · apply supportedOn_add
    · exact supportedOn_scale _ (supportedOn_coord rfl)
    · exact supportedOn_scale _ (supportedOn_coord rfl)

omit [DecidableEq B] in
private theorem owners_disjoint {i j : B} (h : i ≠ j) :
    Disjoint {k : Coordinate B | k.1 = i} {k : Coordinate B | k.1 = j} := by
  apply Set.disjoint_left.mpr
  intro k hi hj
  exact h (hi.symm.trans hj)

/-- Same-body reduction: one constant and four bilinear terms, with no squares. -/
def sameOwnerPoly [CommRing R] (i : B) (v w : R × R) : Poly B R :=
  (constant (det v w)).add
    ((bilinear (w.2 - v.2) (i, 0) (i, 2)).add
      ((bilinear (w.1 - v.1) (i, 0) (i, 3)).add
        ((bilinear (v.1 - w.1) (i, 1) (i, 2)).add
          (bilinear (w.2 - v.2) (i, 1) (i, 3)))))

theorem eval_sameOwnerPoly [CommRing R] (i : B) (v w : R × R)
    (x : Coordinate B → R) :
    (sameOwnerPoly i v w).eval x =
      det (x (i, 0), x (i, 1)) (rotate (x (i, 2)) (x (i, 3)) (w - v)) + det v w := by
  have h02 : (i, (0 : Fin 4)) ≠ (i, (2 : Fin 4)) := by simp
  have h03 : (i, (0 : Fin 4)) ≠ (i, (3 : Fin 4)) := by simp
  have h12 : (i, (1 : Fin 4)) ≠ (i, (2 : Fin 4)) := by simp
  have h13 : (i, (1 : Fin 4)) ≠ (i, (3 : Fin 4)) := by simp
  simp only [sameOwnerPoly, eval_add, eval_constant, eval_bilinear _ h02,
    eval_bilinear _ h03, eval_bilinear _ h12, eval_bilinear _ h13,
    det, rotate, Prod.fst_sub, Prod.snd_sub]
  ring

/-- Different owners have disjoint coordinate blocks, so their unreduced
determinant is already squarefree. -/
def mixedOwnerPoly [CommRing R] (i j : B) (v w : R × R) : Poly B R :=
  ((xPoly i v).mul (yPoly j w)).add (((yPoly i v).mul (xPoly j w)).scale (-1))

theorem eval_mixedOwnerPoly [CommRing R] {i j : B} (h : i ≠ j)
    (v w : R × R) (x : Coordinate B → R) :
    (mixedOwnerPoly i j v w).eval x =
      det (position x (.moving i v)) (position x (.moving j w)) := by
  have hxy := separated_of_support (supportedOn_xPoly i v) (supportedOn_yPoly j w)
    (owners_disjoint h)
  have hyx := separated_of_support (supportedOn_yPoly i v) (supportedOn_xPoly j w)
    (owners_disjoint h)
  simp only [mixedOwnerPoly, eval_add, eval_scale, eval_mul hxy, eval_mul hyx,
    eval_xPoly, eval_yPoly, det]
  ring

/-- Determinant extension for every pair of vertex labels. -/
def edgePoly [CommRing R] : Vertex B R → Vertex B R → Poly B R
  | .fixed v, .fixed w => constant (det v w)
  | .fixed v, .moving j w => ((yPoly j w).scale v.1).add ((xPoly j w).scale (-v.2))
  | .moving i v, .fixed w => ((xPoly i v).scale w.2).add ((yPoly i v).scale (-w.1))
  | .moving i v, .moving j w =>
      if i = j then sameOwnerPoly i v w else mixedOwnerPoly i j v w

/-- Only this algebraic hypothesis distinguishes physical rotations from
independent corner coordinates. -/
def UnitRotations [CommRing R] (x : Coordinate B → R) : Prop :=
  ∀ i, x (i, 2) ^ 2 + x (i, 3) ^ 2 = 1

theorem eval_edgePoly [CommRing R] (x : Coordinate B → R) (hx : UnitRotations x)
    (v w : Vertex B R) :
    (edgePoly v w).eval x = det (position x v) (position x w) := by
  cases v with
  | fixed v =>
    cases w with
    | fixed w => simp [edgePoly, position]
    | moving j w =>
      simp only [edgePoly, eval_add, eval_scale, eval_xPoly, eval_yPoly, position, det]
      ring
  | moving i v =>
    cases w with
    | fixed w =>
      simp only [edgePoly, eval_add, eval_scale, eval_xPoly, eval_yPoly, position, det]
      ring
    | moving j w =>
      by_cases hij : i = j
      · subst j
        simp only [edgePoly, ↓reduceIte, eval_sameOwnerPoly, position]
        exact (det_same_owner_unit _ (hx i) v w).symm
      · simpa only [edgePoly, if_neg hij] using eval_mixedOwnerPoly hij v w x

/-- Twice the signed area of the triangle with the given ordered vertices. -/
def fanPoly [CommRing R] (a b c : Vertex B R) : Poly B R :=
  (edgePoly a b).add ((edgePoly b c).add (edgePoly c a))

theorem eval_fanPoly [CommRing R] (x : Coordinate B → R) (hx : UnitRotations x)
    (a b c : Vertex B R) :
    (fanPoly a b c).eval x =
      det (position x b - position x a) (position x c - position x a) := by
  simp only [fanPoly, eval_add, eval_edgePoly x hx, det, Prod.fst_sub, Prod.snd_sub]
  ring

def shoelacePoly [Field R] (l : List (Vertex B R)) : Poly B R :=
  scale (1 / 2) (Multiaffine.Polynomial.sum ((List.range l.length).map fun i =>
    edgePoly (l.getD i (.fixed (0, 0))) (l.getD ((i + 1) % l.length) (.fixed (0, 0)))))

omit [DecidableEq B] in
private theorem sum_range_map [AddCommMonoid R] (f : ℕ → R) (n : ℕ) :
    ((List.range n).map f).sum = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => rw [List.sum_range_succ, Finset.sum_range_succ, ih]

theorem eval_shoelacePoly [Field R] (x : Coordinate B → R) (hx : UnitRotations x)
    (l : List (Vertex B R)) :
    (shoelacePoly l).eval x =
      (∑ i ∈ Finset.range l.length,
        det (position x (l.getD i (.fixed (0, 0))))
          (position x (l.getD ((i + 1) % l.length) (.fixed (0, 0))))) / 2 := by
  simp only [shoelacePoly, eval_scale, eval_sum, List.map_map, Function.comp_def,
    eval_edgePoly x hx, sum_range_map]
  ring

/-- Mixture weights are arbitrary here. Their positivity is needed only when
the geometric fan bound is applied, not for the polynomial identity. -/
def weightedShoelacePoly [Field R] (ls : List (R × List (Vertex B R))) : Poly B R :=
  Multiaffine.Polynomial.sum (ls.map fun t => (shoelacePoly t.2).scale t.1)

theorem eval_weightedShoelacePoly [Field R] (x : Coordinate B → R)
    (hx : UnitRotations x) (ls : List (R × List (Vertex B R))) :
    (weightedShoelacePoly ls).eval x =
      (ls.map fun t => t.1 *
        ((∑ i ∈ Finset.range t.2.length,
          det (position x (t.2.getD i (.fixed (0, 0))))
            (position x (t.2.getD ((i + 1) % t.2.length) (.fixed (0, 0))))) / 2)).sum := by
  simp only [weightedShoelacePoly, eval_sum, List.map_map, Function.comp_def, eval_scale,
    eval_shoelacePoly x hx]

theorem fan_positive_of_corners [Finite B] {lo hi x : Coordinate B → ℝ}
    (hx : UnitRotations x) (hbox : InBox lo hi x) (a b c : Vertex B ℝ)
    (hcorners : ∀ bits, 0 < (fanPoly a b c).eval (corner lo hi bits)) :
    0 < det (position x b - position x a) (position x c - position x a) := by
  rw [← eval_fanPoly x hx]
  exact (fanPoly a b c).strict_lower_bound hbox hcorners

theorem weighted_bound_of_corners [Finite B] {lo hi x : Coordinate B → ℝ}
    (hx : UnitRotations x) (hbox : InBox lo hi x)
    (ls : List (ℝ × List (Vertex B ℝ))) {target : ℝ}
    (hcorners : ∀ bits, target ≤ (weightedShoelacePoly ls).eval (corner lo hi bits)) :
    target ≤ (ls.map fun t => t.1 *
      ((∑ i ∈ Finset.range t.2.length,
        det (position x (t.2.getD i (.fixed (0, 0))))
          (position x (t.2.getD ((i + 1) % t.2.length) (.fixed (0, 0))))) / 2)).sum := by
  rw [← eval_weightedShoelacePoly x hx]
  exact (weightedShoelacePoly ls).lower_bound hbox hcorners

omit [DecidableEq B] in
/-- The closed rotation arc lies in the rectangle used by the certificate.
The proof also allows the limiting half-width `π/2`. -/
theorem rotation_rectangle {h δ : ℝ} (hh : 0 ≤ h) (hπ : h ≤ Real.pi / 2)
    (hδ : -h ≤ δ ∧ δ ≤ h) :
    Real.cos h ≤ Real.cos δ ∧ Real.cos δ ≤ 1 ∧
      -Real.sin h ≤ Real.sin δ ∧ Real.sin δ ≤ Real.sin h := by
  have hc := Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg δ)
    (show h ≤ Real.pi by linarith [Real.pi_pos]) (abs_le.mpr hδ)
  rw [Real.cos_abs] at hc
  have hslo := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi / 2) ≤ -h by linarith)
    (show δ ≤ Real.pi / 2 by linarith [hδ.2]) hδ.1
  have hshi := Real.sin_le_sin_of_le_of_le_pi_div_two
    (show -(Real.pi / 2) ≤ δ by linarith [hδ.1]) hπ hδ.2
  exact ⟨hc, Real.cos_le_one δ, by simpa only [Real.sin_neg] using hslo, hshi⟩

/-- Actual coordinates relative to the rotation midpoint. -/
noncomputable def parameters (t : B → ℝ × ℝ) (δ : B → ℝ) : Coordinate B → ℝ :=
  fun (i, k) => ![(t i).1, (t i).2, Real.cos (δ i), Real.sin (δ i)] k

noncomputable def boxLower (tlo : B → ℝ × ℝ) (h : B → ℝ) : Coordinate B → ℝ :=
  fun (i, k) => ![(tlo i).1, (tlo i).2, Real.cos (h i), -Real.sin (h i)] k

noncomputable def boxUpper (thi : B → ℝ × ℝ) (h : B → ℝ) : Coordinate B → ℝ :=
  fun (i, k) => ![(thi i).1, (thi i).2, 1, Real.sin (h i)] k

omit [DecidableEq B] in
theorem parameters_unit (t : B → ℝ × ℝ) (δ : B → ℝ) :
    UnitRotations (parameters t δ) := by
  intro i
  simp [parameters, Real.cos_sq_add_sin_sq]

omit [DecidableEq B] in
theorem parameters_mem_box {tlo thi t : B → ℝ × ℝ} {h δ : B → ℝ}
    (ht : ∀ i, (tlo i).1 ≤ (t i).1 ∧ (t i).1 ≤ (thi i).1 ∧
      (tlo i).2 ≤ (t i).2 ∧ (t i).2 ≤ (thi i).2)
    (hh : ∀ i, 0 ≤ h i ∧ h i ≤ Real.pi / 2)
    (hδ : ∀ i, -(h i) ≤ δ i ∧ δ i ≤ h i) :
    InBox (boxLower tlo h) (boxUpper thi h) (parameters t δ) := by
  rintro ⟨i, k⟩
  have hr := rotation_rectangle (hh i).1 (hh i).2 (hδ i)
  fin_cases k
  · exact ⟨(ht i).1, (ht i).2.1⟩
  · exact ⟨(ht i).2.2.1, (ht i).2.2.2⟩
  · exact ⟨hr.1, hr.2.1⟩
  · exact hr.2.2

omit [DecidableEq B] in
/-- Absorbing the midpoint rotation into local vertices is exact. -/
theorem rotate_add (α δ : ℝ) (v : ℝ × ℝ) :
    rotate (Real.cos δ) (Real.sin δ) (rotate (Real.cos α) (Real.sin α) v) =
      rotate (Real.cos (α + δ)) (Real.sin (α + δ)) v := by
  ext <;> simp only [rotate, Real.cos_add, Real.sin_add] <;> ring

/-- Coordinate pairs use the same plane as the geometric development. -/
def toPlane (v : ℝ × ℝ) : Plane := ⟨v.1, v.2⟩

noncomputable def planePosition (x : Coordinate B → ℝ) (v : Vertex B ℝ) : Plane :=
  toPlane (position x v)

omit [DecidableEq B] in
theorem cross_toPlane (v w : ℝ × ℝ) : cross (toPlane v) (toPlane w) = det v w := rfl

omit [DecidableEq B] in
theorem planePosition_parameters (t : B → Plane) (δ : B → ℝ) (i : B) (v : ℝ × ℝ) :
    planePosition (parameters (fun j => ((t j).re, (t j).im)) δ) (.moving i v) =
      t i + Complex.exp ((δ i : ℂ) * Complex.I) * toPlane v := by
  rw [Complex.exp_ofReal_mul_I]
  apply Complex.ext <;>
    simp [planePosition, parameters, position, place, rotate, toPlane,
      Complex.mul_re, Complex.mul_im, -Complex.ofReal_cos, -Complex.ofReal_sin, mul_comm]

theorem eval_edgePoly_plane (x : Coordinate B → ℝ) (hx : UnitRotations x)
    (v w : Vertex B ℝ) :
    (edgePoly v w).eval x = cross (planePosition x v) (planePosition x w) := by
  rw [eval_edgePoly x hx]
  rfl

theorem eval_fanPoly_plane (x : Coordinate B → ℝ) (hx : UnitRotations x)
    (a b c : Vertex B ℝ) :
    (fanPoly a b c).eval x =
      cross (planePosition x b - planePosition x a) (planePosition x c - planePosition x a) := by
  rw [eval_fanPoly x hx]
  rfl

omit [DecidableEq B] in
private theorem planePosition_getD (x : Coordinate B → ℝ) (l : List (Vertex B ℝ)) (i : ℕ) :
    (l.map (planePosition x)).getD i 0 =
      planePosition x (l.getD i (.fixed (0, 0))) :=
  List.getD_map l (.fixed (0, 0)) (planePosition x)

/-- The extension evaluates to the shared signed shoelace expression. -/
theorem eval_shoelacePoly_plane (x : Coordinate B → ℝ) (hx : UnitRotations x)
    (l : List (Vertex B ℝ)) :
    (shoelacePoly l).eval x = shoelace (l.map (planePosition x)) := by
  rw [eval_shoelacePoly x hx]
  simp only [shoelace, List.length_map, planePosition_getD]
  rfl

theorem eval_weightedShoelacePoly_plane (x : Coordinate B → ℝ) (hx : UnitRotations x)
    (ls : List (ℝ × List (Vertex B ℝ))) :
    (weightedShoelacePoly ls).eval x =
      (ls.map fun t => t.1 * shoelace (t.2.map (planePosition x))).sum := by
  simp only [weightedShoelacePoly, eval_sum, List.map_map, Function.comp_def, eval_scale,
    eval_shoelacePoly_plane x hx]

end MoserWorm.LowerBound.Corner
