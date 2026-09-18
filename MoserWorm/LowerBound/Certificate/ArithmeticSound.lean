import MoserWorm.LowerBound.Certificate.Basic
import MoserWorm.LowerBound.Certificate.Sound
import MoserWorm.Common.Interval.Rational
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List

/-! Soundness of the executable reduced polynomials and centered coefficient bound.
`Sound` supplies generic coefficient arithmetic; `LeafSound` uses this module. -/

namespace MoserWorm.LowerBound.Certificate

def PointEncloses (v : ℝ × ℝ) (V : DIval × DIval) : Prop :=
  v.1 ∈ V.1 ∧ v.2 ∈ V.2

/-- Labels have the same owner and their local coordinates are enclosed. -/
inductive VertexEncloses : Corner.Vertex BodyId ℝ → IVertex → Prop where
  | fixed {v V} (h : PointEncloses v V) : VertexEncloses (.fixed v) (.fixed V)
  | moving (i : BodyId) {v V} (h : PointEncloses v V) :
      VertexEncloses (.moving i v) (.moving i V)

theorem determinant_mem {v w : ℝ × ℝ} {V W : DIval × DIval}
    (hv : PointEncloses v V) (hw : PointEncloses w W) :
    Corner.det v w ∈ determinant V W :=
  DIval.mem_sub (DIval.mem_mul hv.1 hw.2) (DIval.mem_mul hv.2 hw.1)

theorem rotatePoint_mem_coords {v : ℝ × ℝ} {V : DIval × DIval}
    (hv : PointEncloses v V) {s c : ℝ} {S C : DIval} (hs : s ∈ S) (hc : c ∈ C) :
    PointEncloses (Corner.rotate c s v) (rotatePoint S C V) :=
  ⟨DIval.mem_sub (DIval.mem_mul hc hv.1) (DIval.mem_mul hs hv.2),
    DIval.mem_add (DIval.mem_mul hs hv.1) (DIval.mem_mul hc hv.2)⟩

theorem PointEncloses.sub {v w : ℝ × ℝ} {V W : DIval × DIval}
    (hv : PointEncloses v V) (hw : PointEncloses w W) :
    PointEncloses (v - w) (V.1.sub W.1, V.2.sub W.2) :=
  ⟨DIval.mem_sub hv.1 hw.1, DIval.mem_sub hv.2 hw.2⟩

theorem directPosition_mem {v : Corner.Vertex BodyId ℝ} {V : IVertex}
    (hv : VertexEncloses v V) {box : Coordinate → DIval} {x : Coordinate → ℝ}
    (hbox : ∀ i, x i ∈ box i) :
    PointEncloses (Corner.position x v) (directPosition box V) := by
  cases hv with
  | fixed hv => exact hv
  | moving i hv =>
    have hr := rotatePoint_mem_coords hv (hbox (i, 3)) (hbox (i, 2))
    exact ⟨DIval.mem_add (hbox (i, 0)) hr.1, DIval.mem_add (hbox (i, 1)) hr.2⟩

theorem directDifference_mem {a b : Corner.Vertex BodyId ℝ} {A B : IVertex}
    (ha : VertexEncloses a A) (hb : VertexEncloses b B)
    {box : Coordinate → DIval} {x : Coordinate → ℝ} (hbox : ∀ i, x i ∈ box i) :
    PointEncloses (Corner.position x a - Corner.position x b)
      (directDifference box A B) := by
  have hp := (directPosition_mem ha hbox).sub (directPosition_mem hb hbox)
  cases ha with
  | fixed ha =>
    cases hb <;> exact hp
  | @moving i v V hv =>
    cases hb with
    | fixed hb => exact hp
    | @moving j w W hw =>
      by_cases hij : i = j
      · subst j
        have hsub : Corner.position x (.moving i v) - Corner.position x (.moving i w) =
            Corner.rotate (x (i, 2)) (x (i, 3)) (v - w) := by
          ext <;> simp [Corner.position, Corner.place, Corner.rotate] <;> ring
        simpa only [directDifference, ↓reduceIte, hsub] using
          rotatePoint_mem_coords (hv.sub hw) (hbox (i, 3)) (hbox (i, 2))
      · simpa only [directDifference, if_neg hij] using hp

theorem directFanBound_mem {a b c : Corner.Vertex BodyId ℝ} {A B C : IVertex}
    (ha : VertexEncloses a A) (hb : VertexEncloses b B) (hc : VertexEncloses c C)
    {box : Coordinate → DIval} {x : Coordinate → ℝ} (hbox : ∀ i, x i ∈ box i) :
    Corner.det (Corner.position x b - Corner.position x a)
      (Corner.position x c - Corner.position x a) ∈ directFanBound box A B C :=
  determinant_mem (directDifference_mem hb ha hbox) (directDifference_mem hc ha hbox)

theorem xPolynomial_encloses (i : BodyId) {v : ℝ × ℝ} {V : DIval × DIval}
    (hv : PointEncloses v V) :
    CoeffEncloses (Corner.xPoly i v) (xPolynomial i V) :=
  (CoeffEncloses.coord (i, 0)).add
    (((CoeffEncloses.coord (i, 2)).scale hv.1).add
      ((CoeffEncloses.coord (i, 3)).scale (DIval.mem_neg hv.2)))

theorem yPolynomial_encloses (i : BodyId) {v : ℝ × ℝ} {V : DIval × DIval}
    (hv : PointEncloses v V) :
    CoeffEncloses (Corner.yPoly i v) (yPolynomial i V) :=
  (CoeffEncloses.coord (i, 1)).add
    (((CoeffEncloses.coord (i, 2)).scale hv.2).add
      ((CoeffEncloses.coord (i, 3)).scale hv.1))

theorem bilinear_encloses {a : ℝ} {A : DIval} (ha : a ∈ A)
    {i j : Coordinate} (hij : i ≠ j) :
    CoeffEncloses (Corner.bilinear a i j) (bilinear A i j) :=
  .cons ⟨by simp [hij], by simp, ha⟩ .nil

theorem sameBodyPolynomial_encloses (i : BodyId) {v w : ℝ × ℝ} {V W : DIval × DIval}
    (hv : PointEncloses v V) (hw : PointEncloses w W) :
    CoeffEncloses (Corner.sameOwnerPoly i v w) (sameBodyPolynomial i V W) :=
  (CoeffEncloses.constant (determinant_mem hv hw)).add
    ((bilinear_encloses (DIval.mem_sub hw.2 hv.2) (by simp)).add
      ((bilinear_encloses (DIval.mem_sub hw.1 hv.1) (by simp)).add
        ((bilinear_encloses (DIval.mem_sub hv.1 hw.1) (by simp)).add
          (bilinear_encloses (DIval.mem_sub hw.2 hv.2) (by simp)))))

private theorem separate_owners {i j : BodyId} (h : i ≠ j) :
    Disjoint {k : Coordinate | k.1 = i} {k : Coordinate | k.1 = j} := by
  apply Set.disjoint_left.mpr
  intro k hi hj
  exact h (hi.symm.trans hj)

theorem edgePolynomial_encloses {v w : Corner.Vertex BodyId ℝ} {V W : IVertex}
    (hv : VertexEncloses v V) (hw : VertexEncloses w W) :
    CoeffEncloses (Corner.edgePoly v w) (edgePolynomial V W) := by
  cases hv with
  | fixed hv =>
    cases hw with
    | fixed hw => exact CoeffEncloses.constant (determinant_mem hv hw)
    | moving j hw =>
      exact ((yPolynomial_encloses j hw).scale hv.1).add
        ((xPolynomial_encloses j hw).scale (DIval.mem_neg hv.2))
  | @moving i v V hv =>
    cases hw with
    | fixed hw =>
      exact ((xPolynomial_encloses i hv).scale hw.2).add
        ((yPolynomial_encloses i hv).scale (DIval.mem_neg hw.1))
    | @moving j w W hw =>
      by_cases hij : i = j
      · subst j
        simpa only [Corner.edgePoly, edgePolynomial, ↓reduceIte] using
          sameBodyPolynomial_encloses i hv hw
      · have hxy := Multiaffine.Polynomial.separated_of_support
          (Corner.supportedOn_xPoly i v) (Corner.supportedOn_yPoly j w) (separate_owners hij)
        have hyx := Multiaffine.Polynomial.separated_of_support
          (Corner.supportedOn_yPoly i v) (Corner.supportedOn_xPoly j w) (separate_owners hij)
        simp only [Corner.edgePoly, edgePolynomial, if_neg hij, Corner.mixedOwnerPoly]
        exact ((xPolynomial_encloses i hv).mul (yPolynomial_encloses j hw) hxy).add
          (((yPolynomial_encloses i hv).mul (xPolynomial_encloses j hw) hyx).scale
            (by simpa using DIval.mem_ofInt (-1)))

theorem fanPolynomial_encloses {a b c : Corner.Vertex BodyId ℝ} {A B C : IVertex}
    (ha : VertexEncloses a A) (hb : VertexEncloses b B) (hc : VertexEncloses c C) :
    CoeffEncloses (Corner.fanPoly a b c) (fanPolynomial A B C) :=
  (edgePolynomial_encloses ha hb).add
    ((edgePolynomial_encloses hb hc).add (edgePolynomial_encloses hc ha))

theorem zeroVertex_encloses :
    VertexEncloses (.fixed (0, 0)) (.fixed (DIval.ofInt 0, DIval.ofInt 0)) :=
  .fixed ⟨by simpa using DIval.mem_ofInt 0, by simpa using DIval.mem_ofInt 0⟩

theorem VertexEncloses.getD {l : List (Corner.Vertex BodyId ℝ)} {L : List IVertex}
    (h : List.Forall₂ VertexEncloses l L) (i : ℕ) :
    VertexEncloses (l.getD i (.fixed (0, 0)))
      (L.getD i (.fixed (DIval.ofInt 0, DIval.ofInt 0))) := by
  induction h generalizing i with
  | nil => simpa using zeroVertex_encloses
  | cons hv h ih =>
    cases i with
    | zero => exact hv
    | succ i => exact ih i

theorem shoelacePolynomial_encloses {l : List (Corner.Vertex BodyId ℝ)} {L : List IVertex}
    (h : List.Forall₂ VertexEncloses l L) :
    CoeffEncloses (Corner.shoelacePoly l) (shoelacePolynomial L) := by
  unfold Corner.shoelacePoly shoelacePolynomial
  apply CoeffEncloses.scale
  · apply CoeffEncloses.sum
    rw [← h.length_eq]
    induction List.range l.length with
    | nil => exact .nil
    | cons i is ih =>
      exact .cons (edgePolynomial_encloses (VertexEncloses.getD h i)
        (VertexEncloses.getD h ((i + 1) % l.length))) ih
  · simpa using DIval.mem_ratio 1 2 (by norm_num)

private noncomputable def realCenter (box : Coordinate → DIval) (i : Coordinate) : ℝ :=
  DIval.val (DyadicBox.midpoint (box i))

private noncomputable def realRadius (box : Coordinate → DIval) (i : Coordinate) : ℝ :=
  DIval.val (max ((box i).hi - DyadicBox.midpoint (box i))
    (DyadicBox.midpoint (box i) - (box i).lo))

private def affineInterval (box : Coordinate → DIval) (i : Coordinate) : IPoly Coordinate :=
  let m := DyadicBox.midpoint (box i)
  [([], DIval.pt m), ([i], DIval.pt (max ((box i).hi - m) (m - (box i).lo)))]

private noncomputable def affineReal (box : Coordinate → DIval) (i : Coordinate) :
    SparsePolynomial Coordinate ℝ :=
  [([], realCenter box i), ([i], realRadius box i)]

private noncomputable def monomialReal (box : Coordinate → DIval) (s : List Coordinate) :
    SparsePolynomial Coordinate ℝ :=
  s.foldr (fun i p => mulReal (affineReal box i) p) [([], 1)]

private def monomialInterval (box : Coordinate → DIval) (s : List Coordinate) :
    IPoly Coordinate :=
  s.foldr (fun i p => (affineInterval box i).mul p) (IPoly.constant (DIval.ofInt 1))

private noncomputable def centeredReal (p : SparsePolynomial Coordinate ℝ)
    (box : Coordinate → DIval) : SparsePolynomial Coordinate ℝ :=
  p.flatMap fun t => scaleReal t.2 (monomialReal box t.1)

private theorem affine_values_enclosed (box : Coordinate → DIval) (i : Coordinate) :
    ValuesEnclosed (affineReal box i) (affineInterval box i) :=
  .cons ⟨rfl, DIval.mem_pt _⟩ (.cons ⟨rfl, DIval.mem_pt _⟩ .nil)

private theorem monomial_values_enclosed (box : Coordinate → DIval) (s : List Coordinate) :
    ValuesEnclosed (monomialReal box s) (monomialInterval box s) := by
  induction s with
  | nil => exact .cons ⟨rfl, by simpa using DIval.mem_ofInt 1⟩ .nil
  | cons i s ih => exact (affine_values_enclosed box i).mul ih

private theorem centered_values_enclosed {p : SparsePolynomial Coordinate ℝ}
    {q : IPoly Coordinate} (h : ValuesEnclosed p q) (box : Coordinate → DIval) :
    ValuesEnclosed (centeredReal p box) (centeredPolynomial q box) := by
  induction h with
  | nil => exact .nil
  | @cons t u p q htu h ih =>
    change ValuesEnclosed
      (scaleReal t.2 (monomialReal box t.1) ++ centeredReal p box)
      ((monomialInterval box u.1).scale u.2 ++ centeredPolynomial q box)
    apply ValuesEnclosed.append _ ih
    rw [htu.1]
    exact (monomial_values_enclosed box u.1).scale htu.2

private theorem eval_affineReal (box : Coordinate → DIval) (i : Coordinate)
    (y : Coordinate → ℝ) :
    evalReal (affineReal box i) y = realCenter box i + realRadius box i * y i := by
  simp [affineReal, evalReal]

private theorem eval_monomialReal (box : Coordinate → DIval) (s : List Coordinate)
    (y : Coordinate → ℝ) :
    evalReal (monomialReal box s) y =
      (s.map fun i => realCenter box i + realRadius box i * y i).prod := by
  induction s with
  | nil => simp [monomialReal, evalReal]
  | cons i s ih =>
    change evalReal (mulReal (affineReal box i) (monomialReal box s)) y = _
    rw [evalReal_mul, eval_affineReal, ih, List.map_cons, List.prod_cons]

private theorem eval_centeredReal (p : SparsePolynomial Coordinate ℝ)
    (box : Coordinate → DIval) (y : Coordinate → ℝ) :
    evalReal (centeredReal p box) y =
      evalReal p (fun i => realCenter box i + realRadius box i * y i) := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    change evalReal (scaleReal t.2 (monomialReal box t.1) ++ centeredReal p box) y = _
    rw [evalReal_append, evalReal_scale, eval_monomialReal, ih, evalReal_cons]

private theorem abs_monomial_le_one (s : List Coordinate) {y : Coordinate → ℝ}
    (hy : ∀ i, |y i| ≤ 1) : |(s.map y).prod| ≤ 1 := by
  change (absHom : ℝ →*₀ ℝ) (s.map y).prod ≤ 1
  rw [map_list_prod]
  apply (List.prod_map_le_pow_length₀ (f := (absHom : ℝ →*₀ ℝ))
    (t := s.map y) (r := (1 : ℝ)) (fun z _ => abs_nonneg z) ?_).trans (by simp)
  intro z hz
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hz
  exact hy i

/-- Multiplication by any number of unit coordinates cannot increase the
maximum absolute endpoint of a coefficient interval. -/
private theorem coefficient_unit_mem {a z : ℝ} {A : DIval}
    (ha : a ∈ A) (hz : |z| ≤ 1) :
    a * z ∈ (⟨-((max A.lo.natAbs A.hi.natAbs : ℕ) : ℤ),
      ((max A.lo.natAbs A.hi.natAbs : ℕ) : ℤ)⟩ : DIval) := by
  let size : Int := (max A.lo.natAbs A.hi.natAbs : ℕ)
  have hlo : (A.lo.natAbs : Int) ≤ size := by
    dsimp [size]
    exact_mod_cast Nat.le_max_left A.lo.natAbs A.hi.natAbs
  have hhi : (A.hi.natAbs : Int) ≤ size := by
    dsimp [size]
    exact_mod_cast Nat.le_max_right A.lo.natAbs A.hi.natAbs
  have hleft : -size ≤ A.lo := (neg_le_neg hlo).trans (by
    rw [Int.natCast_natAbs]
    exact neg_abs_le _)
  have hright : A.hi ≤ size := Int.le_natAbs.trans hhi
  have habs : |a * 2 ^ dfxS| ≤ (size : ℝ) := by
    apply abs_le.mpr
    obtain ⟨ha1, ha2⟩ := DIval.mem_def.mp ha
    have hl : -(size : ℝ) ≤ (A.lo : ℝ) := by exact_mod_cast hleft
    have hu : (A.hi : ℝ) ≤ (size : ℝ) := by exact_mod_cast hright
    exact ⟨hl.trans ha1, ha2.trans hu⟩
  have hprod : |a * z * 2 ^ dfxS| ≤ (size : ℝ) := by
    rw [show a * z * 2 ^ dfxS = (a * 2 ^ dfxS) * z by ring, abs_mul]
    have hm : |a * 2 ^ dfxS| * |z| ≤ |a * 2 ^ dfxS| := by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hz (abs_nonneg (a * 2 ^ dfxS))
    exact hm.trans habs
  apply DIval.mem_def.mpr
  change ((-size : Int) : ℝ) ≤ a * z * 2 ^ dfxS ∧ a * z * 2 ^ dfxS ≤ (size : ℝ)
  simpa only [Int.cast_neg] using abs_le.mp hprod

private theorem unitRange_mem_values {p : SparsePolynomial Coordinate ℝ}
    {q : IPoly Coordinate} (h : ValuesEnclosed p q) {y : Coordinate → ℝ}
    (hy : ∀ i, |y i| ≤ 1) : evalReal p y ∈ unitRange q := by
  induction h with
  | nil => simpa [unitRange, evalReal] using DIval.mem_ofInt 0
  | @cons t u p q htu h ih =>
    rw [evalReal_cons]
    apply DIval.mem_add _ ih
    rw [htu.1]
    cases hs : u.1 with
    | nil => simpa [hs] using htu.2
    | cons i s =>
      simpa [hs] using coefficient_unit_mem htu.2 (abs_monomial_le_one u.1 hy)

private theorem box_in_center_radius {box : Coordinate → DIval} {x : Coordinate → ℝ}
    (hx : ∀ i, x i ∈ box i) :
    Multiaffine.InBox (fun i => realCenter box i - realRadius box i)
      (fun i => realCenter box i + realRadius box i) x := by
  intro i
  let m := DyadicBox.midpoint (box i)
  let r := max ((box i).hi - m) (m - (box i).lo)
  have hl : m - r ≤ (box i).lo := by
    have := le_max_right ((box i).hi - m) (m - (box i).lo)
    dsimp [r]
    omega
  have hu : (box i).hi ≤ m + r := by
    have := le_max_left ((box i).hi - m) (m - (box i).lo)
    dsimp [r]
    omega
  obtain ⟨hxlo, hxhi⟩ := DIval.mem_iff_val.mp (hx i)
  constructor
  · apply le_trans _ hxlo
    change DIval.val m - DIval.val r ≤ DIval.val (box i).lo
    unfold DIval.val
    rw [← sub_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hl) (by positivity)
  · apply le_trans hxhi
    change DIval.val (box i).hi ≤ DIval.val m + DIval.val r
    unfold DIval.val
    rw [← add_div]
    exact div_le_div_of_nonneg_right (by exact_mod_cast hu) (by positivity)

private theorem normalized_coordinate {m r x : ℝ} (hx : m - r ≤ x ∧ x ≤ m + r) :
    |(x - m) / r| ≤ 1 ∧ m + r * ((x - m) / r) = x := by
  have hr : 0 ≤ r := by linarith
  by_cases hz : r = 0
  · have heq : x = m := by rw [hz] at hx; linarith
    simp [hz, heq]
  · have hrp : 0 < r := lt_of_le_of_ne hr (Ne.symm hz)
    constructor
    · rw [abs_div, abs_of_pos hrp]
      apply (div_le_one hrp).mpr
      exact abs_le.mpr ⟨by linarith, by linarith⟩
    · field_simp [hz]
      ring

/-- Sparse evaluation is enough for the bound. The input may already have
been sorted, collected, or supplied as verified literal data. -/
theorem centeredBound_mem_values {r : SparsePolynomial Coordinate ℝ}
    {q : IPoly Coordinate} (hr : ValuesEnclosed r q)
    {box : Coordinate → DIval} {x : Coordinate → ℝ}
    (hx : ∀ i, x i ∈ box i) : evalReal r x ∈ centeredBound q box := by
  let y : Coordinate → ℝ := fun i => (x i - realCenter box i) / realRadius box i
  have hxy := fun i => normalized_coordinate (box_in_center_radius hx i)
  have hy : ∀ i, |y i| ≤ 1 := fun i => (hxy i).1
  have htransform : (fun i => realCenter box i + realRadius box i * y i) = x :=
    funext fun i => (hxy i).2
  have hc := ((centered_values_enclosed hr box).sort
    (fun i j => coordinateCode i ≤ coordinateCode j)).collect
  have hb := unitRange_mem_values hc hy
  rw [evalReal_collect, evalReal_sort, eval_centeredReal, htransform] at hb
  exact hb

/-- The executable centered, sorted, collected coefficient bound encloses the
polynomial at every point of the input box, including zero-width intervals. -/
theorem centeredBound_mem {p : Multiaffine.Polynomial Coordinate ℝ}
    {q : IPoly Coordinate} (h : CoeffEncloses p q)
    {box : Coordinate → DIval} {x : Coordinate → ℝ}
    (hx : ∀ i, x i ∈ box i) : p.eval x ∈ centeredBound q box := by
  obtain ⟨r, hr, heq⟩ := h.toSparse
  rw [← heq]
  exact centeredBound_mem_values hr hx

/-- Collecting raw coefficients before expansion is also sound. This permits
the checker to reduce repeated monomials before their affine expansions. -/
theorem centeredBound_precollect_mem {p : Multiaffine.Polynomial Coordinate ℝ}
    {q : IPoly Coordinate} (h : CoeffEncloses p q) (le : Coordinate → Coordinate → Bool)
    {box : Coordinate → DIval} {x : Coordinate → ℝ}
    (hx : ∀ i, x i ∈ box i) :
    p.eval x ∈ centeredBound (collect (sortSupports le q)) box := by
  obtain ⟨r, hr, heq⟩ := h.toSparse
  have hm := centeredBound_mem_values (hr.sort le).collect hx
  simpa only [evalReal_collect, evalReal_sort, heq] using hm

theorem centeredBound_lower {p : Multiaffine.Polynomial Coordinate ℝ}
    {q : IPoly Coordinate} (h : CoeffEncloses p q)
    {box : Coordinate → DIval} {x : Coordinate → ℝ}
    (hx : ∀ i, x i ∈ box i) :
    DIval.val (centeredBound q box).lo ≤ p.eval x :=
  (DIval.mem_iff_val.mp (centeredBound_mem h hx)).1

theorem centeredBound_pos {p : Multiaffine.Polynomial Coordinate ℝ}
    {q : IPoly Coordinate} (h : CoeffEncloses p q)
    {box : Coordinate → DIval} {x : Coordinate → ℝ}
    (hx : ∀ i, x i ∈ box i) (hcheck : 0 < (centeredBound q box).lo) :
    0 < p.eval x := by
  have hpos : 0 < DIval.val (centeredBound q box).lo :=
    div_pos (by exact_mod_cast hcheck) (by positivity)
  exact hpos.trans_le (centeredBound_lower h hx)

theorem fanPositive_pos {a b c : Corner.Vertex BodyId ℝ} {A B C : IVertex}
    (ha : VertexEncloses a A) (hb : VertexEncloses b B) (hc : VertexEncloses c C)
    {box : Coordinate → DIval} {x : Coordinate → ℝ}
    (hx : Corner.UnitRotations x) (hbox : ∀ i, x i ∈ box i)
    (hcheck : fanPositive box A B C = true) : 0 < (Corner.fanPoly a b c).eval x := by
  simp only [fanPositive, Bool.or_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with h | h
  · rw [Corner.eval_fanPoly x hx]
    have hpos : 0 < DIval.val (directFanBound box A B C).lo :=
      div_pos (by exact_mod_cast h) (by positivity)
    exact hpos.trans_le (DIval.mem_iff_val.mp (directFanBound_mem ha hb hc hbox)).1
  · exact centeredBound_pos (fanPolynomial_encloses ha hb hc) hbox h

private theorem ratio_le_of_mem {v : ℝ} {I : DIval} (hv : v ∈ I)
    {num den : Int} (hden : 0 < den) (hcheck : num * dfxOne ≤ den * I.lo) :
    (num : ℝ) / (den : ℝ) ≤ v := by
  apply le_trans _ (DIval.mem_iff_val.mp hv).1
  have hdenR : (0 : ℝ) < den := by exact_mod_cast hden
  rw [DIval.val, div_le_div_iff₀ hdenR (by positivity)]
  have hc : (num : ℝ) * dfxOne ≤ (den : ℝ) * I.lo := by
    exact_mod_cast hcheck
  norm_num [dfxOne, dfxS] at hc ⊢
  nlinarith [hc]

theorem centeredBound_ratio {p : Multiaffine.Polynomial Coordinate ℝ}
    {q : IPoly Coordinate} (h : CoeffEncloses p q)
    {box : Coordinate → DIval} {x : Coordinate → ℝ}
    (hx : ∀ i, x i ∈ box i) {num den : Int} (hden : 0 < den)
    (hcheck : num * dfxOne ≤ den * (centeredBound q box).lo) :
    (num : ℝ) / (den : ℝ) ≤ p.eval x :=
  ratio_le_of_mem (centeredBound_mem h hx) hden hcheck

theorem areaValid_lower {p : Multiaffine.Polynomial Coordinate ℝ}
    {q : IPoly Coordinate} (h : CoeffEncloses p q)
    {box : Coordinate → DIval} {x : Coordinate → ℝ} (hx : ∀ i, x i ∈ box i)
    (hcheck : areaValid box q = true) : (239 / 1000 : ℝ) ≤ p.eval x := by
  simp only [areaValid, Bool.or_eq_true, decide_eq_true_eq] at hcheck
  have hden : (0 : Int) < 1000 := by norm_num
  rcases hcheck with hcheck | hcheck
  · exact ratio_le_of_mem (centeredBound_precollect_mem h
      (fun i j => coordinateCode i ≤ coordinateCode j) hx) hden hcheck
  · exact centeredBound_ratio h hx hden hcheck

end MoserWorm.LowerBound.Certificate
