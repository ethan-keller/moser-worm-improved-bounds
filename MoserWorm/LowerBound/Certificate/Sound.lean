import MoserWorm.LowerBound.Certificate.Model
import MoserWorm.Common.Interval.Sound
import MoserWorm.LowerBound.Corner
import MoserWorm.LowerBound.Fan

/-! Coefficient enclosures imply geometric fan and mixture bounds. -/

open MeasureTheory
open scoped ENNReal

namespace MoserWorm.LowerBound.Certificate

variable {ι : Type} [DecidableEq ι]

/-- The listed monomials match exactly, and every real coefficient is enclosed. -/
def CoeffEncloses (p : Multiaffine.Polynomial ι ℝ) (q : IPoly ι) : Prop :=
  List.Forall₂ (fun t u => u.1.Nodup ∧ u.1.toFinset = t.1 ∧ t.2 ∈ u.2) p q

def ValuesEnclosed (p : SparsePolynomial ι ℝ) (q : IPoly ι) : Prop :=
  List.Forall₂ (fun t u => t.1 = u.1 ∧ t.2 ∈ u.2) p q

noncomputable def evalReal (p : SparsePolynomial ι ℝ) (x : ι → ℝ) : ℝ :=
  (p.map fun t => t.2 * (t.1.map x).prod).sum

omit [DecidableEq ι] in
@[simp] theorem evalReal_nil (x : ι → ℝ) :
    evalReal ([] : SparsePolynomial ι ℝ) x = 0 := rfl

omit [DecidableEq ι] in
@[simp] theorem evalReal_cons (t : List ι × ℝ)
    (p : SparsePolynomial ι ℝ) (x : ι → ℝ) :
    evalReal (t :: p) x = t.2 * (t.1.map x).prod + evalReal p x := rfl

omit [DecidableEq ι] in
private theorem evalMonomial_mem (s : List ι) {box : ι → DIval} {x : ι → ℝ}
    (hx : ∀ i, x i ∈ box i) :
    (s.map x).prod ∈ evalMonomial box s := by
  induction s with
  | nil => simpa [evalMonomial] using DIval.mem_ofInt 1
  | cons i s ih => exact DIval.mem_mul (hx i) ih

omit [DecidableEq ι] in
theorem evalBox_mem_values {p : SparsePolynomial ι ℝ} {q : IPoly ι}
    (h : ValuesEnclosed p q) {box : ι → DIval} {x : ι → ℝ}
    (hx : ∀ i, x i ∈ box i) : evalReal p x ∈ evalBox q box := by
  induction h with
  | nil => simpa [evalReal, evalBox] using DIval.mem_ofInt 0
  | @cons t u p q htu h ih =>
    rw [evalReal_cons]
    apply DIval.mem_add _ ih
    apply DIval.mem_mul htu.2
    rw [htu.1]
    exact evalMonomial_mem _ hx

theorem evalReal_insert (s : List ι) (a : ℝ) (p : SparsePolynomial ι ℝ)
    (x : ι → ℝ) :
    evalReal (insertCoefficient (· + ·) s a p) x =
      a * (s.map x).prod + evalReal p x := by
  induction p with
  | nil => simp [insertCoefficient]
  | cons t p ih =>
    rcases t with ⟨t, b⟩
    by_cases hst : s = t
    · subst t
      simp only [insertCoefficient, ↓reduceIte, evalReal_cons]
      ring
    · simp only [insertCoefficient, if_neg hst, evalReal_cons, ih]
      ring

theorem evalReal_collect (p : SparsePolynomial ι ℝ) (x : ι → ℝ) :
    evalReal (collectCoefficients (· + ·) p) x = evalReal p x := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    rw [collectCoefficients, evalReal_insert, ih, evalReal_cons]

theorem ValuesEnclosed.insert {p : SparsePolynomial ι ℝ} {q : IPoly ι}
    (h : ValuesEnclosed p q) (s : List ι) {a : ℝ} {A : DIval} (ha : a ∈ A) :
    ValuesEnclosed (insertCoefficient (· + ·) s a p)
      (insertCoefficient DIval.add s A q) := by
  induction h with
  | nil => exact .cons ⟨rfl, ha⟩ .nil
  | @cons t u p q htu h ih =>
    rcases t with ⟨t, b⟩
    rcases u with ⟨u, B⟩
    obtain ⟨htu, hb⟩ := htu
    dsimp at htu hb
    subst u
    by_cases hst : s = t
    · simp only [insertCoefficient, if_pos hst]
      exact .cons ⟨rfl, DIval.mem_add ha hb⟩ h
    · simp only [insertCoefficient, if_neg hst]
      exact .cons ⟨rfl, hb⟩ ih

theorem ValuesEnclosed.collect {p : SparsePolynomial ι ℝ} {q : IPoly ι}
    (h : ValuesEnclosed p q) :
    ValuesEnclosed (collectCoefficients (· + ·) p) (Certificate.collect q) := by
  induction h with
  | nil => exact .nil
  | @cons t u p q htu h ih =>
    change ValuesEnclosed
      (insertCoefficient (· + ·) t.1 t.2 (collectCoefficients (· + ·) p))
      (insertCoefficient DIval.add u.1 u.2 (Certificate.collect q))
    rw [← htu.1]
    exact ih.insert t.1 htu.2

theorem CoeffEncloses.toSparse {p : Multiaffine.Polynomial ι ℝ} {q : IPoly ι}
    (h : CoeffEncloses p q) :
    ∃ r : SparsePolynomial ι ℝ, ValuesEnclosed r q ∧
      ∀ x, evalReal r x = p.eval x := by
  induction h with
  | nil => exact ⟨[], .nil, fun _ => rfl⟩
  | @cons t u p q htu h ih =>
    obtain ⟨r, hr, heq⟩ := ih
    refine ⟨(u.1, t.2) :: r, .cons ⟨rfl, htu.2.2⟩ hr, ?_⟩
    intro x
    rw [evalReal_cons, Multiaffine.Polynomial.eval_cons, heq]
    congr 2
    rw [← htu.2.1]
    exact (List.prod_toFinset _ htu.1).symm

def scaleReal (a : ℝ) (p : SparsePolynomial ι ℝ) : SparsePolynomial ι ℝ :=
  p.map fun t => (t.1, a * t.2)

def mulReal (p q : SparsePolynomial ι ℝ) : SparsePolynomial ι ℝ :=
  p.flatMap fun t => q.map fun u => (t.1 ++ u.1, t.2 * u.2)

omit [DecidableEq ι] in
theorem ValuesEnclosed.append {p r : SparsePolynomial ι ℝ} {q s : IPoly ι}
    (hp : ValuesEnclosed p q) (hr : ValuesEnclosed r s) :
    ValuesEnclosed (p ++ r) (q ++ s) := by
  induction hp with
  | nil => exact hr
  | cons h hp ih => exact .cons h ih

omit [DecidableEq ι] in
theorem ValuesEnclosed.scale {p : SparsePolynomial ι ℝ} {q : IPoly ι}
    (hp : ValuesEnclosed p q) {a : ℝ} {A : DIval} (ha : a ∈ A) :
    ValuesEnclosed (scaleReal a p) (q.scale A) := by
  induction hp with
  | nil => exact .nil
  | cons h hp ih => exact .cons ⟨h.1, DIval.mem_mul ha h.2⟩ ih

omit [DecidableEq ι] in
theorem ValuesEnclosed.mul {p r : SparsePolynomial ι ℝ} {q s : IPoly ι}
    (hp : ValuesEnclosed p q) (hr : ValuesEnclosed r s) :
    ValuesEnclosed (mulReal p r) (q.mul s) := by
  induction hp with
  | nil => exact .nil
  | @cons t u p q htu hp ih =>
    apply ValuesEnclosed.append _ ih
    clear ih
    induction hr with
    | nil => exact .nil
    | @cons v w r s hvw hr ihr =>
      exact .cons ⟨by dsimp only; rw [htu.1, hvw.1], DIval.mem_mul htu.2 hvw.2⟩ ihr

omit [DecidableEq ι] in
theorem evalReal_append (p q : SparsePolynomial ι ℝ) (x : ι → ℝ) :
    evalReal (p ++ q) x = evalReal p x + evalReal q x := by
  simp [evalReal, List.map_append, List.sum_append]

omit [DecidableEq ι] in
theorem evalReal_scale (a : ℝ) (p : SparsePolynomial ι ℝ) (x : ι → ℝ) :
    evalReal (scaleReal a p) x = a * evalReal p x := by
  induction p with
  | nil => simp [scaleReal]
  | cons t p ih =>
    change (a * t.2) * (t.1.map x).prod + evalReal (scaleReal a p) x = _
    rw [ih, evalReal_cons]
    ring

omit [DecidableEq ι] in
theorem evalReal_mul (p q : SparsePolynomial ι ℝ) (x : ι → ℝ) :
    evalReal (mulReal p q) x = evalReal p x * evalReal q x := by
  induction p with
  | nil => simp [mulReal]
  | cons t p ih =>
    change evalReal ((q.map fun u => (t.1 ++ u.1, t.2 * u.2)) ++ mulReal p q) x = _
    rw [evalReal_append, ih, evalReal_cons, add_mul]
    congr 1
    clear ih
    induction q with
    | nil => simp
    | cons u q ihq =>
      simp only [List.map_cons, evalReal_cons, List.map_append, List.prod_append, ihq]
      ring

def sortReal (le : ι → ι → Bool) (p : SparsePolynomial ι ℝ) :
    SparsePolynomial ι ℝ :=
  p.map fun t => (sortSupport le t.1, t.2)

omit [DecidableEq ι] in
theorem insertSupport_perm (le : ι → ι → Bool) (i : ι) (s : List ι) :
    (insertSupport le i s).Perm (i :: s) := by
  induction s with
  | nil => exact .refl _
  | cons j s ih =>
    simp only [insertSupport]
    split
    · exact .refl _
    · exact (List.Perm.cons j ih).trans (List.Perm.swap i j s)

omit [DecidableEq ι] in
theorem sortSupport_perm (le : ι → ι → Bool) (s : List ι) :
    (sortSupport le s).Perm s := by
  induction s with
  | nil => exact .refl _
  | cons i s ih =>
    exact (insertSupport_perm le i (sortSupport le s)).trans (List.Perm.cons i ih)

omit [DecidableEq ι] in
theorem ValuesEnclosed.sort {p : SparsePolynomial ι ℝ} {q : IPoly ι}
    (h : ValuesEnclosed p q) (le : ι → ι → Bool) :
    ValuesEnclosed (sortReal le p) (sortSupports le q) := by
  induction h with
  | nil => exact .nil
  | cons h hp ih => exact .cons ⟨by dsimp only; rw [h.1], h.2⟩ ih

omit [DecidableEq ι] in
theorem evalReal_sort (le : ι → ι → Bool) (p : SparsePolynomial ι ℝ)
    (x : ι → ℝ) : evalReal (sortReal le p) x = evalReal p x := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    change t.2 * ((sortSupport le t.1).map x).prod + evalReal (sortReal le p) x = _
    rw [ih, evalReal_cons, ((sortSupport_perm le t.1).map x).prod_eq]

theorem evalBox_mem {p : Multiaffine.Polynomial ι ℝ} {q : IPoly ι}
    (h : CoeffEncloses p q) {box : ι → DIval} {x : ι → ℝ}
    (hx : ∀ i, x i ∈ box i) : p.eval x ∈ evalBox q box := by
  obtain ⟨r, hr, heq⟩ := h.toSparse
  rw [← heq]
  exact evalBox_mem_values hr hx

/-- Collecting interval coefficients remains sound; it can remove dependency overestimation. -/
theorem bound_mem {p : Multiaffine.Polynomial ι ℝ} {q : IPoly ι}
    (h : CoeffEncloses p q) {box : ι → DIval} {x : ι → ℝ}
    (hx : ∀ i, x i ∈ box i) : p.eval x ∈ bound q box := by
  obtain ⟨r, hr, heq⟩ := h.toSparse
  rw [← heq, ← evalReal_collect r x]
  exact evalBox_mem_values hr.collect hx

theorem bound_lower {p : Multiaffine.Polynomial ι ℝ} {q : IPoly ι}
    (h : CoeffEncloses p q) {box : ι → DIval} {x : ι → ℝ}
    (hx : ∀ i, x i ∈ box i) :
    DIval.val (bound q box).lo ≤ p.eval x :=
  (DIval.mem_iff_val.mp (bound_mem h hx)).1

theorem bound_pos {p : Multiaffine.Polynomial ι ℝ} {q : IPoly ι}
    (h : CoeffEncloses p q) {box : ι → DIval} {x : ι → ℝ}
    (hx : ∀ i, x i ∈ box i) (hcheck : 0 < (bound q box).lo) : 0 < p.eval x := by
  have hpos : 0 < DIval.val (bound q box).lo := by
    unfold DIval.val
    exact div_pos (by exact_mod_cast hcheck) (by positivity)
  exact hpos.trans_le (bound_lower h hx)

/-- An integer comparison certifies a rational lower bound without floating-point arithmetic. -/
theorem bound_ratio {p : Multiaffine.Polynomial ι ℝ} {q : IPoly ι}
    (h : CoeffEncloses p q) {box : ι → DIval} {x : ι → ℝ}
    (hx : ∀ i, x i ∈ box i) {num den : Int} (hden : 0 < den)
    (hcheck : num * dfxOne ≤ den * (bound q box).lo) :
    (num : ℝ) / (den : ℝ) ≤ p.eval x := by
  apply le_trans _ (bound_lower h hx)
  have hdenR : (0 : ℝ) < den := by exact_mod_cast hden
  rw [DIval.val, div_le_div_iff₀ hdenR (by positivity)]
  have hc : (num : ℝ) * dfxOne ≤ (den : ℝ) * (bound q box).lo := by
    exact_mod_cast hcheck
  norm_num [dfxOne, dfxS] at hc ⊢
  nlinarith [hc]

namespace CoeffEncloses

theorem sortSupports {p : Multiaffine.Polynomial ι ℝ} {q : IPoly ι}
    (h : CoeffEncloses p q) (le : ι → ι → Bool) :
    CoeffEncloses p (Certificate.sortSupports le q) := by
  induction h with
  | nil => exact .nil
  | @cons t u p q htu h ih =>
    have hp := sortSupport_perm le u.1
    refine .cons ⟨hp.nodup_iff.mpr htu.1, ?_, htu.2.2⟩ ih
    calc
      (sortSupport le u.1).toFinset = u.1.toFinset := by
        ext i
        simp only [List.mem_toFinset]
        exact hp.mem_iff
      _ = t.1 := htu.2.1

theorem constant {a : ℝ} {A : DIval} (ha : a ∈ A) :
    CoeffEncloses (Multiaffine.Polynomial.constant (ι := ι) a) (IPoly.constant A) :=
  .cons ⟨by simp, by simp, ha⟩ .nil

theorem coord (i : ι) :
    CoeffEncloses (Multiaffine.Polynomial.coord (R := ℝ) i) (IPoly.coord i) :=
  .cons ⟨by simp, by simp, by simpa using DIval.mem_ofInt 1⟩ .nil

theorem add {p r : Multiaffine.Polynomial ι ℝ} {q s : IPoly ι}
    (hp : CoeffEncloses p q) (hr : CoeffEncloses r s) :
    CoeffEncloses (p.add r) (q.add s) := by
  induction hp with
  | nil => exact hr
  | cons h hp ih => exact .cons h ih

theorem scale {p : Multiaffine.Polynomial ι ℝ} {q : IPoly ι}
    (hp : CoeffEncloses p q) {a : ℝ} {A : DIval} (ha : a ∈ A) :
    CoeffEncloses (p.scale a) (q.scale A) := by
  induction hp with
  | nil => exact .nil
  | cons h hp ih => exact .cons ⟨h.1, h.2.1, DIval.mem_mul ha h.2.2⟩ ih

theorem sum {ps : List (Multiaffine.Polynomial ι ℝ)} {qs : List (IPoly ι)}
    (h : List.Forall₂ CoeffEncloses ps qs) :
    CoeffEncloses (Multiaffine.Polynomial.sum ps) (IPoly.sum qs) := by
  induction h with
  | nil => exact .nil
  | cons hp h ih => exact hp.add ih

private theorem mul_term {p : Multiaffine.Polynomial ι ℝ} {q : IPoly ι}
    (h : CoeffEncloses p q) {t : Finset ι × ℝ} {u : List ι × DIval}
    (htu : u.1.Nodup ∧ u.1.toFinset = t.1 ∧ t.2 ∈ u.2) :
    (∀ v ∈ p, Disjoint t.1 v.1) →
    CoeffEncloses (p.map fun v => (t.1 ∪ v.1, t.2 * v.2))
      (q.map fun v => (u.1 ++ v.1, u.2.mul v.2)) := by
  induction h with
  | nil => exact fun _ => .nil
  | @cons v w p q hvw h ih =>
    intro hsep
    refine .cons ⟨?_, ?_, DIval.mem_mul htu.2.2 hvw.2.2⟩ ?_
    · apply List.nodup_append.mpr
      refine ⟨htu.1, hvw.1, ?_⟩
      intro a ha b hb hab
      subst b
      apply Finset.disjoint_left.mp (hsep v (by simp))
      · rw [← htu.2.1]
        exact List.mem_toFinset.mpr ha
      · rw [← hvw.2.1]
        exact List.mem_toFinset.mpr hb
    · simp only [List.toFinset_append, htu.2.1, hvw.2.1]
    · exact ih fun v hv => hsep v (by simp [hv])

theorem mul {p r : Multiaffine.Polynomial ι ℝ} {q s : IPoly ι}
    (hp : CoeffEncloses p q) (hr : CoeffEncloses r s) :
    p.Separated r → CoeffEncloses (p.mul r) (q.mul s) := by
  induction hp with
  | nil => exact fun _ => .nil
  | @cons t u p q htu hp ih =>
    intro hsep
    apply CoeffEncloses.add
    · exact hr.mul_term htu fun v hv => hsep t (by simp) v hv
    · exact ih fun v hv w hw => hsep v (by simp [hv]) w hw

end CoeffEncloses

section Geometry

variable {B : Type} [DecidableEq B]

/-- Realization in the canonical complex plane. -/
noncomputable def realize (x : Corner.Coordinate B → ℝ) (v : Corner.Vertex B ℝ) : Plane :=
  ⟨(Corner.position x v).1, (Corner.position x v).2⟩

noncomputable def points (x : Corner.Coordinate B → ℝ)
    (l : List (Corner.Vertex B ℝ)) : List Plane :=
  l.map (realize x)

omit [DecidableEq B] in
theorem points_getD (x : Corner.Coordinate B → ℝ) (l : List (Corner.Vertex B ℝ)) (i : ℕ) :
    (points x l).getD i 0 = realize x (l.getD i (.fixed (0, 0))) :=
  List.getD_map l (.fixed (0, 0)) (realize x)

theorem eval_fanPoly (x : Corner.Coordinate B → ℝ) (hx : Corner.UnitRotations x)
    (a b c : Corner.Vertex B ℝ) :
    (Corner.fanPoly a b c).eval x =
      cross (realize x b - realize x a) (realize x c - realize x a) := by
  rw [Corner.eval_fanPoly x hx]
  rfl

theorem eval_shoelacePoly (x : Corner.Coordinate B → ℝ) (hx : Corner.UnitRotations x)
    (l : List (Corner.Vertex B ℝ)) :
    (Corner.shoelacePoly l).eval x = shoelace (points x l) := by
  rw [Corner.eval_shoelacePoly x hx]
  unfold shoelace
  rw [show (points x l).length = l.length from List.length_map ..]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [points_getD, points_getD]
  rfl

theorem fanConditions_of_positive_evals {x : Corner.Coordinate B → ℝ}
    (hx : Corner.UnitRotations x) {l : List (Corner.Vertex B ℝ)} (h3 : 3 ≤ l.length)
    (hfirst : ∀ i, 2 ≤ i → i < l.length →
      0 < (Corner.fanPoly (l.getD 0 (.fixed (0, 0)))
        (l.getD 1 (.fixed (0, 0))) (l.getD i (.fixed (0, 0)))).eval x)
    (hnext : ∀ i, 2 ≤ i → i + 1 < l.length →
      0 < (Corner.fanPoly (l.getD 0 (.fixed (0, 0)))
        (l.getD i (.fixed (0, 0))) (l.getD (i + 1) (.fixed (0, 0)))).eval x) :
    FanConditions (points x l) := by
  have hlen : (points x l).length = l.length := List.length_map ..
  refine ⟨by simpa [hlen] using h3, ?_, ?_⟩
  · intro i hi him
    rw [points_getD, points_getD, points_getD, ← eval_fanPoly x hx]
    exact hfirst i hi (by simpa [hlen] using him)
  · intro i hi him
    rw [points_getD, points_getD, points_getD, ← eval_fanPoly x hx]
    exact hnext i hi (by simpa [hlen] using him)

theorem eval_weightedShoelacePoly (x : Corner.Coordinate B → ℝ)
    (hx : Corner.UnitRotations x) (ls : List (ℝ × List (Corner.Vertex B ℝ))) :
    (Corner.weightedShoelacePoly ls).eval x =
      (ls.map fun t => t.1 * shoelace (points x t.2)).sum := by
  rw [Corner.weightedShoelacePoly, Multiaffine.Polynomial.eval_sum, List.map_map]
  change (ls.map fun t => ((Corner.shoelacePoly t.2).scale t.1).eval x).sum = _
  simp only [Multiaffine.Polynomial.eval_scale, eval_shoelacePoly x hx]

private theorem sum_get {α : Type} (l : List α) (f : α → ℝ) :
    (∑ i : Fin l.length, f (l.get i)) = (l.map f).sum := by
  rw [← List.sum_ofFn]
  change (List.ofFn (f ∘ l.get)).sum = _
  rw [← List.map_ofFn, List.ofFn_get]

/-- Individual signed values may be negative; only the mixture weights need be nonnegative. -/
theorem weightedShoelacePoly_le_volume_of_bounds {x : Corner.Coordinate B → ℝ}
    (hx : Corner.UnitRotations x) (ls : List (ℝ × List (Corner.Vertex B ℝ)))
    (hweight : ∀ t ∈ ls, 0 ≤ t.1) (hsum : (ls.map Prod.fst).sum ≤ 1)
    {K : Set Plane}
    (hbound : ∀ t ∈ ls, ENNReal.ofReal (shoelace (points x t.2)) ≤ volume K) :
    ENNReal.ofReal ((Corner.weightedShoelacePoly ls).eval x) ≤ volume K := by
  by_cases htop : volume K = ⊤
  · simp [htop]
  rw [ENNReal.ofReal_le_iff_le_toReal htop, eval_weightedShoelacePoly x hx,
    ← sum_get ls (fun t => t.1 * shoelace (points x t.2))]
  calc
    ∑ i : Fin ls.length, (ls.get i).1 * shoelace (points x (ls.get i).2)
        ≤ ∑ i : Fin ls.length, (ls.get i).1 * (volume K).toReal :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
        ((ENNReal.ofReal_le_iff_le_toReal htop).mp (hbound _ (List.get_mem ..)))
        (hweight _ (List.get_mem ..))
    _ = (ls.map Prod.fst).sum * (volume K).toReal := by
      rw [← Finset.sum_mul, sum_get ls Prod.fst]
    _ ≤ 1 * (volume K).toReal :=
      mul_le_mul_of_nonneg_right hsum ENNReal.toReal_nonneg
    _ = (volume K).toReal := one_mul _

end Geometry

end MoserWorm.LowerBound.Certificate
