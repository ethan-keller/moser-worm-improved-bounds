import MoserWorm.LowerBound.Certificate.LeafSound
import Mathlib.Data.List.Rotate
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-! Signed shoelace bounds from recursive separation by nonzero chords. -/

open MeasureTheory Set
open scoped ENNReal

namespace MoserWorm.LowerBound.Certificate.Chord.Geometry

private theorem sum_getD (l : List ℝ) :
    (∑ i ∈ Finset.range l.length, l.getD i 0) = l.sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.length_cons, Finset.sum_range_succ', List.getD_cons_succ,
      List.getD_cons_zero, ih, List.sum_cons]
    exact add_comm _ _

/-- The indexed area definition equals the cyclic list of edge determinants. -/
theorem shoelace_eq_zipWith (l : List Plane) :
    shoelace l = (List.zipWith cross l (l.rotate 1)).sum / 2 := by
  unfold shoelace
  congr 1
  rw [← sum_getD]
  have hlen : (List.zipWith cross l (l.rotate 1)).length = l.length := by simp
  rw [hlen]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi' : i < l.length := Finset.mem_range.mp hi
  have hm : (i + 1) % l.length < l.length := Nat.mod_lt _ (by omega)
  rw [List.getD_eq_getElem _ _ hi', List.getD_eq_getElem _ _ hm,
    List.getD_eq_getElem _ _ (hlen.symm ▸ hi'), List.getElem_zipWith,
    List.getElem_rotate]

/-- Moving the starting point of the cycle preserves signed shoelace. -/
theorem shoelace_rotate (l : List Plane) (n : ℕ) :
    shoelace (l.rotate n) = shoelace l := by
  rw [shoelace_eq_zipWith, shoelace_eq_zipWith]
  have h := List.zipWith_rotate_distrib cross l (l.rotate 1) n (by simp)
  have he : (l.rotate n).rotate 1 = (l.rotate 1).rotate n := by
    simp only [List.rotate_rotate, Nat.add_comm]
  rw [he, ← h, (List.rotate_perm _ _).sum_eq]

private noncomputable def closedCross (origin : Plane) : Plane → List Plane → ℝ
  | prev, [] => cross prev origin
  | prev, p :: ps => cross prev p + closedCross origin p ps

private theorem closedCross_eq_zipWith (a p : Plane) (ps : List Plane) :
    closedCross a p ps = (List.zipWith cross (p :: ps) (ps ++ [a])).sum := by
  induction ps generalizing p with
  | nil => simp [closedCross]
  | cons q qs ih => simpa [closedCross] using congrArg (cross p q + ·) (ih q)

private theorem shoelace_cons (a : Plane) (ps : List Plane) :
    shoelace (a :: ps) = closedCross a a ps / 2 := by
  rw [shoelace_eq_zipWith, closedCross_eq_zipWith]
  rw [List.rotate_cons_succ ps a 0, List.rotate_zero]

private theorem closedCross_cut (a b p : Plane) (xs ys : List Plane) :
    closedCross a p (xs ++ b :: ys) =
      closedCross a p (xs ++ [b]) + closedCross a a (b :: ys) := by
  induction xs generalizing p with
  | nil => simp only [List.nil_append, closedCross, cross_swap b a]; ring
  | cons x xs ih => simp only [List.cons_append, closedCross, ih]; ring

/-- Closing the two oriented arcs adds opposite copies of the chord, which cancel. -/
theorem shoelace_cut (a b : Plane) (xs ys : List Plane) :
    shoelace (a :: (xs ++ b :: ys)) =
      shoelace (a :: (xs ++ [b])) + shoelace (a :: b :: ys) := by
  simp only [shoelace_cons]
  rw [closedCross_cut a b a xs ys]
  ring

/-- Convex hull of the points occurring in a finite cyclic list. -/
def hull (l : List Plane) : Set Plane := convexHull ℝ {p | p ∈ l}

theorem measurableSet_hull (l : List Plane) : MeasurableSet (hull l) :=
  (l.finite_toSet.isClosed_convexHull ℝ).measurableSet

theorem hull_subset {l : List Plane} {K : Set Plane} (hK : Convex ℝ K)
    (hmem : ∀ p ∈ l, p ∈ K) : hull l ⊆ K :=
  convexHull_min hmem hK

private theorem cross_sub_right (u p a : Plane) :
    cross u (p - a) = cross u p - cross u a := by
  simp only [cross_apply, Complex.sub_re, Complex.sub_im]
  ring

/-- Closed halfplane guards extend from vertices to the entire finite hull. -/
theorem hull_cross_le {a u : Plane} {l : List Plane}
    (h : ∀ p ∈ l, cross u (p - a) ≤ 0) :
    hull l ⊆ {p | cross u p ≤ cross u a} := by
  apply convexHull_min _ (convex_halfSpace_le (cross_isLinearMap_right u) _)
  intro p hp
  have := h p hp
  simpa only [Set.mem_ofPred_eq, cross_sub_right, sub_nonpos] using this

theorem hull_cross_ge {a u : Plane} {l : List Plane}
    (h : ∀ p ∈ l, 0 ≤ cross u (p - a)) :
    hull l ⊆ {p | cross u a ≤ cross u p} := by
  apply convexHull_min _ (convex_halfSpace_ge (cross_isLinearMap_right u) _)
  intro p hp
  have := h p hp
  simpa only [Set.mem_ofPred_eq, cross_sub_right, sub_nonneg] using this

/-- Opposite closed halfplanes intersect on a null line when their direction is nonzero. -/
theorem volume_hull_union {a u : Plane} (hu : u ≠ 0) {l r : List Plane}
    (hl : ∀ p ∈ l, cross u (p - a) ≤ 0)
    (hr : ∀ p ∈ r, 0 ≤ cross u (p - a)) :
    volume (hull l ∪ hull r) = volume (hull l) + volume (hull r) := by
  have hnull : volume (hull l ∩ hull r) = 0 := by
    refine measure_mono_null (fun p hp => ?_)
      (volume_setOf_cross_eq u hu (cross u a))
    exact le_antisymm (hull_cross_le hl hp.1) (hull_cross_ge hr hp.2)
  simpa only [hnull, add_zero] using
    (measure_union_add_inter (μ := volume) (hull l) (measurableSet_hull r))

/-- Interior vertices of the two arcs lie in opposite closed chord halfplanes.
Both polarities are permitted. The endpoints must be distinct as points. -/
def ChordSeparated (a b : Plane) (xs ys : List Plane) : Prop :=
  b ≠ a ∧
    ((∀ p ∈ xs, cross (b - a) (p - a) ≤ 0) ∧
      (∀ p ∈ ys, 0 ≤ cross (b - a) (p - a)) ∨
     (∀ p ∈ ys, cross (b - a) (p - a) ≤ 0) ∧
      (∀ p ∈ xs, 0 ≤ cross (b - a) (p - a)))

private theorem arc_cross_le {a b : Plane} {xs : List Plane}
    (h : ∀ p ∈ xs, cross (b - a) (p - a) ≤ 0) :
    ∀ p ∈ a :: (xs ++ [b]), cross (b - a) (p - a) ≤ 0 := by
  intro p hp
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | hp | rfl
  · simp [cross]
  · exact h _ hp
  · rw [cross_self]

private theorem arc_cross_ge {a b : Plane} {xs : List Plane}
    (h : ∀ p ∈ xs, 0 ≤ cross (b - a) (p - a)) :
    ∀ p ∈ a :: (xs ++ [b]), 0 ≤ cross (b - a) (p - a) := by
  intro p hp
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | hp | rfl
  · simp [cross]
  · exact h _ hp
  · rw [cross_self]

/-- The separated child hulls have additive area, without a covering or simplicity assumption. -/
theorem volume_cut_union {a b : Plane} {xs ys : List Plane}
    (h : ChordSeparated a b xs ys) :
    volume (hull (a :: (xs ++ [b])) ∪ hull (a :: b :: ys)) =
      volume (hull (a :: (xs ++ [b]))) + volume (hull (a :: b :: ys)) := by
  have hne : b - a ≠ 0 := sub_ne_zero.mpr h.1
  have hright : ∀ (P : Plane → Prop),
      (∀ p ∈ a :: (ys ++ [b]), P p) → ∀ p ∈ a :: b :: ys, P p := by
    intro P h p hp
    apply h
    simpa only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false, false_or, or_comm,
      or_left_comm, or_assoc] using hp
  rcases h.2 with ⟨hl, hr⟩ | ⟨hr, hl⟩
  · exact volume_hull_union hne (arc_cross_le hl) (hright _ (arc_cross_ge hr))
  · rw [Set.union_comm, add_comm]
    exact volume_hull_union hne (hright _ (arc_cross_le hr)) (arc_cross_ge hl)

theorem hull_cut_left (a b : Plane) (xs ys : List Plane) :
    hull (a :: (xs ++ [b])) ⊆ hull (a :: (xs ++ b :: ys)) := by
  apply hull_subset (convex_convexHull ℝ _)
  intro p hp
  apply subset_convexHull ℝ _
  simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hp ⊢
  rcases hp with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (Or.inl h))

theorem hull_cut_right (a b : Plane) (xs ys : List Plane) :
    hull (a :: b :: ys) ⊆ hull (a :: (xs ++ b :: ys)) := by
  apply hull_subset (convex_convexHull ℝ _)
  intro p hp
  apply subset_convexHull ℝ _
  simp only [List.mem_cons, List.mem_append] at hp ⊢
  rcases hp with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr h)

/-- Binary gluing uses only null overlap, not nonnegativity of the signed areas. -/
theorem shoelace_cut_le_hull {a b : Plane} {xs ys : List Plane}
    (hsep : ChordSeparated a b xs ys)
    (hl : ENNReal.ofReal (shoelace (a :: (xs ++ [b]))) ≤
      volume (hull (a :: (xs ++ [b]))))
    (hr : ENNReal.ofReal (shoelace (a :: b :: ys)) ≤
      volume (hull (a :: b :: ys))) :
    ENNReal.ofReal (shoelace (a :: (xs ++ b :: ys))) ≤
      volume (hull (a :: (xs ++ b :: ys))) := by
  rw [shoelace_cut]
  calc
    ENNReal.ofReal (shoelace (a :: (xs ++ [b])) + shoelace (a :: b :: ys))
        ≤ ENNReal.ofReal (shoelace (a :: (xs ++ [b]))) +
            ENNReal.ofReal (shoelace (a :: b :: ys)) := ENNReal.ofReal_add_le
    _ ≤ volume (hull (a :: (xs ++ [b]))) + volume (hull (a :: b :: ys)) :=
      add_le_add hl hr
    _ = volume (hull (a :: (xs ++ [b])) ∪ hull (a :: b :: ys)) :=
      (volume_cut_union hsep).symm
    _ ≤ volume (hull (a :: (xs ++ b :: ys))) :=
      measure_mono (Set.union_subset (hull_cut_left a b xs ys) (hull_cut_right a b xs ys))

/-- A finite recursive dissection into blocks with three to five entries.
Rotations permit a cut between any two positions in the cyclic list. -/
inductive Dissection : List Plane → Prop
  | short {l : List Plane} (h3 : 3 ≤ l.length) (h5 : l.length ≤ 5) : Dissection l
  | cut {a b : Plane} {xs ys : List Plane} (hsep : ChordSeparated a b xs ys)
      (left : Dissection (a :: (xs ++ [b]))) (right : Dissection (a :: b :: ys)) :
      Dissection (a :: (xs ++ b :: ys))
  | rotate {l : List Plane} (n : ℕ) (h : Dissection (l.rotate n)) : Dissection l

/-- A recursively separated cycle bounds its finite hull's area. -/
theorem Dissection.le_hull {l : List Plane} (h : Dissection l) :
    ENNReal.ofReal (shoelace l) ≤ volume (hull l) := by
  induction h with
  | short h3 h5 =>
    exact short_shoelace_le_volume h3 h5 (convex_convexHull ℝ _)
      (fun p hp => subset_convexHull ℝ _ hp)
  | cut hsep _ _ hl hr => exact shoelace_cut_le_hull hsep hl hr
  | @rotate l n _ ih =>
    have hh : hull (l.rotate n) = hull l := by simp only [hull, List.mem_rotate]
    simpa only [shoelace_rotate, hh] using ih

/-- The containing convex set need not be measurable, bounded, or of finite area. -/
theorem Dissection.le_volume {l : List Plane} (h : Dissection l)
    {K : Set Plane} (hK : Convex ℝ K) (hmem : ∀ p ∈ l, p ∈ K) :
    ENNReal.ofReal (shoelace l) ≤ volume K :=
  h.le_hull.trans (measure_mono (hull_subset hK hmem))

end MoserWorm.LowerBound.Certificate.Chord.Geometry

