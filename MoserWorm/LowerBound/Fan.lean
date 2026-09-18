/-
Copyright (c) 2026 Ethan Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Keller
-/
import MoserWorm.Common.Area

/-! A fan area bound using only the manuscript's determinant tests.
The polygon may be concave. No boundary winding or convex vertex ordering is required. -/

open MeasureTheory Set
open scoped ENNReal

namespace MoserWorm

/-- Strict determinant tests for a fan based at the first point. -/
def FanConditions (l : List Plane) : Prop :=
  3 ≤ l.length ∧
  (∀ i, 2 ≤ i → i < l.length →
    0 < cross (l.getD 1 0 - l.getD 0 0) (l.getD i 0 - l.getD 0 0)) ∧
  (∀ i, 2 ≤ i → i + 1 < l.length →
    0 < cross (l.getD i 0 - l.getD 0 0) (l.getD (i + 1) 0 - l.getD 0 0))

/-- Within an open half-plane, positive consecutive determinants are transitive. -/
theorem cross_pos_trans {r a b c : Plane}
    (hra : 0 < cross r a) (hrb : 0 < cross r b) (hrc : 0 < cross r c)
    (hab : 0 < cross a b) (hbc : 0 < cross b c) : 0 < cross a c := by
  have hid : cross a c * cross r b =
      cross a b * cross r c + cross r a * cross b c := by
    simp only [cross_apply]
    ring
  have hprod : 0 < cross a c * cross r b := by
    rw [hid]
    exact add_pos (mul_pos hab hrc) (mul_pos hra hbc)
  exact (mul_pos_iff_of_pos_right hrb).mp hprod

/-- The local fan tests imply a positive determinant between every ordered pair of rays. -/
theorem fan_cross_pos (w : ℕ → Plane) (n : ℕ)
    (hfirst : ∀ i, 2 ≤ i → i < n →
      0 < cross (w 1 - w 0) (w i - w 0))
    (hnext : ∀ i, 2 ≤ i → i + 1 < n →
      0 < cross (w i - w 0) (w (i + 1) - w 0)) :
    ∀ p q, 1 ≤ p → p < q → q < n →
      0 < cross (w p - w 0) (w q - w 0) := by
  intro p q hp hpq hq
  by_cases hp1 : p = 1
  · subst p
    exact hfirst q (by omega) hq
  have hp2 : 2 ≤ p := by omega
  induction q using Nat.strong_induction_on with
  | h q ih =>
    by_cases hlast : q = p + 1
    · subst q
      exact hnext p hp2 hq
    have hpred : p < q - 1 := by omega
    apply cross_pos_trans
      (hfirst p hp2 (by omega))
      (hfirst (q - 1) (by omega) (by omega))
      (hfirst q (by omega) hq)
      (ih (q - 1) (by omega) hpred (by omega))
    simpa only [Nat.sub_add_cancel (show 1 ≤ q by omega)] using
      hnext (q - 1) (by omega) (by omega)

/-- The fan triangles have pairwise null intersections, so their areas add inside `H`. -/
theorem fan_volume_bound (w : ℕ → Plane) (n : ℕ)
    (hfirst : ∀ i, 2 ≤ i → i < n →
      0 < cross (w 1 - w 0) (w i - w 0))
    (hnext : ∀ i, 2 ≤ i → i + 1 < n →
      0 < cross (w i - w 0) (w (i + 1) - w 0))
    {K : Set Plane} (hK : Convex ℝ K) (hmemK : ∀ i, i < n → w i ∈ K) :
    ENNReal.ofReal (∑ j ∈ Finset.range (n - 2),
      cross (w (j + 1) - w 0) (w (j + 2) - w 0) / 2) ≤ volume K := by
  have hspoke := fan_cross_pos w n hfirst hnext
  have hpos : ∀ j, j < n - 2 → 0 < cross (w (j + 1) - w 0) (w (j + 2) - w 0) := fun j hj =>
    hspoke (j + 1) (j + 2) (by omega) (by omega) (by omega)
  -- the fan triangles
  set T : ℕ → Set Plane := fun j => convexHull ℝ ({w 0, w (j + 1), w (j + 2)} : Set Plane) with hT
  have hTsub : ∀ j, j < n - 2 → T j ⊆ K := by
    intro j hj
    simp only [hT]
    refine convexHull_min ?_ hK
    rintro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    · exact hmemK 0 (by omega)
    · exact hmemK (j + 1) (by omega)
    · exact hmemK (j + 2) (by omega)
  have hTmeas : ∀ j : ℕ, MeasurableSet (T j) := by
    intro j
    simp only [hT]
    exact ((Set.toFinite _).isClosed_convexHull (𝕜 := ℝ)).measurableSet
  have hTvol : ∀ j, j < n - 2 → volume (T j)
      = ENNReal.ofReal (cross (w (j + 1) - w 0) (w (j + 2) - w 0) / 2) := by
    intro j hj
    simp only [hT]
    rw [volume_triangle, abs_of_pos (hpos j hj)]
  -- pairwise intersections of the fan triangles are null
  have hAE : ∀ i j, i < n - 2 → j < n - 2 → i < j → volume (T i ∩ T j) = 0 := by
    intro i j hi hj hij
    have hu0 : w (i + 2) - w 0 ≠ 0 := by
      intro h0
      have hlt := hspoke (i + 2) (j + 2) (by omega) (by omega) (by omega)
      rw [h0] at hlt
      simp at hlt
    set u : Plane := w (i + 2) - w 0 with hu
    -- `T i` lies (weakly) on the right of the spoke through `w (i + 2)`
    have hTi : T i ⊆ {z : Plane | cross u z ≤ cross u (w 0)} := by
      simp only [hT]
      refine convexHull_min ?_ (convex_halfSpace_le (cross_isLinearMap_right u) _)
      rintro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · change cross u (w 0) ≤ cross u (w 0)
        exact le_refl _
      · change cross u (w (i + 1)) ≤ cross u (w 0)
        have hlt := hspoke (i + 1) (i + 2) (by omega) (by omega) (by omega)
        have e : cross u (w (i + 1)) - cross u (w 0)
            = -cross (w (i + 1) - w 0) (w (i + 2) - w 0) := by
          rw [hu]
          simp only [cross_apply, Complex.sub_re, Complex.sub_im]
          ring
        linarith
      · change cross u (w (i + 2)) ≤ cross u (w 0)
        have e : cross u (w (i + 2)) - cross u (w 0) = 0 := by
          rw [hu]
          simp only [cross_apply, Complex.sub_re, Complex.sub_im]
          ring
        linarith
    -- `T j` lies (weakly) on the left of that spoke
    have hTj : T j ⊆ {z : Plane | cross u (w 0) ≤ cross u z} := by
      simp only [hT]
      refine convexHull_min ?_ (convex_halfSpace_ge (cross_isLinearMap_right u) _)
      rintro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl
      · change cross u (w 0) ≤ cross u (w 0)
        exact le_refl _
      · change cross u (w 0) ≤ cross u (w (j + 1))
        rcases eq_or_lt_of_le (show i + 2 ≤ j + 1 by omega) with heq | hlt'
        · have e : cross u (w (j + 1)) - cross u (w 0) = 0 := by
            rw [hu, ← heq]
            simp only [cross_apply, Complex.sub_re, Complex.sub_im]
            ring
          linarith
        · have hgt := hspoke (i + 2) (j + 1) (by omega) hlt' (by omega)
          have e : cross u (w (j + 1)) - cross u (w 0)
              = cross (w (i + 2) - w 0) (w (j + 1) - w 0) := by
            rw [hu]
            simp only [cross_apply, Complex.sub_re, Complex.sub_im]
            ring
          linarith
      · change cross u (w 0) ≤ cross u (w (j + 2))
        have hgt := hspoke (i + 2) (j + 2) (by omega) (by omega) (by omega)
        have e : cross u (w (j + 2)) - cross u (w 0)
            = cross (w (i + 2) - w 0) (w (j + 2) - w 0) := by
          rw [hu]
          simp only [cross_apply, Complex.sub_re, Complex.sub_im]
          ring
        linarith
    refine measure_mono_null (fun z hz => ?_) (volume_setOf_cross_eq u hu0 (cross u (w 0)))
    exact le_antisymm (hTi hz.1) (hTj hz.2)
  -- additivity over the fan
  have hUnion : volume (⋃ j ∈ Finset.range (n - 2), T j)
      = ∑ j ∈ Finset.range (n - 2), volume (T j) := by
    apply measure_biUnion_finset₀
    · intro i hi j hj hij
      have hi' : i < n - 2 := by simpa using hi
      have hj' : j < n - 2 := by simpa using hj
      change volume (T i ∩ T j) = 0
      have hne : i ≠ j := hij
      rcases lt_or_gt_of_ne hne with h | h
      · exact hAE i j hi' hj' h
      · rw [Set.inter_comm]
        exact hAE j i hj' hi' h
    · exact fun j _ => (hTmeas j).nullMeasurableSet
  calc ENNReal.ofReal (∑ j ∈ Finset.range (n - 2),
        cross (w (j + 1) - w 0) (w (j + 2) - w 0) / 2)
      = ∑ j ∈ Finset.range (n - 2),
          ENNReal.ofReal (cross (w (j + 1) - w 0) (w (j + 2) - w 0) / 2) :=
        ENNReal.ofReal_sum_of_nonneg fun j hj =>
          div_nonneg (hpos j (Finset.mem_range.mp hj)).le (by norm_num)
    _ = ∑ j ∈ Finset.range (n - 2), volume (T j) :=
        Finset.sum_congr rfl fun j hj => (hTvol j (Finset.mem_range.mp hj)).symm
    _ = volume (⋃ j ∈ Finset.range (n - 2), T j) := hUnion.symm
    _ ≤ volume K :=
        measure_mono (Set.iUnion₂_subset fun j hj => hTsub j (Finset.mem_range.mp hj))

/-- The manuscript's fan lemma, including strict positivity. -/
theorem fan_shoelace_pos_le_volume (l : List Plane) (h : FanConditions l)
    {K : Set Plane} (hK : Convex ℝ K) (hmem : ∀ p ∈ l, p ∈ K) :
    0 < shoelace l ∧ ENNReal.ofReal (shoelace l) ≤ volume K := by
  obtain ⟨h3, hfirst, hnext⟩ := h
  rw [shoelace_eq_fan l h3]
  have hspoke := fan_cross_pos (fun i => l.getD i 0) l.length hfirst hnext
  have hpos : ∀ j ∈ Finset.range (l.length - 2),
      0 < cross (l.getD (j + 1) 0 - l.getD 0 0)
        (l.getD (j + 2) 0 - l.getD 0 0) / 2 := by
    intro j hj
    exact div_pos (hspoke (j + 1) (j + 2) (by omega) (by omega)
      (by have := Finset.mem_range.mp hj; omega)) (by norm_num)
  refine ⟨?_, fan_volume_bound _ _ hfirst hnext hK ?_⟩
  · exact Finset.sum_pos' (fun j hj => (hpos j hj).le)
      ⟨0, Finset.mem_range.mpr (by omega), hpos 0 (Finset.mem_range.mpr (by omega))⟩
  · intro i hi
    apply hmem
    rw [List.getD_eq_getElem l 0 hi]
    exact List.getElem_mem hi

/-- A nonnegative mixture with total weight at most one is another area lower bound. -/
theorem fan_mixture_le_volume {ι : Type*} (s : Finset ι)
    (l : ι → List Plane) (weight : ι → ℝ)
    (hweight : ∀ i ∈ s, 0 ≤ weight i) (hsum : ∑ i ∈ s, weight i ≤ 1)
    (hfan : ∀ i ∈ s, FanConditions (l i))
    {K : Set Plane} (hK : Convex ℝ K) (hmem : ∀ i ∈ s, ∀ p ∈ l i, p ∈ K) :
    ENNReal.ofReal (∑ i ∈ s, weight i * shoelace (l i)) ≤ volume K := by
  have hb i hi := fan_shoelace_pos_le_volume (l i) (hfan i hi) hK (hmem i hi)
  calc
    ENNReal.ofReal (∑ i ∈ s, weight i * shoelace (l i))
        = ∑ i ∈ s, ENNReal.ofReal (weight i) * ENNReal.ofReal (shoelace (l i)) := by
          rw [ENNReal.ofReal_sum_of_nonneg
            (fun i hi => mul_nonneg (hweight i hi) (hb i hi).1.le)]
          exact Finset.sum_congr rfl fun i hi => ENNReal.ofReal_mul (hweight i hi)
    _ ≤ ∑ i ∈ s, ENNReal.ofReal (weight i) * volume K :=
      Finset.sum_le_sum fun i hi => mul_le_mul_right (hb i hi).2 _
    _ = ENNReal.ofReal (∑ i ∈ s, weight i) * volume K := by
      rw [ENNReal.ofReal_sum_of_nonneg hweight, Finset.sum_mul]
    _ ≤ 1 * volume K :=
      mul_le_mul_left (by simpa using ENNReal.ofReal_le_ofReal hsum) _
    _ = volume K := one_mul _

end MoserWorm
