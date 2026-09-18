/-
Copyright (c) 2026 Ethan Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Keller
-/
import MoserWorm.LowerBound.Domain
import MoserWorm.LowerBound.Fan
import MoserWorm.UpperBound.NormalForm

/-! Every five-cycle has signed shoelace at most the area of its convex hull.
Affine maximization reduces to extreme vertices. A nonpositive turn reduces to a
quadrilateral; otherwise the cycle is a boundary polygon or pentagram. The boundary
case uses the fan bound, and a pentagram is dominated by one of three quadrilaterals. -/

open Set MeasureTheory
open scoped ENNReal

noncomputable section

namespace MoserWorm.Pentagon

open UpperBound

def area (v : Fin 5 → Plane) : ℝ := shoelace [v 0, v 1, v 2, v 3, v 4]

theorem five_fan (a b c d e : Plane) :
    shoelace [a, b, c, d, e] =
      (cross (b - a) (c - a) + cross (c - a) (d - a) +
        cross (d - a) (e - a)) / 2 := by
  rw [shoelace_eq_fan _ (by norm_num)]
  norm_num [Finset.sum_range_succ, List.getD]
  ring

theorem four_fan (a b c d : Plane) :
    shoelace [a, b, c, d] =
      (cross (b - a) (c - a) + cross (c - a) (d - a)) / 2 := by
  rw [shoelace_eq_fan _ (by norm_num)]
  norm_num [Finset.sum_range_succ, List.getD]
  ring

theorem area_shift (v : Fin 5 → Plane) (k : Fin 5) :
    area (fun i => v (i + k)) = area v := by
  fin_cases k <;> norm_num [area, five_fan, cross, Fin.add_def] <;> ring!

theorem bound_of_nonpos {K : Set Plane} (hK : Convex ℝ K)
    (v : Fin 5 → Plane) (hv : ∀ i, v i ∈ K)
    (h : turn (v 0) (v 1) (v 2) ≤ 0) :
    ENNReal.ofReal (area v) ≤ volume K := by
  apply (ENNReal.ofReal_le_ofReal (show area v ≤ shoelace [v 0, v 2, v 3, v 4] from ?_)).trans
    (quadrilateral_shoelace_le_volume hK (hv 0) (hv 2) (hv 3) (hv 4))
  rw [area, five_fan, four_fan]
  change cross (v 1 - v 0) (v 2 - v 0) ≤ 0 at h
  linarith

theorem star_algebra {q x y z w d : ℝ} (hq : 0 < q) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (hid : q * d = x * w - y * z) :
    x + w - q ≤ w + z ∨ x + w - q ≤ x + y ∨ x + w - q ≤ d + z := by
  by_cases hx : x - z ≤ q
  · left; linarith
  by_cases hw : w - y ≤ q
  · right; left; linarith
  right; right
  have h₁ := mul_nonneg (show 0 ≤ x - z - q by linarith)
    (show 0 ≤ w - y - q by linarith)
  have h₂ := mul_nonneg (show 0 ≤ x - z - q by linarith) hy
  have h₃ := mul_nonneg (show 0 ≤ w - y by linarith) hz
  have hp : 0 ≤ q * (d + z - (x + w - q)) := by nlinarith
  have := nonneg_of_mul_nonneg_right hp hq
  linarith

theorem star_bound {K : Set Plane} (hK : Convex ℝ K)
    (a b c d e : Plane) (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K)
    (hd : d ∈ K) (he : e ∈ K)
    (hq : 0 < turn a b e) (hy : 0 ≤ turn a b c) (hz : 0 ≤ turn a d e) :
    ENNReal.ofReal (shoelace [a, c, e, b, d]) ≤ volume K := by
  change 0 < cross (b - a) (e - a) at hq
  change 0 ≤ cross (b - a) (c - a) at hy
  change 0 ≤ cross (d - a) (e - a) at hz
  have hid : cross (b - a) (e - a) * cross (c - a) (d - a) =
      cross (c - a) (e - a) * cross (b - a) (d - a) -
        cross (b - a) (c - a) * cross (d - a) (e - a) := by
    simp only [cross_apply, Complex.sub_re, Complex.sub_im]
    ring
  rcases star_algebra hq hy hz hid with h | h | h
  · apply (ENNReal.ofReal_le_ofReal (show shoelace [a, c, e, b, d] ≤
        shoelace [a, b, d, e] from ?_)).trans
      (quadrilateral_shoelace_le_volume hK ha hb hd he)
    rw [five_fan, four_fan, cross_swap (e - a) (b - a)]
    linarith
  · apply (ENNReal.ofReal_le_ofReal (show shoelace [a, c, e, b, d] ≤
        shoelace [a, b, c, e] from ?_)).trans
      (quadrilateral_shoelace_le_volume hK ha hb hc he)
    rw [five_fan, four_fan, cross_swap (e - a) (b - a)]
    linarith
  · apply (ENNReal.ofReal_le_ofReal (show shoelace [a, c, e, b, d] ≤
        shoelace [a, c, d, e] from ?_)).trans
      (quadrilateral_shoelace_le_volume hK ha hc hd he)
    rw [five_fan, four_fan, cross_swap (e - a) (b - a)]
    linarith

theorem cycle (a b c d e : Plane) :
    shoelace [a, b, c, d, e] = shoelace [b, c, d, e, a] := by
  simp only [five_fan, cross_apply, Complex.sub_re, Complex.sub_im]
  ring

theorem convex_first (b c d e : Plane) :
    ConvexOn ℝ univ (fun a => shoelace [a, b, c, d, e]) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ r s _ _ hrs
  have hs : s = 1 - r := by linarith
  subst s
  apply le_of_eq
  simp only [five_fan, cross_apply, Complex.sub_re, Complex.sub_im,
    Complex.add_re, Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  ring

theorem push_vertex {V : Set Plane} (a b c d e : Plane) (ha : a ∈ convexHull ℝ V) :
    ∃ x ∈ V, shoelace [a, b, c, d, e] ≤ shoelace [b, c, d, e, x] := by
  obtain ⟨x, hx, he⟩ := (convex_first b c d e).exists_ge_of_mem_convexHull
    (subset_univ V) ha
  exact ⟨x, hx, he.trans_eq (cycle x b c d e)⟩

theorem turn_isometry (g : Plane ≃ᵢ Plane) :
    (∀ a b c, turn (g a) (g b) (g c) = turn a b c) ∨
      (∀ a b c, turn (g a) (g b) (g c) = -turn a b c) := by
  obtain ⟨u, t, hu, h | h⟩ := isometry_complex_classification g
  all_goals
    have hn : u.re * u.re + u.im * u.im = 1 := by
      simpa only [Complex.normSq_apply, hu, one_pow] using Complex.normSq_eq_norm_sq u
  · left
    intro a b c
    calc
      turn (g a) (g b) (g c) =
          (u.re * u.re + u.im * u.im) * turn a b c := by
        rw [h a, h b, h c]
        simp only [turn, cross_apply, Complex.sub_re, Complex.sub_im,
          Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im]
        ring
      _ = turn a b c := by rw [hn, one_mul]
  · right
    intro a b c
    calc
      turn (g a) (g b) (g c) =
          -((u.re * u.re + u.im * u.im) * turn a b c) := by
        rw [h a, h b, h c]
        simp only [turn, cross_apply, Complex.sub_re, Complex.sub_im,
          Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.conj_re, Complex.conj_im]
        ring
      _ = -turn a b c := by rw [hn, one_mul]

theorem turn_reverse (a b c : Plane) : turn c b a = -turn a b c := by
  rw [turn_rotate, turn_swap]

theorem boundary_order (v : Fin 5 → Plane) (hv : Function.Injective v)
    (hex : ∀ i, v i ∈ extremePoints ℝ (convexHull ℝ (range v))) :
    ∃ e : Equiv.Perm (Fin 5), ∀ i j k, i < j → j < k →
      0 < turn (v (e i)) (v (e j)) (v (e k)) := by
  have hnc : ¬ Collinear ℝ (range v) := by
    intro h
    exact inGenPos_of_extreme hv hex 0 1 2 (by decide) (by decide) (by decide)
      (h.subset (by
        rintro _ (rfl | rfl | rfl)
        all_goals exact mem_range_self _))
  obtain ⟨g, F, _, hF, _, _, _, _⟩ :=
    floorPolygon_exists v hv Fin.val Fin.val_injective hnc hex
  obtain ⟨e, _, he⟩ := F.exists_boundary
  rcases turn_isometry g with hg | hg
  · refine ⟨e, ?_⟩
    intro i j k hij hjk
    simpa only [hF, hg] using he i j k hij hjk
  · refine ⟨Fin.revPerm.trans e, ?_⟩
    intro i j k hij hjk
    have hh := he k.rev j.rev i.rev (Fin.rev_lt_rev.mpr hjk) (Fin.rev_lt_rev.mpr hij)
    rw [hF, hF, hF, hg, turn_reverse] at hh
    simpa only [neg_neg, Equiv.trans_apply, Fin.revPerm_apply] using hh

def cyclic (i j k : Fin 5) : Bool :=
  decide (i < j ∧ j < k ∨ j < k ∧ k < i ∨ k < i ∧ i < j)

theorem cyclic_sub : ∀ i j k t : Fin 5,
    cyclic (i - t) (j - t) (k - t) = cyclic i j k := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
-- Fixing the first rank at zero leaves only 5^4 index tuples for the kernel.
theorem classify :
    ∀ b c d e : Fin 5,
      let p : Fin 5 → Fin 5 := ![0, b, c, d, e]
      ([0, b, c, d, e] : List (Fin 5)).Nodup →
      (∀ i, cyclic (p i) (p (i + 1)) (p (i + 2)) = true) →
      (∀ i, p i = i) ∨ (∀ i, p i = 2 * i) := by
  decide +kernel

theorem classify_perm (p : Equiv.Perm (Fin 5))
    (hp : ∀ i, cyclic (p i) (p (i + 1)) (p (i + 2)) = true) :
    (∃ k, ∀ i, p i = i + k) ∨ (∃ k, ∀ i, p i = 2 * i + k) := by
  let q : Fin 5 → Fin 5 := fun i => p i - p 0
  have hq : Function.Injective q := by
    intro i j h
    apply p.injective
    simpa only [q, sub_add_cancel] using congrArg (fun z => z + p 0) h
  have hzero : q 0 = 0 := sub_self _
  have he : ![0, q 1, q 2, q 3, q 4] = q := by
    funext i
    fin_cases i
    · exact hzero.symm
    all_goals rfl
  have hn : [q 0, q 1, q 2, q 3, q 4].Nodup :=
    (show ([0, 1, 2, 3, 4] : List (Fin 5)).Nodup by decide).map hq
  rw [hzero] at hn
  have hc : ∀ i, cyclic (q i) (q (i + 1)) (q (i + 2)) = true := by
    intro i
    simpa only [q, cyclic_sub] using hp i
  rcases classify (q 1) (q 2) (q 3) (q 4) hn
      (by simpa only [he] using hc) with h | h
  · refine Or.inl ⟨p 0, ?_⟩
    intro i
    simpa only [he, q, sub_add_cancel] using congrArg (fun z => z + p 0) (h i)
  · refine Or.inr ⟨p 0, ?_⟩
    intro i
    simpa only [he, q, sub_add_cancel] using congrArg (fun z => z + p 0) (h i)

theorem cyclic_turn {v : Fin 5 → Plane}
    (hv : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {i j k : Fin 5} (h : cyclic i j k = true) :
    0 < turn (v i) (v j) (v k) := by
  simp only [cyclic, decide_eq_true_eq] at h
  rcases h with ⟨hij, hjk⟩ | ⟨hjk, hki⟩ | ⟨hki, hij⟩
  · exact hv i j k hij hjk
  · rw [turn_rotate]; exact hv j k i hjk hki
  · rw [turn_rotate, turn_rotate]; exact hv k i j hki hij

theorem cyclic_of_positive {v : Fin 5 → Plane}
    (hv : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k))
    {i j k : Fin 5} (h : 0 < turn (v i) (v j) (v k)) :
    cyclic i j k = true := by
  have hij : i ≠ j := by
    rintro rfl
    simp [turn, cross] at h
  have hjk : j ≠ k := by
    rintro rfl
    change 0 < cross (v j - v i) (v j - v i) at h
    rw [cross_self] at h
    exact lt_irrefl _ h
  have hki : k ≠ i := by
    rintro rfl
    simp [turn, cross] at h
  by_contra hn
  have hs : cyclic j i k = true := by
    simp only [cyclic, decide_eq_true_eq] at hn ⊢
    omega
  have hh := cyclic_turn hv hs
  rw [turn_swap] at hh
  linarith

theorem positive_injective {v : Fin 5 → Plane}
    (hv : ∀ i, 0 < turn (v i) (v (i + 1)) (v (i + 2))) :
    Function.Injective v := by
  have h₁ : ∀ i, v i ≠ v (i + 1) := by
    intro i he
    have h := hv i
    rw [he] at h
    simp [turn, cross] at h
  have h₂ : ∀ i, v i ≠ v (i + 2) := by
    intro i he
    have h := hv i
    rw [he] at h
    simp [turn, cross] at h
  have hd : ∀ i j : Fin 5,
      i = j ∨ j = i + 1 ∨ j = i + 2 ∨ i = j + 1 ∨ i = j + 2 := by
    decide +kernel
  intro i j he
  rcases hd i j with h | h | h | h | h
  · exact h
  · exact False.elim (h₁ i (h ▸ he))
  · exact False.elim (h₂ i (h ▸ he))
  · exact False.elim (h₁ j (h ▸ he.symm))
  · exact False.elim (h₂ j (h ▸ he.symm))

theorem boundary_bound {K : Set Plane} (hK : Convex ℝ K)
    (v : Fin 5 → Plane) (hv : ∀ i, v i ∈ K)
    (ho : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k)) :
    ENNReal.ofReal (area v) ≤ volume K := by
  apply (fan_shoelace_pos_le_volume [v 0, v 1, v 2, v 3, v 4] ?_ hK ?_).2
  · refine ⟨by norm_num, ?_, ?_⟩
    · intro i hi hj
      have hil : i < 5 := hj
      interval_cases i <;> simpa only [List.getD, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.getD_some, turn] using
          ho 0 1 _ (by decide) (by decide)
    · intro i hi hj
      have hil : i < 4 := by have : i + 1 < 5 := hj; omega
      interval_cases i <;> simpa only [List.getD, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.getD_some, turn] using
          ho 0 _ _ (by decide) (by decide)
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    all_goals exact hv _

theorem star_ordered_bound {K : Set Plane} (hK : Convex ℝ K)
    (v : Fin 5 → Plane) (hv : ∀ i, v i ∈ K)
    (ho : ∀ i j k, i < j → j < k → 0 < turn (v i) (v j) (v k)) :
    ENNReal.ofReal (area (fun i => v (2 * i))) ≤ volume K := by
  exact star_bound hK (v 0) (v 1) (v 2) (v 3) (v 4)
    (hv 0) (hv 1) (hv 2) (hv 3) (hv 4)
    (ho 0 1 4 (by decide) (by decide))
    (ho 0 1 2 (by decide) (by decide)).le
    (ho 0 3 4 (by decide) (by decide)).le

theorem star_shift (v : Fin 5 → Plane) (k : Fin 5) :
    area (fun i => v (2 * i + k)) = area (fun i => v (2 * i)) := by
  have hf : ∀ i k : Fin 5, 2 * i + k = 2 * (i + 3 * k) := by decide +kernel
  simp_rw [hf]
  exact area_shift (fun i => v (2 * i)) (3 * k)

theorem extreme_bound {K : Set Plane} (hK : Convex ℝ K)
    (v : Fin 5 → Plane) (hex : ∀ i, v i ∈ extremePoints ℝ K) :
    ENNReal.ofReal (area v) ≤ volume K := by
  have hv : ∀ i, v i ∈ K := fun i => (hex i).1
  by_cases ht : ∀ i, 0 < turn (v i) (v (i + 1)) (v (i + 2))
  · have hsub : convexHull ℝ (range v) ⊆ K :=
      convexHull_min (by rintro _ ⟨i, rfl⟩; exact hv i) hK
    have hex' : ∀ i, v i ∈ extremePoints ℝ (convexHull ℝ (range v)) := by
      intro i
      exact inter_extremePoints_subset_extremePoints_of_subset hsub
        ⟨subset_convexHull ℝ _ (mem_range_self i), hex i⟩
    obtain ⟨e, he⟩ := boundary_order v (positive_injective ht) hex'
    have hc : ∀ i, cyclic (e.symm i) (e.symm (i + 1)) (e.symm (i + 2)) = true := by
      intro i
      apply cyclic_of_positive he
      simpa only [e.apply_symm_apply] using ht i
    rcases classify_perm e.symm hc with ⟨k, hk⟩ | ⟨k, hk⟩
    · have hv' : v = fun i => v (e (i + k)) := by
        funext i
        rw [← hk, e.apply_symm_apply]
      rw [hv']
      rw [area_shift (fun i => v (e i)) k]
      exact boundary_bound hK (fun i => v (e i)) (fun i => hv (e i)) he
    · have hv' : v = fun i => v (e (2 * i + k)) := by
        funext i
        rw [← hk, e.apply_symm_apply]
      rw [hv']
      rw [star_shift (fun i => v (e i)) k]
      exact star_ordered_bound hK (fun i => v (e i)) (fun i => hv (e i)) he
  · push Not at ht
    obtain ⟨i, hi⟩ := ht
    have hb := bound_of_nonpos hK (fun j => v (j + i)) (fun j => hv (j + i))
      (by simpa only [zero_add, add_zero, add_comm] using hi)
    simpa only [area_shift] using hb

/-- Successive affine maximization reduces any five points to extreme points. -/
theorem bound {K : Set Plane} (hK : Convex ℝ K)
    (v : Fin 5 → Plane) (hv : ∀ i, v i ∈ K) :
    ENNReal.ofReal (area v) ≤ volume K := by
  classical
  let F : Finset Plane := Finset.univ.image v
  obtain ⟨V, hV, _, hHull⟩ := finite_hull_extreme_vertices F
  have hvV : ∀ i, v i ∈ convexHull ℝ (V : Set Plane) := by
    intro i
    rw [hHull]
    exact subset_convexHull ℝ _ (by simp [F])
  obtain ⟨a, ha, h₁⟩ := push_vertex (v 0) (v 1) (v 2) (v 3) (v 4) (hvV 0)
  obtain ⟨b, hb, h₂⟩ := push_vertex (v 1) (v 2) (v 3) (v 4) a (hvV 1)
  obtain ⟨c, hc, h₃⟩ := push_vertex (v 2) (v 3) (v 4) a b (hvV 2)
  obtain ⟨d, hd, h₄⟩ := push_vertex (v 3) (v 4) a b c (hvV 3)
  obtain ⟨e, he, h₅⟩ := push_vertex (v 4) a b c d (hvV 4)
  have hnew := extreme_bound (convex_convexHull ℝ (F : Set Plane))
    ![a, b, c, d, e] (by
      intro i
      rw [← hV]
      fin_cases i
      · exact ha
      · exact hb
      · exact hc
      · exact hd
      · exact he)
  refine (ENNReal.ofReal_le_ofReal (h₁.trans (h₂.trans (h₃.trans (h₄.trans h₅))))).trans
    (hnew.trans (measure_mono ?_))
  refine convexHull_min ?_ hK
  rintro x hx
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
  exact hv i

end MoserWorm.Pentagon

namespace MoserWorm

/-- Any signed five-cycle is bounded by its containing convex set, in any order. -/
theorem pentagon_shoelace_le_volume {K : Set Plane} (hK : Convex ℝ K)
    {a b c d e : Plane} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K)
    (hd : d ∈ K) (he : e ∈ K) :
    ENNReal.ofReal (shoelace [a, b, c, d, e]) ≤ volume K := by
  apply Pentagon.bound hK ![a, b, c, d, e]
  intro i
  fin_cases i
  · exact ha
  · exact hb
  · exact hc
  · exact hd
  · exact he

/-- The five-label interface permits repetitions and collinear vertices. -/
theorem shoelace_le_volume_of_length_five {l : List Plane} (hl : l.length = 5)
    {K : Set Plane} (hK : Convex ℝ K) (hmem : ∀ p ∈ l, p ∈ K) :
    ENNReal.ofReal (shoelace l) ≤ volume K := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, _ | ⟨e, l⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hl <;> try omega
  have hnil : l = [] := List.eq_nil_iff_length_eq_zero.mpr (by omega)
  subst l
  exact pentagon_shoelace_le_volume hK
    (hmem a (by simp)) (hmem b (by simp)) (hmem c (by simp))
    (hmem d (by simp)) (hmem e (by simp))

/-- The signed shoelace bound for the convex hull of the five listed points. -/
theorem shoelace_le_convexHull_of_length_five {l : List Plane} (hl : l.length = 5) :
    ENNReal.ofReal (shoelace l) ≤ volume (convexHull ℝ (l.toFinset : Set Plane)) := by
  classical
  exact shoelace_le_volume_of_length_five hl (convex_convexHull ℝ _) (fun p hp =>
    subset_convexHull ℝ _ (List.mem_toFinset.mpr hp))

end MoserWorm
