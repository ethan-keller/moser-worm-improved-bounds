/-
Copyright (c) 2026 Ethan Keller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ethan Keller

Modified for MoserWorm: shared imports, manuscript traversal and centering
identities, and normalization lemmas.
-/
import MoserWorm.Common.Polyline
import MoserWorm.Common.Isometry

open Set MeasureTheory Complex ComplexConjugate
open scoped Real

namespace MoserWorm

noncomputable def crownY : ℝ := Real.sqrt 8745 / 1024

theorem crownY_sq : crownY ^ 2 = 8745 / 1048576 := by
  have h := Real.sq_sqrt (show (0 : ℝ) ≤ 8745 by norm_num)
  dsimp [crownY]
  nlinarith


noncomputable def vertsT : List ℂ :=
  [⟨-(1 / 4), -(Real.sqrt 3 / 12)⟩, ⟨1 / 4, -(Real.sqrt 3 / 12)⟩, ⟨0, Real.sqrt 3 / 6⟩]

/-- Splayed U (`SP`): centered hull vertices (CCW). -/
noncomputable def vertsU : List ℂ :=
  [⟨-(3 + 2 * Real.cos (11 * π / 24) + Real.cos (11 * π / 12)) / 12,
    -(2 * Real.sin (11 * π / 24) + Real.sin (11 * π / 12)) / 12⟩,
   ⟨(1 - 2 * Real.cos (11 * π / 24) - Real.cos (11 * π / 12)) / 12,
    -(2 * Real.sin (11 * π / 24) + Real.sin (11 * π / 12)) / 12⟩,
   ⟨(1 + 2 * Real.cos (11 * π / 24) - Real.cos (11 * π / 12)) / 12,
    (2 * Real.sin (11 * π / 24) - Real.sin (11 * π / 12)) / 12⟩,
   ⟨(1 + 2 * Real.cos (11 * π / 24) + 3 * Real.cos (11 * π / 12)) / 12,
    (2 * Real.sin (11 * π / 24) + 3 * Real.sin (11 * π / 12)) / 12⟩]

/-- Crown `C`, sign `σ = +1`: centered hull vertices (CCW). -/
noncomputable def vertsC : List ℂ :=
  [⟨-(7 / 16), 0⟩, ⟨49 / 128, -crownY⟩, ⟨7 / 16, 0⟩, ⟨-(49 / 128), crownY⟩]

/-- Crown `C`, sign `σ = -1` (mirror crown): centered hull vertices (CCW). -/
noncomputable def vertsCm : List ℂ :=
  [⟨-(7 / 16), 0⟩, ⟨-(49 / 128), -crownY⟩, ⟨7 / 16, 0⟩, ⟨49 / 128, crownY⟩]

private lemma norm_mk (a b : ℝ) : ‖(⟨a, b⟩ : ℂ)‖ = Real.sqrt (a ^ 2 + b ^ 2) := by
  have h : ‖(⟨a, b⟩ : ℂ)‖ ^ 2 = a ^ 2 + b ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_mk]; ring
  rw [← h, Real.sqrt_sq (norm_nonneg _)]


noncomputable def arcSeg : ℝ → ℂ := polyline [⟨-(1 / 2), 0⟩, ⟨1 / 2, 0⟩]
/-- The centered vee in the paper's traversal order. -/
noncomputable def pathT : List ℂ :=
  [⟨-(1 / 4), -(Real.sqrt 3 / 12)⟩, ⟨0, Real.sqrt 3 / 6⟩,
    ⟨1 / 4, -(Real.sqrt 3 / 12)⟩]
noncomputable def arcT : ℝ → ℂ := polyline pathT
/-- The splayed-U arc (path order = hull order). -/
noncomputable def arcU : ℝ → ℂ := polyline vertsU
/-- The `σ = +1` crown arc (zigzag path through the joints). -/
noncomputable def arcC : ℝ → ℂ :=
  polyline [⟨-(7 / 16), 0⟩, ⟨-(49 / 128), crownY⟩, ⟨49 / 128, -crownY⟩, ⟨7 / 16, 0⟩]
/-- The `σ = -1` crown arc. -/
noncomputable def arcCm : ℝ → ℂ :=
  polyline [⟨-(7 / 16), 0⟩, ⟨-(49 / 128), -crownY⟩, ⟨49 / 128, crownY⟩, ⟨7 / 16, 0⟩]

private lemma sub_mk (a b c d : ℝ) : (⟨a, b⟩ : ℂ) - ⟨c, d⟩ = ⟨a - c, b - d⟩ := by
  apply Complex.ext <;> simp

private lemma edist_mk (a b c d : ℝ) :
    edist (⟨a, b⟩ : ℂ) (⟨c, d⟩ : ℂ) =
      ENNReal.ofReal (Real.sqrt ((a - c) ^ 2 + (b - d) ^ 2)) := by
  rw [edist_dist, dist_eq_norm, sub_mk, norm_mk]

/-- **The segment is a unit arc.** -/
theorem isUnitArc_arcSeg : IsUnitArc arcSeg := by
  refine ⟨(polyline_continuous _).continuousOn, ?_⟩
  rw [arcSeg, arcLength_polyline _ (by norm_num)]
  simp only [List.length_cons, List.length_nil]
  rw [show (2 - 1 : ℕ) = 1 from rfl, Finset.sum_range_one]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  rw [edist_mk]
  rw [show (-(1 / 2) - 1 / 2 : ℝ) ^ 2 + ((0 : ℝ) - 0) ^ 2 = 1 ^ 2 by norm_num,
    Real.sqrt_sq (by norm_num)]
  simp [ENNReal.ofReal_one]

/-- **The vee is a unit arc** (two segments of length `1/2`). -/
theorem isUnitArc_arcT : IsUnitArc arcT := by
  have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  refine ⟨(polyline_continuous _).continuousOn, ?_⟩
  rw [arcT, arcLength_polyline _ (by simp [pathT])]
  simp only [pathT, List.length_cons, List.length_nil]
  rw [show (3 - 1 : ℕ) = 2 from rfl, Finset.sum_range_succ, Finset.sum_range_one]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  rw [edist_mk, edist_mk]
  rw [show (-(1 / 4) - 0 : ℝ) ^ 2 +
      (-(Real.sqrt 3 / 12) - Real.sqrt 3 / 6) ^ 2 = (1 / 2) ^ 2 by
        linear_combination h3 / 16,
    show (0 - 1 / 4 : ℝ) ^ 2 +
      (Real.sqrt 3 / 6 - -(Real.sqrt 3 / 12)) ^ 2 = (1 / 2) ^ 2 by
        linear_combination h3 / 16,
    Real.sqrt_sq (by norm_num)]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

/-- **The splayed U is a unit arc** (three segments of length `1/3`). -/
theorem isUnitArc_arcU : IsUnitArc arcU := by
  have h2 := Real.sin_sq_add_cos_sq (11 * π / 24)
  have h3 := Real.sin_sq_add_cos_sq (11 * π / 12)
  refine ⟨(polyline_continuous _).continuousOn, ?_⟩
  rw [arcU, arcLength_polyline _ (by simp [vertsU])]
  simp only [vertsU, List.length_cons, List.length_nil]
  rw [show (4 - 1 : ℕ) = 3 from rfl, Finset.sum_range_succ, Finset.sum_range_succ,
    Finset.sum_range_one]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  rw [edist_mk, edist_mk, edist_mk]
  rw [show (-(3 + 2 * Real.cos (11 * π / 24) + Real.cos (11 * π / 12)) / 12 -
        (1 - 2 * Real.cos (11 * π / 24) - Real.cos (11 * π / 12)) / 12 : ℝ) ^ 2 +
        (-(2 * Real.sin (11 * π / 24) + Real.sin (11 * π / 12)) / 12 -
          -(2 * Real.sin (11 * π / 24) + Real.sin (11 * π / 12)) / 12) ^ 2
        = (1 / 3) ^ 2 by ring,
    show ((1 - 2 * Real.cos (11 * π / 24) - Real.cos (11 * π / 12)) / 12 -
        (1 + 2 * Real.cos (11 * π / 24) - Real.cos (11 * π / 12)) / 12 : ℝ) ^ 2 +
        (-(2 * Real.sin (11 * π / 24) + Real.sin (11 * π / 12)) / 12 -
          (2 * Real.sin (11 * π / 24) - Real.sin (11 * π / 12)) / 12) ^ 2
        = (1 / 3) ^ 2 by linear_combination h2 / 9,
    show ((1 + 2 * Real.cos (11 * π / 24) - Real.cos (11 * π / 12)) / 12 -
        (1 + 2 * Real.cos (11 * π / 24) + 3 * Real.cos (11 * π / 12)) / 12 : ℝ) ^ 2 +
        ((2 * Real.sin (11 * π / 24) - Real.sin (11 * π / 12)) / 12 -
          (2 * Real.sin (11 * π / 24) + 3 * Real.sin (11 * π / 12)) / 12) ^ 2
        = (1 / 3) ^ 2 by linear_combination h3 / 9,
    Real.sqrt_sq (by norm_num)]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num


theorem isUnitArc_arcC : IsUnitArc arcC := by
  refine ⟨(polyline_continuous _).continuousOn, ?_⟩
  rw [arcC, arcLength_polyline _ (by norm_num)]
  simp only [List.length_cons, List.length_nil]
  rw [show (4 - 1 : ℕ) = 3 from rfl, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_one]
  simp only [List.getD_cons_zero, List.getD_cons_succ]
  rw [edist_mk, edist_mk, edist_mk]
  have h := crownY_sq
  rw [show (-(7 / 16) - -(49 / 128) : ℝ) ^ 2 + (0 - crownY) ^ 2 =
      (109 / 1024) ^ 2 by nlinarith,
    show (-(49 / 128) - 49 / 128 : ℝ) ^ 2 + (crownY - -crownY) ^ 2 =
      (806 / 1024) ^ 2 by nlinarith,
    show (49 / 128 - 7 / 16 : ℝ) ^ 2 + (-crownY - 0) ^ 2 =
      (109 / 1024) ^ 2 by nlinarith,
    Real.sqrt_sq (by norm_num), Real.sqrt_sq (by norm_num)]
  rw [← ENNReal.ofReal_add (by norm_num) (by norm_num),
    ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num


private lemma sq3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)

private lemma expT_eq :
    Complex.exp ((π / 3 : ℝ) * Complex.I) = ⟨1 / 2, Real.sqrt 3 / 2⟩ := by
  apply Complex.ext
  · rw [Complex.exp_ofReal_mul_I_re, Real.cos_pi_div_three]
  · rw [Complex.exp_ofReal_mul_I_im, Real.sin_pi_div_three]

private lemma mirrorT0 :
    (starRingEnd ℂ) (⟨-(1 / 4), -(Real.sqrt 3 / 12)⟩ : ℂ) =
      (⟨1 / 2, Real.sqrt 3 / 2⟩ : ℂ) * ⟨0, Real.sqrt 3 / 6⟩ := by
  rw [conj_mk]
  apply Complex.ext
  · simp only [Complex.mul_re]
    linear_combination sq3 / 12
  · simp only [Complex.mul_im]
    ring

private lemma mirrorT1 :
    (starRingEnd ℂ) (⟨1 / 4, -(Real.sqrt 3 / 12)⟩ : ℂ) =
      (⟨1 / 2, Real.sqrt 3 / 2⟩ : ℂ) * ⟨1 / 4, -(Real.sqrt 3 / 12)⟩ := by
  rw [conj_mk]
  apply Complex.ext
  · simp only [Complex.mul_re]
    linear_combination -sq3 / 24
  · simp only [Complex.mul_im]
    ring

private lemma mirrorT2 :
    (starRingEnd ℂ) (⟨0, Real.sqrt 3 / 6⟩ : ℂ) =
      (⟨1 / 2, Real.sqrt 3 / 2⟩ : ℂ) * ⟨-(1 / 4), -(Real.sqrt 3 / 12)⟩ := by
  rw [conj_mk]
  apply Complex.ext
  · simp only [Complex.mul_re]
    linear_combination -sq3 / 24
  · simp only [Complex.mul_im]
    ring

private lemma setT : {z | z ∈ vertsT} =
    ({⟨-(1 / 4), -(Real.sqrt 3 / 12)⟩, ⟨1 / 4, -(Real.sqrt 3 / 12)⟩,
      ⟨0, Real.sqrt 3 / 6⟩} : Set ℂ) := by
  ext z; simp [vertsT]

/-- Conjugation rotates the vee vertex set by `e^{iπ/3}`. -/
theorem conj_image_vertsT :
    (starRingEnd ℂ) '' {z | z ∈ vertsT} =
      (fun v => Complex.exp ((π / 3 : ℝ) * Complex.I) * v) '' {z | z ∈ vertsT} := by
  rw [setT, expT_eq, Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
    Set.image_insert_eq, Set.image_insert_eq, Set.image_singleton,
    mirrorT0, mirrorT1, mirrorT2]
  ext w
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

/-! The splayed U in exponential coordinates: with `ζ = e^{i·11π/24}` the
centered vertices are `q₀ = -(3+2ζ+ζ²)/12`, `q₁ = (1-2ζ-ζ²)/12`,
`q₂ = (1+2ζ-ζ²)/12`, `q₃ = (1+2ζ+3ζ²)/12`, and the mirror algebra reduces to
the single relation `e^{iπ/12}·ζ² = e^{iπ} = -1`. -/

/-- The first splayed-U heading rotation `ζ = e^{i·11π/24}`. -/
noncomputable def zetaU : ℂ := Complex.exp ((11 * π / 24 : ℝ) * Complex.I)

private lemma zetaU_sq : zetaU ^ 2 = Complex.exp ((11 * π / 12 : ℝ) * Complex.I) := by
  rw [zetaU, sq, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma zetaU_ne : zetaU ≠ 0 := Complex.exp_ne_zero _

private lemma vertsU_eq :
    vertsU = [-(3 + 2 * zetaU + zetaU ^ 2) / 12, (1 - 2 * zetaU - zetaU ^ 2) / 12,
      (1 + 2 * zetaU - zetaU ^ 2) / 12, (1 + 2 * zetaU + 3 * zetaU ^ 2) / 12] := by
  have hre : zetaU.re = Real.cos (11 * π / 24) := Complex.exp_ofReal_mul_I_re _
  have him : zetaU.im = Real.sin (11 * π / 24) := Complex.exp_ofReal_mul_I_im _
  have hre2 : (zetaU ^ 2).re = Real.cos (11 * π / 12) := by
    rw [zetaU_sq]; exact Complex.exp_ofReal_mul_I_re _
  have him2 : (zetaU ^ 2).im = Real.sin (11 * π / 12) := by
    rw [zetaU_sq]; exact Complex.exp_ofReal_mul_I_im _
  simp only [vertsU, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · rw [eq_div_iff (by norm_num : (12 : ℂ) ≠ 0)]
      apply Complex.ext <;>
        simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
          Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
          Complex.one_re, Complex.one_im, Complex.re_ofNat, Complex.im_ofNat,
          hre, him, hre2, him2] <;>
        ring

private lemma huzU :
    Complex.exp ((π / 12 : ℝ) * Complex.I) * zetaU ^ 2 = -1 := by
  rw [zetaU_sq, ← Complex.exp_add,
    show ((π / 12 : ℝ) : ℂ) * Complex.I + ((11 * π / 12 : ℝ) : ℂ) * Complex.I =
      (π : ℂ) * Complex.I by push_cast; ring]
  exact Complex.exp_pi_mul_I

private lemma conj_zetaU :
    (starRingEnd ℂ) zetaU = -(Complex.exp ((π / 12 : ℝ) * Complex.I) * zetaU) := by
  have h1 : (starRingEnd ℂ) zetaU * zetaU = 1 := by
    rw [zetaU, conj_exp_mul_I, ← Complex.exp_add,
      show ((-(11 * π / 24) : ℝ) : ℂ) * Complex.I + ((11 * π / 24 : ℝ) : ℂ) * Complex.I =
        0 by push_cast; ring]
    exact Complex.exp_zero
  have h2 : -(Complex.exp ((π / 12 : ℝ) * Complex.I) * zetaU) * zetaU = 1 := by
    linear_combination -huzU
  exact mul_right_cancel₀ zetaU_ne (h1.trans h2.symm)

private lemma mirrorU0 :
    (starRingEnd ℂ) (-(3 + 2 * zetaU + zetaU ^ 2) / 12) =
      Complex.exp ((π / 12 : ℝ) * Complex.I) * ((1 + 2 * zetaU + 3 * zetaU ^ 2) / 12) := by
  simp only [map_div₀, map_neg, map_add, map_mul, map_pow, map_ofNat]
  rw [conj_zetaU]
  linear_combination (-(Complex.exp ((π / 12 : ℝ) * Complex.I) + 3) / 12) * huzU

private lemma mirrorU1 :
    (starRingEnd ℂ) ((1 - 2 * zetaU - zetaU ^ 2) / 12) =
      Complex.exp ((π / 12 : ℝ) * Complex.I) * ((1 + 2 * zetaU - zetaU ^ 2) / 12) := by
  simp only [map_div₀, map_sub, map_mul, map_pow, map_ofNat, map_one]
  rw [conj_zetaU]
  linear_combination ((1 - Complex.exp ((π / 12 : ℝ) * Complex.I)) / 12) * huzU

private lemma mirrorU2 :
    (starRingEnd ℂ) ((1 + 2 * zetaU - zetaU ^ 2) / 12) =
      Complex.exp ((π / 12 : ℝ) * Complex.I) * ((1 - 2 * zetaU - zetaU ^ 2) / 12) := by
  simp only [map_div₀, map_sub, map_add, map_mul, map_pow, map_ofNat, map_one]
  rw [conj_zetaU]
  linear_combination ((1 - Complex.exp ((π / 12 : ℝ) * Complex.I)) / 12) * huzU

private lemma mirrorU3 :
    (starRingEnd ℂ) ((1 + 2 * zetaU + 3 * zetaU ^ 2) / 12) =
      Complex.exp ((π / 12 : ℝ) * Complex.I) * (-(3 + 2 * zetaU + zetaU ^ 2) / 12) := by
  simp only [map_div₀, map_add, map_mul, map_pow, map_ofNat, map_one]
  rw [conj_zetaU]
  linear_combination ((3 * Complex.exp ((π / 12 : ℝ) * Complex.I) + 1) / 12) * huzU

private lemma setU : {z | z ∈ vertsU} =
    ({-(3 + 2 * zetaU + zetaU ^ 2) / 12, (1 - 2 * zetaU - zetaU ^ 2) / 12,
      (1 + 2 * zetaU - zetaU ^ 2) / 12, (1 + 2 * zetaU + 3 * zetaU ^ 2) / 12} : Set ℂ) := by
  ext z; simp [vertsU_eq]

/-- Conjugation rotates the splayed-U vertex set by `e^{iπ/12}`. -/
theorem conj_image_vertsU :
    (starRingEnd ℂ) '' {z | z ∈ vertsU} =
      (fun v => Complex.exp ((π / 12 : ℝ) * Complex.I) * v) '' {z | z ∈ vertsU} := by
  rw [setU, Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq,
    Set.image_singleton, Set.image_insert_eq, Set.image_insert_eq,
    Set.image_insert_eq, Set.image_singleton, mirrorU0, mirrorU1, mirrorU2, mirrorU3]
  ext w
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

private lemma neg_mk (a b : ℝ) : -(⟨a, b⟩ : ℂ) = ⟨-a, -b⟩ := by
  apply Complex.ext <;> simp

private lemma setCp : {z | z ∈ vertsC} =
    ({⟨-(7 / 16), 0⟩, ⟨49 / 128, -crownY⟩, ⟨7 / 16, 0⟩, ⟨-(49 / 128), crownY⟩} : Set ℂ) := by
  ext z; simp [vertsC]

private lemma setCm : {z | z ∈ vertsCm} =
    ({⟨-(7 / 16), 0⟩, ⟨-(49 / 128), -crownY⟩, ⟨7 / 16, 0⟩, ⟨49 / 128, crownY⟩} : Set ℂ) := by
  ext z; simp [vertsCm]

/-- The crown vertex set is centrally symmetric. -/
theorem neg_image_vertsC :
    (fun v : ℂ => -v) '' {z | z ∈ vertsC} = {z | z ∈ vertsC} := by
  rw [setCp, Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq,
    Set.image_singleton, neg_mk, neg_mk, neg_mk, neg_mk]
  ext w
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, neg_neg, neg_zero]
  constructor
  · rintro (rfl | rfl | rfl | rfl) <;> simp
  · rintro (rfl | rfl | rfl | rfl) <;> simp

/-- Conjugation exchanges the two crown vertex sets. -/
theorem conj_image_vertsC :
    (starRingEnd ℂ) '' {z | z ∈ vertsC} = {z | z ∈ vertsCm} := by
  rw [setCp, setCm, Set.image_insert_eq, Set.image_insert_eq, Set.image_insert_eq,
    Set.image_singleton, conj_mk, conj_mk, conj_mk, conj_mk]
  ext w
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, neg_neg, neg_zero]
  tauto

noncomputable def vertsL : List ℂ := [⟨-(1 / 2), 0⟩, ⟨1 / 2, 0⟩]

noncomputable def pathC : List ℂ :=
  [⟨-(7 / 16), 0⟩, ⟨-(49 / 128), crownY⟩, ⟨49 / 128, -crownY⟩, ⟨7 / 16, 0⟩]

/-- The paper's vertex-average centers before centering. -/
noncomputable def centerT : ℂ := ⟨0, Real.sqrt 3 / 12⟩
noncomputable def centerU : ℂ :=
  ⟨(3 + 2 * Real.cos (11 * π / 24) + Real.cos (11 * π / 12)) / 12,
    (2 * Real.sin (11 * π / 24) + Real.sin (11 * π / 12)) / 12⟩
noncomputable def centerC : ℂ := 7 / 16

/-- Exact uncentered vertex lists in the paper's curve traversal order. -/
noncomputable def paperVertsT : List ℂ :=
  [⟨-(1 / 4), 0⟩, ⟨0, Real.sqrt 3 / 4⟩, ⟨1 / 4, 0⟩]
noncomputable def paperVertsU : List ℂ :=
  [0, 1 / 3,
    ⟨(1 + Real.cos (11 * π / 24)) / 3, Real.sin (11 * π / 24) / 3⟩,
    ⟨(1 + Real.cos (11 * π / 24) + Real.cos (11 * π / 12)) / 3,
      (Real.sin (11 * π / 24) + Real.sin (11 * π / 12)) / 3⟩]
noncomputable def paperVertsC : List ℂ :=
  [0, ⟨7 / 128, crownY⟩, ⟨105 / 128, -crownY⟩, 7 / 8]

theorem pathT_add_center : pathT.map (fun z => z + centerT) = paperVertsT := by
  simp only [pathT, paperVertsT, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_⟩ <;> apply Complex.ext <;> simp [centerT]
  ring

theorem vertsU_add_center : vertsU.map (fun z => z + centerU) = paperVertsU := by
  simp only [vertsU, paperVertsU, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply Complex.ext <;> simp [centerU] <;> ring

theorem pathC_add_center : pathC.map (fun z => z + centerC) = paperVertsC := by
  simp only [pathC, paperVertsC, List.map_cons, List.map_nil, List.cons.injEq, and_true]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> (apply Complex.ext <;> norm_num [centerC])

theorem isUnitArc_paperT : IsUnitArc (polyline paperVertsT) := by
  rw [← pathT_add_center]
  exact isUnitArc_polyline_map_add pathT (by norm_num [pathT]) centerT isUnitArc_arcT

theorem isUnitArc_paperU : IsUnitArc (polyline paperVertsU) := by
  rw [← vertsU_add_center]
  exact isUnitArc_polyline_map_add vertsU (by norm_num [vertsU]) centerU isUnitArc_arcU

theorem isUnitArc_paperC : IsUnitArc (polyline paperVertsC) := by
  rw [← pathC_add_center]
  exact isUnitArc_polyline_map_add pathC (by norm_num [pathC]) centerC isUnitArc_arcC

theorem pathT_vertexSet : {z | z ∈ pathT} = {z | z ∈ vertsT} := by
  ext z
  simp only [pathT, vertsT, List.mem_cons, List.not_mem_nil, or_false, mem_ofPred_eq]
  tauto

theorem pathC_vertexSet : {z | z ∈ pathC} = {z | z ∈ vertsC} := by
  ext z
  simp only [pathC, vertsC, List.mem_cons, List.not_mem_nil, or_false, mem_ofPred_eq]
  tauto

theorem convexHull_trace_arcSeg :
    convexHull ℝ (trace arcSeg) = convexHull ℝ {z | z ∈ vertsL} :=
  convexHull_trace_polyline vertsL (by norm_num [vertsL])

theorem convexHull_trace_arcT :
    convexHull ℝ (trace arcT) = convexHull ℝ {z | z ∈ vertsT} := by
  rw [arcT, convexHull_trace_polyline _ (by norm_num [pathT]), pathT_vertexSet]

theorem convexHull_trace_arcU :
    convexHull ℝ (trace arcU) = convexHull ℝ {z | z ∈ vertsU} :=
  convexHull_trace_polyline _ (by norm_num [vertsU])

theorem convexHull_trace_arcC :
    convexHull ℝ (trace arcC) = convexHull ℝ {z | z ∈ vertsC} := by
  change convexHull ℝ (trace (polyline pathC)) = _
  rw [convexHull_trace_polyline _ (by norm_num [pathC]), pathC_vertexSet]

theorem vertsT_sum : vertsT.sum = 0 := by
  apply Complex.ext <;> simp [vertsT]
  ring

theorem vertsU_sum : vertsU.sum = 0 := by
  apply Complex.ext <;> simp [vertsU] <;> ring

theorem vertsC_sum : vertsC.sum = 0 := by
  apply Complex.ext <;> simp [vertsC]

theorem rotationSet_vertsT_period :
    rotationSet (2 * π / 3) {z | z ∈ vertsT} = {z | z ∈ vertsT} := by
  have he : Complex.exp ((2 * π / 3 : ℝ) * Complex.I) =
      (⟨-(1 / 2), Real.sqrt 3 / 2⟩ : ℂ) := by
    rw [show (2 * π / 3 : ℝ) = π / 3 + π / 3 by ring, exp_add_mul_I, expT_eq]
    apply Complex.ext <;> simp only [Complex.mul_re, Complex.mul_im] <;> nlinarith [sq3]
  have h0 : (⟨-(1 / 2), Real.sqrt 3 / 2⟩ : ℂ) *
      ⟨-(1 / 4), -(Real.sqrt 3 / 12)⟩ = ⟨1 / 4, -(Real.sqrt 3 / 12)⟩ := by
    apply Complex.ext <;> simp only [Complex.mul_re, Complex.mul_im] <;> nlinarith [sq3]
  have h1 : (⟨-(1 / 2), Real.sqrt 3 / 2⟩ : ℂ) *
      ⟨1 / 4, -(Real.sqrt 3 / 12)⟩ = ⟨0, Real.sqrt 3 / 6⟩ := by
    apply Complex.ext <;> simp only [Complex.mul_re, Complex.mul_im] <;> nlinarith [sq3]
  have h2 : (⟨-(1 / 2), Real.sqrt 3 / 2⟩ : ℂ) *
      ⟨0, Real.sqrt 3 / 6⟩ = ⟨-(1 / 4), -(Real.sqrt 3 / 12)⟩ := by
    apply Complex.ext <;> simp only [Complex.mul_re, Complex.mul_im] <;> nlinarith [sq3]
  rw [rotationSet, setT, he, Set.image_insert_eq, Set.image_insert_eq,
    Set.image_singleton, h0, h1, h2]
  ext z
  simp only [mem_insert_iff, mem_singleton_iff]
  tauto

theorem rotationSet_vertsC_period :
    rotationSet π {z | z ∈ vertsC} = {z | z ∈ vertsC} := by
  simpa [rotationSet, Complex.exp_pi_mul_I] using neg_image_vertsC

noncomputable def familyArcs : Fin 4 → ℝ → ℂ := ![arcSeg, arcT, arcU, arcC]
noncomputable def familyVertexLists : Fin 4 → List ℂ := ![vertsL, vertsT, vertsU, vertsC]

theorem familyArcs_unit (i : Fin 4) : IsUnitArc (familyArcs i) := by
  fin_cases i
  · exact isUnitArc_arcSeg
  · exact isUnitArc_arcT
  · exact isUnitArc_arcU
  · exact isUnitArc_arcC

theorem familyArcs_hull (i : Fin 4) :
    convexHull ℝ (trace (familyArcs i)) = convexHull ℝ {z | z ∈ familyVertexLists i} := by
  fin_cases i
  · exact convexHull_trace_arcSeg
  · exact convexHull_trace_arcT
  · exact convexHull_trace_arcU
  · exact convexHull_trace_arcC

/-- The four traces in the manuscript's uncentered coordinates. -/
noncomputable def paperFamilyArcs : Fin 4 → ℝ → ℂ :=
  ![arcSeg, polyline paperVertsT, polyline paperVertsU, polyline paperVertsC]

noncomputable def familyCenters : Fin 4 → ℂ := ![0, centerT, centerU, centerC]

theorem paperFamilyArcs_eq_translate (i : Fin 4) :
    paperFamilyArcs i = ⇑(IsometryEquiv.addRight (familyCenters i)) ∘ familyArcs i := by
  fin_cases i
  · funext t
    change arcSeg t = arcSeg t + 0
    simp
  · change polyline paperVertsT = ⇑(IsometryEquiv.addRight centerT) ∘ polyline pathT
    rw [← pathT_add_center]
    funext t
    exact polyline_map_add pathT (by norm_num [pathT]) centerT t
  · change polyline paperVertsU = ⇑(IsometryEquiv.addRight centerU) ∘ polyline vertsU
    rw [← vertsU_add_center]
    funext t
    exact polyline_map_add vertsU (by norm_num [vertsU]) centerU t
  · change polyline paperVertsC = ⇑(IsometryEquiv.addRight centerC) ∘ polyline pathC
    rw [← pathC_add_center]
    funext t
    exact polyline_map_add pathC (by norm_num [pathC]) centerC t

theorem paperFamilyArcs_unit (i : Fin 4) : IsUnitArc (paperFamilyArcs i) := by
  rw [paperFamilyArcs_eq_translate]
  exact isUnitArc_isometry _ _ (familyArcs_unit i)

end MoserWorm
