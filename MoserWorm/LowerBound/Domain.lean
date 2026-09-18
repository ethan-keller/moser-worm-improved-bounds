import MoserWorm.LowerBound.Placement
import MoserWorm.Common.Area
import MoserWorm.Common.Box.Sound
import MoserWorm.Common.Interval.Rational
import MoserWorm.LowerBound.Certificate.RootBasic

open Set MeasureTheory Complex
open scoped ENNReal

namespace MoserWorm

noncomputable section

def tau : ℝ := 239 / 1000
noncomputable def translationX : ℝ := 8 * tau / Real.sqrt 3 - 1 / 2
def translationY : ℝ := 2 * tau
def outerX : ℝ := 603894 / 1000000
def outerY : ℝ := 478 / 1000

theorem translationY_eq_outerY : translationY = outerY := by
  norm_num [translationY, outerY, tau]

theorem translationX_lt_outerX : translationX < outerX := by
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  have hsq : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hl : (173205 / 100000 : ℝ) < Real.sqrt 3 := by nlinarith
  unfold translationX outerX tau
  apply (sub_lt_iff_lt_add).2
  apply (div_lt_iff₀ hs).2
  nlinarith

private theorem cross_convex_combination (u p x y : ℂ) (a b : ℝ) (hab : a + b = 1) :
    cross u (a • x + b • y - p) =
      a * cross u (x - p) + b * cross u (y - p) := by
  simp only [cross_apply, Complex.sub_re, Complex.sub_im, Complex.add_re,
    Complex.add_im, Complex.smul_re, Complex.smul_im, smul_eq_mul]
  linear_combination (u.re * p.im - u.im * p.re) * hab

private theorem convex_cross_nonneg (u p : ℂ) :
    Convex ℝ {z : ℂ | 0 ≤ cross u (z - p)} := by
  intro x hx y hy a b ha hb hab
  change 0 ≤ cross u (a • x + b • y - p)
  rw [cross_convex_combination _ _ _ _ _ _ hab]
  exact add_nonneg (mul_nonneg ha hx) (mul_nonneg hb hy)

private theorem convex_cross_nonpos (u p : ℂ) :
    Convex ℝ {z : ℂ | cross u (z - p) ≤ 0} := by
  intro x hx y hy a b ha hb hab
  change cross u (a • x + b • y - p) ≤ 0
  rw [cross_convex_combination _ _ _ _ _ _ hab]
  exact add_nonpos (mul_nonpos_of_nonneg_of_nonpos ha hx)
    (mul_nonpos_of_nonneg_of_nonpos hb hy)

private theorem triangle_subset {K : Set ℂ} (hK : Convex ℝ K)
    {a b c : ℂ} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) :
    convexHull ℝ ({a, b, c} : Set ℂ) ⊆ K := by
  apply convexHull_min _ hK
  intro z hz
  simp only [mem_insert_iff, mem_singleton_iff] at hz
  rcases hz with rfl | rfl | rfl <;> assumption

private theorem triangle_compact (a b c : ℂ) :
    IsCompact (convexHull ℝ ({a, b, c} : Set ℂ)) :=
  (((finite_singleton c).insert b).insert a).isCompact_convexHull ℝ

/-- Two triangles on opposite sides of a common chord have additive area. -/
theorem opposite_triangles_area_le {K : Set ℂ} (hK : Convex ℝ K)
    {a b c d : ℂ} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) (hd : d ∈ K)
    (hab : b - a ≠ 0)
    (hpos : 0 ≤ cross (b - a) (c - a)) (hneg : cross (b - a) (d - a) ≤ 0) :
    ENNReal.ofReal ((cross (b - a) (c - a) - cross (b - a) (d - a)) / 2)
      ≤ volume K := by
  let S := convexHull ℝ ({a, b, c} : Set ℂ)
  let T := convexHull ℝ ({a, b, d} : Set ℂ)
  have hS : S ⊆ {z : ℂ | 0 ≤ cross (b - a) (z - a)} := by
    apply triangle_subset (convex_cross_nonneg _ _)
    · simp [cross]
    · change 0 ≤ cross (b - a) (b - a)
      rw [cross_self]
    · exact hpos
  have hT : T ⊆ {z : ℂ | cross (b - a) (z - a) ≤ 0} := by
    apply triangle_subset (convex_cross_nonpos _ _)
    · simp [cross]
    · change cross (b - a) (b - a) ≤ 0
      rw [cross_self]
    · exact hneg
  have hinter : S ∩ T ⊆ {z : ℂ | cross (b - a) (z - a) = 0} := by
    intro z hz
    exact le_antisymm (hT hz.2) (hS hz.1)
  have hnull : volume (S ∩ T) = 0 :=
    measure_mono_null hinter (volume_cross_line (b - a) a hab)
  have harea : volume (S ∪ T) = volume S + volume T :=
    measure_union₀ (triangle_compact a b d).measurableSet.nullMeasurableSet hnull
  have hsub : S ∪ T ⊆ K :=
    union_subset (triangle_subset hK ha hb hc) (triangle_subset hK ha hb hd)
  have h : volume (S ∪ T) ≤ volume K := measure_mono hsub
  rw [harea, show volume S = _ from volume_triangle a b c,
    show volume T = _ from volume_triangle a b d,
    abs_of_nonneg hpos, abs_of_nonpos hneg,
    ← ENNReal.ofReal_add (div_nonneg hpos (by norm_num))
      (div_nonneg (neg_nonneg.2 hneg) (by norm_num))] at h
  convert h using 1
  congr 1
  ring

/-- Chord/extent bound in determinant form. No position relative to the chord
is assumed for the two points measuring the perpendicular extent. -/
theorem chord_cross_bound {K : Set ℂ} (hK : Convex ℝ K)
    {a b c d : ℂ} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) (hd : d ∈ K) :
    ENNReal.ofReal (|cross (b - a) (c - d)| / 2) ≤ volume K := by
  by_cases hab : b - a = 0
  · simp [hab, cross]
  have he : cross (b - a) (c - d) =
      cross (b - a) (c - a) - cross (b - a) (d - a) := by
    simp only [cross_apply, Complex.sub_re, Complex.sub_im]
    ring
  rw [he]
  by_cases hpos : 0 ≤ cross (b - a) (c - a)
  · by_cases hneg : cross (b - a) (d - a) ≤ 0
    · rw [abs_of_nonneg (sub_nonneg.2 (hneg.trans hpos))]
      exact opposite_triangles_area_le hK ha hb hc hd hab hpos hneg
    · have hdp : 0 ≤ cross (b - a) (d - a) := (lt_of_not_ge hneg).le
      by_cases hcd : cross (b - a) (d - a) ≤ cross (b - a) (c - a)
      · refine (ENNReal.ofReal_le_ofReal ?_).trans (triangle_area_le_volume hK ha hb hc)
        rw [abs_of_nonneg (sub_nonneg.2 hcd), abs_of_nonneg hpos]
        linarith
      · refine (ENNReal.ofReal_le_ofReal ?_).trans (triangle_area_le_volume hK ha hb hd)
        rw [abs_of_nonpos (sub_nonpos.2 (le_of_not_ge hcd)), abs_of_nonneg hdp]
        linarith
  · have hcn : cross (b - a) (c - a) ≤ 0 := (lt_of_not_ge hpos).le
    by_cases hdp : 0 ≤ cross (b - a) (d - a)
    · rw [abs_of_nonpos (sub_nonpos.2 (hcn.trans hdp))]
      convert opposite_triangles_area_le hK ha hb hd hc hab hdp hcn using 1
      congr 1
      ring
    · have hdn : cross (b - a) (d - a) ≤ 0 := (lt_of_not_ge hdp).le
      by_cases hcd : cross (b - a) (d - a) ≤ cross (b - a) (c - a)
      · refine (ENNReal.ofReal_le_ofReal ?_).trans (triangle_area_le_volume hK ha hb hd)
        rw [abs_of_nonneg (sub_nonneg.2 hcd), abs_of_nonpos hdn]
        linarith
      · refine (ENNReal.ofReal_le_ofReal ?_).trans (triangle_area_le_volume hK ha hb hc)
        rw [abs_of_nonpos (sub_nonpos.2 (le_of_not_ge hcd)), abs_of_nonpos hcn]
        linarith

theorem triangle_shoelace_eq (a b c : ℂ) :
    shoelace [a, b, c] = cross (b - a) (c - a) / 2 := by
  norm_num [shoelace, Finset.sum_range_succ, cross]
  ring

theorem quadrilateral_shoelace_eq (a b c d : ℂ) :
    shoelace [a, b, c, d] = cross (c - a) (d - b) / 2 := by
  norm_num [shoelace, Finset.sum_range_succ, cross]
  ring

/-- Three-point signed shoelace bounds require no fan-validity test. -/
theorem triangle_shoelace_le_volume {K : Set ℂ} (hK : Convex ℝ K)
    {a b c : ℂ} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) :
    ENNReal.ofReal (shoelace [a, b, c]) ≤ volume K := by
  rw [triangle_shoelace_eq]
  exact (ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right (le_abs_self _) (by norm_num))).trans
    (triangle_area_le_volume hK ha hb hc)

/-- Any ordered four points in a convex set give a signed shoelace lower
bound, even for a crossed or degenerate quadrilateral. -/
theorem quadrilateral_shoelace_le_volume {K : Set ℂ} (hK : Convex ℝ K)
    {a b c d : ℂ} (ha : a ∈ K) (hb : b ∈ K) (hc : c ∈ K) (hd : d ∈ K) :
    ENNReal.ofReal (shoelace [a, b, c, d]) ≤ volume K := by
  rw [quadrilateral_shoelace_eq]
  exact (ENNReal.ofReal_le_ofReal
    (div_le_div_of_nonneg_right (le_abs_self _) (by norm_num))).trans
    (chord_cross_bound hK ha hc hd hb)

/-- Perpendicular projection width of a compact set relative to a nonzero
chord. Dividing the determinant by the chord length gives unit projection. -/
def perpendicularExtent (a b : ℂ) (S : Set ℂ) : ℝ :=
  (sSup ((fun z => cross (b - a) (z - a)) '' S) -
    sInf ((fun z => cross (b - a) (z - a)) '' S)) / ‖b - a‖

/-- The manuscript's compact-set chord lemma, including one-sided extents. -/
theorem chord_bound {K S : Set ℂ} (hK : Convex ℝ K)
    {a b : ℂ} (ha : a ∈ K) (hb : b ∈ K) (hab : b - a ≠ 0)
    (hS : IsCompact S) (hne : S.Nonempty) (hSK : S ⊆ K) :
    ENNReal.ofReal (‖b - a‖ * perpendicularExtent a b S / 2) ≤ volume K := by
  let f : ℂ → ℝ := fun z => cross (b - a) (z - a)
  have hf : Continuous f := by unfold f cross; fun_prop
  obtain ⟨c, hc, hmax⟩ := hS.exists_isMaxOn hne hf.continuousOn
  obtain ⟨d, hd, hmin⟩ := hS.exists_isMinOn hne hf.continuousOn
  have hgreat : IsGreatest (f '' S) (f c) := by
    refine ⟨⟨c, hc, rfl⟩, ?_⟩
    rintro y ⟨z, hz, rfl⟩
    exact hmax hz
  have hleast : IsLeast (f '' S) (f d) := by
    refine ⟨⟨d, hd, rfl⟩, ?_⟩
    rintro y ⟨z, hz, rfl⟩
    exact hmin hz
  have he : cross (b - a) (c - d) = f c - f d := by
    simp only [f, cross_apply, Complex.sub_re, Complex.sub_im]
    ring
  have h := chord_cross_bound hK ha hb (hSK hc) (hSK hd)
  rw [he, abs_of_nonneg (sub_nonneg.2 (hmax hd))] at h
  have hn : ‖b - a‖ ≠ 0 := norm_ne_zero_iff.2 hab
  convert h using 1
  congr 1
  change ‖b - a‖ * ((sSup (f '' S) - sInf (f '' S)) / ‖b - a‖) / 2 =
    (f c - f d) / 2
  rw [hgreat.csSup_eq, hleast.csInf_eq]
  field_simp

private theorem triangle_width_inequality (x y n : ℝ) (hn : 0 ≤ n)
    (hnorm : n ^ 2 = x ^ 2 + y ^ 2) :
    Real.sqrt 3 * n ≤ 2 * |y| ∨
      Real.sqrt 3 * n ≤ |Real.sqrt 3 * x - y| ∨
      Real.sqrt 3 * n ≤ |Real.sqrt 3 * x + y| := by
  have hs : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hs2 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  have hsn : (Real.sqrt 3 * n) ^ 2 = 3 * n ^ 2 := by rw [mul_pow, hs2]
  have hsx : (Real.sqrt 3 * |x|) ^ 2 = 3 * x ^ 2 := by rw [mul_pow, hs2, sq_abs]
  by_cases hy : Real.sqrt 3 * n ≤ 2 * |y|
  · exact Or.inl hy
  have hysq : (2 * |y|) ^ 2 ≤ (Real.sqrt 3 * n) ^ 2 :=
    (sq_le_sq₀ (by positivity) (mul_nonneg hs hn)).2 (le_of_not_ge hy)
  have hxy : |y| ≤ Real.sqrt 3 * |x| := by
    apply (sq_le_sq₀ (abs_nonneg y) (by positivity)).1
    rw [hsx, sq_abs]
    nlinarith [sq_abs y]
  have hsum : Real.sqrt 3 * n ≤ Real.sqrt 3 * |x| + |y| := by
    apply (sq_le_sq₀ (mul_nonneg hs hn) (by positivity)).1
    have hp := mul_nonneg (abs_nonneg y) (sub_nonneg.2 hxy)
    nlinarith [sq_abs y]
  rcases le_total 0 x with hx | hx
  · rcases le_total 0 y with hy | hy
    · right; right
      calc
        Real.sqrt 3 * n ≤ Real.sqrt 3 * |x| + |y| := hsum
        _ = Real.sqrt 3 * x + y := by rw [abs_of_nonneg hx, abs_of_nonneg hy]
        _ ≤ |Real.sqrt 3 * x + y| := le_abs_self _
    · right; left
      calc
        Real.sqrt 3 * n ≤ Real.sqrt 3 * |x| + |y| := hsum
        _ = Real.sqrt 3 * x - y := by rw [abs_of_nonneg hx, abs_of_nonpos hy]; ring
        _ ≤ |Real.sqrt 3 * x - y| := le_abs_self _
  · rcases le_total 0 y with hy | hy
    · right; left
      calc
        Real.sqrt 3 * n ≤ Real.sqrt 3 * |x| + |y| := hsum
        _ = -(Real.sqrt 3 * x - y) := by rw [abs_of_nonpos hx, abs_of_nonneg hy]; ring
        _ ≤ |Real.sqrt 3 * x - y| := neg_le_abs _
    · right; right
      calc
        Real.sqrt 3 * n ≤ Real.sqrt 3 * |x| + |y| := hsum
        _ = -(Real.sqrt 3 * x + y) := by rw [abs_of_nonpos hx, abs_of_nonpos hy]; ring
        _ ≤ |Real.sqrt 3 * x + y| := neg_le_abs _

/-- The equilateral triangle has width at least √3/4 in every direction,
stated homogeneously so no division by a possibly zero direction is needed. -/
theorem triangle_cross_width (u : ℂ) :
    ∃ v ∈ vertsT, ∃ w ∈ vertsT,
      Real.sqrt 3 * ‖u‖ / 4 ≤ |cross u (v - w)| := by
  have hn : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, pow_two]
  rcases triangle_width_inequality u.re u.im ‖u‖ (norm_nonneg _) hn with h | h | h
  · refine ⟨⟨1 / 4, -(Real.sqrt 3 / 12)⟩, by simp [vertsT],
      ⟨-(1 / 4), -(Real.sqrt 3 / 12)⟩, by simp [vertsT], ?_⟩
    have he : cross u (⟨1 / 4, -(Real.sqrt 3 / 12)⟩ -
        (⟨-(1 / 4), -(Real.sqrt 3 / 12)⟩ : ℂ)) = -u.im / 2 := by
      simp only [cross_apply, Complex.sub_re, Complex.sub_im]; ring
    rw [he, abs_div, abs_neg]
    norm_num
    linarith
  · refine ⟨⟨0, Real.sqrt 3 / 6⟩, by simp [vertsT],
      ⟨-(1 / 4), -(Real.sqrt 3 / 12)⟩, by simp [vertsT], ?_⟩
    have he : cross u (⟨0, Real.sqrt 3 / 6⟩ -
        (⟨-(1 / 4), -(Real.sqrt 3 / 12)⟩ : ℂ)) =
        (Real.sqrt 3 * u.re - u.im) / 4 := by
      simp only [cross_apply, Complex.sub_re, Complex.sub_im]; ring
    rw [he, abs_div]
    norm_num
    linarith
  · refine ⟨⟨0, Real.sqrt 3 / 6⟩, by simp [vertsT],
      ⟨1 / 4, -(Real.sqrt 3 / 12)⟩, by simp [vertsT], ?_⟩
    have he : cross u (⟨0, Real.sqrt 3 / 6⟩ -
        (⟨1 / 4, -(Real.sqrt 3 / 12)⟩ : ℂ)) =
        (Real.sqrt 3 * u.re + u.im) / 4 := by
      simp only [cross_apply, Complex.sub_re, Complex.sub_im]; ring
    rw [he, abs_div]
    norm_num
    linarith

theorem placed_triangle_cross_width (p : Placement) (u : ℂ) :
    ∃ v ∈ placementHull p, ∃ w ∈ placementHull p,
      Real.sqrt 3 * ‖u‖ / 4 ≤ |cross u (v - w)| := by
  let r := Complex.exp (p.angle 0 * Complex.I)
  obtain ⟨v, hv, w, hw, hh⟩ := triangle_cross_width ((starRingEnd ℂ) r * u)
  refine ⟨placeVertex p 0 v, placeVertex_mem_placementHull p 0 hv,
    placeVertex p 0 w, placeVertex_mem_placementHull p 0 hw, ?_⟩
  have hnorm : ‖(starRingEnd ℂ) r * u‖ = ‖u‖ := by
    simp [r]
  have he : cross u (placeVertex p 0 v - placeVertex p 0 w) =
      cross ((starRingEnd ℂ) r * u) (v - w) := by
    simp only [placeVertex, cross_apply, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
      Complex.conj_re, Complex.conj_im, r]
    ring
  rw [he]
  rw [hnorm] at hh
  exact hh

/-- Diameter estimate, stated for every chord to avoid an attainment premise. -/
theorem placement_chord_norm_bound (p : Placement) {a b : ℂ}
    (ha : a ∈ placementHull p) (hb : b ∈ placementHull p) :
    ‖b - a‖ ≤ 8 * placementArea p / Real.sqrt 3 := by
  obtain ⟨v, hv, w, hw, hh⟩ := placed_triangle_cross_width p (b - a)
  have he := chord_cross_bound (placementHull_convex p) ha hb hv hw
  have hreal := (ENNReal.ofReal_le_iff_le_toReal (placementVolume_ne_top p)).1 he
  have hs : 0 < Real.sqrt 3 := Real.sqrt_pos.2 (by norm_num)
  apply (le_div_iff₀ hs).2
  change |cross (b - a) (v - w)| / 2 ≤ placementArea p at hreal
  nlinarith

theorem placement_translation_estimate (p : Placement) (i : Fin 3) :
    |(p.translation i).re| + 1 / 2 ≤ 8 * placementArea p / Real.sqrt 3 ∧
      |(p.translation i).im| ≤ 2 * placementArea p := by
  have he := endpoint_mem_placementHull p
  have ht := translation_mem_placementHull p i
  constructor
  · by_cases hx : 0 ≤ (p.translation i).re
    · have hn := placement_chord_norm_bound p he.1 ht
      rw [sub_neg_eq_add] at hn
      have hr := (le_abs_self (p.translation i - (-(1 / 2) : ℂ)).re).trans
        (Complex.abs_re_le_norm _)
      rw [abs_of_nonneg hx]
      norm_num at hr
      linarith
    · have hn := placement_chord_norm_bound p he.2 ht
      have hr := (neg_le_abs (p.translation i - (1 / 2 : ℂ)).re).trans
        (Complex.abs_re_le_norm _)
      rw [abs_of_nonpos (le_of_not_ge hx)]
      norm_num at hr
      linarith
  · have h := triangle_area_le_volume (placementHull_convex p) he.1 he.2 ht
    have hc : cross ((1 / 2 : ℂ) - (-(1 / 2) : ℂ))
        (p.translation i - (-(1 / 2) : ℂ)) = (p.translation i).im := by
      norm_num [cross]
    rw [hc] at h
    have hr := (ENNReal.ofReal_le_iff_le_toReal (placementVolume_ne_top p)).1 h
    change |(p.translation i).im| / 2 ≤ placementArea p at hr
    linarith

def TranslationBounds (p : Placement) : Prop :=
  ∀ i, |(p.translation i).re| ≤ translationX ∧ |(p.translation i).im| ≤ translationY

def OuterTranslationBounds (p : Placement) : Prop :=
  ∀ i, |(p.translation i).re| ≤ outerX ∧ |(p.translation i).im| ≤ outerY

def InLowerDomain (p : Placement) : Prop := AnglesNormalized p ∧ TranslationBounds p

theorem translation_bounds_of_area_le (p : Placement) (hA : placementArea p ≤ tau) :
    TranslationBounds p := by
  intro i
  obtain ⟨hx, hy⟩ := placement_translation_estimate p i
  have hs : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg _
  have hq : 8 * placementArea p / Real.sqrt 3 ≤ 8 * tau / Real.sqrt 3 :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hA (by norm_num)) hs
  constructor
  · unfold translationX
    linarith
  · unfold translationY
    linarith

theorem TranslationBounds.outer {p : Placement} (hp : TranslationBounds p) :
    OuterTranslationBounds p := by
  intro i
  exact ⟨(hp i).1.trans translationX_lt_outerX.le,
    (hp i).2.trans_eq translationY_eq_outerY⟩

/-- The old out-of-domain premise is a theorem for the simplified domain. -/
theorem outside_translation_domain (p : Placement) (hp : ¬ TranslationBounds p) :
    ENNReal.ofReal tau ≤ placementVolume p := by
  rw [ENNReal.ofReal_le_iff_le_toReal (placementVolume_ne_top p)]
  by_contra h
  exact hp (translation_bounds_of_area_le p (le_of_not_ge h))

theorem outside_lower_domain (p : Placement) (hn : AnglesNormalized p)
    (hp : ¬ InLowerDomain p) : ENNReal.ofReal tau ≤ placementVolume p :=
  outside_translation_domain p (fun ht => hp ⟨hn, ht⟩)

theorem lower_domain_of_small_area (p : Placement) (hn : AnglesNormalized p)
    (hA : placementVolume p < ENNReal.ofReal tau) : InLowerDomain p := by
  refine ⟨hn, ?_⟩
  by_contra h
  exact (not_le_of_gt hA) (outside_translation_domain p h)

/-- Coordinate order agrees with the manuscript: three angles followed by
the x/y translation pair of T, U, and C. -/
noncomputable def placementCoordinates (p : Placement) : Fin 9 → ℝ :=
  ![p.angle 0, p.angle 1, p.angle 2,
    (p.translation 0).re, (p.translation 0).im,
    (p.translation 1).re, (p.translation 1).im,
    (p.translation 2).re, (p.translation 2).im]

@[simp] theorem placementCoordinates_angle (p : Placement) (i : Fin 3) :
    placementCoordinates p ⟨i.val, by omega⟩ = p.angle i := by
  fin_cases i <;> rfl

@[simp] theorem placementCoordinates_tx (p : Placement) (i : Fin 3) :
    placementCoordinates p ⟨3 + 2 * i.val, by omega⟩ = (p.translation i).re := by
  fin_cases i <;> rfl

@[simp] theorem placementCoordinates_ty (p : Placement) (i : Fin 3) :
    placementCoordinates p ⟨3 + 2 * i.val + 1, by omega⟩ = (p.translation i).im := by
  fin_cases i <;> rfl

noncomputable def placementFromCoordinates (x : Fin 9 → ℝ) : Placement :=
  ⟨fun i => x ⟨i.val, by omega⟩,
    fun i => ⟨x ⟨3 + 2 * i.val, by omega⟩, x ⟨3 + 2 * i.val + 1, by omega⟩⟩⟩

@[simp] theorem placementCoordinates_fromCoordinates (x : Fin 9 → ℝ) :
    placementCoordinates (placementFromCoordinates x) = x := by
  funext i
  fin_cases i <;> rfl

@[simp] theorem placementFromCoordinates_coordinates (p : Placement) :
    placementFromCoordinates (placementCoordinates p) = p := by
  cases p with
  | mk angle translation =>
    unfold placementFromCoordinates
    congr 1
    · funext i
      exact placementCoordinates_angle ⟨angle, translation⟩ i
    · funext i
      apply Complex.ext
      · exact placementCoordinates_tx ⟨angle, translation⟩ i
      · exact placementCoordinates_ty ⟨angle, translation⟩ i

noncomputable def domainLowerCorner : Fin 9 → ℝ :=
  ![0, 0, 0, -translationX, -translationY, -translationX, -translationY,
    -translationX, -translationY]

noncomputable def domainUpperCorner : Fin 9 → ℝ :=
  ![Real.pi / 3, 2 * Real.pi, Real.pi, translationX, translationY,
    translationX, translationY, translationX, translationY]

noncomputable def outerDomainLowerCorner : Fin 9 → ℝ :=
  ![0, 0, 0, -outerX, -outerY, -outerX, -outerY, -outerX, -outerY]

noncomputable def outerDomainUpperCorner : Fin 9 → ℝ :=
  ![Real.pi / 3, 2 * Real.pi, Real.pi, outerX, outerY, outerX, outerY, outerX, outerY]

theorem outerDomainLowerCorner_le : outerDomainLowerCorner ≤ domainLowerCorner := by
  intro i
  fin_cases i <;> simp [outerDomainLowerCorner, domainLowerCorner, translationY_eq_outerY] <;>
    linarith [translationX_lt_outerX]

theorem domainUpperCorner_le_outer : domainUpperCorner ≤ outerDomainUpperCorner := by
  intro i
  fin_cases i <;> simp [outerDomainUpperCorner, domainUpperCorner, translationY_eq_outerY] <;>
    linarith [translationX_lt_outerX]

noncomputable def lowerPlacementBox : Set (Fin 9 → ℝ) :=
  Icc domainLowerCorner domainUpperCorner

theorem lowerPlacementBox_compact : IsCompact lowerPlacementBox := isCompact_Icc

theorem placementCoordinates_mem_iff (p : Placement) :
    placementCoordinates p ∈ lowerPlacementBox ↔ InLowerDomain p := by
  simp only [lowerPlacementBox, mem_Icc, Pi.le_def, InLowerDomain, AnglesNormalized,
    TranslationBounds, abs_le]
  simp only [Fin.forall_fin_succ, placementCoordinates, domainLowerCorner,
    domainUpperCorner, Matrix.cons_val_zero, Matrix.cons_val_succ,
    Fin.succ_zero_eq_one, Fin.succ_one_eq_two]
  simp only [Fin.forall_fin_zero, and_true]
  tauto

/-- Any checked dyadic enclosure of the two domain corners covers every
geometrically relevant placement. This is the root interface for BoxTree. -/
theorem lower_domain_mem_root (root : DyadicBox 9)
    (hlo : ∀ i : Fin 9, DIval.val root[i].lo ≤ domainLowerCorner i)
    (hhi : ∀ i : Fin 9, domainUpperCorner i ≤ DIval.val root[i].hi)
    {p : Placement} (hp : InLowerDomain p) :
    root.Mem (placementCoordinates p) := by
  have hm := (placementCoordinates_mem_iff p).2 hp
  intro i
  exact DIval.mem_iff_val.2 ⟨(hlo i).trans (hm.1 i), (hm.2 i).trans (hhi i)⟩

theorem lower_domain_mem_outer_root (root : DyadicBox 9)
    (hlo : ∀ i : Fin 9, DIval.val root[i].lo ≤ outerDomainLowerCorner i)
    (hhi : ∀ i : Fin 9, outerDomainUpperCorner i ≤ DIval.val root[i].hi)
    {p : Placement} (hp : InLowerDomain p) :
    root.Mem (placementCoordinates p) :=
  lower_domain_mem_root root
    (fun i => (hlo i).trans (outerDomainLowerCorner_le i))
    (fun i => (domainUpperCorner_le_outer i).trans (hhi i)) hp

/-- The concrete certificate root encloses the paper's angular limits and
the proved rational outer translation limits. No endpoint premise remains. -/
theorem certificate_root_outer_bounds :
    (∀ i : Fin 9, DIval.val LowerBound.Certificate.root[i].lo ≤ outerDomainLowerCorner i) ∧
    (∀ i : Fin 9, outerDomainUpperCorner i ≤ DIval.val LowerBound.Certificate.root[i].hi) := by
  have hx : outerX ≤ DIval.val (DIval.ratio 603894 1000000).hi := by
    exact (DIval.mem_iff_val.1 (DIval.mem_ratio 603894 1000000 (by norm_num))).2
  have hy : outerY ≤ DIval.val (DIval.ratio 478 1000).hi := by
    exact (DIval.mem_iff_val.1 (DIval.mem_ratio 478 1000 (by norm_num))).2
  have hxn : DIval.val (-(DIval.ratio 603894 1000000).hi) ≤ -outerX := by
    simpa only [DIval.val, Int.cast_neg, neg_div] using neg_le_neg hx
  have hyn : DIval.val (-(DIval.ratio 478 1000).hi) ≤ -outerY := by
    simpa only [DIval.val, Int.cast_neg, neg_div] using neg_le_neg hy
  have hp3 : Real.pi / 3 ≤ DIval.val (DIval.piI.mul (DIval.ratio 1 3)).hi := by
    have h := (DIval.mem_iff_val.1
      (DIval.mem_mul DIval.mem_piI (DIval.mem_ratio 1 3 (by norm_num)))).2
    simpa [div_eq_mul_inv] using h
  have hp2 : 2 * Real.pi ≤ DIval.val (DIval.piI.mul (DIval.ofInt 2)).hi := by
    have h := (DIval.mem_iff_val.1
      (DIval.mem_mul DIval.mem_piI (DIval.mem_ofInt 2))).2
    simpa [mul_comm] using h
  have hp : Real.pi ≤ DIval.val DIval.piI.hi :=
    (DIval.mem_iff_val.1 DIval.mem_piI).2
  constructor
  · intro i
    fin_cases i
    · change DIval.val 0 ≤ 0
      simp [DIval.val]
    · change DIval.val 0 ≤ 0
      simp [DIval.val]
    · change DIval.val 0 ≤ 0
      simp [DIval.val]
    · exact hxn
    · exact hyn
    · exact hxn
    · exact hyn
    · exact hxn
    · exact hyn
  · intro i
    fin_cases i
    · exact hp3
    · exact hp2
    · exact hp
    · exact hx
    · exact hy
    · exact hx
    · exact hy
    · exact hx
    · exact hy

theorem lower_domain_mem_certificate_root {p : Placement} (hp : InLowerDomain p) :
    LowerBound.Certificate.root.Mem (placementCoordinates p) :=
  lower_domain_mem_outer_root LowerBound.Certificate.root
    certificate_root_outer_bounds.1 certificate_root_outer_bounds.2 hp

theorem small_placement_mem_certificate_root (p : Placement) (hn : AnglesNormalized p)
    (hA : placementVolume p < ENNReal.ofReal tau) :
    LowerBound.Certificate.root.Mem (placementCoordinates p) :=
  lower_domain_mem_certificate_root (lower_domain_of_small_area p hn hA)

/-- Only the finite computation on the stated domain remains an input;
normalization and exclusion of its complement are proved above. -/
theorem universal_cover_lower_bound_of_domain
    (hcert : ∀ p : Placement, InLowerDomain p → ENNReal.ofReal tau ≤ placementVolume p)
    (K : Set ℂ) (hK : IsConvexUniversalCover K) :
    ENNReal.ofReal tau ≤ volume K := by
  obtain ⟨p, hp, hvol⟩ := cover_contains_normalized_placement K hK.1 hK.2
  have hbound : ENNReal.ofReal tau ≤ placementVolume p := by
    by_cases hd : InLowerDomain p
    · exact hcert p hd
    · exact outside_lower_domain p hp hd
  exact hbound.trans hvol

theorem universal_cover_lower_bound_of_box
    (hcert : ∀ p : Placement, placementCoordinates p ∈ lowerPlacementBox →
      ENNReal.ofReal tau ≤ placementVolume p)
    (K : Set ℂ) (hK : IsConvexUniversalCover K) :
    ENNReal.ofReal tau ≤ volume K :=
  universal_cover_lower_bound_of_domain
    (fun p hp => hcert p ((placementCoordinates_mem_iff p).2 hp)) K hK

theorem universal_cover_lower_bound_of_root (root : DyadicBox 9)
    (hlo : ∀ i : Fin 9, DIval.val root[i].lo ≤ domainLowerCorner i)
    (hhi : ∀ i : Fin 9, domainUpperCorner i ≤ DIval.val root[i].hi)
    (hcert : ∀ p : Placement, root.Mem (placementCoordinates p) →
      ENNReal.ofReal tau ≤ placementVolume p)
    (K : Set ℂ) (hK : IsConvexUniversalCover K) :
    ENNReal.ofReal tau ≤ volume K :=
  universal_cover_lower_bound_of_domain
    (fun p hp => hcert p (lower_domain_mem_root root hlo hhi hp)) K hK

/-- Capstone interface for the concrete root: the only remaining input is
the area bound established by its checked finite certificate. -/
theorem universal_cover_lower_bound_of_certificate_root
    (hcert : ∀ p : Placement, LowerBound.Certificate.root.Mem (placementCoordinates p) →
      ENNReal.ofReal tau ≤ placementVolume p)
    (K : Set ℂ) (hK : IsConvexUniversalCover K) :
    ENNReal.ofReal tau ≤ volume K :=
  universal_cover_lower_bound_of_domain
    (fun p hp => hcert p (lower_domain_mem_certificate_root hp)) K hK

end

end MoserWorm
