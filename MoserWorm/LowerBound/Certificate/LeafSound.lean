import MoserWorm.LowerBound.Certificate.ArithmeticSound
import MoserWorm.LowerBound.Pentagon

/-! The executable leaf checks imply the area bound for the paper's physical placements. -/

open MeasureTheory
open scoped ENNReal

namespace MoserWorm.LowerBound.Certificate

def PlaneEnclosed (z : Plane) (v : DIval × DIval) : Prop :=
  z.re ∈ v.1 ∧ z.im ∈ v.2

theorem complex_rotation_encloses {θ : ℝ} {v : Plane} {V : DIval × DIval} {s c : DIval}
    (hv : PlaneEnclosed v V) (hs : Real.sin θ ∈ s) (hc : Real.cos θ ∈ c) :
    PlaneEnclosed (Complex.exp ((θ : ℂ) * Complex.I) * v) (rotatePoint s c V) := by
  constructor
  · simpa only [rotatePoint, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im] using
      DIval.mem_sub (DIval.mem_mul hc hv.1) (DIval.mem_mul hs hv.2)
  · simpa only [rotatePoint, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, add_comm] using
      DIval.mem_add (DIval.mem_mul hs hv.1) (DIval.mem_mul hc hv.2)

theorem bodyT_encloses : List.Forall₂ PlaneEnclosed vertsT bodyT := by
  have hr : Real.sqrt 3 ∈ (DIval.ofInt 3).sqrtI := by
    simpa using DIval.mem_sqrtI (DIval.mem_ofInt 3) (by norm_num)
  unfold vertsT bodyT
  refine .cons ⟨?_, ?_⟩ (.cons ⟨?_, ?_⟩ (.cons ⟨?_, ?_⟩ .nil))
  · simpa [neg_div, div_eq_mul_inv] using DIval.mem_ratio (-1) 4 (by norm_num)
  · simpa [div_eq_mul_inv] using
      DIval.mem_neg (DIval.mem_mul hr (DIval.mem_ratio 1 12 (by norm_num)))
  · simpa using DIval.mem_ratio 1 4 (by norm_num)
  · simpa [div_eq_mul_inv] using
      DIval.mem_neg (DIval.mem_mul hr (DIval.mem_ratio 1 12 (by norm_num)))
  · simpa using DIval.mem_ofInt 0
  · simpa [div_eq_mul_inv] using
      DIval.mem_mul hr (DIval.mem_ratio 1 6 (by norm_num))

theorem bodyC_encloses : List.Forall₂ PlaneEnclosed vertsC bodyC := by
  have hr : Real.sqrt 8745 ∈ (DIval.ofInt 8745).sqrtI := by
    simpa using DIval.mem_sqrtI (DIval.mem_ofInt 8745) (by norm_num)
  have hy : crownY ∈ (DIval.ofInt 8745).sqrtI.mul (DIval.ratio 1 1024) := by
    simpa [crownY, div_eq_mul_inv] using
      DIval.mem_mul hr (DIval.mem_ratio 1 1024 (by norm_num))
  unfold vertsC bodyC
  refine .cons ⟨?_, ?_⟩ (.cons ⟨?_, ?_⟩ (.cons ⟨?_, ?_⟩ (.cons ⟨?_, ?_⟩ .nil)))
  · simpa [neg_div] using DIval.mem_ratio (-7) 16 (by norm_num)
  · simpa using DIval.mem_ofInt 0
  · simpa using DIval.mem_ratio 49 128 (by norm_num)
  · exact DIval.mem_neg hy
  · simpa using DIval.mem_ratio 7 16 (by norm_num)
  · simpa using DIval.mem_ofInt 0
  · simpa [neg_div] using DIval.mem_ratio (-49) 128 (by norm_num)
  · exact hy

theorem bodyU_encloses : List.Forall₂ PlaneEnclosed vertsU bodyU := by
  have ha : 11 * Real.pi / 24 ∈ DIval.piI.mul (DIval.ratio 11 24) := by
    convert DIval.mem_mul DIval.mem_piI (DIval.mem_ratio 11 24 (by norm_num)) using 1
    push_cast
    ring
  have hb : 11 * Real.pi / 12 ∈ DIval.piI.mul (DIval.ratio 11 12) := by
    convert DIval.mem_mul DIval.mem_piI (DIval.mem_ratio 11 12 (by norm_num)) using 1
    push_cast
    ring
  obtain ⟨hs, hc⟩ := DIval.mem_sincosIv ha (by decide) (by decide)
  obtain ⟨hs₂, hc₂⟩ := DIval.mem_sincosIv hb (by decide) (by decide)
  have hk := DIval.mem_ratio 1 12 (by norm_num)
  have h1 := DIval.mem_ofInt 1
  have h2 := DIval.mem_ofInt 2
  have h3 := DIval.mem_ofInt 3
  unfold vertsU bodyU
  refine .cons ⟨?_, ?_⟩ (.cons ⟨?_, ?_⟩ (.cons ⟨?_, ?_⟩ (.cons ⟨?_, ?_⟩ .nil)))
  · convert DIval.mem_mul
      (DIval.mem_neg (DIval.mem_add (DIval.mem_add h3 (DIval.mem_mul h2 hc)) hc₂)) hk
      using 1 <;> first | rfl | (push_cast; ring)
  · convert DIval.mem_mul
      (DIval.mem_neg (DIval.mem_add (DIval.mem_mul h2 hs) hs₂)) hk
      using 1 <;> first | rfl | (push_cast; ring)
  · convert DIval.mem_mul
      (DIval.mem_sub (DIval.mem_sub h1 (DIval.mem_mul h2 hc)) hc₂) hk
      using 1 <;> first | rfl | (push_cast; ring)
  · convert DIval.mem_mul
      (DIval.mem_neg (DIval.mem_add (DIval.mem_mul h2 hs) hs₂)) hk
      using 1 <;> first | rfl | (push_cast; ring)
  · convert DIval.mem_mul
      (DIval.mem_sub (DIval.mem_add h1 (DIval.mem_mul h2 hc)) hc₂) hk
      using 1 <;> first | rfl | (push_cast; ring)
  · convert DIval.mem_mul (DIval.mem_sub (DIval.mem_mul h2 hs) hs₂) hk
      using 1 <;> first | rfl | (push_cast; ring)
  · convert DIval.mem_mul
      (DIval.mem_add (DIval.mem_add h1 (DIval.mem_mul h2 hc)) (DIval.mem_mul h3 hc₂)) hk
      using 1 <;> first | rfl | (push_cast; ring)
  · convert DIval.mem_mul
      (DIval.mem_add (DIval.mem_mul h2 hs) (DIval.mem_mul h3 hs₂)) hk
      using 1 <;> first | rfl | (push_cast; ring)

theorem bodyVertices_encloses (i : BodyId) :
    List.Forall₂ PlaneEnclosed (vertices i) (bodyVertices i) := by
  fin_cases i
  · exact bodyT_encloses
  · exact bodyU_encloses
  · exact bodyC_encloses

noncomputable def midpointAngle (box : PlacementBox) (i : BodyId) : ℝ :=
  DIval.val (DyadicBox.midpoint (angleInterval box i))

noncomputable def liftedParameters (box : PlacementBox) (p : Placement) : Coordinate → ℝ :=
  Corner.parameters (fun i => ((p.translation i).re, (p.translation i).im))
    (fun i => p.angle i - midpointAngle box i)

theorem liftedParameters_unit (box : PlacementBox) (p : Placement) :
    Corner.UnitRotations (liftedParameters box p) :=
  Corner.parameters_unit _ _

theorem anglesValid_spec {box : PlacementBox} (h : anglesValid box = true) (i : BodyId) :
    -64 * dfxOne ≤ DyadicBox.midpoint (angleInterval box i) ∧
      DyadicBox.midpoint (angleInterval box i) ≤ 64 * dfxOne ∧
      0 ≤ angleRadius box i ∧ angleRadius box i ≤ DIval.pi2Lo := by
  have hi : i ∈ ([0, 1, 2] : List BodyId) := by fin_cases i <;> simp
  exact of_decide_eq_true (List.all_eq_true.mp h i hi)

private theorem val_mono {a b : Int} (h : a ≤ b) : DIval.val a ≤ DIval.val b :=
  div_le_div_of_nonneg_right (by exact_mod_cast h) (by positivity)

theorem angle_mem {box : PlacementBox} {p : Placement}
    (h : box.Mem (placementCoordinates p)) (i : BodyId) :
    p.angle i ∈ angleInterval box i := by
  simpa only [placementCoordinates_angle, Fin.getElem_fin, angleInterval] using
    h ⟨i.val, by omega⟩

theorem translation_mem {box : PlacementBox} {p : Placement}
    (h : box.Mem (placementCoordinates p)) (i : BodyId) :
    (p.translation i).re ∈ translationInterval box i false ∧
      (p.translation i).im ∈ translationInterval box i true := by
  constructor
  · simpa only [placementCoordinates_tx, translationInterval, Bool.false_eq_true,
      ↓reduceIte, Nat.add_zero, Fin.getElem_fin] using h ⟨3 + 2 * i.val, by omega⟩
  · simpa only [placementCoordinates_ty, translationInterval, ↓reduceIte, Fin.getElem_fin] using
      h ⟨3 + 2 * i.val + 1, by omega⟩

theorem angle_residual_mem {box : PlacementBox} {p : Placement}
    (h : box.Mem (placementCoordinates p)) (i : BodyId) :
    -DIval.val (angleRadius box i) ≤ p.angle i - midpointAngle box i ∧
      p.angle i - midpointAngle box i ≤ DIval.val (angleRadius box i) := by
  have ha := angle_mem h i
  let m := DyadicBox.midpoint (angleInterval box i)
  let r := angleRadius box i
  have hlo : m - r ≤ (angleInterval box i).lo := by
    have := le_max_right ((angleInterval box i).hi - m) (m - (angleInterval box i).lo)
    change _ ≤ r at this
    omega
  have hhi : (angleInterval box i).hi ≤ m + r := by
    have := le_max_left ((angleInterval box i).hi - m) (m - (angleInterval box i).lo)
    change _ ≤ r at this
    omega
  have hscale : (0 : ℝ) < 2 ^ dfxS := by positivity
  have hl : DIval.val m - DIval.val r ≤ p.angle i := by
    change (m : ℝ) / 2 ^ dfxS - (r : ℝ) / 2 ^ dfxS ≤ _
    rw [← sub_div, div_le_iff₀ hscale]
    exact (by exact_mod_cast hlo : (m : ℝ) - (r : ℝ) ≤ (angleInterval box i).lo).trans ha.1
  have hu : p.angle i ≤ DIval.val m + DIval.val r := by
    change _ ≤ (m : ℝ) / 2 ^ dfxS + (r : ℝ) / 2 ^ dfxS
    rw [← add_div, le_div_iff₀ hscale]
    exact ha.2.trans (by exact_mod_cast hhi)
  change -DIval.val r ≤ p.angle i - DIval.val m ∧
    p.angle i - DIval.val m ≤ DIval.val r
  constructor <;> linarith

theorem liftedBox_mem {box : PlacementBox} {p : Placement}
    (hv : anglesValid box = true) (hbox : box.Mem (placementCoordinates p)) :
    ∀ k, liftedParameters box p k ∈ liftedBox box k := by
  rintro ⟨i, k⟩
  have hvalid := anglesValid_spec hv i
  have hr0 : 0 ≤ DIval.val (angleRadius box i) :=
    div_nonneg (by exact_mod_cast hvalid.2.2.1) (by positivity)
  have hrπ : DIval.val (angleRadius box i) ≤ Real.pi / 2 :=
    (val_mono hvalid.2.2.2).trans (DIval.mem_iff_val.mp DIval.mem_piHalfI).1
  have hrange : |angleRadius box i| ≤ 64 * dfxOne := by
    rw [abs_of_nonneg hvalid.2.2.1]
    exact hvalid.2.2.2.trans (by decide)
  obtain ⟨hs, hc⟩ := DIval.mem_sincos hrange
  have hr := Corner.rotation_rectangle hr0 hrπ (angle_residual_mem hbox i)
  fin_cases k
  · exact (translation_mem hbox i).1
  · exact (translation_mem hbox i).2
  · change Real.cos (p.angle i - midpointAngle box i) ∈
      (⟨(DIval.sincos (angleRadius box i)).2.lo, dfxOne⟩ : DIval)
    apply DIval.mem_iff_val.mpr
    refine ⟨(DIval.mem_iff_val.mp hc).1.trans hr.1, ?_⟩
    convert hr.2.1 using 1
    norm_num [DIval.val, dfxOne, dfxS]
  · change Real.sin (p.angle i - midpointAngle box i) ∈
      (⟨-(DIval.sincos (angleRadius box i)).1.hi,
        (DIval.sincos (angleRadius box i)).1.hi⟩ : DIval)
    apply DIval.mem_iff_val.mpr
    refine ⟨?_, hr.2.2.2.trans (DIval.mem_iff_val.mp hs).2⟩
    simpa [DIval.val, neg_div] using
      (neg_le_neg (DIval.mem_iff_val.mp hs).2).trans hr.2.2.1

noncomputable def localVertex (box : PlacementBox) (i : BodyId) (v : Plane) :
    Corner.Vertex BodyId ℝ :=
  let z := Complex.exp ((midpointAngle box i : ℂ) * Complex.I) * v
  .moving i (z.re, z.im)

noncomputable def realVertices (box : PlacementBox) : List (Corner.Vertex BodyId ℝ) :=
  [.fixed (-(1 / 2), 0), .fixed (1 / 2, 0)] ++
    ([0, 1, 2] : List BodyId).flatMap fun i => (vertices i).map (localVertex box i)

theorem realVertices_length (box : PlacementBox) : (realVertices box).length = 13 := rfl

theorem realVertices_encloses {box : PlacementBox} (h : anglesValid box = true) :
    List.Forall₂ VertexEncloses (realVertices box) (rotatedVertices box) := by
  apply List.rel_append
  · refine .cons (.fixed ⟨?_, ?_⟩) (.cons (.fixed ⟨?_, ?_⟩) .nil)
    · simpa [neg_div, div_eq_mul_inv] using DIval.mem_ratio (-1) 2 (by norm_num)
    · simpa using DIval.mem_ofInt 0
    · simpa using DIval.mem_ratio 1 2 (by norm_num)
    · simpa using DIval.mem_ofInt 0
  · apply List.rel_flatMap (R := Eq) (.cons rfl (.cons rfl (.cons rfl .nil)))
    intro i j hij
    subst j
    have hi := anglesValid_spec h i
    have hmid : |DyadicBox.midpoint (angleInterval box i)| ≤ 64 * dfxOne := by
      exact abs_le.mpr ⟨by simpa [neg_mul] using hi.1, hi.2.1⟩
    obtain ⟨hs, hc⟩ := DIval.mem_sincos hmid
    refine List.rel_map (R := PlaneEnclosed) ?_ (bodyVertices_encloses i)
    intro v V hv
    apply VertexEncloses.moving
    exact complex_rotation_encloses hv hs hc

private theorem realize_parameters (t : BodyId → ℝ × ℝ) (δ : BodyId → ℝ)
    (i : BodyId) (v : Plane) :
    realize (Corner.parameters t δ) (.moving i (v.re, v.im)) =
      (⟨(t i).1, (t i).2⟩ : Plane) + Complex.exp ((δ i : ℂ) * Complex.I) * v := by
  apply Complex.ext <;>
    simp [realize, Corner.parameters, Corner.position, Corner.place, Corner.rotate,
      Complex.mul_re, Complex.mul_im, Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im, add_comm]

theorem realize_localVertex (box : PlacementBox) (p : Placement) (i : BodyId) (v : Plane) :
    realize (liftedParameters box p) (localVertex box i v) = placeVertex p i v := by
  unfold liftedParameters localVertex
  rw [realize_parameters]
  change p.translation i +
    Complex.exp (((p.angle i - midpointAngle box i : ℝ) : ℂ) * Complex.I) *
      (Complex.exp ((midpointAngle box i : ℂ) * Complex.I) * v) = _
  rw [← mul_assoc, ← Complex.exp_add]
  have he : (((p.angle i - midpointAngle box i : ℝ) : ℂ) * Complex.I) +
      (midpointAngle box i : ℂ) * Complex.I = (p.angle i : ℂ) * Complex.I := by
    push_cast
    ring
  rw [he]
  exact add_comm _ _

theorem realVertices_mem (box : PlacementBox) (p : Placement) :
    ∀ v ∈ realVertices box, realize (liftedParameters box p) v ∈ placementHull p := by
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · convert (endpoint_mem_placementHull p).1 using 1
      norm_num [realize, Corner.position, Complex.ext_iff]
    · convert (endpoint_mem_placementHull p).2 using 1
      norm_num [realize, Corner.position, Complex.ext_iff]
  · obtain ⟨i, _, hv⟩ := List.mem_flatMap.mp hv
    obtain ⟨z, hz, rfl⟩ := List.mem_map.mp hv
    rw [realize_localVertex]
    exact placeVertex_mem_placementHull p i hz

noncomputable def selectedRealPoints (box : PlacementBox) (labels : List Label) :
    List (Corner.Vertex BodyId ℝ) :=
  labels.map fun i => (realVertices box).getD i.val (.fixed (0, 0))

theorem selectedPoints_encloses {box : PlacementBox} (h : anglesValid box = true)
    (labels : List Label) :
    List.Forall₂ VertexEncloses (selectedRealPoints box labels)
      (selectedPoints (rotatedVertices box) labels) := by
  induction labels with
  | nil => exact .nil
  | cons i labels ih => exact .cons (VertexEncloses.getD (realVertices_encloses h) i.val) ih

theorem selectedRealPoints_mem (box : PlacementBox) (p : Placement) (labels : List Label) :
    ∀ v ∈ selectedRealPoints box labels,
      realize (liftedParameters box p) v ∈ placementHull p := by
  intro v hv
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
  apply realVertices_mem box p
  rw [List.getD_eq_getElem _ _ (by rw [realVertices_length]; exact i.isLt)]
  exact List.getElem_mem _

/-- Lists of three to five points need no orientation checks. -/
theorem short_shoelace_le_volume {l : List Plane} (h3 : 3 ≤ l.length)
    (h5 : l.length ≤ 5) {K : Set Plane} (hK : Convex ℝ K)
    (hmem : ∀ p ∈ l, p ∈ K) : ENNReal.ofReal (shoelace l) ≤ volume K := by
  by_cases hl : l.length = 5
  · exact shoelace_le_volume_of_length_five hl hK hmem
  have h4 : l.length ≤ 4 := by omega
  rcases l with _ | ⟨a, l⟩
  · simp at h3
  rcases l with _ | ⟨b, l⟩
  · simp at h3
  rcases l with _ | ⟨c, l⟩
  · simp at h3
  rcases l with _ | ⟨d, l⟩
  · exact triangle_shoelace_le_volume hK
      (hmem a (by simp)) (hmem b (by simp)) (hmem c (by simp))
  have hl : l = [] :=
    List.eq_nil_iff_length_eq_zero.mpr (by simp only [List.length_cons] at h4; omega)
  subst l
  exact quadrilateral_shoelace_le_volume hK
    (hmem a (by simp)) (hmem b (by simp)) (hmem c (by simp)) (hmem d (by simp))

theorem fanValid_sound {l : List (Corner.Vertex BodyId ℝ)} {L : List IVertex}
    (h : List.Forall₂ VertexEncloses l L) {box : Coordinate → DIval} {x : Coordinate → ℝ}
    (hx : Corner.UnitRotations x) (hbox : ∀ i, x i ∈ box i)
    (hcheck : fanValid box L = true) : FanConditions (points x l) := by
  simp only [fanValid, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨h3, hfirst⟩, hnext⟩ := hcheck
  have hlen := h.length_eq
  apply fanConditions_of_positive_evals hx (by omega)
  · intro i hi him
    have hc := hfirst (i - 2) (List.mem_range.mpr (by omega))
    rw [show i - 2 + 2 = i by omega] at hc
    exact fanPositive_pos (VertexEncloses.getD h 0) (VertexEncloses.getD h 1)
      (VertexEncloses.getD h i) hx hbox hc
  · intro i hi him
    have hc := hnext (i - 2) (List.mem_range.mpr (by omega))
    rw [show i - 2 + 2 = i by omega, show i - 2 + 3 = i + 1 by omega] at hc
    exact fanPositive_pos (VertexEncloses.getD h 0) (VertexEncloses.getD h i)
      (VertexEncloses.getD h (i + 1)) hx hbox hc

/-- The checker may bypass determinant tests for lists of three to five vertices. -/
theorem shortOrFan_le_volume {l : List (Corner.Vertex BodyId ℝ)} {L : List IVertex}
    (h : List.Forall₂ VertexEncloses l L) {box : Coordinate → DIval} {x : Coordinate → ℝ}
    (hx : Corner.UnitRotations x) (hbox : ∀ i, x i ∈ box i)
    (h3 : 3 ≤ L.length) (hcheck : L.length ≤ 5 ∨ fanValid box L = true)
    {K : Set Plane} (hK : Convex ℝ K) (hmem : ∀ v ∈ l, realize x v ∈ K) :
    ENNReal.ofReal (shoelace (points x l)) ≤ volume K := by
  have hpoints : ∀ p ∈ points x l, p ∈ K := by
    intro p hp
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hp
    exact hmem v hv
  rcases hcheck with h5 | hfan
  · apply short_shoelace_le_volume _ _ hK hpoints
    · simpa only [points, List.length_map, h.length_eq] using h3
    · simpa only [points, List.length_map, h.length_eq] using h5
  · exact (fan_shoelace_pos_le_volume _ (fanValid_sound h hx hbox hfan) hK hpoints).2

/-- The executable short-list shortcut and the determinant checks are both sound. -/
theorem polygonValid_le_volume {l : List (Corner.Vertex BodyId ℝ)} {L : List IVertex}
    (h : List.Forall₂ VertexEncloses l L) {box : Coordinate → DIval} {x : Coordinate → ℝ}
    (hx : Corner.UnitRotations x) (hbox : ∀ i, x i ∈ box i)
    (hcheck : polygonValid box L = true) {K : Set Plane} (hK : Convex ℝ K)
    (hmem : ∀ v ∈ l, realize x v ∈ K) :
    ENNReal.ofReal (shoelace (points x l)) ≤ volume K := by
  by_cases hlen : L.length = 3 ∨ L.length = 4 ∨ L.length = 5
  · exact shortOrFan_le_volume h hx hbox (by omega) (.inl (by omega)) hK hmem
  · have hf : fanValid box L = true := by simpa [polygonValid, hlen] using hcheck
    apply (fan_shoelace_pos_le_volume _ (fanValid_sound h hx hbox hf) hK ?_).2
    intro z hz
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hz
    exact hmem v hv

noncomputable def realLeaf (box : PlacementBox) (leaf : Leaf) :
    List (ℝ × List (Corner.Vertex BodyId ℝ)) :=
  leaf.map fun f => (DIval.val f.weight, selectedRealPoints box f.labels)

theorem realLeaf_encloses {box : PlacementBox} (hv : anglesValid box = true) (leaf : Leaf) :
    CoeffEncloses (Corner.weightedShoelacePoly (realLeaf box leaf))
      (IPoly.sum (leaf.map fun f =>
        (shoelacePolynomial (selectedPoints (rotatedVertices box) f.labels)).scale
          (DIval.pt f.weight))) := by
  unfold Corner.weightedShoelacePoly realLeaf
  rw [List.map_map]
  apply CoeffEncloses.sum
  induction leaf with
  | nil => exact .nil
  | cons f leaf ih =>
    exact .cons ((shoelacePolynomial_encloses (selectedPoints_encloses hv f.labels)).scale
      (DIval.mem_pt f.weight)) ih

private theorem realLeaf_weight_sum (box : PlacementBox) (leaf : Leaf) :
    ((realLeaf box leaf).map Prod.fst).sum = DIval.val ((leaf.map WeightedFan.weight).sum) := by
  induction leaf with
  | nil => simp [realLeaf, DIval.val]
  | cons f leaf ih =>
    change DIval.val f.weight + ((realLeaf box leaf).map Prod.fst).sum =
      DIval.val (f.weight + (leaf.map WeightedFan.weight).sum)
    rw [ih]
    simp only [DIval.val, Int.cast_add, add_div]

/-- Every accepted leaf proves the target for every actual placement in its box. -/
theorem checkLeaf_sound {box : PlacementBox} {leaf : Leaf}
    (hcheck : checkLeaf box leaf = true) {p : Placement}
    (hbox : box.Mem (placementCoordinates p)) :
    ENNReal.ofReal (239 / 1000 : ℝ) ≤ placementVolume p := by
  simp only [checkLeaf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hcheck
  obtain ⟨⟨⟨⟨_, hv⟩, hsum⟩, hfans⟩, htarget⟩ := hcheck
  have hvars := liftedBox_mem hv hbox
  have hunit := liftedParameters_unit box p
  have hlower := areaValid_lower (realLeaf_encloses hv leaf) hvars htarget
  apply (ENNReal.ofReal_le_ofReal hlower).trans
  apply weightedShoelacePoly_le_volume_of_bounds hunit (realLeaf box leaf)
  · intro t ht
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ht
    exact div_nonneg (by exact_mod_cast (hfans f hf).1.1) (by positivity)
  · rw [realLeaf_weight_sum]
    exact (val_mono hsum).trans_eq (by norm_num [DIval.val, dfxOne, dfxS])
  · intro t ht
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ht
    exact polygonValid_le_volume (selectedPoints_encloses hv f.labels) hunit hvars
      (hfans f hf).2 (placementHull_convex p) (selectedRealPoints_mem box p f.labels)

theorem checkLeaf_sound_coordinates {box : PlacementBox} {leaf : Leaf}
    (hcheck : checkLeaf box leaf = true) {x : Fin 9 → ℝ} (hbox : box.Mem x) :
    ENNReal.ofReal (239 / 1000 : ℝ) ≤ placementVolume (placementFromCoordinates x) :=
  checkLeaf_sound hcheck (by simpa only [placementCoordinates_fromCoordinates] using hbox)

end MoserWorm.LowerBound.Certificate
