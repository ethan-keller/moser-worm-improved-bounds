import MoserWorm.LowerBound.Family

open Set MeasureTheory Complex
open scoped ENNReal

namespace MoserWorm

/-- The three movable hulls, in the order T, U, C. -/
noncomputable def vertices : Fin 3 → List ℂ := ![vertsT, vertsU, vertsC]

noncomputable def vertexArray (i : Fin 3) : Array ℂ := (vertices i).toArray

noncomputable def vertexSet (i : Fin 3) : Set ℂ := {z | z ∈ vertices i}

/-- Angles are in radians; each body has one shared complex translation. -/
structure Placement where
  angle : Fin 3 → ℝ
  translation : Fin 3 → ℂ

noncomputable def placeVertex (p : Placement) (i : Fin 3) (v : ℂ) : ℂ :=
  Complex.exp (p.angle i * Complex.I) * v + p.translation i

noncomputable def placedVertices (p : Placement) : Set ℂ :=
  {(-(1 / 2) : ℂ), (1 / 2 : ℂ)} ∪ ⋃ i, placeVertex p i '' vertexSet i

noncomputable def placementHull (p : Placement) : Set ℂ :=
  convexHull ℝ (placedVertices p)

noncomputable def placementVolume (p : Placement) : ℝ≥0∞ :=
  volume (placementHull p)

noncomputable def placementArea (p : Placement) : ℝ := (placementVolume p).toReal

def AnglesNormalized (p : Placement) : Prop :=
  p.angle 0 ∈ Icc 0 (Real.pi / 3) ∧
  p.angle 1 ∈ Icc 0 (2 * Real.pi) ∧
  p.angle 2 ∈ Icc 0 Real.pi

theorem placedVertices_finite (p : Placement) : (placedVertices p).Finite := by
  apply Set.Finite.union ((finite_singleton _).insert _)
  apply Set.finite_iUnion
  intro i
  exact (List.finite_toSet (vertices i)).image _

theorem placementHull_convex (p : Placement) : Convex ℝ (placementHull p) :=
  convex_convexHull ℝ _

theorem endpoint_mem_placementHull (p : Placement) :
    (-(1 / 2) : ℂ) ∈ placementHull p ∧ (1 / 2 : ℂ) ∈ placementHull p := by
  constructor <;> apply subset_convexHull ℝ _ <;> simp [placedVertices]

theorem placeVertex_mem_placementHull (p : Placement) (i : Fin 3) {v : ℂ}
    (hv : v ∈ vertices i) : placeVertex p i v ∈ placementHull p := by
  apply subset_convexHull ℝ _
  exact Or.inr (mem_iUnion.2 ⟨i, ⟨v, hv, rfl⟩⟩)

theorem placementHull_compact (p : Placement) : IsCompact (placementHull p) :=
  (placedVertices_finite p).isCompact_convexHull ℝ

theorem placementVolume_ne_top (p : Placement) : placementVolume p ≠ ⊤ :=
  (placementHull_compact p).measure_lt_top.ne

theorem ofReal_placementArea (p : Placement) :
    ENNReal.ofReal (placementArea p) = placementVolume p :=
  ENNReal.ofReal_toReal (placementVolume_ne_top p)

theorem vertices_length_pos (i : Fin 3) : 0 < (vertices i).length := by
  fin_cases i <;> norm_num [vertices, vertsT, vertsU, vertsC]

theorem vertices_sum (i : Fin 3) : (vertices i).sum = 0 := by
  fin_cases i
  · exact vertsT_sum
  · exact vertsU_sum
  · exact vertsC_sum

/-- Each translation is the average of its placed vertices, hence is in H. -/
theorem translation_mem_placementHull (p : Placement) (i : Fin 3) :
    p.translation i ∈ placementHull p := by
  let n := (vertices i).length
  have hn : (0 : ℝ) < n := by exact_mod_cast vertices_length_pos i
  have hz : (∑ j : Fin n, (vertices i)[j.val]) = 0 := by
    rw [← List.sum_ofFn, List.ofFn_getElem]
    exact vertices_sum i
  have hm := (placementHull_convex p).sum_mem
    (t := Finset.univ) (w := fun _ : Fin n => (1 : ℝ) / n)
    (z := fun j : Fin n => placeVertex p i ((vertices i)[j.val]))
    (fun _ _ => by positivity)
    (by simp [n, ne_of_gt hn])
    (fun j _ => placeVertex_mem_placementHull p i (List.getElem_mem j.isLt))
  have hs : (∑ j : Fin n, placeVertex p i ((vertices i)[j.val])) = n • p.translation i := by
    simp only [placeVertex, Finset.sum_add_distrib, ← Finset.mul_sum, hz, mul_zero,
      zero_add, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [← Finset.smul_sum, hs, ← Nat.cast_smul_eq_nsmul ℝ, smul_smul,
    one_div_mul_cancel hn.ne', one_smul] at hm
  exact hm

theorem placeVertex_image (p : Placement) (i : Fin 3) :
    placeVertex p i '' vertexSet i =
      (fun z => z + p.translation i) '' rotationSet (p.angle i) (vertexSet i) := by
  rw [rotationSet, Set.image_image]
  rfl

theorem placedVertices_eq_of_rotations {p q : Placement}
    (ht : ∀ i, p.translation i = q.translation i)
    (hr : ∀ i, rotationSet (p.angle i) (vertexSet i) =
      rotationSet (q.angle i) (vertexSet i)) :
    placedVertices p = placedVertices q := by
  unfold placedVertices
  congr 1
  apply iUnion_congr
  intro i
  rw [placeVertex_image, placeVertex_image, ht i, hr i]

/-- Arbitrary isometric placements after anchoring the unit segment. -/
noncomputable def anchoredVertices (g : Fin 3 → (ℂ ≃ᵢ ℂ)) : Set ℂ :=
  {(-(1 / 2) : ℂ), (1 / 2 : ℂ)} ∪ ⋃ i, g i '' vertexSet i

private theorem placement_of_oriented_crown (g : Fin 3 → (ℂ ≃ᵢ ℂ))
    (hc : ∃ a b : ℂ, ‖a‖ = 1 ∧ g 2 '' vertexSet 2 = (fun z => a * z + b) '' vertexSet 2) :
    ∃ p : Placement, placedVertices p = anchoredVertices g := by
  have hex : ∀ i : Fin 3, ∃ a b : ℂ, ‖a‖ = 1 ∧
      g i '' vertexSet i = (fun z => a * z + b) '' vertexSet i := by
    intro i
    fin_cases i
    · apply isometry_image_of_conj_symmetry (g 0) (vertexSet 0) (Real.pi / 3)
      exact conj_image_vertsT
    · apply isometry_image_of_conj_symmetry (g 1) (vertexSet 1) (Real.pi / 12)
      exact conj_image_vertsU
    · exact hc
  choose a b ha he using hex
  let p : Placement := ⟨fun i => (a i).arg, b⟩
  refine ⟨p, ?_⟩
  unfold placedVertices anchoredVertices
  congr 1
  apply iUnion_congr
  intro i
  rw [he i]
  congr 1
  funext z
  simp only [placeVertex, p, exp_arg_mul_I (ha i)]

theorem anchoredVertices_conj (g : Fin 3 → (ℂ ≃ᵢ ℂ)) :
    anchoredVertices (fun i => (g i).trans conjIsom) =
      conjIsom '' anchoredVertices g := by
  unfold anchoredVertices
  rw [Set.image_union, show conjIsom '' {(-(1 / 2) : ℂ), (1 / 2 : ℂ)} =
      {(-(1 / 2) : ℂ), (1 / 2 : ℂ)} by rw [conjIsom_coe]; exact conj_image_segment,
    Set.image_iUnion]
  congr 1
  apply iUnion_congr
  intro i
  rw [Set.image_image]
  rfl

/-- Mirror reduction is unconditional: one global reflection removes the
crown chirality, while the T and U vertex symmetries remove their local ones. -/
theorem anchored_isometries_to_placement (g : Fin 3 → (ℂ ≃ᵢ ℂ)) :
    ∃ p : Placement,
      placementVolume p = volume (convexHull ℝ (anchoredVertices g)) := by
  obtain ⟨a, b, ha, hC | hC⟩ := isometry_complex_classification (g 2)
  · obtain ⟨p, hp⟩ := placement_of_oriented_crown g
      ⟨a, b, ha, congrArg (fun f : ℂ → ℂ => f '' vertexSet 2) (funext hC)⟩
    exact ⟨p, by simp only [placementVolume, placementHull, hp]⟩
  · let g' : Fin 3 → (ℂ ≃ᵢ ℂ) := fun i => (g i).trans conjIsom
    have hc : ∃ a' b' : ℂ, ‖a'‖ = 1 ∧
        g' 2 '' vertexSet 2 = (fun z => a' * z + b') '' vertexSet 2 := by
      refine ⟨(starRingEnd ℂ) a, (starRingEnd ℂ) b, by simpa using ha, ?_⟩
      congr 1
      funext z
      change conjIsom ((g 2) z) = _
      rw [conjIsom_coe, hC z, map_add, map_mul]
      simp
    obtain ⟨p, hp⟩ := placement_of_oriented_crown g' hc
    refine ⟨p, ?_⟩
    change volume (convexHull ℝ (placedVertices p)) = _
    rw [hp, show anchoredVertices g' = conjIsom '' anchoredVertices g from
      anchoredVertices_conj g, convexHull_image_isometry, volume_image_isometry]

noncomputable def anglePeriod : Fin 3 → ℝ :=
  ![2 * Real.pi / 3, 2 * Real.pi, Real.pi]

theorem anglePeriod_pos (i : Fin 3) : 0 < anglePeriod i := by
  fin_cases i <;> simp [anglePeriod, Real.pi_pos]

theorem vertex_rotation_periodic (i : Fin 3) :
    Function.Periodic (fun a => rotationSet a (vertexSet i)) (anglePeriod i) := by
  fin_cases i
  · exact rotationSet_periodic rotationSet_vertsT_period
  · exact rotationSet_two_pi_periodic _
  · exact rotationSet_periodic rotationSet_vertsC_period

theorem exists_period_reduced_placement (p : Placement) :
    ∃ q : Placement, (∀ i, q.angle i ∈ Icc 0 (anglePeriod i)) ∧
      q.translation = p.translation ∧ placedVertices q = placedVertices p := by
  have hex : ∀ i : Fin 3, ∃ b ∈ Icc (0 : ℝ) (anglePeriod i),
      rotationSet (p.angle i) (vertexSet i) = rotationSet b (vertexSet i) :=
    fun i => rotationSet_angle_representative (anglePeriod_pos i) (vertex_rotation_periodic i) _
  choose b hb he using hex
  refine ⟨⟨b, p.translation⟩, hb, rfl, ?_⟩
  apply placedVertices_eq_of_rotations (p := ⟨b, p.translation⟩) (q := p) (fun _ => rfl)
  exact fun i => (he i).symm

noncomputable def halfTurnPlacement (p : Placement) : Placement :=
  ⟨fun i => p.angle i + Real.pi, fun i => -p.translation i⟩

theorem placedVertices_halfTurn (p : Placement) :
    placedVertices (halfTurnPlacement p) =
      (IsometryEquiv.neg ℂ) '' placedVertices p := by
  unfold placedVertices
  rw [Set.image_union, Set.image_iUnion]
  have hseg : (IsometryEquiv.neg ℂ) '' {(-(1 / 2) : ℂ), (1 / 2 : ℂ)} =
      {(-(1 / 2) : ℂ), (1 / 2 : ℂ)} := by
    rw [Set.image_pair]
    change {(-(-(1 / 2)) : ℂ), -(1 / 2)} = _
    rw [neg_neg, Set.pair_comm]
  rw [hseg]
  congr 1
  apply iUnion_congr
  intro i
  rw [Set.image_image]
  congr 1
  funext v
  change Complex.exp (((p.angle i + Real.pi : ℝ) : ℂ) * Complex.I) * v + -p.translation i =
    -(Complex.exp (p.angle i * Complex.I) * v + p.translation i)
  rw [exp_add_mul_I, Complex.exp_pi_mul_I]
  ring

theorem placementVolume_halfTurn (p : Placement) :
    placementVolume (halfTurnPlacement p) = placementVolume p := by
  change volume (convexHull ℝ (placedVertices (halfTurnPlacement p))) = _
  rw [placedVertices_halfTurn, convexHull_image_isometry, volume_image_isometry]
  rfl

/-- The triangle interval is halved using a global half-turn, not by
incorrectly assigning the triangle rotational period π/3. -/
theorem normalize_placement_angles (p : Placement) :
    ∃ q : Placement, AnglesNormalized q ∧ placementVolume q = placementVolume p := by
  obtain ⟨r, hr, _, he⟩ := exists_period_reduced_placement p
  have hvol : placementVolume r = placementVolume p := by
    simp only [placementVolume, placementHull, he]
  by_cases ht : r.angle 0 ≤ Real.pi / 3
  · refine ⟨r, ⟨⟨(hr 0).1, ht⟩, ?_, ?_⟩, hvol⟩
    · exact hr 1
    · exact hr 2
  · obtain ⟨u, hu, heu⟩ := rotationSet_angle_representative
      (anglePeriod_pos 1) (vertex_rotation_periodic 1) (r.angle 1 + Real.pi)
    obtain ⟨c, hc, hec⟩ := rotationSet_angle_representative
      (anglePeriod_pos 2) (vertex_rotation_periodic 2) (r.angle 2 + Real.pi)
    let q : Placement := ⟨![r.angle 0 - Real.pi / 3, u, c], fun i => -r.translation i⟩
    have hT : rotationSet (r.angle 0 - Real.pi / 3) (vertexSet 0) =
        rotationSet (r.angle 0 + Real.pi) (vertexSet 0) := by
      have hper := (vertex_rotation_periodic 0).nsmul 2 (r.angle 0 - Real.pi / 3)
      have hx : r.angle 0 - Real.pi / 3 + (2 : ℕ) • anglePeriod 0 =
          r.angle 0 + Real.pi := by simp [anglePeriod]; ring
      rw [hx] at hper
      exact hper.symm
    have hset : placedVertices q = placedVertices (halfTurnPlacement r) := by
      apply placedVertices_eq_of_rotations (p := q) (q := halfTurnPlacement r) (fun _ => rfl)
      intro i
      fin_cases i
      · exact hT
      · exact heu.symm
      · exact hec.symm
    refine ⟨q, ⟨?_, hu, hc⟩, ?_⟩
    · have hr0 : 0 ≤ r.angle 0 ∧ r.angle 0 ≤ 2 * Real.pi / 3 := hr 0
      change 0 ≤ r.angle 0 - Real.pi / 3 ∧ r.angle 0 - Real.pi / 3 ≤ Real.pi / 3
      constructor <;> linarith
    · calc
        placementVolume q = placementVolume (halfTurnPlacement r) := by
          simp only [placementVolume, placementHull, hset]
        _ = placementVolume r := placementVolume_halfTurn r
        _ = placementVolume p := hvol

/-- Simultaneous placements of L,T,U,C before fixing any frame. -/
noncomputable def jointVertices (g : Fin 4 → (ℂ ≃ᵢ ℂ)) : Set ℂ :=
  g 0 '' {(-(1 / 2) : ℂ), (1 / 2 : ℂ)} ∪
    ⋃ i : Fin 3, g i.succ '' vertexSet i

noncomputable def anchorJoint (g : Fin 4 → (ℂ ≃ᵢ ℂ)) : Fin 3 → (ℂ ≃ᵢ ℂ) :=
  fun i => (g i.succ).trans (g 0).symm

theorem anchor_joint_vertices (g : Fin 4 → (ℂ ≃ᵢ ℂ)) :
    anchoredVertices (anchorJoint g) = (g 0).symm '' jointVertices g := by
  unfold anchoredVertices jointVertices
  rw [Set.image_union, Set.image_iUnion]
  have h0 : (g 0).symm '' (g 0 '' {(-(1 / 2) : ℂ), (1 / 2 : ℂ)}) =
      {(-(1 / 2) : ℂ), (1 / 2 : ℂ)} := by
    simp [Set.image_image]
  rw [h0]
  congr 1
  apply iUnion_congr
  intro i
  rw [Set.image_image]
  rfl

/-- Every joint isometry placement has an equal-area placement in the
paper's angular ranges. There is no normalization hypothesis. -/
theorem normalize_joint_placement (g : Fin 4 → (ℂ ≃ᵢ ℂ)) :
    ∃ p : Placement, AnglesNormalized p ∧
      placementVolume p = volume (convexHull ℝ (jointVertices g)) := by
  obtain ⟨q, hq⟩ := anchored_isometries_to_placement (anchorJoint g)
  obtain ⟨p, hp, he⟩ := normalize_placement_angles q
  refine ⟨p, hp, he.trans ?_⟩
  rw [hq, anchor_joint_vertices, convexHull_image_isometry, volume_image_isometry]

theorem familyVertexLists_zero :
    {z | z ∈ familyVertexLists 0} = {(-(1 / 2) : ℂ), (1 / 2 : ℂ)} := by
  have hn : (⟨-(1 / 2), 0⟩ : ℂ) = -(1 / 2) := by apply Complex.ext <;> norm_num
  have hp : (⟨1 / 2, 0⟩ : ℂ) = 1 / 2 := by apply Complex.ext <;> norm_num
  change {z | z ∈ vertsL} = _
  unfold vertsL
  rw [hn, hp]
  ext z
  simp

theorem familyVertexLists_succ (i : Fin 3) :
    {z | z ∈ familyVertexLists i.succ} = vertexSet i := by
  fin_cases i <;> rfl

theorem jointVertices_eq_iUnion (g : Fin 4 → (ℂ ≃ᵢ ℂ)) :
    jointVertices g = ⋃ i : Fin 4, g i '' {z | z ∈ familyVertexLists i} := by
  ext z
  constructor
  · rintro (hz | hz)
    · apply mem_iUnion.2
      exact ⟨0, by rwa [familyVertexLists_zero]⟩
    · obtain ⟨i, hi⟩ := mem_iUnion.1 hz
      exact mem_iUnion.2 ⟨i.succ, by rwa [familyVertexLists_succ]⟩
  · intro hz
    obtain ⟨i, hi⟩ := mem_iUnion.1 hz
    cases i using Fin.cases with
    | zero => exact Or.inl (by rwa [familyVertexLists_zero] at hi)
    | succ i =>
      exact Or.inr (mem_iUnion.2 ⟨i, by rwa [familyVertexLists_succ] at hi⟩)

private theorem hull_iUnion_mono_of_hulls {ι : Type*} (s t : ι → Set ℂ)
    (h : ∀ i, convexHull ℝ (s i) ⊆ convexHull ℝ (t i)) :
    convexHull ℝ (⋃ i, s i) ⊆ convexHull ℝ (⋃ i, t i) := by
  apply convexHull_min _ (convex_convexHull ℝ _)
  intro z hz
  obtain ⟨i, hi⟩ := mem_iUnion.1 hz
  exact convexHull_mono (subset_iUnion t i) (h i (subset_convexHull ℝ _ hi))

theorem convexHull_jointVertices_eq_arcs (g : Fin 4 → (ℂ ≃ᵢ ℂ)) :
    convexHull ℝ (jointVertices g) =
      convexHull ℝ (⋃ i : Fin 4, g i '' trace (familyArcs i)) := by
  rw [jointVertices_eq_iUnion]
  have he : ∀ i : Fin 4, convexHull ℝ (g i '' {z | z ∈ familyVertexLists i}) =
      convexHull ℝ (g i '' trace (familyArcs i)) := by
    intro i
    rw [convexHull_image_isometry, convexHull_image_isometry, familyArcs_hull]
  exact le_antisymm (hull_iUnion_mono_of_hulls _ _ (fun i => (he i).le))
    (hull_iUnion_mono_of_hulls _ _ (fun i => (he i).ge))

theorem normalize_joint_arcs (g : Fin 4 → (ℂ ≃ᵢ ℂ)) :
    ∃ p : Placement, AnglesNormalized p ∧
      placementVolume p = volume (convexHull ℝ (⋃ i : Fin 4, g i '' trace (familyArcs i))) := by
  obtain ⟨p, hp, he⟩ := normalize_joint_placement g
  exact ⟨p, hp, he.trans (congrArg volume (convexHull_jointVertices_eq_arcs g))⟩

/-- The bridge also names the exact uncentered curves of the manuscript,
rather than requiring the caller to absorb their centers implicitly. -/
theorem normalize_paper_joint_arcs (g : Fin 4 → (ℂ ≃ᵢ ℂ)) :
    ∃ p : Placement, AnglesNormalized p ∧
      placementVolume p =
        volume (convexHull ℝ (⋃ i : Fin 4, g i '' trace (paperFamilyArcs i))) := by
  let g' : Fin 4 → (ℂ ≃ᵢ ℂ) := fun i => (IsometryEquiv.addRight (familyCenters i)).trans (g i)
  obtain ⟨p, hp, he⟩ := normalize_joint_arcs g'
  have hi : ∀ i : Fin 4, g' i '' trace (familyArcs i) = g i '' trace (paperFamilyArcs i) := by
    intro i
    rw [paperFamilyArcs_eq_translate, trace_isometry_comp, Set.image_image]
    rfl
  refine ⟨p, hp, he.trans ?_⟩
  congr 2
  exact iUnion_congr hi

/-- The cover-to-normalized-family bridge, including all mirror and frame
choices, holds for every convex universal cover of the shared unit arcs. -/
theorem cover_contains_normalized_placement (K : Set ℂ) (hK : Convex ℝ K)
    (hc : IsUniversalCover K) :
    ∃ p : Placement, AnglesNormalized p ∧ placementVolume p ≤ volume K := by
  have hcover : ∀ i : Fin 4, ∃ g : ℂ ≃ᵢ ℂ,
      g '' trace (familyArcs i) ⊆ K := fun i => hc _ (familyArcs_unit i)
  choose g hg using hcover
  have hv : ∀ i : Fin 4, g i '' {z | z ∈ familyVertexLists i} ⊆ K := by
    intro i z hz
    obtain ⟨v, hv, rfl⟩ := hz
    have hmem : v ∈ convexHull ℝ (trace (familyArcs i)) := by
      rw [familyArcs_hull]
      exact subset_convexHull ℝ _ hv
    have himg : g i v ∈ convexHull ℝ (g i '' trace (familyArcs i)) := by
      rw [convexHull_image_isometry]
      exact ⟨v, hmem, rfl⟩
    exact convexHull_min (hg i) hK himg
  have hjoint : jointVertices g ⊆ K := by
    apply union_subset
    · rw [← familyVertexLists_zero]
      exact hv 0
    · apply iUnion_subset
      intro i
      rw [← familyVertexLists_succ]
      exact hv i.succ
  obtain ⟨p, hp, hvol⟩ := normalize_joint_placement g
  exact ⟨p, hp, hvol.le.trans (measure_mono (convexHull_min hjoint hK))⟩

end MoserWorm
