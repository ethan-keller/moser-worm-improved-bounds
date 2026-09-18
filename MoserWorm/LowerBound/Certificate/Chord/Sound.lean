import MoserWorm.LowerBound.Certificate.Chord.Basic
import Mathlib.Data.List.Rotate
import MoserWorm.LowerBound.Certificate.Chord.Geometry

open MeasureTheory
open scoped ENNReal

namespace MoserWorm.LowerBound.Certificate.Chord

/-- A cut can be put in the generic geometry theorem's linear-list form. -/
theorem cut_decomposition (labels : List Label) (i j : Nat)
    (hij : i < j) (hj : j < labels.length) :
    ∃ pre xs ys : List Label,
      pre.length = i ∧ xs.length + i + 1 = j ∧
      labels = pre ++ labels.getD i 0 :: (xs ++ labels.getD j 0 :: ys) := by
  have hi : i < labels.length := hij.trans hj
  let pre := labels.take i
  let xs := (labels.drop (i + 1)).take (j - i - 1)
  let ys := labels.drop (j + 1)
  have hpre : pre.length = i := by simp [pre, Nat.min_eq_left (Nat.le_of_lt hi)]
  have hxs : xs.length = j - i - 1 := by
    simp only [xs, List.length_take, List.length_drop]
    exact Nat.min_eq_left (by omega)
  have htail : labels.drop (i + 1) = xs ++ labels.getD j 0 :: ys := by
    calc
      labels.drop (i + 1) = xs ++ (labels.drop (i + 1)).drop (j - i - 1) :=
        (List.take_append_drop _ _).symm
      _ = xs ++ labels.drop j := by
        rw [List.drop_drop, show i + 1 + (j - i - 1) = j by omega]
      _ = xs ++ labels.getD j 0 :: ys := by
        rw [List.drop_eq_getElem_cons hj, List.getD_eq_getElem _ _ hj]
  refine ⟨pre, xs, ys, hpre, by omega, ?_⟩
  calc
    labels = pre ++ labels.drop i := (List.take_append_drop _ _).symm
    _ = pre ++ labels.getD i 0 :: (xs ++ labels.getD j 0 :: ys) := by
      rw [List.drop_eq_getElem_cons hi, List.getD_eq_getElem _ _ hi, htail]

theorem leftArc_normal_form (pre xs ys : List Label) (a b : Label) :
    leftArc (pre ++ a :: (xs ++ b :: ys)) pre.length (pre.length + xs.length + 1) =
      a :: (xs ++ [b]) := by
  unfold leftArc
  rw [List.drop_append_length]
  have hn : pre.length + xs.length + 1 - pre.length + 1 = xs.length + 1 + 1 := by omega
  rw [hn, List.take_succ_cons, List.take_append]
  simp

theorem rightArc_normal_form (pre xs ys : List Label) (a b : Label) :
    rightArc (pre ++ a :: (xs ++ b :: ys)) pre.length (pre.length + xs.length + 1) =
      b :: ((ys ++ pre) ++ [a]) := by
  unfold rightArc
  rw [List.drop_append, List.take_append]
  have hdrop : (pre.drop (pre.length + xs.length + 1)) = [] :=
    List.drop_eq_nil_of_le (by omega)
  rw [hdrop]
  have hn : pre.length + xs.length + 1 - pre.length = xs.length + 1 := by omega
  rw [hn, List.drop_succ_cons, List.drop_append_length]
  simp [List.append_assoc]

theorem rotate_normal_form (pre xs ys : List Label) (a b : Label) :
    (pre ++ a :: (xs ++ b :: ys)).rotate pre.length =
      a :: (xs ++ b :: (ys ++ pre)) := by
  rw [List.rotate_eq_drop_append_take (by simp), List.drop_append_length,
    List.take_append_length]
  simp [List.append_assoc]

noncomputable def turn (p : Label → Plane) (t : Triple) : ℝ :=
  cross (p t.2.1 - p t.1) (p t.2.2 - p t.1)

/-- The closed half-plane guards include chord endpoints automatically.
`true` puts the first oriented arc on the nonpositive side of the chord. -/
theorem sideTests_sound (p : Label → Plane) (labels : List Label) (i j : Nat)
    (side : Bool)
    (h : ∀ t ∈ sideTests labels i j side, 0 ≤ turn p t) :
    let a := p (labels.getD i 0)
    let b := p (labels.getD j 0)
    (∀ k ∈ leftArc labels i j,
      if side then cross (b - a) (p k - a) ≤ 0
      else 0 ≤ cross (b - a) (p k - a)) ∧
    (∀ k ∈ rightArc labels i j,
      if side then 0 ≤ cross (b - a) (p k - a)
      else cross (b - a) (p k - a) ≤ 0) := by
  dsimp only
  constructor <;> intro k hk
  all_goals
    by_cases ha : k = labels.getD i 0
    · subst k
      cases side <;> simp [cross_apply]
    by_cases hb : k = labels.getD j 0
    · subst k
      cases side <;> simp [cross_apply, mul_comm]
  · cases side with
    | false =>
      have hm : (labels.getD i 0, labels.getD j 0, k) ∈ sideTests labels i j false := by
        simp only [sideTests, Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_map]
        exact Or.inl ⟨k, by
          simpa only [List.mem_filter, Bool.and_eq_true, bne_iff_ne] using
            And.intro hk (And.intro ha hb), rfl⟩
      exact h _ hm
    | true =>
      have hm : (labels.getD i 0, k, labels.getD j 0) ∈ sideTests labels i j true := by
        simp only [sideTests, ↓reduceIte, List.mem_append, List.mem_map]
        exact Or.inl ⟨k, by
          simpa only [List.mem_filter, Bool.and_eq_true, bne_iff_ne] using
            And.intro hk (And.intro ha hb), rfl⟩
      have ht := h _ hm
      simp only [turn] at ht
      rw [cross_swap] at ht
      exact neg_nonneg.mp ht
  · cases side with
    | false =>
      have hm : (labels.getD i 0, k, labels.getD j 0) ∈ sideTests labels i j false := by
        simp only [sideTests, Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_map]
        exact Or.inr ⟨k, by
          simpa only [List.mem_filter, Bool.and_eq_true, bne_iff_ne] using
            And.intro hk (And.intro ha hb), rfl⟩
      have ht := h _ hm
      simp only [turn] at ht
      rw [cross_swap] at ht
      exact neg_nonneg.mp ht
    | true =>
      have hm : (labels.getD i 0, labels.getD j 0, k) ∈ sideTests labels i j true := by
        simp only [sideTests, ↓reduceIte, List.mem_append, List.mem_map]
        exact Or.inr ⟨k, by
          simpa only [List.mem_filter, Bool.and_eq_true, bne_iff_ne] using
            And.intro hk (And.intro ha hb), rfl⟩
      exact h _ hm

/-- Exact geometric evidence; every child uses the reconstructed oriented arc.
Terminal bounds hold in every convex set containing that terminal's vertices.
There is no assumption that a cut is geometrically valid. -/
inductive Evidence (p : Label → Plane) : List Label → Witness → Prop where
  | terminal {labels}
      (bound : ∀ K : Set Plane, Convex ℝ K → (∀ k ∈ labels, p k ∈ K) →
        ENNReal.ofReal (shoelace (labels.map p)) ≤ volume K) :
      Evidence p labels .terminal
  | rotate {labels offset child} (index : offset < labels.length)
      (childEvidence : Evidence p (labels.rotate offset) child) :
      Evidence p labels (.rotate offset child)
  | cut {labels i j side nz l r}
      (indices : i < j ∧ j < labels.length ∧ 2 ≤ j - i ∧ j - i ≤ labels.length - 2)
      (nonzero : p (labels.getD i 0) ≠ p (labels.getD j 0))
      (sides : ∀ t ∈ sideTests labels i j side, 0 ≤ turn p t)
      (leftEvidence : Evidence p (leftArc labels i j) l)
      (rightEvidence : Evidence p (rightArc labels i j) r) :
      Evidence p labels (.cut i j side nz l r)

private theorem hull_rotate (l : List Plane) (n : Nat) :
    Geometry.hull (l.rotate n) = Geometry.hull l := by
  simp only [Geometry.hull, List.mem_rotate]

/-- The generic cut-area argument supports both short and longer fan terminals. -/
theorem Evidence.le_hull {p : Label → Plane} {labels : List Label} {w : Witness}
    (h : Evidence p labels w) :
    ENNReal.ofReal (shoelace (labels.map p)) ≤ volume (Geometry.hull (labels.map p)) := by
  induction h with
  | @terminal labels bound =>
    apply bound _ (convex_convexHull ℝ _)
    intro k hk
    exact subset_convexHull ℝ _ (List.mem_map.mpr ⟨k, hk, rfl⟩)
  | @rotate labels offset child index _ ih =>
    simpa only [List.map_rotate, Geometry.shoelace_rotate, hull_rotate] using ih
  | @cut labels i j side nz l r indices nonzero sides _ _ ihl ihr =>
    let a := labels.getD i 0
    let b := labels.getD j 0
    obtain ⟨pre, xs, ys, hpre, hxs, heq⟩ :=
      cut_decomposition labels i j indices.1 indices.2.1
    change labels = pre ++ a :: (xs ++ b :: ys) at heq
    have hj : pre.length + xs.length + 1 = j := by omega
    have hleft := leftArc_normal_form pre xs ys a b
    rw [← heq, hj, hpre] at hleft
    have hright := rightArc_normal_form pre xs ys a b
    rw [← heq, hj, hpre] at hright
    have hrotate := rotate_normal_form pre xs ys a b
    rw [← heq, hpre] at hrotate
    obtain ⟨hl, hr⟩ := sideTests_sound p labels i j side sides
    have hxmem : ∀ k ∈ xs, k ∈ leftArc labels i j := by
      intro k hk
      rw [hleft]
      simp [hk]
    have hymem : ∀ k ∈ ys ++ pre, k ∈ rightArc labels i j := by
      intro k hk
      rw [hright]
      exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl hk)))
    have hsep : Geometry.ChordSeparated (p a) (p b) (xs.map p) ((ys ++ pre).map p) := by
      refine ⟨Ne.symm nonzero, ?_⟩
      cases side with
      | false =>
        apply Or.inr
        constructor
        · intro q hq
          obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
          exact hr k (hymem k hk)
        · intro q hq
          obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
          exact hl k (hxmem k hk)
      | true =>
        apply Or.inl
        constructor
        · intro q hq
          obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
          exact hl k (hxmem k hk)
        · intro q hq
          obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
          exact hr k (hymem k hk)
    have hleftbound :
        ENNReal.ofReal (shoelace (p a :: (xs.map p ++ [p b]))) ≤
          volume (Geometry.hull (p a :: (xs.map p ++ [p b]))) := by
      simpa only [hleft, List.map_cons, List.map_append, List.map_nil] using ihl
    have hrightrotate :
        (p a :: p b :: (ys ++ pre).map p).rotate 1 = (rightArc labels i j).map p := by
      rw [hright]
      change (p a :: p b :: (ys ++ pre).map p).rotate (0 + 1) = _
      rw [List.rotate_cons_succ, List.rotate_zero]
      simp only [List.map_cons, List.map_append, List.map_nil, List.cons_append]
    rw [← hrightrotate] at ihr
    have hrightbound :
        ENNReal.ofReal (shoelace (p a :: p b :: (ys ++ pre).map p)) ≤
          volume (Geometry.hull (p a :: p b :: (ys ++ pre).map p)) := by
      simpa only [Geometry.shoelace_rotate, hull_rotate] using ihr
    have hparent :
        (labels.map p).rotate i = p a :: (xs.map p ++ p b :: (ys ++ pre).map p) := by
      rw [← List.map_rotate, hrotate]
      simp only [List.map_cons, List.map_append]
    have hb := Geometry.shoelace_cut_le_hull hsep hleftbound hrightbound
    rw [← hparent] at hb
    simpa only [Geometry.shoelace_rotate, hull_rotate] using hb

theorem Evidence.le_volume {p : Label → Plane} {labels : List Label} {w : Witness}
    (h : Evidence p labels w) {K : Set Plane} (hK : Convex ℝ K)
    (hmem : ∀ k ∈ labels, p k ∈ K) :
    ENNReal.ofReal (shoelace (labels.map p)) ≤ volume K := by
  apply h.le_hull.trans (measure_mono (Geometry.hull_subset hK ?_))
  intro q hq
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
  exact hmem k hk

theorem excludesZero_sound {a : DIval} {x : ℝ} (hx : x ∈ a)
    (hc : excludesZero a = true) : x ≠ 0 := by
  simp only [excludesZero, Bool.or_eq_true, decide_eq_true_eq] at hc
  obtain ⟨hl, hu⟩ := DIval.mem_iff_val.mp hx
  rcases hc with hc | hc
  · have hp : 0 < DIval.val a.lo :=
      div_pos (by exact_mod_cast hc) (by positivity)
    linarith
  · have hn : DIval.val a.hi < 0 :=
      div_neg_of_neg_of_pos (by exact_mod_cast hc) (by positivity)
    linarith

theorem fanNonnegative_sound {a b c : Corner.Vertex BodyId ℝ} {A B C : IVertex}
    (ha : VertexEncloses a A) (hb : VertexEncloses b B) (hc : VertexEncloses c C)
    {box : Coordinate → DIval} {x : Coordinate → ℝ}
    (hx : Corner.UnitRotations x) (hbox : ∀ i, x i ∈ box i)
    (hcheck : fanNonnegative box A B C = true) :
    0 ≤ cross (realize x b - realize x a) (realize x c - realize x a) := by
  simp only [fanNonnegative, Kernel.bound_eq, Bool.or_eq_true, decide_eq_true_eq] at hcheck
  rcases hcheck with h | h
  · have hm := (DIval.mem_iff_val.mp (directFanBound_mem ha hb hc hbox)).1
    have h0 : 0 ≤ DIval.val (directFanBound box A B C).lo :=
      div_nonneg (by exact_mod_cast h) (by positivity)
    exact h0.trans hm
  · rw [← eval_fanPoly x hx]
    have h0 : 0 ≤ DIval.val (centeredBound (fanPolynomial A B C) box).lo :=
      div_nonneg (by exact_mod_cast h) (by positivity)
    exact h0.trans (centeredBound_lower (fanPolynomial_encloses ha hb hc) hbox)

theorem nonzeroCheck_sound {box : Coordinate → DIval} {x : Coordinate → ℝ}
    {v : Label → IVertex} {r : Label → Corner.Vertex BodyId ℝ}
    (hv : ∀ k, VertexEncloses (r k) (v k))
    (hx : Corner.UnitRotations x) (hbox : ∀ i, x i ∈ box i)
    {a b : Label} {w : NonzeroWitness} (hc : nonzeroCheck box v a b w = true) :
    realize x (r a) ≠ realize x (r b) := by
  intro heq
  cases w with
  | coordinate =>
    have hm := directDifference_mem (hv b) (hv a) hbox
    have hre := congrArg Complex.re heq
    have him := congrArg Complex.im heq
    simp only [realize] at hre him
    simp only [nonzeroCheck, Bool.or_eq_true] at hc
    rcases hc with hc | hc
    · have hn := excludesZero_sound hm.1 hc
      apply hn
      change (Corner.position x (r b)).1 - (Corner.position x (r a)).1 = 0
      exact sub_eq_zero.mpr hre.symm
    · have hn := excludesZero_sound hm.2 hc
      apply hn
      change (Corner.position x (r b)).2 - (Corner.position x (r a)).2 = 0
      exact sub_eq_zero.mpr him.symm
  | side k reversed =>
    cases reversed with
    | false =>
      have hc' : Certificate.fanPositive box (v a) (v b) (v k) = true := by
        simpa only [nonzeroCheck, Kernel.fanPositive_eq] using hc
      have hp := fanPositive_pos (hv a) (hv b) (hv k) hx hbox hc'
      rw [eval_fanPoly x hx, heq] at hp
      simp [cross_apply] at hp
    | true =>
      have hc' : Certificate.fanPositive box (v a) (v k) (v b) = true := by
        simpa only [nonzeroCheck, Kernel.fanPositive_eq] using hc
      have hp := fanPositive_pos (hv a) (hv k) (hv b) hx hbox hc'
      rw [eval_fanPoly x hx, heq] at hp
      simp [cross_apply] at hp

theorem map_encloses {v : Label → IVertex} {r : Label → Corner.Vertex BodyId ℝ}
    (hv : ∀ k, VertexEncloses (r k) (v k)) (labels : List Label) :
    List.Forall₂ VertexEncloses (labels.map r) (labels.map v) := by
  induction labels with
  | nil => exact .nil
  | cons k labels ih => exact .cons (hv k) ih

/-- The interval-to-geometry bridge is unconditional for every enclosed
physical placement, including tied vertices and zero side determinants. -/
theorem check_sound {box : Coordinate → DIval} {x : Coordinate → ℝ}
    {v : Label → IVertex} {r : Label → Corner.Vertex BodyId ℝ}
    (hv : ∀ k, VertexEncloses (r k) (v k))
    (hx : Corner.UnitRotations x) (hbox : ∀ i, x i ∈ box i)
    (w : Witness) (labels : List Label) (hc : check box v labels w = true) :
    Evidence (fun k => realize x (r k)) labels w := by
  induction w generalizing labels with
  | terminal =>
    change Kernel.polygonValid box (labels.map v) = true at hc
    rw [Kernel.polygonValid_eq] at hc
    apply Evidence.terminal
    intro K hK hmem
    have hb := polygonValid_le_volume (map_encloses hv labels) hx hbox hc hK
      (by
        intro q hq
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hq
        exact hmem k hk)
    simpa only [points, List.map_map, Function.comp_def] using hb
  | rotate offset child ih =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq] at hc
    exact .rotate hc.1 (ih _ (by
      simpa only [List.rotate_eq_drop_append_take (Nat.le_of_lt hc.1)] using hc.2))
  | cut i j side nz l r ihl ihr =>
    simp only [check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
    obtain ⟨⟨⟨⟨hi, hn⟩, hs⟩, hl⟩, hr⟩ := hc
    refine .cut hi (nonzeroCheck_sound hv hx hbox hn) ?_ (ihl _ hl) (ihr _ hr)
    intro t ht
    exact fanNonnegative_sound (hv t.1) (hv t.2.1) (hv t.2.2) hx hbox (hs t ht)

theorem originalAreaPolynomial_eq (vertices : List IVertex) (leaf : Leaf) :
    originalAreaPolynomial
      (fun k => vertices.getD k.val (.fixed (DIval.ofInt 0, DIval.ofInt 0))) leaf =
    IPoly.sum (leaf.map fun f =>
      (shoelacePolynomial (selectedPoints vertices f.labels)).scale (DIval.pt f.weight)) := rfl

noncomputable def realLabels (box : PlacementBox) (k : Label) :
    Corner.Vertex BodyId ℝ :=
  (realVertices box).getD k.val (.fixed (0, 0))

/-- Physical-placement bridge, preserving the original total weight, each
original cyclic polygon, and the original mixed shoelace lower bound.
The geometric bound consumes the `Evidence` component. -/
theorem checkAnnotatedLeaf_evidence {box : PlacementBox} {leaf : AnnotatedLeaf}
    (hc : checkAnnotatedLeaf box leaf = true) {p : Placement}
    (hp : box.Mem (placementCoordinates p)) :
    (((plainLeaf leaf).map WeightedFan.weight).sum ≤ dfxOne) ∧
    (∀ f ∈ leaf, 0 ≤ f.fan.weight ∧ f.fan.labels.Nodup ∧
      Evidence (fun k => realize (liftedParameters box p) (realLabels box k))
        f.fan.labels f.witness) ∧
    (239 / 1000 : ℝ) ≤
      (Corner.weightedShoelacePoly (realLeaf box (plainLeaf leaf))).eval
        (liftedParameters box p) := by
  simp only [checkAnnotatedLeaf, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨_, ha⟩, hw⟩, hf⟩, harea⟩ := hc
  rw [Kernel.areaValid_eq] at harea
  have hvars := liftedBox_mem ha hp
  have hunit := liftedParameters_unit box p
  refine ⟨hw, ?_, ?_⟩
  · intro f hmem
    obtain ⟨⟨hweight, hlabels⟩, hcheck⟩ := hf f hmem
    refine ⟨hweight, hlabels, check_sound ?_ hunit hvars f.witness f.fan.labels hcheck⟩
    intro k
    exact VertexEncloses.getD (realVertices_encloses ha) k.val
  · exact areaValid_lower (realLeaf_encloses ha (plainLeaf leaf)) hvars harea

private theorem realLeaf_weight_sum (box : PlacementBox) (leaf : Leaf) :
    ((realLeaf box leaf).map Prod.fst).sum = DIval.val ((leaf.map WeightedFan.weight).sum) := by
  induction leaf with
  | nil => simp [realLeaf, DIval.val]
  | cons f leaf ih =>
    change DIval.val f.weight + ((realLeaf box leaf).map Prod.fst).sum =
      DIval.val (f.weight + (leaf.map WeightedFan.weight).sum)
    rw [ih]
    simp only [DIval.val, Int.cast_add, add_div]

/-- Geometric soundness of the annotated leaf checker. -/
theorem checkAnnotatedLeaf_sound {box : PlacementBox} {leaf : AnnotatedLeaf}
    (hc : checkAnnotatedLeaf box leaf = true) {p : Placement}
    (hp : box.Mem (placementCoordinates p)) :
    ENNReal.ofReal (239 / 1000 : ℝ) ≤ placementVolume p := by
  obtain ⟨hw, hf, harea⟩ := checkAnnotatedLeaf_evidence hc hp
  apply (ENNReal.ofReal_le_ofReal harea).trans
  apply weightedShoelacePoly_le_volume_of_bounds (liftedParameters_unit box p)
    (realLeaf box (plainLeaf leaf))
  · intro t ht
    obtain ⟨f, hmem, rfl⟩ := List.mem_map.mp ht
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hmem
    exact div_nonneg (by exact_mod_cast (hf a ha).1) (by positivity)
  · rw [realLeaf_weight_sum]
    have h : DIval.val ((List.map WeightedFan.weight (plainLeaf leaf)).sum) ≤ DIval.val dfxOne :=
      div_le_div_of_nonneg_right (by exact_mod_cast hw) (by positivity)
    exact h.trans_eq (by norm_num [DIval.val, dfxOne, dfxS])
  · intro t ht
    obtain ⟨f, hmem, rfl⟩ := List.mem_map.mp ht
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hmem
    have hb := (hf a ha).2.2.le_volume (placementHull_convex p) (by
      intro k hk
      exact selectedRealPoints_mem box p a.fan.labels (realLabels box k)
        (List.mem_map.mpr ⟨k, hk, rfl⟩))
    simpa only [points, selectedRealPoints, realLabels, List.map_map, Function.comp_def] using hb

theorem checkAnnotatedLeaf_sound_coordinates {box : PlacementBox} {leaf : AnnotatedLeaf}
    (hc : checkAnnotatedLeaf box leaf = true) {x : Fin 9 → ℝ} (hx : box.Mem x) :
    ENNReal.ofReal (239 / 1000 : ℝ) ≤ placementVolume (placementFromCoordinates x) :=
  checkAnnotatedLeaf_sound hc (by simpa only [placementCoordinates_fromCoordinates] using hx)


/-- The area lower bound throughout a closed placement box. -/
def coordinateBoxBound (box : PlacementBox) : Prop :=
  ∀ x : Fin 9 → ℝ, box.Mem x →
    ENNReal.ofReal tau ≤ placementVolume (placementFromCoordinates x)

/-- Promote an accepted annotated tree to its real box-area bound. -/
theorem coordinateBoxBound_of_annotated {box : PlacementBox} {tree : AnnotatedTree}
    (h : BoxTree.check checkAnnotatedLeaf box tree = true) : coordinateBoxBound box :=
  BoxTree.check_sound checkAnnotatedLeaf
    (fun x => ENNReal.ofReal tau ≤ placementVolume (placementFromCoordinates x))
    (fun _ _ hc _ hx => checkAnnotatedLeaf_sound_coordinates hc hx) tree box h

/-- Reuse a legacy tree's existing acceptance theorem without rechecking its data. -/
theorem coordinateBoxBound_of_legacy {box : PlacementBox} {tree : BoxTree 9 Leaf}
    (h : BoxTree.check Certificate.checkLeaf box tree = true) : coordinateBoxBound box :=
  BoxTree.check_sound Certificate.checkLeaf
    (fun x => ENNReal.ofReal tau ≤ placementVolume (placementFromCoordinates x))
    (fun _ _ hc _ hx => Certificate.checkLeaf_sound_coordinates hc hx) tree box h

/-- Combine adjacent certified boxes, independently of their leaf witness format. -/
theorem coordinateBoxBound_split {box : PlacementBox} (axis : Fin 9)
    (hl : coordinateBoxBound (box.left axis)) (hr : coordinateBoxBound (box.right axis)) :
    coordinateBoxBound box :=
  DyadicBox.of_split axis hl hr

theorem root_lower_bound_of_coordinateBoxBound (h : coordinateBoxBound Certificate.root) :
    ∀ p : Placement, Certificate.root.Mem (placementCoordinates p) →
      ENNReal.ofReal tau ≤ placementVolume p := by
  intro p hp
  simpa only [placementFromCoordinates_coordinates] using h (placementCoordinates p) hp


end MoserWorm.LowerBound.Certificate.Chord
