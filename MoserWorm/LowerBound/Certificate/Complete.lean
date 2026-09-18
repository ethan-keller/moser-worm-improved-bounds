import MoserWorm.LowerBound.Certificate.LeafSound

open MeasureTheory

namespace MoserWorm.LowerBound.Certificate

theorem root_lower_bound_of_accepted {tree : BoxTree 9 Leaf}
    (h : BoxTree.check checkLeaf root tree = true) :
    ∀ p : Placement, root.Mem (placementCoordinates p) →
      ENNReal.ofReal tau ≤ placementVolume p := by
  have hs := BoxTree.check_sound checkLeaf
    (fun x => ENNReal.ofReal tau ≤ placementVolume (placementFromCoordinates x))
    (fun _ _ h _ hx => checkLeaf_sound_coordinates h hx) tree root h
  intro p hp
  simpa only [placementFromCoordinates_coordinates] using hs (placementCoordinates p) hp

theorem universal_cover_lower_bound_of_accepted {tree : BoxTree 9 Leaf}
    (h : BoxTree.check checkLeaf root tree = true)
    (K : Set Plane) (hK : IsConvexUniversalCover K) :
    ENNReal.ofReal tau ≤ volume K :=
  universal_cover_lower_bound_of_certificate_root (root_lower_bound_of_accepted h) K hK

theorem optimalArea_lower_bound_of_accepted {tree : BoxTree 9 Leaf}
    (h : BoxTree.check checkLeaf root tree = true) :
    ENNReal.ofReal tau ≤ optimalArea :=
  le_optimalArea (universal_cover_lower_bound_of_accepted h)

end MoserWorm.LowerBound.Certificate
