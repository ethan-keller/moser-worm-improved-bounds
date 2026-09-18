import MoserWorm.Common.Audit
import MoserWorm.UpperBound.Main
import MoserWorm.LowerBound.Main

namespace MoserWorm

theorem bounds :
    ENNReal.ofReal (239 / 1000 : ℝ) ≤ optimalArea ∧
    optimalArea ≤ ENNReal.ofReal
      (7170601298323360123534337 / 29109471743520000000000000 : ℝ) := by
  refine ⟨optimalArea_lower_bound, ?_⟩
  simpa [UpperBound.areaK] using optimalArea_upper_bound

end MoserWorm

audit_axioms MoserWorm.bounds
