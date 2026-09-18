import MoserWorm.Common.Audit
import MoserWorm.LowerBound.Certificate.Complete
import MoserWorm.LowerBound.Certificate.Generated.Assembly

open MeasureTheory

namespace MoserWorm

open LowerBound.Certificate

theorem lower_bound (K : Set Plane) (hK : IsConvexUniversalCover K) :
    ENNReal.ofReal (239 / 1000 : ℝ) ≤ volume K :=
  universal_cover_lower_bound_of_certificate_root Generated.rootLowerBound K hK

theorem optimalArea_lower_bound : ENNReal.ofReal (239 / 1000 : ℝ) ≤ optimalArea :=
  le_optimalArea lower_bound

end MoserWorm

audit_axioms MoserWorm.lower_bound MoserWorm.optimalArea_lower_bound
