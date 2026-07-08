import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Homotopy.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Monotone.Maps.Owner

/-!
# Monotonicity in the additive analytic homotopy category

Changing a bounded representative to a larger numeric bound does not change
its image in the additive analytic homotopy category.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Rebounding a bounded complex preserves its homotopy-category object. -/
theorem TraceAnalyticAdditiveHomotopyCategory.weightBoundedObject_rebound
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    (complex :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy lower) :
    TraceAnalyticAdditiveHomotopyCategory.weightBoundedObject
        (complex.rebound bound_le) =
      TraceAnalyticAdditiveHomotopyCategory.weightBoundedObject complex :=
  rfl

/-- Rebounding a bounded chain map preserves its homotopy-category morphism. -/
theorem TraceAnalyticAdditiveHomotopyCategory.weightBoundedMap_rebound
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy lower}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    TraceAnalyticAdditiveHomotopyCategory.weightBoundedMap
        (hom.rebound bound_le) =
      TraceAnalyticAdditiveHomotopyCategory.weightBoundedMap hom :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
