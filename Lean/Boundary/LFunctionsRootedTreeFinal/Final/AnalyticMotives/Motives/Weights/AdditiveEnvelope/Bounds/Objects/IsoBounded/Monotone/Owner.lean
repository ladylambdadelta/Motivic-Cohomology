import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Monotone.Objects.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Objects.IsoBounded.Owner

/-!
# Monotonicity of iso-bounded additive analytic objects

Increasing the numeric weight bound preserves an iso-bounded object by rebounding
its bounded representative.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Rebound an iso-bounded object along an inequality of numeric bounds. -/
def TraceAnalyticAdditiveObject.IsoBoundedBy.rebound
    {object : TraceAnalyticAdditiveObject}
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    (isoBounded : TraceAnalyticAdditiveObject.IsoBoundedBy object lower) :
    TraceAnalyticAdditiveObject.IsoBoundedBy object upper where
  representative := isoBounded.boundedRepresentative.rebound bound_le
  iso := isoBounded.objectIsoRepresentative

/-- Rebounding preserves the underlying bounded representative object. -/
theorem TraceAnalyticAdditiveObject.IsoBoundedBy.rebound_representative_object
    {object : TraceAnalyticAdditiveObject}
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    (isoBounded : TraceAnalyticAdditiveObject.IsoBoundedBy object lower) :
    (isoBounded.rebound bound_le).boundedRepresentative.object =
      isoBounded.boundedRepresentative.object :=
  rfl

/-- Rebounding preserves the actual isomorphism target object. -/
theorem TraceAnalyticAdditiveObject.IsoBoundedBy.rebound_weightLevel_le
    {object : TraceAnalyticAdditiveObject}
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    (isoBounded : TraceAnalyticAdditiveObject.IsoBoundedBy object lower) :
    (isoBounded.rebound bound_le).boundedRepresentative.object.weightLevel ≤
      upper :=
  (isoBounded.rebound bound_le).representative_weightLevel_le

end AnalyticMotives
end LFunctions
end Boundary
