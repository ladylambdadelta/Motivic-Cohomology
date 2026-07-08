import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Objects.Owner

/-!
# Monotonicity of bounded finite trace families

Increasing the numeric weight bound gives an inclusion of bounded finite
analytic trace families.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Rebound a finite trace family along an inequality of weight bounds. -/
def TraceAnalyticAdditiveObject.BoundedBy.rebound
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    (object : TraceAnalyticAdditiveObject.BoundedBy lower) :
    TraceAnalyticAdditiveObject.BoundedBy upper :=
  ⟨object.object,
    Nat.le_trans
      object.weightLevel_le
      bound_le⟩

/-- Rebounding preserves the underlying finite trace family. -/
theorem TraceAnalyticAdditiveObject.BoundedBy.rebound_object
    {lower upper : Nat}
    (bound_le : lower ≤ upper)
    (object : TraceAnalyticAdditiveObject.BoundedBy lower) :
    (object.rebound bound_le).object =
      object.object :=
  rfl

/-- Rebounding the bounded zero family preserves the underlying zero family. -/
theorem TraceAnalyticAdditiveObject.BoundedBy.rebound_zero_object
    {lower upper : Nat}
    (bound_le : lower ≤ upper) :
    ((TraceAnalyticAdditiveObject.zeroBoundedBy lower).rebound
      bound_le).object =
      TraceAnalyticAdditiveObject.zero :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
