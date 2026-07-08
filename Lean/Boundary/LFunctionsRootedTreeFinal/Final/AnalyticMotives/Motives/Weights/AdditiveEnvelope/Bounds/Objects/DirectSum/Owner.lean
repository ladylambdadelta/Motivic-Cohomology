import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Objects.Owner

/-!
# Boundedness of direct sums of additive analytic objects

The additive-envelope direct sum is concatenation of finite trace families.
Since weights are computed by a recursive maximum, a direct sum of two bounded
families is bounded by the same numeric weight bound.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A direct sum of two bounded finite trace families is bounded. -/
theorem TraceAnalyticAdditiveObject.weightLevel_directSum_le
    (left right : TraceAnalyticAdditiveObject)
    {bound : Nat}
    (left_le : left.weightLevel ≤ bound)
    (right_le : right.weightLevel ≤ bound) :
    (TraceAnalyticAdditiveObject.directSum left right).weightLevel ≤ bound :=
  match left with
  | [] => right_le
  | object :: tail =>
      max_le
        (max_le_iff.mp left_le).left
        (TraceAnalyticAdditiveObject.weightLevel_directSum_le
          tail
          right
          (max_le_iff.mp left_le).right
          right_le)

/-- Direct sum as an operation on bounded finite trace families. -/
def TraceAnalyticAdditiveObject.BoundedBy.directSum
    {bound : Nat}
    (left right : TraceAnalyticAdditiveObject.BoundedBy bound) :
    TraceAnalyticAdditiveObject.BoundedBy bound :=
  ⟨TraceAnalyticAdditiveObject.directSum left.object right.object,
    TraceAnalyticAdditiveObject.weightLevel_directSum_le
      left.object
      right.object
      left.weightLevel_le
      right.weightLevel_le⟩

/-- The underlying object of a bounded direct sum is the ordinary direct sum. -/
theorem TraceAnalyticAdditiveObject.BoundedBy.directSum_object
    {bound : Nat}
    (left right : TraceAnalyticAdditiveObject.BoundedBy bound) :
    (left.directSum right).object =
      TraceAnalyticAdditiveObject.directSum left.object right.object :=
  rfl

/-- The bounded direct sum has the expected weight inequality. -/
theorem TraceAnalyticAdditiveObject.BoundedBy.directSum_weightLevel_le
    {bound : Nat}
    (left right : TraceAnalyticAdditiveObject.BoundedBy bound) :
    (left.directSum right).object.weightLevel ≤ bound :=
  (left.directSum right).weightLevel_le

end AnalyticMotives
end LFunctions
end Boundary
