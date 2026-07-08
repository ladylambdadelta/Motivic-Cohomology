import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Objects.DirectSum.Owner

/-!
# Degreewise direct sums of bounded additive analytic complexes

For two complexes bounded by the same numeric weight level, the direct sum of
their degree objects is again a bounded finite trace family in each degree.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The degreewise direct sum object of two bounded additive analytic complexes. -/
def TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.degreeDirectSumObject
    {bound : Nat}
    (left right : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound)
    (degree : ℤ) :
    TraceAnalyticAdditiveObject.BoundedBy bound :=
  (left.degreeObject degree).directSum
    (right.degreeObject degree)

/-- The degreewise bounded direct sum has the ordinary direct-sum object underneath. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.degreeDirectSumObject_object
    {bound : Nat}
    (left right : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound)
    (degree : ℤ) :
    (left.degreeDirectSumObject right degree).object =
      TraceAnalyticAdditiveObject.directSum
        (left.complex.objectAt degree)
        (right.complex.objectAt degree) :=
  rfl

/-- The degreewise direct sum object satisfies the same numeric weight bound. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.degreeDirectSumObject_weightLevel_le
    {bound : Nat}
    (left right : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound)
    (degree : ℤ) :
    (left.degreeDirectSumObject right degree).object.weightLevel ≤ bound :=
  (left.degreeDirectSumObject right degree).weightLevel_le

end AnalyticMotives
end LFunctions
end Boundary
