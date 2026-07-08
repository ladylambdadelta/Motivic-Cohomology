import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Objects.DirectSum.Owner

/-!
# Shifted degreewise direct sums of bounded additive analytic complexes

For two bounded complexes, one may form a bounded finite trace family by taking
one degree from the left complex and a shifted degree from the right complex.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The direct sum of one degree object and a shifted degree object. -/
def TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.shiftedDegreeDirectSumObject
    {bound : Nat}
    (left right : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound)
    (degree shift : ℤ) :
    TraceAnalyticAdditiveObject.BoundedBy bound :=
  (left.degreeObject degree).directSum
    (right.degreeObject (degree + shift))

/-- The shifted degreewise direct sum has the ordinary direct-sum object underneath. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.shiftedDegreeDirectSumObject_object
    {bound : Nat}
    (left right : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound)
    (degree shift : ℤ) :
    (left.shiftedDegreeDirectSumObject right degree shift).object =
      TraceAnalyticAdditiveObject.directSum
        (left.complex.objectAt degree)
        (right.complex.objectAt (degree + shift)) :=
  rfl

/-- The shifted degreewise direct sum satisfies the same numeric weight bound. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.shiftedDegreeDirectSumObject_weightLevel_le
    {bound : Nat}
    (left right : TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound)
    (degree shift : ℤ) :
    (left.shiftedDegreeDirectSumObject right degree shift).object.weightLevel ≤
      bound :=
  (left.shiftedDegreeDirectSumObject right degree shift).weightLevel_le

end AnalyticMotives
end LFunctions
end Boundary
