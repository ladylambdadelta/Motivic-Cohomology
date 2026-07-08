import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.ShiftedDegreeDirectSum.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Maps.Owner

/-!
# Standard degree objects for bounded analytic mapping cones

The standard cochain mapping-cone degree over a map `source ⟶ target` is the
direct sum of the source degree shifted by one and the target degree.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The standard bounded finite trace family in a mapping-cone degree. -/
def TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom.mappingConeDegreeObject
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (degree : ℤ) :
    TraceAnalyticAdditiveObject.BoundedBy bound :=
  (source.degreeObject (degree + (1 : ℤ))).directSum
    (target.degreeObject degree)

/-- The mapping-cone degree object is shifted source degree plus target degree. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom.mappingConeDegreeObject_object
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (degree : ℤ) :
    (hom.mappingConeDegreeObject degree).object =
      TraceAnalyticAdditiveObject.directSum
        (source.complex.objectAt (degree + (1 : ℤ)))
        (target.complex.objectAt degree) :=
  rfl

/-- The standard mapping-cone degree object satisfies the ambient weight bound. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom.mappingConeDegreeObject_weightLevel_le
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (degree : ℤ) :
    (hom.mappingConeDegreeObject degree).object.weightLevel ≤ bound :=
  (hom.mappingConeDegreeObject degree).weightLevel_le

end AnalyticMotives
end LFunctions
end Boundary
