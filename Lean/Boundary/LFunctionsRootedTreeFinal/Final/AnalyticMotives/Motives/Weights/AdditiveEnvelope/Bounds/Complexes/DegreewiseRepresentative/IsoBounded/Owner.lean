import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.DegreewiseRepresentative.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Objects.IsoBounded.Owner

/-!
# Iso-bounded degree objects from degreewise representatives

A degreewise bounded representative of a complex makes each actual degree
object bounded up to analytic isomorphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The actual degree object of a represented complex is iso-bounded. -/
def TraceAnalyticAdditiveCochainComplex.DegreewiseBoundedRepresentative.degreeIsoBounded
    {bound : Nat}
    (representative :
      TraceAnalyticAdditiveCochainComplex.DegreewiseBoundedRepresentative bound)
    (degree : ℤ) :
    TraceAnalyticAdditiveObject.IsoBoundedBy
      (representative.complex.objectAt degree)
      bound where
  representative := representative.degreeObject degree
  iso := representative.degreeObjectIso degree

/-- The iso-bounded representative in a degree is the chosen bounded degree object. -/
theorem TraceAnalyticAdditiveCochainComplex.DegreewiseBoundedRepresentative.degreeIsoBounded_representative
    {bound : Nat}
    (representative :
      TraceAnalyticAdditiveCochainComplex.DegreewiseBoundedRepresentative bound)
    (degree : ℤ) :
    (representative.degreeIsoBounded degree).boundedRepresentative =
      representative.degreeObject degree :=
  rfl

/-- The bounded representative in a degree satisfies the ambient weight bound. -/
theorem TraceAnalyticAdditiveCochainComplex.DegreewiseBoundedRepresentative.degreeIsoBounded_weightLevel_le
    {bound : Nat}
    (representative :
      TraceAnalyticAdditiveCochainComplex.DegreewiseBoundedRepresentative bound)
    (degree : ℤ) :
    (representative.degreeIsoBounded degree).boundedRepresentative.object.weightLevel ≤
      bound :=
  (representative.degreeIsoBounded degree).representative_weightLevel_le

end AnalyticMotives
end LFunctions
end Boundary
