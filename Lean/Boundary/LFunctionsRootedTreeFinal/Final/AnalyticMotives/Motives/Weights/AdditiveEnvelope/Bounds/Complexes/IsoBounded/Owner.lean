import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Objects.IsoBounded.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.Owner

/-!
# Complexes with iso-bounded degree objects

An additive analytic complex is degreewise iso-bounded when each actual degree
object is isomorphic to a bounded finite trace-family representative.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- A complex whose degree objects are bounded up to analytic isomorphism. -/
structure TraceAnalyticAdditiveCochainComplex.DegreewiseIsoBoundedBy
    (complex : TraceAnalyticAdditiveCochainComplex)
    (bound : Nat) where
  degreeIsoBounded :
    (degree : ℤ) →
      TraceAnalyticAdditiveObject.IsoBoundedBy
        (complex.objectAt degree)
        bound

/-- The iso-bounded object in a given degree. -/
def TraceAnalyticAdditiveCochainComplex.DegreewiseIsoBoundedBy.degreeObject
    {complex : TraceAnalyticAdditiveCochainComplex}
    {bound : Nat}
    (isoBounded :
      TraceAnalyticAdditiveCochainComplex.DegreewiseIsoBoundedBy
        complex
        bound)
    (degree : ℤ) :
    TraceAnalyticAdditiveObject.IsoBoundedBy
      (complex.objectAt degree)
      bound :=
  isoBounded.degreeIsoBounded degree

/-- The bounded representative in a degree satisfies the ambient weight bound. -/
theorem TraceAnalyticAdditiveCochainComplex.DegreewiseIsoBoundedBy.degreeObject_weightLevel_le
    {complex : TraceAnalyticAdditiveCochainComplex}
    {bound : Nat}
    (isoBounded :
      TraceAnalyticAdditiveCochainComplex.DegreewiseIsoBoundedBy
        complex
        bound)
    (degree : ℤ) :
    (isoBounded.degreeObject degree).boundedRepresentative.object.weightLevel ≤
      bound :=
  (isoBounded.degreeObject degree).representative_weightLevel_le

end AnalyticMotives
end LFunctions
end Boundary
