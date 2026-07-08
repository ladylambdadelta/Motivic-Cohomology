import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.Owner

/-!
# Degreewise bounded representatives of additive analytic complexes

Some constructions, such as Mathlib mapping cones, provide degree objects only
up to canonical isomorphism with the concrete bounded finite trace families used
by the analytic additive envelope.  This file records that degreewise data.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- A complex with a bounded representative for each degree object. -/
structure TraceAnalyticAdditiveCochainComplex.DegreewiseBoundedRepresentative
    (bound : Nat) where
  complex : TraceAnalyticAdditiveCochainComplex
  degreeRepresentative :
    (degree : ℤ) →
      TraceAnalyticAdditiveObject.BoundedBy bound
  degreeIso :
    (degree : ℤ) →
      complex.objectAt degree ≅ (degreeRepresentative degree).object

/-- The bounded representative object in a given degree. -/
def TraceAnalyticAdditiveCochainComplex.DegreewiseBoundedRepresentative.degreeObject
    {bound : Nat}
    (representative :
      TraceAnalyticAdditiveCochainComplex.DegreewiseBoundedRepresentative bound)
    (degree : ℤ) :
    TraceAnalyticAdditiveObject.BoundedBy bound :=
  representative.degreeRepresentative degree

/-- The degree isomorphism to the chosen bounded finite trace family. -/
def TraceAnalyticAdditiveCochainComplex.DegreewiseBoundedRepresentative.degreeObjectIso
    {bound : Nat}
    (representative :
      TraceAnalyticAdditiveCochainComplex.DegreewiseBoundedRepresentative bound)
    (degree : ℤ) :
    representative.complex.objectAt degree ≅
      (representative.degreeObject degree).object :=
  representative.degreeIso degree

/-- The chosen degree object is bounded by the ambient numeric bound. -/
theorem TraceAnalyticAdditiveCochainComplex.DegreewiseBoundedRepresentative.degreeObject_weightLevel_le
    {bound : Nat}
    (representative :
      TraceAnalyticAdditiveCochainComplex.DegreewiseBoundedRepresentative bound)
    (degree : ℤ) :
    (representative.degreeObject degree).object.weightLevel ≤ bound :=
  (representative.degreeObject degree).weightLevel_le

end AnalyticMotives
end LFunctions
end Boundary
