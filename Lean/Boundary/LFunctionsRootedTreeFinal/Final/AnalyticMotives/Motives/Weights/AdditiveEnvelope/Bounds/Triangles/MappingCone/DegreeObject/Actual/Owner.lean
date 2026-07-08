import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.DegreeObject.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.DirectSum.Biproduct.Mathlib.Owner

/-!
# Actual Mathlib degree objects of bounded analytic mapping cones

Mathlib implements the cochain mapping cone as a homotopy cofiber.  In degree
`p`, the actual cone object is canonically isomorphic to the binary biproduct
of the shifted source degree `p + 1` and the target degree `p`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Limits

/-- The actual degree object of Mathlib's mapping cone of a bounded chain map. -/
def TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom.actualMappingConeDegreeObject
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (degree : ℤ) :
    TraceAnalyticAdditiveCategoryObject :=
  (CochainComplex.mappingCone hom).X degree

/-- The actual cone degree is the object field of Mathlib's mapping cone. -/
theorem TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom.actualMappingConeDegreeObject_eq
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (degree : ℤ) :
    hom.actualMappingConeDegreeObject degree =
      (CochainComplex.mappingCone hom).X degree :=
  rfl

/-- The actual cone degree is canonically the source-shift/target biproduct. -/
def TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom.actualMappingConeDegreeIsoBiprod
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (degree : ℤ) :
    hom.actualMappingConeDegreeObject degree ≅
      source.complex.objectAt (degree + (1 : ℤ)) ⊞
        target.complex.objectAt degree :=
  HomologicalComplex.homotopyCofiber.XIsoBiprod
    hom
    degree
    (degree + (1 : ℤ))
    rfl

end AnalyticMotives
end LFunctions
end Boundary
