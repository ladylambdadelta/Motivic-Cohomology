import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.DegreeObject.Concrete.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.ThirdObject.Owner

/-!
# Degrees of the third vertex in bounded analytic mapping-cone triangles

The third vertex is represented by Mathlib's mapping-cone complex.  Its degree
objects are canonically isomorphic to the source-shift/target binary biproducts.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Limits

/-- The degree object of the concrete complex representing the third vertex. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObjectDegree
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (degree : ℤ) :
    TraceAnalyticAdditiveCategoryObject :=
  hom.actualMappingConeDegreeObject degree

/-- The third-object degree is the actual Mathlib cone degree object. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObjectDegree_eq
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (degree : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObjectDegree
        hom
        degree =
      hom.actualMappingConeDegreeObject degree :=
  rfl

/-- Each third-object degree is the shifted-source/target biproduct. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObjectDegreeIsoBiprod
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (degree : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObjectDegree
        hom
        degree ≅
      source.complex.objectAt (degree + (1 : ℤ)) ⊞
      target.complex.objectAt degree :=
  hom.actualMappingConeDegreeIsoBiprod degree

/-- Each third-object degree is isomorphic to the concrete bounded degree object. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObjectDegreeIsoStandard
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (degree : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObjectDegree
        hom
        degree ≅
      (hom.mappingConeDegreeObject degree).object :=
  hom.actualMappingConeDegreeIsoStandard degree

end AnalyticMotives
end LFunctions
end Boundary
