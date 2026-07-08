import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.DegreewiseRepresentative.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.ThirdObject.Degrees.Owner

/-!
# Degreewise bounded representatives for mapping-cone third vertices

The concrete complex representing the third vertex of a bounded mapping-cone
triangle has, in every degree, a bounded finite trace-family representative
canonically isomorphic to its actual Mathlib degree object.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The mapping-cone complex equipped with bounded representatives in every degree. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.degreewiseBoundedRepresentative
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    TraceAnalyticAdditiveCochainComplex.DegreewiseBoundedRepresentative bound where
  complex := CochainComplex.mappingCone hom
  degreeRepresentative := hom.mappingConeDegreeObject
  degreeIso :=
    fun degree =>
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObjectDegreeIsoStandard
        hom
        degree

/-- The representative complex is Mathlib's mapping-cone complex. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.degreewiseBoundedRepresentative_complex
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.degreewiseBoundedRepresentative
      hom).complex =
      CochainComplex.mappingCone hom :=
  rfl

/-- The representative degree object is the standard bounded cone-degree object. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.degreewiseBoundedRepresentative_degreeObject
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (degree : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.degreewiseBoundedRepresentative
      hom).degreeObject degree =
      hom.mappingConeDegreeObject degree :=
  rfl

/-- Each mapping-cone degree representative satisfies the ambient weight bound. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.degreewiseBoundedRepresentative_degreeObject_weightLevel_le
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (degree : ℤ) :
    ((TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.degreewiseBoundedRepresentative
      hom).degreeObject degree).object.weightLevel ≤ bound :=
  (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.degreewiseBoundedRepresentative
    hom).degreeObject_weightLevel_le degree

end AnalyticMotives
end LFunctions
end Boundary
