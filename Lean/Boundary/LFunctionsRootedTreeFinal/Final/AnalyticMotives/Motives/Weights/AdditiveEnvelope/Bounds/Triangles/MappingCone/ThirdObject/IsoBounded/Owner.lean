import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Complexes.IsoBounded.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.ThirdObject.Degrees.IsoBounded.Owner

/-!
# Degreewise iso-bounded mapping-cone third-object complexes

The concrete mapping-cone complex representing the third vertex is degreewise
iso-bounded by the same ambient weight bound as the source and target.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Mathlib's mapping-cone complex is degreewise iso-bounded. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObjectDegreewiseIsoBounded
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    TraceAnalyticAdditiveCochainComplex.DegreewiseIsoBoundedBy
      (CochainComplex.mappingCone hom)
      bound where
  degreeIsoBounded :=
    fun degree =>
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObjectDegreeIsoBounded
        hom
        degree

/-- The degreewise iso-bounded datum uses the standard cone-degree representative. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObjectDegreewiseIsoBounded_representative
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (degree : ℤ) :
    ((TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObjectDegreewiseIsoBounded
      hom).degreeObject degree).boundedRepresentative =
      hom.mappingConeDegreeObject degree :=
  rfl

/-- The representative degree object satisfies the ambient bound. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObjectDegreewiseIsoBounded_weightLevel_le
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (degree : ℤ) :
    ((TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObjectDegreewiseIsoBounded
      hom).degreeObject degree).boundedRepresentative.object.weightLevel ≤
      bound :=
  (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObjectDegreewiseIsoBounded
    hom).degreeObject_weightLevel_le degree

end AnalyticMotives
end LFunctions
end Boundary
