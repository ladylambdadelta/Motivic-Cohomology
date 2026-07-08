import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.Core.ThirdIsoBounded.Degrees.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Package.ThirdIsoBounded.Owner

/-!
# Degree accessors for full bounded mapping-cone packages

The full bounded mapping-cone package exposes the actual cone degree object and
the standard bounded cone-degree representative in each degree.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The actual degree object of the full mapping-cone package's third representative. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_thirdDegreeObject
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (degree : ℤ) :
    TraceAnalyticAdditiveObject :=
  (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded
    hom).thirdDegreeObject degree

/-- The bounded representative is the standard cone-degree object. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_thirdDegreeBoundedRepresentative
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (degree : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded
      hom).thirdDegreeBoundedRepresentative degree =
      hom.mappingConeDegreeObject degree :=
  rfl

/-- The standard cone-degree representative satisfies the ambient bound. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_thirdDegreeBoundedRepresentative_weightLevel_le
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (degree : ℤ) :
    ((TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded
      hom).thirdDegreeBoundedRepresentative degree).object.weightLevel ≤ bound :=
  (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded
    hom).thirdDegreeBoundedRepresentative_weightLevel_le degree

end AnalyticMotives
end LFunctions
end Boundary
