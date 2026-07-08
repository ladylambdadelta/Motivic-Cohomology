import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.Core.ThirdIsoBounded.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Package.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.ThirdObject.IsoBounded.Owner

/-!
# Packaged bounded mapping-cone triangles with iso-bounded third vertices

Every bounded chain map determines a bounded distinguished triangle whose third
vertex is represented by Mathlib's mapping-cone complex, degreewise iso-bounded
by the same ambient weight bound.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The full bounded mapping-cone triangle package with iso-bounded third vertex data. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangleWithThirdIsoBounded
      bound where
  boundedTriangle :=
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangle hom
  thirdComplex := CochainComplex.mappingCone hom
  thirdObject_eq := rfl
  thirdIsoBounded :=
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObjectDegreewiseIsoBounded
      hom

/-- The underlying bounded triangle is the packaged mapping-cone triangle. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_trianglePackage
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded
      hom).trianglePackage =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangle
        hom :=
  rfl

/-- The representative third complex is Mathlib's mapping-cone complex. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_thirdComplex
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded
      hom).thirdRepresentativeComplex =
      CochainComplex.mappingCone hom :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
