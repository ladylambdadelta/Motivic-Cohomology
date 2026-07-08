import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Package.ThirdIsoBounded.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.ThirdObject.Maps.Connecting.Owner

/-!
# Named maps in full bounded mapping-cone packages

The full bounded mapping-cone package exposes the source map, cone inclusion,
and connecting morphism through the named concrete mapping-cone maps.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The first morphism of the full package is the named bounded map. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_firstMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded
      hom).trianglePackage.triangle.mor₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap hom :=
  rfl

/-- The second morphism of the full package is the named cone-inclusion map. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_secondMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded
      hom).trianglePackage.triangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap hom :=
  rfl

/-- The third morphism of the full package is the named connecting map. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_connectingMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded
      hom).trianglePackage.triangle.mor₃ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap hom :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
