import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Package.ThirdIsoBounded.Maps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.ThirdObject.Maps.Exactness.Owner

/-!
# Named-map exactness for full bounded mapping-cone packages

The full bounded mapping-cone package inherits the three consecutive zero
composites for the named bounded map, cone inclusion, and connecting map.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The first two named maps of the full package compose to zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_firstMap_comp_secondMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap hom ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap hom =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.first_comp_secondMap
    hom

/-- The cone inclusion followed by the connecting map is zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_secondMap_comp_connectingMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap hom ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap hom =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap_comp_connectingMap
    hom

/-- The connecting map followed by the shifted bounded map is zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_connectingMap_comp_shifted_firstMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap hom ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
          hom)⟦(1 : ℤ)⟧' =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap_comp_shifted_firstMap
    hom

end AnalyticMotives
end LFunctions
end Boundary
