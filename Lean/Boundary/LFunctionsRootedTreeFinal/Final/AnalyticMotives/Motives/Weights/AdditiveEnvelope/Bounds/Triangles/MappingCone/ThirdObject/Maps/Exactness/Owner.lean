import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Package.Exactness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.ThirdObject.Maps.Connecting.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.ThirdObject.Maps.Owner

/-!
# Exactness at the target of a bounded analytic mapping-cone triangle

The bounded map into its mapping cone followed by the cone-inclusion map is
zero in the analytic homotopy category.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The bounded map followed by the target-to-cone inclusion is zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.first_comp_secondMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap hom ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap hom =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangle_first_comp_second
    hom

/-- The target-to-cone inclusion followed by the connecting map is zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap_comp_connectingMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap hom ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap hom =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangle_second_comp_third
    hom

/-- The connecting map followed by the shifted bounded map is zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap_comp_shifted_firstMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap hom ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
          hom)⟦(1 : ℤ)⟧' =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangle_third_comp_shifted_first
    hom

end AnalyticMotives
end LFunctions
end Boundary
