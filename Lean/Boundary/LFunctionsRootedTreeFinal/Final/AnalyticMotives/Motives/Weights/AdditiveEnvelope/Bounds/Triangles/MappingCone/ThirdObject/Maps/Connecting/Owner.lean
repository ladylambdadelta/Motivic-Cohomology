import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.ThirdObject.Maps.Owner

/-!
# Connecting maps from bounded analytic mapping cones

The third morphism of a bounded mapping-cone triangle is the connecting map
from the cone object to the shifted source object.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The connecting morphism from the mapping cone to the shifted source object. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject hom ⟶
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        hom)⟦(1 : ℤ)⟧ :=
  (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.triangle hom).mor₃

/-- The connecting map is the third morphism of the mapping-cone triangle. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap_eq
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap hom =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.triangle hom).mor₃ :=
  rfl

/-- The third morphism of the mapping-cone triangle is the named connecting map. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.triangle_mor₃
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.triangle hom).mor₃ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap hom :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
