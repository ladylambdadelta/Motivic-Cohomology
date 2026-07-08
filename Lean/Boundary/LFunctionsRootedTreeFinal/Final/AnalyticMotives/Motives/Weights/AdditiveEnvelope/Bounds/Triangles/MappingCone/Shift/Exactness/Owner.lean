import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Package.ThirdIsoBounded.Maps.Exactness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Shift.Owner

/-!
# Exactness for shifted bounded mapping-cone triangles

Applying the existing mapping-cone exactness theorems to the shifted bounded
map gives the three named zero composites in the shifted mapping-cone triangle.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The shifted bounded map followed by the shifted-map cone inclusion is zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shifted_firstMap_comp_secondMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
          (hom.shift shift) ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
          (hom.shift shift) =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_firstMap_comp_secondMap
    (hom.shift shift)

/-- The shifted-map cone inclusion followed by its connecting map is zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shifted_secondMap_comp_connectingMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
          (hom.shift shift) ≫
        TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
          (hom.shift shift) =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_secondMap_comp_connectingMap
    (hom.shift shift)

/-- The shifted-map connecting map followed by the shifted first map is zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shifted_connectingMap_comp_shifted_firstMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
          (hom.shift shift) ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
          (hom.shift shift))⟦(1 : ℤ)⟧' =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_connectingMap_comp_shifted_firstMap
    (hom.shift shift)

end AnalyticMotives
end LFunctions
end Boundary
