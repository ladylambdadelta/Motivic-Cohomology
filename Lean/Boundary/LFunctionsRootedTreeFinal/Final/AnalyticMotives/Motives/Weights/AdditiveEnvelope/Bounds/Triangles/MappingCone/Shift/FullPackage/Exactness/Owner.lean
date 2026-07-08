import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Package.ThirdIsoBounded.Maps.Exactness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Shift.FullPackage.Maps.Owner

/-!
# Exactness in shifted full mapping-cone packages

The three consecutive composites in the full package attached to a shifted
bounded map vanish.  These are the concrete exactness statements that later
comparison functors must preserve.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The shifted bounded map followed by the shifted-map cone inclusion is zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_first_comp_second
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

/-- The shifted-map cone inclusion followed by the shifted-map connecting map is zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_second_comp_connecting
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
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_connecting_comp_shifted_first
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

/-- The first two triangle morphisms of the shifted full package compose to zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_triangle_first_comp_second
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage
      hom
      shift).trianglePackage.triangle.mor₁ ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage
          hom
          shift).trianglePackage.triangle.mor₂ =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_first_comp_second
    hom
    shift

/-- The second and third triangle morphisms of the shifted full package compose to zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_triangle_second_comp_third
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage
      hom
      shift).trianglePackage.triangle.mor₂ ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage
          hom
          shift).trianglePackage.triangle.mor₃ =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_second_comp_connecting
    hom
    shift

/-- The third morphism followed by the shifted first morphism in the shifted full package
is zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_triangle_third_comp_shifted_first
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage
      hom
      shift).trianglePackage.triangle.mor₃ ≫
        ((TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage
          hom
          shift).trianglePackage.triangle.mor₁)⟦(1 : ℤ)⟧' =
      0 :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_connecting_comp_shifted_first
    hom
    shift

end AnalyticMotives
end LFunctions
end Boundary
