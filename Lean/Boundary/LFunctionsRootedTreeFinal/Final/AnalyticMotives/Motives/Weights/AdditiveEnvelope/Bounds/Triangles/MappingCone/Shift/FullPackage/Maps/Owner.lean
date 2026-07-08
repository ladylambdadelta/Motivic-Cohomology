import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Package.ThirdIsoBounded.Maps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Shift.FullPackage.Owner

/-!
# Named maps in shifted full mapping-cone packages

The full package attached to a shifted bounded map has the shifted bounded map,
the shifted-map cone inclusion, and the shifted-map connecting morphism as its
three triangle morphisms.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The first morphism of the shifted full package is the shifted bounded map. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_firstMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage
      hom
      shift).trianglePackage.triangle.mor₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (hom.shift shift) :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_firstMap
    (hom.shift shift)

/-- The second morphism of the shifted full package is the shifted-map cone inclusion. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_secondMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage
      hom
      shift).trianglePackage.triangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
        (hom.shift shift) :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_secondMap
    (hom.shift shift)

/-- The third morphism of the shifted full package is the shifted-map connecting map. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_connectingMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage
      hom
      shift).trianglePackage.triangle.mor₃ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (hom.shift shift) :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_connectingMap
    (hom.shift shift)

end AnalyticMotives
end LFunctions
end Boundary
