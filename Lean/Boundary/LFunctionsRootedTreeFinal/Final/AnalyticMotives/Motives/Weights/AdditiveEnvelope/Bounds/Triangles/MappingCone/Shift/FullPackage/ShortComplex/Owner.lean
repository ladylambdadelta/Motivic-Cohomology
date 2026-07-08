import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Package.ThirdIsoBounded.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Shift.FullPackage.Exactness.Owner

/-!
# Short complexes from shifted full mapping-cone packages

The full mapping-cone package attached to a shifted bounded map carries the
short complex formed by its first two triangle morphisms.  This exposes the
two-step trace presentation that comparison functors preserve.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The short complex attached to the full mapping-cone package of a shifted bounded map. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_shortComplex
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_shortComplex
    (hom.shift shift)

/-- The shifted full-package short complex is the full-package short complex of the shifted map. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_shortComplex_eq
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_shortComplex
        hom
        shift =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_shortComplex
        (hom.shift shift) :=
  rfl

/-- The left vertex is the shifted source object. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_shortComplex_X₁
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_shortComplex
      hom
      shift).X₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (hom.shift shift) :=
  rfl

/-- The middle vertex is the shifted target object. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_shortComplex_X₂
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_shortComplex
      hom
      shift).X₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (hom.shift shift) :=
  rfl

/-- The right vertex is the mapping-cone object of the shifted bounded map. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_shortComplex_X₃
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_shortComplex
      hom
      shift).X₃ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        (hom.shift shift) :=
  rfl

/-- The first short-complex morphism is the shifted bounded map. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_shortComplex_f
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_shortComplex
      hom
      shift).f =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (hom.shift shift) :=
  rfl

/-- The second short-complex morphism is the shifted-map cone inclusion. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_shortComplex_g
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_shortComplex
      hom
      shift).g =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
        (hom.shift shift) :=
  rfl

/-- The two morphisms in the shifted full-package short complex compose to zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_shortComplex_zero
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_shortComplex
      hom
      shift).f ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_shortComplex
          hom
          shift).g =
      0 :=
  (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedFullPackage_shortComplex
    hom
    shift).zero

end AnalyticMotives
end LFunctions
end Boundary
