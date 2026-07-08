import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Package.ThirdIsoBounded.ShortComplex.Vertices.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Shift.Exactness.Owner

/-!
# Short complexes for shifted bounded mapping-cone triangles

The mapping-cone short complex of the shifted bounded map has the shifted
source, shifted target, and shifted-map cone as its vertices, with the shifted
bounded map and shifted-map cone inclusion as its first two morphisms.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The short complex attached to the mapping-cone package of the shifted bounded map. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedShortComplex
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_shortComplex
    (hom.shift shift)

/-- The left vertex of the shifted-map short complex is the shifted source object. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedShortComplex_leftVertex
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedShortComplex
      hom
      shift).X₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (hom.shift shift) :=
  rfl

/-- The middle vertex of the shifted-map short complex is the shifted target object. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedShortComplex_middleVertex
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedShortComplex
      hom
      shift).X₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (hom.shift shift) :=
  rfl

/-- The right vertex of the shifted-map short complex is the shifted-map cone object. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedShortComplex_rightVertex
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedShortComplex
      hom
      shift).X₃ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.thirdObject
        (hom.shift shift) :=
  rfl

/-- The first map of the shifted-map short complex is the shifted bounded map. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedShortComplex_firstMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedShortComplex
      hom
      shift).f =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (hom.shift shift) :=
  rfl

/-- The second map of the shifted-map short complex is the shifted-map cone inclusion. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedShortComplex_secondMap
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedShortComplex
      hom
      shift).g =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondMap
        (hom.shift shift) :=
  rfl

/-- The first two maps in the shifted-map short complex compose to zero. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedShortComplex_zero
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedShortComplex
      hom
      shift).f ≫
        (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedShortComplex
          hom
          shift).g =
      0 :=
  (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedShortComplex
    hom
    shift).zero

end AnalyticMotives
end LFunctions
end Boundary
