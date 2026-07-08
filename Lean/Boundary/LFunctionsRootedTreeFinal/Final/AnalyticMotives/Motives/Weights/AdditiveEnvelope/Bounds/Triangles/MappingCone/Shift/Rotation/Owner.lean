import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Package.ThirdIsoBounded.Rotation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.Shift.Owner

/-!
# Rotations of shifted-map mapping-cone triangles

The rotated and inverse-rotated mapping-cone triangles of the shifted bounded
map are obtained by applying the existing full-package rotation constructions
to `hom.shift n`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The rotated mapping-cone triangle of the shifted bounded map. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    Triangle TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle
    (hom.shift shift)

/-- The rotated shifted-map mapping-cone triangle is distinguished. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle_distinguished
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedRotatedTriangle
        hom
        shift ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_rotatedTriangle_distinguished
    (hom.shift shift)

/-- The inverse-rotated mapping-cone triangle of the shifted bounded map. -/
def TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    Triangle TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle
    (hom.shift shift)

/-- The inverse-rotated shifted-map mapping-cone triangle is distinguished. -/
theorem TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle_distinguished
    {bound : Nat}
    {source target :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy bound}
    (hom :
      TraceAnalyticAdditiveCochainComplex.WeightBoundedBy.Hom source target)
    (shift : ℤ) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.shiftedInverseRotatedTriangle
        hom
        shift ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.boundedTriangleWithThirdIsoBounded_inverseRotatedTriangle_distinguished
    (hom.shift shift)

end AnalyticMotives
end LFunctions
end Boundary
