import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Homotopy.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.ConeComparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Triangulated.Owner

/-!
# Additive homotopy truncation triangles

This file forms the mapping-cone triangle of the concrete lower truncation
inclusion and records that Mathlib's homotopy-category triangulation makes it
distinguished.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- The additive homotopy mapping-cone triangle of the concrete lower
truncation inclusion `truncLE(cut, K) ⟶ K`. -/
def additiveLowerInclusionTriangle
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    Triangle TraceAnalyticAdditiveHomotopyCategory :=
  CochainComplex.mappingCone.triangleh
    (TraceAnalyticMotivicTStructure.additiveTruncLEInclusionMap cut complex)

/-- The lower-inclusion mapping-cone triangle is distinguished in the additive
analytic homotopy category. -/
theorem additiveLowerInclusionTriangle_distinguished
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.additiveLowerInclusionTriangle
        cut
        complex ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticAdditiveHomotopyCategory.mappingCone_triangle_distinguished
    (TraceAnalyticMotivicTStructure.additiveTruncLEInclusionMap cut complex)

/-- The first morphism of the lower-inclusion triangle is the homotopy image
of the concrete lower truncation inclusion. -/
theorem additiveLowerInclusionTriangle_mor₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveLowerInclusionTriangle
      cut
      complex).mor₁ =
      TraceAnalyticMotivicTStructure.homotopyTruncLEInclusionMap
        cut
        complex :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
