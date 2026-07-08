import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CutPair.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Triangulated.Owner

/-!
# Normalized additive truncation triangle

This file forms the mapping-cone triangle for the normalized lower inclusion
`truncLE(cut - 1, K) ⟶ K`, the lower side paired with the upper truncation
boundary `cut`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- The additive homotopy mapping-cone triangle for the normalized lower
inclusion `truncLE(cut - 1, K) ⟶ K`. -/
def additiveNormalizedLowerInclusionTriangle
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    Triangle TraceAnalyticAdditiveHomotopyCategory :=
  CochainComplex.mappingCone.triangleh
    (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
      cut
      complex)

/-- The normalized lower-inclusion triangle is distinguished in the additive
analytic homotopy category. -/
theorem additiveNormalizedLowerInclusionTriangle_distinguished
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionTriangle
        cut
        complex ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticAdditiveHomotopyCategory.mappingCone_triangle_distinguished
    (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
      cut
      complex)

/-- The first morphism of the normalized lower-inclusion triangle is the
homotopy image of the normalized lower inclusion. -/
theorem additiveNormalizedLowerInclusionTriangle_mor₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionTriangle
      cut
      complex).mor₁ =
      TraceAnalyticAdditiveHomotopyCategory.mapOf
        (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
          cut
          complex) :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
