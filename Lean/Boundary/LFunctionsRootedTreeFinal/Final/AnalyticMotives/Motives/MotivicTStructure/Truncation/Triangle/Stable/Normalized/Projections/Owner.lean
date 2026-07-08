import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ConeVertex.Owner

/-!
# Normalized stable truncation triangle projections

This file exposes the vertices and morphisms of the normalized stable
lower-inclusion triangle in terms of the paired lower truncation, the stable
Verdier image of the original complex, and the named stable cone vertex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The first vertex of the normalized stable lower-inclusion triangle is the
stable image of the paired lower truncation. -/
theorem stableNormalizedLowerInclusionTriangle_obj₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionTriangle
      cut
      complex).obj₁ =
      TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticAdditiveHomotopyCategory.objectOf
          (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE
            cut
            complex)) :=
  rfl

/-- The second vertex of the normalized stable lower-inclusion triangle is the
stable image of the original additive complex. -/
theorem stableNormalizedLowerInclusionTriangle_obj₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionTriangle
      cut
      complex).obj₂ =
      TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticAdditiveHomotopyCategory.objectOf complex) :=
  rfl

/-- The first morphism of the normalized stable lower-inclusion triangle is the
Verdier image of the paired lower truncation inclusion map. -/
theorem stableNormalizedLowerInclusionTriangle_firstMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionTriangle
      cut
      complex).mor₁ =
      TraceAnalyticDMgmComparisonSource.mapOf
        (TraceAnalyticAdditiveHomotopyCategory.mapOf
          (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
            cut
            complex)) :=
  rfl

/-- The third vertex of the normalized stable lower-inclusion triangle is the
named stable cone vertex. -/
theorem stableNormalizedLowerInclusionTriangle_obj₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionTriangle
      cut
      complex).obj₃ =
      TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionConeVertex
        cut
        complex :=
  rfl

/-- The second morphism of the normalized stable lower-inclusion triangle is
the named stable cone map. -/
theorem stableNormalizedLowerInclusionTriangle_secondMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionTriangle
      cut
      complex).mor₂ =
      TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionConeMap
        cut
        complex :=
  rfl

/-- The third morphism of the normalized stable lower-inclusion triangle is
the named stable connecting map. -/
theorem stableNormalizedLowerInclusionTriangle_thirdMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionTriangle
      cut
      complex).mor₃ =
      TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionConnectingMap
        cut
        complex :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
