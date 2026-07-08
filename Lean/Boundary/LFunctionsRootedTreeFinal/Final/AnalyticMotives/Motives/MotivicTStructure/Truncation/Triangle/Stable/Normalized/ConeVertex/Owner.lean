import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeVertex.Owner

/-!
# Normalized stable cone vertex

This file names the cone vertex and remaining two morphisms of the normalized
stable lower-inclusion triangle.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- The cone vertex of the normalized stable lower-inclusion triangle. -/
def stableNormalizedLowerInclusionConeVertex
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticStableMotiveCategory :=
  (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionTriangle
    cut
    complex).obj₃

/-- The cone map of the normalized stable lower-inclusion triangle. -/
def stableNormalizedLowerInclusionConeMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticAdditiveHomotopyCategory.objectOf complex) ⟶
      TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionConeVertex
        cut
        complex :=
  (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionTriangle
    cut
    complex).mor₂

/-- The connecting morphism of the normalized stable lower-inclusion
triangle. -/
def stableNormalizedLowerInclusionConnectingMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionConeVertex
        cut
        complex ⟶
      TraceAnalyticStableMotiveCategory.objectOf
        (TraceAnalyticAdditiveHomotopyCategory.objectOf
          (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE
            cut
            complex))⟦(1 : ℤ)⟧ :=
  (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionTriangle
    cut
    complex).mor₃

/-- Projection formula for the normalized stable cone vertex. -/
theorem stableNormalizedLowerInclusionConeVertex_eq_obj₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionConeVertex
        cut
        complex =
      (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionTriangle
        cut
        complex).obj₃ :=
  rfl

/-- The third vertex of the normalized stable lower-inclusion triangle is the
named normalized cone vertex. -/
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

/-- Projection formula for the normalized stable cone map. -/
theorem stableNormalizedLowerInclusionConeMap_eq_mor₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionConeMap
        cut
        complex =
      (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionTriangle
        cut
        complex).mor₂ :=
  rfl

/-- The second map of the normalized stable lower-inclusion triangle is the
named normalized cone map. -/
theorem stableNormalizedLowerInclusionTriangle_mor₂
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

/-- The normalized stable cone map is the Verdier quotient image of the
normalized additive cone map. -/
theorem stableNormalizedLowerInclusionConeMap_eq_mapOf_additiveNormalizedConeMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionConeMap
        cut
        complex =
      TraceAnalyticStableMotiveCategory.mapOf
        (TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionConeMap
          cut
          complex) :=
  rfl

/-- Projection formula for the normalized stable connecting map. -/
theorem stableNormalizedLowerInclusionConnectingMap_eq_mor₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionConnectingMap
        cut
        complex =
      (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionTriangle
        cut
        complex).mor₃ :=
  rfl

/-- The third map of the normalized stable lower-inclusion triangle is the
named normalized connecting map. -/
theorem stableNormalizedLowerInclusionTriangle_mor₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionTriangle
        cut
        complex).mor₃ =
      TraceAnalyticMotivicTStructure
        .stableNormalizedLowerInclusionConnectingMap
        cut
        complex :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
