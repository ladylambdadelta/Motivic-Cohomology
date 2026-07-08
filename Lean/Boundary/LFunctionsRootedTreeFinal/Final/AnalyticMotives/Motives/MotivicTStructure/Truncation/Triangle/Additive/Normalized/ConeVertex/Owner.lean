import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.Owner

/-!
# Normalized additive cone vertex

This file names the cone vertex and remaining two morphisms of the normalized
additive lower-inclusion triangle for `truncLE(cut - 1, K) ⟶ K`.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- The cone vertex of the normalized additive lower-inclusion triangle. -/
def additiveNormalizedLowerInclusionConeVertex
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticAdditiveHomotopyCategory :=
  (TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionTriangle
    cut
    complex).obj₃

/-- The cone map of the normalized additive lower-inclusion triangle. -/
def additiveNormalizedLowerInclusionConeMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticAdditiveHomotopyCategory.objectOf complex ⟶
      TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionConeVertex
        cut
        complex :=
  (TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionTriangle
    cut
    complex).mor₂

/-- The connecting morphism of the normalized additive lower-inclusion
triangle. -/
def additiveNormalizedLowerInclusionConnectingMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionConeVertex
        cut
        complex ⟶
      TraceAnalyticAdditiveHomotopyCategory.objectOf
        (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE
          cut
          complex)⟦(1 : ℤ)⟧ :=
  (TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionTriangle
    cut
    complex).mor₃

/-- Projection formula for the normalized additive cone vertex. -/
theorem additiveNormalizedLowerInclusionConeVertex_eq_obj₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionConeVertex
        cut
        complex =
      (TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionTriangle
        cut
        complex).obj₃ :=
  rfl

/-- The third vertex of the normalized additive lower-inclusion triangle is
the named normalized cone vertex. -/
theorem additiveNormalizedLowerInclusionTriangle_obj₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionTriangle
        cut
        complex).obj₃ =
      TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionConeVertex
        cut
        complex :=
  rfl

/-- Projection formula for the normalized additive cone map. -/
theorem additiveNormalizedLowerInclusionConeMap_eq_mor₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionConeMap
        cut
        complex =
      (TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionTriangle
        cut
        complex).mor₂ :=
  rfl

/-- The second map of the normalized additive lower-inclusion triangle is the
named normalized cone map. -/
theorem additiveNormalizedLowerInclusionTriangle_mor₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionTriangle
        cut
        complex).mor₂ =
      TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionConeMap
        cut
        complex :=
  rfl

/-- Projection formula for the normalized additive connecting map. -/
theorem additiveNormalizedLowerInclusionConnectingMap_eq_mor₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionConnectingMap
        cut
        complex =
      (TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionTriangle
        cut
        complex).mor₃ :=
  rfl

/-- The third map of the normalized additive lower-inclusion triangle is the
named normalized connecting map. -/
theorem additiveNormalizedLowerInclusionTriangle_mor₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionTriangle
        cut
        complex).mor₃ =
      TraceAnalyticMotivicTStructure
        .additiveNormalizedLowerInclusionConnectingMap
        cut
        complex :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
