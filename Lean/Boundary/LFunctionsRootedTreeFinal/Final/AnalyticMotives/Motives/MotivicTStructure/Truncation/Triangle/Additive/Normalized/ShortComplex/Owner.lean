import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeVertex.Owner

/-!
# Normalized additive truncation short complex

The normalized lower-inclusion triangle is distinguished in the additive
homotopy category.  This file extracts the associated short complex, making the
composite-zero field of `truncLE(cut - 1, K) ⟶ K ⟶ cone` explicit.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- The short complex attached to the normalized additive lower-inclusion
distinguished triangle. -/
def additiveNormalizedLowerInclusionShortComplex
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  shortComplexOfDistTriangle
    (TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionTriangle
      cut
      complex)
    (TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionTriangle_distinguished
      cut
      complex)

/-- The first object of the normalized additive short complex is the paired
lower truncation in the homotopy category. -/
theorem additiveNormalizedLowerInclusionShortComplex_X₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionShortComplex
      cut
      complex).X₁ =
      TraceAnalyticAdditiveHomotopyCategory.objectOf
        (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE
          cut
          complex) :=
  rfl

/-- The second object of the normalized additive short complex is the original
complex in the homotopy category. -/
theorem additiveNormalizedLowerInclusionShortComplex_X₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionShortComplex
      cut
      complex).X₂ =
      TraceAnalyticAdditiveHomotopyCategory.objectOf complex :=
  rfl

/-- The third object of the normalized additive short complex is the named cone
vertex of the normalized additive lower-inclusion triangle. -/
theorem additiveNormalizedLowerInclusionShortComplex_X₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionShortComplex
      cut
      complex).X₃ =
      TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionConeVertex
        cut
        complex :=
  rfl

/-- The first map of the normalized additive short complex is the homotopy
image of the paired lower truncation inclusion. -/
theorem additiveNormalizedLowerInclusionShortComplex_f
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionShortComplex
      cut
      complex).f =
      TraceAnalyticAdditiveHomotopyCategory.mapOf
        (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
          cut
          complex) :=
  rfl

/-- The second map of the normalized additive short complex is the cone map of
the normalized additive lower-inclusion triangle. -/
theorem additiveNormalizedLowerInclusionShortComplex_g
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionShortComplex
      cut
      complex).g =
      TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionConeMap
        cut
        complex :=
  rfl

/-- The normalized additive lower-inclusion map followed by its cone map is
zero in the additive homotopy category. -/
theorem additiveNormalizedLowerInclusionShortComplex_zero
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionShortComplex
      cut
      complex).f ≫
        (TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionShortComplex
          cut
          complex).g =
      0 :=
  (TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionShortComplex
    cut
    complex).zero

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
