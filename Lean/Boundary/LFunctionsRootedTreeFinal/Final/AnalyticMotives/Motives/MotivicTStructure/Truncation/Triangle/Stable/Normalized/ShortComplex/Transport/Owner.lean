import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ShortComplex.Owner

/-!
# Verdier transport of the normalized truncation short complex

This file applies the Verdier quotient functor directly to the normalized
additive short complex.  It records the transported composite-zero field before
the later cone-to-upper comparison identifies the transported cone with the
upper truncation.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The Verdier-transported normalized additive lower-inclusion short complex. -/
def stableTransportedNormalizedLowerInclusionShortComplex
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    ShortComplex TraceAnalyticStableMotiveCategory :=
  (TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionShortComplex
    cut
    complex).map TraceAnalyticStableMotiveCategory.quotientFunctor

/-- The first object of the transported normalized short complex is the stable
image of the paired lower truncation. -/
theorem stableTransportedNormalizedLowerInclusionShortComplex_X₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableTransportedNormalizedLowerInclusionShortComplex
      cut
      complex).X₁ =
      TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticAdditiveHomotopyCategory.objectOf
          (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE
            cut
            complex)) :=
  rfl

/-- The second object of the transported normalized short complex is the stable
image of the original complex. -/
theorem stableTransportedNormalizedLowerInclusionShortComplex_X₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableTransportedNormalizedLowerInclusionShortComplex
      cut
      complex).X₂ =
      TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticAdditiveHomotopyCategory.objectOf complex) :=
  rfl

/-- The third object of the transported normalized short complex is the
Verdier image of the additive cone vertex. -/
theorem stableTransportedNormalizedLowerInclusionShortComplex_X₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableTransportedNormalizedLowerInclusionShortComplex
      cut
      complex).X₃ =
      TraceAnalyticStableMotiveCategory.objectOf
        (TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionConeVertex
          cut
          complex) :=
  rfl

/-- The first map of the transported normalized short complex is the stable
image of the paired lower truncation inclusion. -/
theorem stableTransportedNormalizedLowerInclusionShortComplex_f
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableTransportedNormalizedLowerInclusionShortComplex
      cut
      complex).f =
      TraceAnalyticDMgmComparisonSource.mapOf
        (TraceAnalyticAdditiveHomotopyCategory.mapOf
          (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLEInclusionMap
            cut
            complex)) :=
  rfl

/-- The second map of the transported normalized short complex is the Verdier
image of the additive cone map. -/
theorem stableTransportedNormalizedLowerInclusionShortComplex_g
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableTransportedNormalizedLowerInclusionShortComplex
      cut
      complex).g =
      TraceAnalyticStableMotiveCategory.mapOf
        (TraceAnalyticMotivicTStructure.additiveNormalizedLowerInclusionConeMap
          cut
          complex) :=
  rfl

/-- The transported normalized lower-inclusion map followed by the transported
cone map is zero after Verdier localization. -/
theorem stableTransportedNormalizedLowerInclusionShortComplex_zero
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableTransportedNormalizedLowerInclusionShortComplex
      cut
      complex).f ≫
        (TraceAnalyticMotivicTStructure.stableTransportedNormalizedLowerInclusionShortComplex
          cut
          complex).g =
      0 :=
  (TraceAnalyticMotivicTStructure.stableTransportedNormalizedLowerInclusionShortComplex
    cut
    complex).zero

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
