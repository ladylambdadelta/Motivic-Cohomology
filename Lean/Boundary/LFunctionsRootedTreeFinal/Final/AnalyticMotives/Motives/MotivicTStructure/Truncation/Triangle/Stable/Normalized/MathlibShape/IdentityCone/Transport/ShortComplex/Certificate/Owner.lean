import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.MathlibShape.IdentityCone.Transport.ShortComplex.YonedaExact.Paired.Owner

/-!
# Certificate for the named stable cochain-decomposition short complex

This file bundles the concrete vertices, maps, zero composition, and paired
preadditive Yoneda exactness of the named stable cochain-decomposition short
complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The named stable cochain-decomposition short complex has the expected
vertices and maps, has zero composite, and is exact after both preadditive
Yoneda probes under the cochain-level cone-comparison isomorphism. -/
theorem stableCochainDecompositionShortComplex_certificate_of_isIso_cochainMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)]
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
        cut
        complex).X₁ =
        TraceAnalyticDMgmComparisonSource.objectOf
          (TraceAnalyticAdditiveHomotopyCategory.objectOf
            (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE
              cut
              complex)) ∧
      (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
        cut
        complex).X₂ =
        TraceAnalyticDMgmComparisonSource.objectOf
          (TraceAnalyticAdditiveHomotopyCategory.objectOf complex) ∧
        (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
          cut
          complex).X₃ =
          TraceAnalyticMotivicTStructure.stableTruncGE cut complex ∧
          (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
            cut
            complex).f =
            TraceAnalyticDMgmComparisonSource.mapOf
              (TraceAnalyticAdditiveHomotopyCategory.mapOf
                (TraceAnalyticMotivicTStructure
                  .additiveCochainDecompositionLowerMap cut complex)) ∧
            (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
              cut
              complex).g =
              TraceAnalyticMotivicTStructure.stableTruncGEProjectionMap
                cut
                complex ∧
              (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
                cut
                complex).f ≫
                  (TraceAnalyticMotivicTStructure
                    .stableCochainDecompositionShortComplex cut complex).g =
                0 ∧
                ((TraceAnalyticMotivicTStructure
                  .stableCochainDecompositionShortComplex cut complex).map
                    (preadditiveCoyoneda.obj leftProbe)).Exact ∧
                  ((TraceAnalyticMotivicTStructure
                    .stableCochainDecompositionShortComplex cut complex).op.map
                      (preadditiveYoneda.obj rightProbe)).Exact :=
  let exactPair :=
    TraceAnalyticMotivicTStructure
      .stableCochainDecompositionShortComplex_yonedaExact_pair_of_isIso_cochainMap
        cut
        complex
        leftProbe
        rightProbe
  And.intro
    (TraceAnalyticMotivicTStructure
      .stableCochainDecompositionShortComplex_X₁ cut complex)
    (And.intro
      (TraceAnalyticMotivicTStructure
        .stableCochainDecompositionShortComplex_X₂ cut complex)
      (And.intro
        (TraceAnalyticMotivicTStructure
          .stableCochainDecompositionShortComplex_X₃ cut complex)
        (And.intro
          (TraceAnalyticMotivicTStructure
            .stableCochainDecompositionShortComplex_f cut complex)
          (And.intro
            (TraceAnalyticMotivicTStructure
              .stableCochainDecompositionShortComplex_g cut complex)
            (And.intro
              (TraceAnalyticMotivicTStructure
                .stableCochainDecompositionShortComplex_zero cut complex)
              exactPair)))))

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
