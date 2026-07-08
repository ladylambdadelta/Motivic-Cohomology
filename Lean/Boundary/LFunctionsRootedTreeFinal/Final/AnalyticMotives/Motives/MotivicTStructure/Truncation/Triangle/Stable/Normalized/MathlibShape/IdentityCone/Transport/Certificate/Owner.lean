import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.MathlibShape.IdentityCone.Transport.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.MathlibShape.IdentityCone.Transport.YonedaExact.Owner

/-!
# Certificate for the transported stable cochain-decomposition triangle

This file packages the concrete properties of the transported stable
cochain-decomposition triangle: its vertices are the stable lower truncation,
the original stable object, and the stable upper truncation; its first two maps
are the stable truncation maps; the triangle is distinguished; and the
associated Mathlib short complex is exact after both preadditive Yoneda probes.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- The transported stable cochain-decomposition triangle has the concrete
truncation vertices and maps, is distinguished, and supplies paired
preadditive Yoneda exactness for its Mathlib short complex. -/
theorem stableCochainDecompositionTransportedTriangle_certificate
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)]
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    (TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedTriangle cut complex).obj₁ =
        TraceAnalyticMotivicTStructure.stableTruncLE
          (TraceAnalyticMotivicTStructure.decompositionLowerCut cut)
          complex ∧
      (TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedTriangle cut complex).obj₂ =
        TraceAnalyticDMgmComparisonSource.objectOf
          (TraceAnalyticAdditiveHomotopyCategory.objectOf complex) ∧
        (TraceAnalyticMotivicTStructure
          .stableCochainDecompositionTransportedTriangle cut complex).obj₃ =
          TraceAnalyticMotivicTStructure.stableTruncGE cut complex ∧
          (TraceAnalyticMotivicTStructure
            .stableCochainDecompositionTransportedTriangle cut complex).mor₁ =
            (TraceAnalyticMotivicTStructure
              .stableCochainDecompositionShortComplex cut complex).f ∧
            (TraceAnalyticMotivicTStructure
              .stableCochainDecompositionTransportedTriangle cut complex).mor₂ =
              (TraceAnalyticMotivicTStructure
                .stableCochainDecompositionShortComplex cut complex).g ∧
              TraceAnalyticMotivicTStructure
                  .stableCochainDecompositionTransportedTriangle cut complex ∈
                TraceAnalyticDMgmComparisonSource.distinguishedTriangles ∧
                ((shortComplexOfDistTriangle
                  (TraceAnalyticMotivicTStructure
                    .stableCochainDecompositionTransportedTriangle cut complex)
                  (TraceAnalyticMotivicTStructure
                    .stableCochainDecompositionTransportedTriangle_distinguished
                      cut
                      complex)).map
                    (preadditiveCoyoneda.obj leftProbe)).Exact ∧
                  ((shortComplexOfDistTriangle
                    (TraceAnalyticMotivicTStructure
                      .stableCochainDecompositionTransportedTriangle cut complex)
                    (TraceAnalyticMotivicTStructure
                      .stableCochainDecompositionTransportedTriangle_distinguished
                        cut
                        complex)).op.map
                      (preadditiveYoneda.obj rightProbe)).Exact :=
  And.intro
    (TraceAnalyticMotivicTStructure
      .stableCochainDecompositionTransportedTriangle_raw_obj₁ cut complex)
    (And.intro
      (TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedTriangle_raw_obj₂ cut complex)
      (And.intro
        (TraceAnalyticMotivicTStructure
          .stableCochainDecompositionTransportedTriangle_raw_obj₃ cut complex)
        (And.intro
          (TraceAnalyticMotivicTStructure
            .stableCochainDecompositionTransportedTriangle_raw_firstMap
              cut
              complex)
          (And.intro
            (TraceAnalyticMotivicTStructure
              .stableCochainDecompositionTransportedTriangle_raw_secondMap
                cut
                complex)
            (And.intro
              (TraceAnalyticMotivicTStructure
                .stableCochainDecompositionTransportedTriangle_distinguished
                  cut
                  complex)
              (And.intro
                (TraceAnalyticMotivicTStructure
                  .stableCochainDecompositionTransportedTriangle_coyoneda_exact
                    cut
                    complex
                    leftProbe)
                (TraceAnalyticMotivicTStructure
                  .stableCochainDecompositionTransportedTriangle_yoneda_exact
                    cut
                    complex
                    rightProbe)))))))

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
