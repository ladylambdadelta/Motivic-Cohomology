import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.MathlibShape.IdentityCone.Transport.Certificate.Owner

/-!
# Projections from the transported stable triangle certificate

This file exposes the triangle-shape and exactness parts of the transported
stable cochain-decomposition certificate without forcing downstream proofs to
unpack the full conjunction.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- The triangle-shape part of the transported stable cochain-decomposition
certificate: concrete vertices, concrete first two maps, and distinguishedness.
-/
theorem stableCochainDecompositionTransportedTriangle_certificate_triangle_part
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
                TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  let certificate :=
    TraceAnalyticMotivicTStructure
      .stableCochainDecompositionTransportedTriangle_certificate
        cut
        complex
        leftProbe
        rightProbe
  And.intro
    certificate.left
    (And.intro
      certificate.right.left
      (And.intro
        certificate.right.right.left
        (And.intro
          certificate.right.right.right.left
          (And.intro
            certificate.right.right.right.right.left
            certificate.right.right.right.right.right.left))))

/-- The paired preadditive Yoneda exactness part of the transported stable
cochain-decomposition certificate. -/
theorem stableCochainDecompositionTransportedTriangle_certificate_exact_part
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)]
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
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
  let certificate :=
    TraceAnalyticMotivicTStructure
      .stableCochainDecompositionTransportedTriangle_certificate
        cut
        complex
        leftProbe
        rightProbe
  certificate.right.right.right.right.right.right

/-- The transported stable cochain-decomposition certificate also exposes the
third morphism of the triangle as the transported connecting map. -/
theorem stableCochainDecompositionTransportedTriangle_certificate_thirdMap
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
      .stableCochainDecompositionTransportedTriangle cut complex).mor₃ =
      TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedConnectingMap
          cut
          complex :=
  TraceAnalyticMotivicTStructure
    .stableCochainDecompositionTransportedTriangle_raw_thirdMap
      cut
      complex

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
