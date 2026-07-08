import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.MathlibShape.IdentityCone.Transport.ShortComplex.Certificate.Owner

/-!
# Projections from the named stable short-complex certificate

This file exposes the shape and exactness parts of the named stable
cochain-decomposition short-complex certificate separately.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The shape part of the named stable cochain-decomposition short-complex
certificate: vertices, maps, and zero composition. -/
theorem stableCochainDecompositionShortComplex_certificate_shape_part
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
                0 :=
  let certificate :=
    TraceAnalyticMotivicTStructure
      .stableCochainDecompositionShortComplex_certificate_of_isIso_cochainMap
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

/-- The paired exactness part of the named stable cochain-decomposition
short-complex certificate. -/
theorem stableCochainDecompositionShortComplex_certificate_exact_part
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)]
    (leftProbe : StableInfinityOwner.PresentedCategoryᵒᵖ)
    (rightProbe : StableInfinityOwner.PresentedCategory) :
    ((TraceAnalyticMotivicTStructure
      .stableCochainDecompositionShortComplex cut complex).map
        (preadditiveCoyoneda.obj leftProbe)).Exact ∧
      ((TraceAnalyticMotivicTStructure
        .stableCochainDecompositionShortComplex cut complex).op.map
          (preadditiveYoneda.obj rightProbe)).Exact :=
  let certificate :=
    TraceAnalyticMotivicTStructure
      .stableCochainDecompositionShortComplex_certificate_of_isIso_cochainMap
        cut
        complex
        leftProbe
        rightProbe
  certificate.right.right.right.right.right.right

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
