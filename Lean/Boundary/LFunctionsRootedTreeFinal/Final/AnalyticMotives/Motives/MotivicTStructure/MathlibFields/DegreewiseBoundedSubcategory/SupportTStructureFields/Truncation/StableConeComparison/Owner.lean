import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ShortComplex.Transport.Comparison.CochainDecomposition.IsIso.Owner

/-!
# Stable cone-comparison bridge for support truncation

The existing transported cochain-decomposition triangle was originally phrased
using a cochain-level normalized cone-comparison isomorphism.  This file
exposes the weaker stable-localized fact actually needed at the third vertex:
if the stable cone-to-upper comparison is an isomorphism, then the transported
short-complex comparison has an isomorphic third component.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- The stable cone-comparison isomorphism supplies the third-vertex isomorphism
from the normalized cone vertex to the stable upper truncation. -/
def stableNormalizedToCochainDecompositionThirdIsoOfStableConeComparison
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        cut
        complex)] :
    TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionConeVertex
        cut
        complex ≅
      TraceAnalyticMotivicTStructure.stableTruncGE cut complex :=
  asIso
    (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
      cut
      complex)

/-- The stable-level connecting morphism obtained by transporting the
normalized lower-inclusion triangle across the localized cone comparison. -/
def stableCochainDecompositionTransportedConnectingMapOfStableConeComparison
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        cut
        complex)] :
    TraceAnalyticMotivicTStructure.stableTruncGE cut complex ⟶
      TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticAdditiveHomotopyCategory.objectOf
          (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE
            cut
            complex))⟦(1 : ℤ)⟧ :=
  (TraceAnalyticMotivicTStructure
    .stableNormalizedToCochainDecompositionThirdIsoOfStableConeComparison
      cut
      complex).inv ≫
    TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionConnectingMap
      cut
      complex

/-- The cochain-decomposition triangle transported using only the stable
cone-comparison isomorphism. -/
def stableCochainDecompositionTransportedTriangleOfStableConeComparison
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        cut
        complex)] :
    Triangle TraceAnalyticStableMotiveCategory :=
  Triangle.mk
    (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
      cut
      complex).f
    (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
      cut
      complex).g
    (TraceAnalyticMotivicTStructure
      .stableCochainDecompositionTransportedConnectingMapOfStableConeComparison
        cut
        complex)

/-- The normalized stable triangle is isomorphic to the stable-cone transported
cochain-decomposition triangle. -/
def stableNormalizedLowerInclusionTriangleIsoTransportedCochainDecompositionOfStableConeComparison
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        cut
        complex)] :
    TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionTriangle
        cut
        complex ≅
      TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedTriangleOfStableConeComparison
          cut
          complex :=
  Triangle.isoMk
    (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionTriangle
      cut
      complex)
    (TraceAnalyticMotivicTStructure
      .stableCochainDecompositionTransportedTriangleOfStableConeComparison
        cut
        complex)
    (Iso.refl _)
    (Iso.refl _)
    (TraceAnalyticMotivicTStructure
      .stableNormalizedToCochainDecompositionThirdIsoOfStableConeComparison
        cut
        complex)
    (Eq.trans
      (Category.comp_id
        (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionTriangle
          cut
          complex).mor₁)
      (Eq.symm
        (Category.id_comp
          (TraceAnalyticMotivicTStructure
            .stableCochainDecompositionTransportedTriangleOfStableConeComparison
              cut
              complex).mor₁)))
    (Eq.trans
      (Eq.symm
        (TraceAnalyticMotivicTStructure
          .stableNormalizedLowerInclusionConeMap_comp_coneComparisonMap
            cut
            complex))
      (Eq.symm
        (Category.id_comp
          (TraceAnalyticMotivicTStructure
            .stableCochainDecompositionTransportedTriangleOfStableConeComparison
              cut
              complex).mor₂)))
    (Eq.trans
      (Category.comp_id
        (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionTriangle
          cut
          complex).mor₃)
      (Eq.trans
        (Eq.symm
          (Category.id_comp
            (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionTriangle
              cut
              complex).mor₃))
        (Eq.trans
          (congrArg
            (fun left =>
              left ≫
                (TraceAnalyticMotivicTStructure
                  .stableNormalizedLowerInclusionTriangle cut complex).mor₃)
            (Eq.symm
              (TraceAnalyticMotivicTStructure
                .stableNormalizedToCochainDecompositionThirdIsoOfStableConeComparison
                  cut
                  complex).hom_inv_id))
          (Category.assoc
            (TraceAnalyticMotivicTStructure
              .stableNormalizedToCochainDecompositionThirdIsoOfStableConeComparison
                cut
                complex).hom
            (TraceAnalyticMotivicTStructure
              .stableNormalizedToCochainDecompositionThirdIsoOfStableConeComparison
                cut
                complex).inv
            (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionTriangle
              cut
              complex).mor₃))))

/-- The stable-cone transported cochain-decomposition triangle is
distinguished. -/
theorem stableCochainDecompositionTransportedTriangleOfStableConeComparison_distinguished
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        cut
        complex)] :
    TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedTriangleOfStableConeComparison
          cut
          complex ∈
      TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  isomorphic_distinguished
    (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionTriangle
      cut
      complex)
    (TraceAnalyticMotivicTStructure
      .stableNormalizedLowerInclusionTriangle_distinguished cut complex)
    (TraceAnalyticMotivicTStructure
      .stableCochainDecompositionTransportedTriangleOfStableConeComparison
        cut
        complex)
    (TraceAnalyticMotivicTStructure
      .stableNormalizedLowerInclusionTriangleIsoTransportedCochainDecompositionOfStableConeComparison
        cut
        complex)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
