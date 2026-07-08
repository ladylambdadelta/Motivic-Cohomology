import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.MathlibShape.IdentityCone.Owner

/-!
# Transported cochain-decomposition triangle

This file transports the normalized stable lower-inclusion triangle across the
third component of the stable short-complex comparison isomorphism.  The result
is a distinguished triangle whose first two maps are the stable cochain
truncation-decomposition maps.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace TraceAnalyticMotivicTStructure

/-- The third-component isomorphism from the normalized stable cone vertex to
the stable upper truncation, obtained from the short-complex comparison. -/
def stableNormalizedToCochainDecompositionThirdIso
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionConeVertex
        cut
        complex ≅
      TraceAnalyticMotivicTStructure.stableTruncGE cut complex :=
  asIso
    (TraceAnalyticMotivicTStructure
      .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
        cut
        complex).τ₃

/-- The connecting morphism of the transported stable cochain-decomposition
triangle. -/
def stableCochainDecompositionTransportedConnectingMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticMotivicTStructure.stableTruncGE cut complex ⟶
      TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticAdditiveHomotopyCategory.objectOf
          (TraceAnalyticMotivicTStructure.additiveDecompositionTruncLE
            cut
            complex))⟦(1 : ℤ)⟧ :=
  (TraceAnalyticMotivicTStructure
    .stableNormalizedToCochainDecompositionThirdIso cut complex).inv ≫
    TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionConnectingMap
      cut
      complex

/-- The transported stable cochain-decomposition triangle. -/
def stableCochainDecompositionTransportedTriangle
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
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
      .stableCochainDecompositionTransportedConnectingMap cut complex)

/-- The normalized stable triangle is isomorphic to the transported stable
cochain-decomposition triangle. -/
def stableNormalizedLowerInclusionTriangleIsoTransportedCochainDecomposition
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionTriangle
        cut
        complex ≅
      TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedTriangle cut complex :=
  Triangle.isoMk
    (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionTriangle
      cut
      complex)
    (TraceAnalyticMotivicTStructure
      .stableCochainDecompositionTransportedTriangle cut complex)
    (Iso.refl _)
    (Iso.refl _)
    (TraceAnalyticMotivicTStructure
      .stableNormalizedToCochainDecompositionThirdIso cut complex)
    (Eq.trans
      (Category.comp_id
        (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionTriangle
          cut
          complex).mor₁)
      (Eq.symm
        (Category.id_comp
          (TraceAnalyticMotivicTStructure
            .stableCochainDecompositionTransportedTriangle cut complex).mor₁)))
    (Eq.trans
      (Eq.symm
        (ShortComplex.Hom.comm₂₃
          (TraceAnalyticMotivicTStructure
            .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
              cut
              complex)))
      (Eq.symm
        (Category.id_comp
          (TraceAnalyticMotivicTStructure
            .stableCochainDecompositionTransportedTriangle cut complex).mor₂)))
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
                .stableNormalizedToCochainDecompositionThirdIso
                  cut
                  complex).hom_inv_id))
          (Category.assoc
            (TraceAnalyticMotivicTStructure
              .stableNormalizedToCochainDecompositionThirdIso cut complex).hom
            (TraceAnalyticMotivicTStructure
              .stableNormalizedToCochainDecompositionThirdIso cut complex).inv
            (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionTriangle
              cut
              complex).mor₃))))

/-- The transported stable cochain-decomposition triangle is distinguished. -/
theorem stableCochainDecompositionTransportedTriangle_distinguished
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticMotivicTStructure
        .stableCochainDecompositionTransportedTriangle cut complex ∈
      TraceAnalyticDMgmComparisonSource.distinguishedTriangles :=
  isomorphic_distinguished
    (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionTriangle
      cut
      complex)
    (TraceAnalyticMotivicTStructure
      .stableNormalizedLowerInclusionTriangle_distinguished cut complex)
    (TraceAnalyticMotivicTStructure
      .stableCochainDecompositionTransportedTriangle cut complex)
    (TraceAnalyticMotivicTStructure
      .stableNormalizedLowerInclusionTriangleIsoTransportedCochainDecomposition
        cut
        complex)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
