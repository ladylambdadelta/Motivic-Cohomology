import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ShortComplex.Comparison.Map.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ShortComplex.Transport.Comparison.Owner

/-!
# Transported normalized short complex to cochain decomposition

This file composes the inverse of the transported/extracted normalized
short-complex comparison with the existing comparison from the extracted
normalized short complex to the stable cochain-decomposition short complex.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The transported normalized lower-inclusion short complex maps to the stable
cochain-decomposition short complex through the extracted normalized short
complex. -/
def stableTransportedNormalizedLowerInclusionShortComplexToCochainDecomposition
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure
        .stableTransportedNormalizedLowerInclusionShortComplex cut complex ⟶
      TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
        cut
        complex :=
  (TraceAnalyticMotivicTStructure
    .stableNormalizedLowerInclusionShortComplexIsoTransported
      cut
      complex).inv ≫
    TraceAnalyticMotivicTStructure
      .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
        cut
        complex

/-- The first component of the transported normalized comparison to the
cochain-decomposition short complex is the identity. -/
theorem stableTransportedNormalizedLowerInclusionShortComplexToCochainDecomposition_τ₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure
      .stableTransportedNormalizedLowerInclusionShortComplexToCochainDecomposition
        cut
        complex).τ₁ =
      𝟙 _ :=
  Eq.trans
    (ShortComplex.comp_τ₁
      (TraceAnalyticMotivicTStructure
        .stableNormalizedLowerInclusionShortComplexIsoTransported
          cut
          complex).inv
      (TraceAnalyticMotivicTStructure
        .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
          cut
          complex))
    (Eq.trans
      (congrArg
        (fun morphism =>
          morphism ≫
            (TraceAnalyticMotivicTStructure
              .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
                cut
                complex).τ₁)
        (TraceAnalyticMotivicTStructure
          .stableNormalizedLowerInclusionShortComplexIsoTransported_inv_τ₁
            cut
            complex))
      (Eq.trans
      (id_comp
        (TraceAnalyticMotivicTStructure
          .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
            cut
            complex).τ₁)
      (TraceAnalyticMotivicTStructure
        .stableNormalizedLowerInclusionShortComplexToCochainDecomposition_τ₁
          cut
          complex)))

/-- The second component of the transported normalized comparison to the
cochain-decomposition short complex is the identity. -/
theorem stableTransportedNormalizedLowerInclusionShortComplexToCochainDecomposition_τ₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure
      .stableTransportedNormalizedLowerInclusionShortComplexToCochainDecomposition
        cut
        complex).τ₂ =
      𝟙 _ :=
  Eq.trans
    (ShortComplex.comp_τ₂
      (TraceAnalyticMotivicTStructure
        .stableNormalizedLowerInclusionShortComplexIsoTransported
          cut
          complex).inv
      (TraceAnalyticMotivicTStructure
        .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
          cut
          complex))
    (Eq.trans
      (congrArg
        (fun morphism =>
          morphism ≫
            (TraceAnalyticMotivicTStructure
              .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
                cut
                complex).τ₂)
        (TraceAnalyticMotivicTStructure
          .stableNormalizedLowerInclusionShortComplexIsoTransported_inv_τ₂
            cut
            complex))
      (Eq.trans
      (id_comp
        (TraceAnalyticMotivicTStructure
          .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
            cut
            complex).τ₂)
      (TraceAnalyticMotivicTStructure
        .stableNormalizedLowerInclusionShortComplexToCochainDecomposition_τ₂
          cut
          complex)))

/-- The third component of the transported normalized comparison to the
cochain-decomposition short complex is the stable cone-to-upper comparison. -/
theorem stableTransportedNormalizedLowerInclusionShortComplexToCochainDecomposition_τ₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure
      .stableTransportedNormalizedLowerInclusionShortComplexToCochainDecomposition
        cut
        complex).τ₃ =
      TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        cut
        complex :=
  Eq.trans
    (ShortComplex.comp_τ₃
      (TraceAnalyticMotivicTStructure
        .stableNormalizedLowerInclusionShortComplexIsoTransported
          cut
          complex).inv
      (TraceAnalyticMotivicTStructure
        .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
          cut
          complex))
    (Eq.trans
      (congrArg
        (fun morphism =>
          morphism ≫
            (TraceAnalyticMotivicTStructure
              .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
                cut
                complex).τ₃)
        (TraceAnalyticMotivicTStructure
          .stableNormalizedLowerInclusionShortComplexIsoTransported_inv_τ₃
            cut
            complex))
      (Eq.trans
      (id_comp
        (TraceAnalyticMotivicTStructure
          .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
            cut
            complex).τ₃)
      (TraceAnalyticMotivicTStructure
        .stableNormalizedLowerInclusionShortComplexToCochainDecomposition_τ₃
          cut
          complex)))

/-- The transported normalized comparison to the stable cochain-decomposition
short complex has identity first and second components and the stable
cone-to-upper comparison as third component. -/
theorem stableTransportedNormalizedLowerInclusionShortComplexToCochainDecomposition_components
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure
      .stableTransportedNormalizedLowerInclusionShortComplexToCochainDecomposition
        cut
        complex).τ₁ =
        𝟙 _ ∧
      (TraceAnalyticMotivicTStructure
        .stableTransportedNormalizedLowerInclusionShortComplexToCochainDecomposition
          cut
          complex).τ₂ =
        𝟙 _ ∧
        (TraceAnalyticMotivicTStructure
          .stableTransportedNormalizedLowerInclusionShortComplexToCochainDecomposition
            cut
            complex).τ₃ =
          TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
            cut
            complex :=
  And.intro
    (TraceAnalyticMotivicTStructure
      .stableTransportedNormalizedLowerInclusionShortComplexToCochainDecomposition_τ₁
        cut
        complex)
    (And.intro
      (TraceAnalyticMotivicTStructure
        .stableTransportedNormalizedLowerInclusionShortComplexToCochainDecomposition_τ₂
          cut
          complex)
      (TraceAnalyticMotivicTStructure
        .stableTransportedNormalizedLowerInclusionShortComplexToCochainDecomposition_τ₃
          cut
          complex))

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
