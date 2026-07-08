import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ConeComparison.Map.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ShortComplex.Comparison.Front.Owner

/-!
# Stable short-complex comparison map

This file upgrades the component-level comparison between the normalized stable
cone short complex and the stable cochain truncation-decomposition short
complex to an actual morphism of short complexes.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The normalized stable cone short complex maps to the stable cochain
truncation-decomposition short complex by identities on the lower and middle
vertices and the stable cone-to-upper comparison on the third vertex. -/
def stableNormalizedLowerInclusionShortComplexToCochainDecomposition
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionShortComplex
        cut
        complex ⟶
      TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
        cut
        complex :=
  ShortComplex.homMk
    (𝟙 _)
    (𝟙 _)
    (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
      cut
      complex)
    (Eq.trans
      (id_comp
        (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
          cut
          complex).f)
      (Eq.symm
        (comp_id
          (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionShortComplex
            cut
            complex).f)))
    (Eq.trans
      (id_comp
        (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
          cut
          complex).g)
      (Eq.symm
        (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionConeMap_comp_coneComparisonMap
          cut
          complex)))

/-- The first component of the stable short-complex comparison is the identity. -/
theorem stableNormalizedLowerInclusionShortComplexToCochainDecomposition_τ₁
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure
      .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
        cut
        complex).τ₁ =
      𝟙 _ :=
  rfl

/-- The second component of the stable short-complex comparison is the
identity. -/
theorem stableNormalizedLowerInclusionShortComplexToCochainDecomposition_τ₂
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure
      .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
        cut
        complex).τ₂ =
      𝟙 _ :=
  rfl

/-- The third component of the stable short-complex comparison is the stable
cone-to-upper comparison map. -/
theorem stableNormalizedLowerInclusionShortComplexToCochainDecomposition_τ₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure
      .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
        cut
        complex).τ₃ =
      TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        cut
        complex :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
