import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.CochainDecomposition.Stable.ShortComplex.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ConeComparison.Target.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ShortComplex.Owner

/-!
# Front comparison for the normalized stable truncation short complexes

The normalized lower-inclusion cone short complex and the stable image of the
cochain truncation-decomposition short complex have the same lower vertex,
middle vertex, and lower-inclusion map.  The cochain decomposition also
identifies its upper vertex and projection with the named normalized
cone-comparison target.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- The normalized cone short complex and the stable cochain decomposition have
the same lower vertex. -/
theorem stableNormalizedLowerInclusionShortComplex_front_X₁_eq_stableCochainDecomposition
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionShortComplex
      cut
      complex).X₁ =
      (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
        cut
        complex).X₁ :=
  rfl

/-- The normalized cone short complex and the stable cochain decomposition have
the same middle vertex. -/
theorem stableNormalizedLowerInclusionShortComplex_front_X₂_eq_stableCochainDecomposition
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionShortComplex
      cut
      complex).X₂ =
      (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
        cut
        complex).X₂ :=
  rfl

/-- The normalized cone short complex and the stable cochain decomposition have
the same lower-inclusion map. -/
theorem stableNormalizedLowerInclusionShortComplex_front_f_eq_stableCochainDecomposition
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableNormalizedLowerInclusionShortComplex
      cut
      complex).f =
      (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
        cut
        complex).f :=
  rfl

/-- The stable cochain-decomposition upper vertex is the named normalized
cone-comparison target. -/
theorem stableCochainDecompositionShortComplex_X₃_eq_normalizedConeComparisonTarget
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
      cut
      complex).X₃ =
      TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonTarget
        cut
        complex :=
  rfl

/-- The stable cochain-decomposition upper map is the named normalized
cone-comparison projection. -/
theorem stableCochainDecompositionShortComplex_g_eq_normalizedConeComparisonProjection
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.stableCochainDecompositionShortComplex
      cut
      complex).g =
      TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonProjection
        cut
        complex :=
  rfl

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
