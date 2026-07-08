import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ShortComplex.Comparison.Map.Owner

/-!
# Isomorphism criterion for the stable short-complex comparison

This file records that the stable short-complex comparison is an isomorphism
once its third component, the stable cone-to-upper comparison map, is an
isomorphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- If the stable cone-to-upper comparison is an isomorphism, then the induced
short-complex comparison is an isomorphism. -/
theorem stableNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        cut
        complex)] :
    IsIso
      (TraceAnalyticMotivicTStructure
        .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
          cut
          complex) :=
  ShortComplex.isIso_of_isIso
    (TraceAnalyticMotivicTStructure
      .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
        cut
        complex)

/-- If the additive homotopy cone-to-upper comparison belongs to the Verdier
inverted class, then the induced stable short-complex comparison is an
isomorphism. -/
theorem stableNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso_of_inverted
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (inverted :
      TraceAnalyticStableNullSubcategory.invertedMorphisms
        (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonMap
          cut
          complex)) :
    IsIso
      (TraceAnalyticMotivicTStructure
        .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
          cut
          complex) :=
  let stableComparisonIso :
      IsIso
        (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
          cut
          complex) :=
    TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap_isIso_of_inverted
      cut
      complex
      inverted
  haveI :
      IsIso
        (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
          cut
          complex) :=
    stableComparisonIso
  TraceAnalyticMotivicTStructure
    .stableNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso
      cut
      complex

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
