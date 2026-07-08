import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ShortComplex.Comparison.IdentityCone.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ShortComplex.Transport.Comparison.CochainDecomposition.Owner

/-!
# Isomorphism criteria for the transported normalized comparison

This file transfers the existing isomorphism criteria for the extracted
normalized short-complex comparison to the transported normalized short-complex
comparison.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- If the stable cone-to-upper comparison is an isomorphism, then the
transported normalized comparison to the stable cochain-decomposition short
complex is an isomorphism. -/
theorem stableTransportedNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        cut
        complex)] :
    IsIso
      (TraceAnalyticMotivicTStructure
        .stableTransportedNormalizedLowerInclusionShortComplexToCochainDecomposition
          cut
          complex) :=
  let extractedIso :
      IsIso
        (TraceAnalyticMotivicTStructure
          .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
            cut
            complex) :=
    TraceAnalyticMotivicTStructure
      .stableNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso
        cut
        complex
  haveI :
      IsIso
        (TraceAnalyticMotivicTStructure
          .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
            cut
            complex) :=
    extractedIso
  let transportedIso :
      IsIso
        ((TraceAnalyticMotivicTStructure
          .stableNormalizedLowerInclusionShortComplexIsoTransported
            cut
            complex).inv ≫
          TraceAnalyticMotivicTStructure
            .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
              cut
              complex) :=
    IsIso.comp_isIso
  transportedIso

/-- If the additive homotopy cone-to-upper comparison belongs to the Verdier
inverted class, then the transported normalized comparison to the stable
cochain-decomposition short complex is an isomorphism. -/
theorem stableTransportedNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso_of_inverted
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
        .stableTransportedNormalizedLowerInclusionShortComplexToCochainDecomposition
          cut
          complex) :=
  let extractedIso :
      IsIso
        (TraceAnalyticMotivicTStructure
          .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
            cut
            complex) :=
    TraceAnalyticMotivicTStructure
      .stableNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso_of_inverted
        cut
        complex
        inverted
  haveI :
      IsIso
        (TraceAnalyticMotivicTStructure
          .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
            cut
            complex) :=
    extractedIso
  let transportedIso :
      IsIso
        ((TraceAnalyticMotivicTStructure
          .stableNormalizedLowerInclusionShortComplexIsoTransported
            cut
            complex).inv ≫
          TraceAnalyticMotivicTStructure
            .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
              cut
              complex) :=
    IsIso.comp_isIso
  transportedIso

/-- If the normalized cone-to-upper cochain map is an isomorphism, then the
transported normalized comparison to the stable cochain-decomposition short
complex is an isomorphism. -/
theorem stableTransportedNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso_of_isIso_cochainMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    IsIso
      (TraceAnalyticMotivicTStructure
        .stableTransportedNormalizedLowerInclusionShortComplexToCochainDecomposition
          cut
          complex) :=
  let extractedIso :
      IsIso
        (TraceAnalyticMotivicTStructure
          .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
            cut
            complex) :=
    TraceAnalyticMotivicTStructure
      .stableNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso_of_isIso_cochainMap
        cut
        complex
  haveI :
      IsIso
        (TraceAnalyticMotivicTStructure
          .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
            cut
            complex) :=
    extractedIso
  let transportedIso :
      IsIso
        ((TraceAnalyticMotivicTStructure
          .stableNormalizedLowerInclusionShortComplexIsoTransported
            cut
            complex).inv ≫
          TraceAnalyticMotivicTStructure
            .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
              cut
              complex) :=
    IsIso.comp_isIso
  transportedIso

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
