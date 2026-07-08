import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ShortComplex.Comparison.NullCone.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ShortComplex.Transport.Comparison.CochainDecomposition.IsIso.Owner

/-!
# Null-cone criterion for the transported normalized comparison

This file transfers the extracted null-cone criteria to the transported
normalized short-complex comparison.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Nullity of the additive cone of the normalized cone-to-upper comparison
implies the transported normalized short-complex comparison is an isomorphism. -/
theorem stableTransportedNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso_of_nullCone
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (nullCone :
      TraceAnalyticStableNullSubcategory.P
        (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonTriangle
          cut
          complex).obj₃) :
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
      .stableNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso_of_nullCone
        cut
        complex
        nullCone
  haveI :
      IsIso
        (TraceAnalyticMotivicTStructure
          .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
            cut
            complex) :=
    extractedIso
  inferInstance

/-- Nullity of the named additive cone-comparison cone object implies the
transported normalized short-complex comparison is an isomorphism. -/
theorem stableTransportedNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso_of_coneObject_null
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (nullCone :
      TraceAnalyticStableNullSubcategory.P
        (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonConeObject
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
        .stableNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso_of_coneObject_null
        cut
        complex
        nullCone
  haveI :
      IsIso
        (TraceAnalyticMotivicTStructure
          .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
            cut
            complex) :=
    extractedIso
  inferInstance

/-- If the named additive cone-comparison cone object is the middle vertex of a
distinguished extension of null objects, then the transported normalized
comparison to the stable cochain-decomposition short complex is an isomorphism. -/
theorem stableTransportedNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso_of_coneObject_extension
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (coneTriangle : Triangle TraceAnalyticAdditiveHomotopyCategory)
    (coneDistinguished :
      coneTriangle ∈
        TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles)
    (coneVertexEq :
      TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonConeObject
          cut
          complex =
        coneTriangle.obj₂)
    (left : TraceAnalyticStableNullSubcategory.P coneTriangle.obj₁)
    (right : TraceAnalyticStableNullSubcategory.P coneTriangle.obj₃) :
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
      .stableNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso_of_coneObject_extension
        cut
        complex
        coneTriangle
        coneDistinguished
        coneVertexEq
        left
        right
  haveI :
      IsIso
        (TraceAnalyticMotivicTStructure
          .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
            cut
            complex) :=
    extractedIso
  inferInstance

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
