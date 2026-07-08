import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.ConeObject.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.ConeObject.Nullity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ShortComplex.Comparison.IsIso.Owner

/-!
# Null-cone criterion for the stable short-complex comparison

This file composes the additive null-cone inversion criterion with the stable
short-complex isomorphism criterion.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- Nullity of the additive cone of the normalized cone-to-upper comparison
implies the stable short-complex comparison is an isomorphism. -/
theorem stableNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso_of_nullCone
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
        .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
          cut
          complex) :=
  TraceAnalyticMotivicTStructure
    .stableNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso_of_inverted
      cut
      complex
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonMap_inverted_of_nullCone
        cut
        complex
        nullCone)

/-- Nullity of the named additive cone-comparison cone object implies the
stable short-complex comparison is an isomorphism. -/
theorem stableNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso_of_coneObject_null
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
        .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
          cut
          complex) :=
  TraceAnalyticMotivicTStructure
    .stableNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso_of_inverted
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonMap_inverted_of_coneObject_null
          cut
          complex
          nullCone)

/-- If the named additive cone-comparison cone object is the middle vertex of a
distinguished extension of null objects, then the stable short-complex
comparison is an isomorphism. -/
theorem stableNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso_of_coneObject_extension
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
        .stableNormalizedLowerInclusionShortComplexToCochainDecomposition
          cut
          complex) :=
  TraceAnalyticMotivicTStructure
    .stableNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso_of_coneObject_null
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonConeObject_null_of_extension
          cut
          complex
          coneTriangle
          coneDistinguished
          coneVertexEq
          left
          right)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
