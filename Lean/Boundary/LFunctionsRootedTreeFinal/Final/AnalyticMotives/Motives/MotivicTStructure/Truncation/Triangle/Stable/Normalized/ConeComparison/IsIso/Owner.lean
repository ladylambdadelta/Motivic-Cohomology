import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.ConeObject.HomotopyEquiv.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ConeComparison.Map.Owner

/-!
# Isomorphism criterion for the normalized stable cone comparison

This file records the Verdier-localization criterion for the stable
cone-to-upper comparison map to be an isomorphism.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- If the additive homotopy cone-to-upper comparison belongs to the Verdier
inverted class, then its stable image is an isomorphism. -/
theorem stableNormalizedConeComparisonMap_isIso_of_inverted
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (inverted :
      TraceAnalyticStableNullSubcategory.invertedMorphisms
        (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonMap
          cut
          complex)) :
    IsIso
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        cut
        complex) :=
  CategoryTheory.Localization.inverts
    TraceAnalyticStableMotiveCategory.quotientFunctor
    TraceAnalyticStableNullSubcategory.invertedMorphisms
    (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonMap
      cut
      complex)
    inverted

/-- A homotopy equivalence from the concrete mapping cone of the normalized
cone-to-upper map to an identity mapping cone makes the stable cone-to-upper
comparison an isomorphism. -/
theorem stableNormalizedConeComparisonMap_isIso_of_homotopyEquiv_identityCone
    (cut : ℤ)
    (complex target : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (equiv :
      HomotopyEquiv
        (CochainComplex.mappingCone
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonCochainMap cut complex))
        (CochainComplex.mappingCone (𝟙 target))) :
    IsIso
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        cut
        complex) :=
  TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap_isIso_of_inverted
    cut
    complex
    (TraceAnalyticMotivicTStructure
      .additiveNormalizedConeComparisonMap_inverted_of_homotopyEquiv_identityCone
        cut
        complex
        target
        equiv)

/-- An isomorphism from the concrete mapping cone of the normalized cone-to-upper
map to an identity mapping cone makes the stable cone-to-upper comparison an
isomorphism. -/
theorem stableNormalizedConeComparisonMap_isIso_of_iso_identityCone
    (cut : ℤ)
    (complex target : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (iso :
      CochainComplex.mappingCone
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonCochainMap cut complex) ≅
        CochainComplex.mappingCone (𝟙 target)) :
    IsIso
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        cut
        complex) :=
  TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap_isIso_of_inverted
    cut
    complex
    (TraceAnalyticMotivicTStructure
      .additiveNormalizedConeComparisonMap_inverted_of_iso_identityCone
        cut
        complex
        target
        iso)

/-- Nullity of the named additive cone-comparison cone object implies that the
stable cone-to-upper comparison is an isomorphism. -/
theorem stableNormalizedConeComparisonMap_isIso_of_coneObject_null
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (nullCone :
      TraceAnalyticStableNullSubcategory.P
        (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonConeObject
          cut
          complex)) :
    IsIso
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        cut
        complex) :=
  TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap_isIso_of_inverted
    cut
    complex
    (TraceAnalyticMotivicTStructure
      .additiveNormalizedConeComparisonMap_inverted_of_coneObject_null
        cut
        complex
        nullCone)

/-- If the named additive cone-comparison cone object is the middle vertex of a
distinguished extension of null objects, then the stable cone-to-upper
comparison is an isomorphism. -/
theorem stableNormalizedConeComparisonMap_isIso_of_coneObject_extension
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
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        cut
        complex) :=
  TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap_isIso_of_inverted
    cut
    complex
    (TraceAnalyticMotivicTStructure
      .additiveNormalizedConeComparisonMap_inverted_of_coneObject_extension
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
