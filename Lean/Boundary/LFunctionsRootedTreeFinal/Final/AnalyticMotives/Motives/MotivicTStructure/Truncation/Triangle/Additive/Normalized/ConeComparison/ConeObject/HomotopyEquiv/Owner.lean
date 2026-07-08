import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.Contractible.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.ConeObject.IdentityCone.Composites.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.ConeObject.Owner

/-!
# Homotopy-equivalence criterion for the normalized cone-comparison cone object

This file reduces nullity of the concrete normalized cone-comparison cone
object to a homotopy equivalence with Mathlib's contractible identity cone.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- If the concrete mapping cone of the normalized cone-to-upper map is
homotopy equivalent to an identity mapping cone, then the named cone-comparison
cone object is null. -/
theorem additiveNormalizedConeComparisonConeObject_null_of_homotopyEquiv_identityCone
    (cut : ℤ)
    (complex target : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (equiv :
      HomotopyEquiv
        (CochainComplex.mappingCone
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonCochainMap cut complex))
        (CochainComplex.mappingCone (𝟙 target))) :
    TraceAnalyticStableNullSubcategory.P
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonConeObject
        cut
        complex) :=
  TraceAnalyticStableNullSubcategory.objectOf_mem_of_homotopyEquiv_identityCone
    (CochainComplex.mappingCone
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex))
    target
    equiv

/-- A homotopy equivalence from the concrete mapping cone of the normalized
cone-to-upper map to an identity mapping cone makes the additive comparison
map inverted by the analytic Verdier class. -/
theorem additiveNormalizedConeComparisonMap_inverted_of_homotopyEquiv_identityCone
    (cut : ℤ)
    (complex target : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (equiv :
      HomotopyEquiv
        (CochainComplex.mappingCone
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonCochainMap cut complex))
        (CochainComplex.mappingCone (𝟙 target))) :
    TraceAnalyticStableNullSubcategory.invertedMorphisms
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonMap
        cut
        complex) :=
  TraceAnalyticMotivicTStructure
    .additiveNormalizedConeComparisonMap_inverted_of_coneObject_null
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonConeObject_null_of_homotopyEquiv_identityCone
          cut
          complex
          target
          equiv)

/-- If the concrete mapping cone of the normalized cone-to-upper map is
isomorphic to an identity mapping cone, then the named cone-comparison cone
object is null. -/
theorem additiveNormalizedConeComparisonConeObject_null_of_iso_identityCone
    (cut : ℤ)
    (complex target : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (iso :
      CochainComplex.mappingCone
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonCochainMap cut complex) ≅
        CochainComplex.mappingCone (𝟙 target)) :
    TraceAnalyticStableNullSubcategory.P
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonConeObject
        cut
        complex) :=
  TraceAnalyticStableNullSubcategory.objectOf_mem_of_iso_identityCone
    (CochainComplex.mappingCone
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex))
    target
    iso

/-- An isomorphism from the concrete mapping cone of the normalized cone-to-upper
map to an identity mapping cone makes the additive comparison map inverted by
the analytic Verdier class. -/
theorem additiveNormalizedConeComparisonMap_inverted_of_iso_identityCone
    (cut : ℤ)
    (complex target : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (iso :
      CochainComplex.mappingCone
          (TraceAnalyticMotivicTStructure
            .additiveNormalizedConeComparisonCochainMap cut complex) ≅
        CochainComplex.mappingCone (𝟙 target)) :
    TraceAnalyticStableNullSubcategory.invertedMorphisms
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonMap
        cut
        complex) :=
  TraceAnalyticMotivicTStructure
    .additiveNormalizedConeComparisonMap_inverted_of_coneObject_null
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonConeObject_null_of_iso_identityCone
          cut
          complex
          target
          iso)

/-- If the normalized cone-to-upper cochain map is an isomorphism, then the
named cone-comparison cone object is null. -/
theorem additiveNormalizedConeComparisonConeObject_null_of_isIso_cochainMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticStableNullSubcategory.P
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonConeObject
        cut
        complex) :=
  TraceAnalyticMotivicTStructure
    .additiveNormalizedConeComparisonConeObject_null_of_iso_identityCone
      cut
      complex
      (TraceAnalyticMotivicTStructure.additiveTruncGE cut complex)
      (TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonIdentityConeIso cut complex)

/-- If the normalized cone-to-upper cochain map is an isomorphism, then the
additive comparison map is inverted by the analytic Verdier class. -/
theorem additiveNormalizedConeComparisonMap_inverted_of_isIso_cochainMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    [IsIso
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex)] :
    TraceAnalyticStableNullSubcategory.invertedMorphisms
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonMap
        cut
        complex) :=
  TraceAnalyticMotivicTStructure
    .additiveNormalizedConeComparisonMap_inverted_of_coneObject_null
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonConeObject_null_of_isIso_cochainMap
          cut
          complex)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
