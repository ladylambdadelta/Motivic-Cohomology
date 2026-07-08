import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.Inverted.Owner

/-!
# Cone object of the normalized cone-to-upper comparison

This file names the concrete additive homotopy object whose nullity is needed
to prove that the normalized cone-to-upper comparison is inverted by the
Verdier localization.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- The cone object of the normalized additive cone-to-upper comparison map. -/
def additiveNormalizedConeComparisonConeObject
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticAdditiveHomotopyCategory.objectOf
    (CochainComplex.mappingCone
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex))

/-- The cone object is the homotopy image of Mathlib's concrete mapping cone
for the cochain-level cone-to-upper comparison map. -/
theorem additiveNormalizedConeComparisonConeObject_eq_objectOf_mappingCone
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonConeObject
        cut
        complex =
      TraceAnalyticAdditiveHomotopyCategory.objectOf
        (CochainComplex.mappingCone
          (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
            cut
            complex)) :=
  rfl

/-- The third vertex of the cone-comparison triangle is the named cone object. -/
theorem additiveNormalizedConeComparisonTriangle_obj₃
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree] :
    (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonTriangle
      cut
      complex).obj₃ =
      TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonConeObject
        cut
        complex :=
  rfl

/-- Nullity of the named cone object implies that the cone-to-upper comparison
map is inverted by the Verdier morphism class. -/
theorem additiveNormalizedConeComparisonMap_inverted_of_coneObject_null
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (nullCone :
      TraceAnalyticStableNullSubcategory.P
        (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonConeObject
          cut
          complex)) :
    TraceAnalyticStableNullSubcategory.invertedMorphisms
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonMap
        cut
        complex) :=
  Eq.subst
    (motive :=
      fun object =>
        TraceAnalyticStableNullSubcategory.P object →
          TraceAnalyticStableNullSubcategory.invertedMorphisms
            (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonMap
              cut
              complex))
    (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonTriangle_obj₃
      cut
      complex)
    (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonMap_inverted_of_nullCone
      cut
      complex)
    nullCone

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
