import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.Contractible.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.ConeObject.Owner

/-!
# Contractibility criterion for the normalized cone-comparison cone object

This file specializes the homotopy-category contractibility criterion to the
concrete mapping cone of the normalized cone-to-upper cochain map.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

namespace TraceAnalyticMotivicTStructure

/-- A contracting homotopy of the concrete mapping cone of the normalized
cone-to-upper cochain map makes the named cone-comparison cone object null. -/
theorem additiveNormalizedConeComparisonConeObject_null_of_contractible
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (contractible :
      Nonempty
        (Homotopy
          (𝟙
            (CochainComplex.mappingCone
              (TraceAnalyticMotivicTStructure
                .additiveNormalizedConeComparisonCochainMap cut complex)))
          0)) :
    TraceAnalyticStableNullSubcategory.P
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonConeObject
        cut
        complex) :=
  TraceAnalyticStableNullSubcategory.objectOf_mem_of_contractible
    (CochainComplex.mappingCone
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonCochainMap
        cut
        complex))
    contractible

/-- A contracting homotopy of the concrete mapping cone of the normalized
cone-to-upper cochain map makes the additive comparison map inverted by the
analytic Verdier class. -/
theorem additiveNormalizedConeComparisonMap_inverted_of_contractibleCone
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (contractible :
      Nonempty
        (Homotopy
          (𝟙
            (CochainComplex.mappingCone
              (TraceAnalyticMotivicTStructure
                .additiveNormalizedConeComparisonCochainMap cut complex)))
          0)) :
    TraceAnalyticStableNullSubcategory.invertedMorphisms
      (TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonMap
        cut
        complex) :=
  TraceAnalyticMotivicTStructure
    .additiveNormalizedConeComparisonMap_inverted_of_coneObject_null
      cut
      complex
      (TraceAnalyticMotivicTStructure
        .additiveNormalizedConeComparisonConeObject_null_of_contractible
          cut
          complex
          contractible)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
