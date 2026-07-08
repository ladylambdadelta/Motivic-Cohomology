import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.ConeObject.Nullity.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ConeComparison.IsIso.Owner

/-!
# Zero-cone isomorphism criterion for the normalized stable cone comparison

This file composes the concrete zero-cone criterion with the Verdier
isomorphism criterion for the stable cone-to-upper comparison map.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- If the named additive cone-comparison cone object is zero, then the stable
cone-to-upper comparison is an isomorphism. -/
theorem stableNormalizedConeComparisonMap_isIso_of_coneObject_eq_zero
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hzero :
      TraceAnalyticMotivicTStructure.additiveNormalizedConeComparisonConeObject
        cut
        complex = 0) :
    IsIso
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        cut
        complex) :=
  TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap_isIso_of_inverted
    cut
    complex
    (TraceAnalyticMotivicTStructure
      .additiveNormalizedConeComparisonMap_inverted_of_coneObject_eq_zero
        cut
        complex
        hzero)

/-- If the named additive cone-comparison cone object is a zero object, then
the stable cone-to-upper comparison is an isomorphism. -/
theorem stableNormalizedConeComparisonMap_isIso_of_coneObject_isZero
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hzero :
      CategoryTheory.Limits.IsZero
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
      .additiveNormalizedConeComparisonMap_inverted_of_coneObject_isZero
        cut
        complex
        hzero)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
