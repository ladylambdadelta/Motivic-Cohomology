import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.ConeObject.Contractible.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ShortComplex.Comparison.NullCone.Owner

/-!
# Contractible-cone criterion for the stable short-complex comparison

This file composes the concrete contracting-homotopy criterion with the stable
short-complex comparison isomorphism theorem.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- A contracting homotopy of the concrete mapping cone of the normalized
cone-to-upper cochain map makes the stable short-complex comparison an
isomorphism. -/
theorem stableNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso_of_contractibleCone
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
        .additiveNormalizedConeComparisonConeObject_null_of_contractible
          cut
          complex
          contractible)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
