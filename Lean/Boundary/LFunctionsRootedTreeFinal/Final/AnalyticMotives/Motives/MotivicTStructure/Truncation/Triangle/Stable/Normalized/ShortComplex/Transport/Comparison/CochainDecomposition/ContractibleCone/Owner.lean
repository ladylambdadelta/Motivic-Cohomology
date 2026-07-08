import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ShortComplex.Comparison.ContractibleCone.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ShortComplex.Transport.Comparison.CochainDecomposition.NullCone.Owner

/-!
# Contractible-cone criterion for the transported normalized comparison

This file transfers the extracted contractible-cone criterion to the
transported normalized short-complex comparison.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- A contracting homotopy of the concrete mapping cone of the normalized
cone-to-upper cochain map makes the transported normalized short-complex
comparison an isomorphism. -/
theorem stableTransportedNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso_of_contractibleCone
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
        .stableTransportedNormalizedLowerInclusionShortComplexToCochainDecomposition
          cut
          complex) :=
  TraceAnalyticMotivicTStructure
    .stableTransportedNormalizedLowerInclusionShortComplexToCochainDecomposition_isIso_of_coneObject_null
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
