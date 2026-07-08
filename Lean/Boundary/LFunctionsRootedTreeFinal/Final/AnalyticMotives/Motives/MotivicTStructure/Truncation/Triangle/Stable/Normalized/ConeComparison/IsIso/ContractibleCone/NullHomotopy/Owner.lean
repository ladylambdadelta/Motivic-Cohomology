import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Additive.Normalized.ConeComparison.ConeObject.Contractible.NullHomotopy.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.MotivicTStructure.Truncation.Triangle.Stable.Normalized.ConeComparison.IsIso.Owner

/-!
# Null-homotopic-identity isomorphism criterion for the stable cone comparison

This file composes the additive null-homotopic-identity criterion with the
Verdier localization criterion for the normalized stable cone-to-upper
comparison map.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticMotivicTStructure

/-- A null-homotopic identity presentation for the concrete mapping cone of the
normalized cone-to-upper cochain map makes the stable cone comparison an
isomorphism. -/
theorem stableNormalizedConeComparisonMap_isIso_of_identity_eq_nullHomotopicMap
    (cut : ℤ)
    (complex : TraceAnalyticAdditiveCochainComplex)
    [∀ degree, complex.HasHomology degree]
    (hom :
      ∀ i j,
        (ComplexShape.up ℤ).Rel j i →
          (CochainComplex.mappingCone
            (TraceAnalyticMotivicTStructure
              .additiveNormalizedConeComparisonCochainMap cut complex)).X i ⟶
            (CochainComplex.mappingCone
              (TraceAnalyticMotivicTStructure
                .additiveNormalizedConeComparisonCochainMap cut complex)).X j)
    (identity_eq :
      𝟙
          (CochainComplex.mappingCone
            (TraceAnalyticMotivicTStructure
              .additiveNormalizedConeComparisonCochainMap cut complex)) =
        _root_.HomologicalComplex.nullHomotopicMap' hom) :
    IsIso
      (TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap
        cut
        complex) :=
  TraceAnalyticMotivicTStructure.stableNormalizedConeComparisonMap_isIso_of_inverted
    cut
    complex
    (TraceAnalyticMotivicTStructure
      .additiveNormalizedConeComparisonMap_inverted_of_identity_eq_nullHomotopicMap
        cut
        complex
        hom
        identity_eq)

end TraceAnalyticMotivicTStructure

end AnalyticMotives
end LFunctions
end Boundary
