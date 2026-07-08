import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Fractions.Projections.Owner

/-!
# Chosen normalized comparison-source roofs

This file packages the normalized roof supplied by the comparison-source
left-fraction calculus for a morphism between quotient-represented additive
homotopy objects, together with projections of its fraction, normalization
equation, and denominator-isomorphism certificate.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource

/-- A chosen normalized roof representative for a comparison-source morphism
between quotient-represented additive homotopy objects. -/
def normalizedLeftFraction
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom :
      TraceAnalyticDMgmComparisonSource.objectOf source ⟶
        TraceAnalyticDMgmComparisonSource.objectOf target) :
    TraceAnalyticStableNullSubcategory.invertedMorphisms.LeftFraction
      source
      target :=
  (TraceAnalyticDMgmComparisonSource
    .exists_leftFraction_with_normalized_map hom).choose

/-- The chosen normalized roof represents the original comparison-source
morphism as its numerator followed by the inverse denominator. -/
theorem normalizedLeftFraction_map_eq
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom :
      TraceAnalyticDMgmComparisonSource.objectOf source ⟶
        TraceAnalyticDMgmComparisonSource.objectOf target) :
    hom =
      TraceAnalyticDMgmComparisonSource.quotientFunctor.map
          (TraceAnalyticDMgmComparisonSource
            .normalizedLeftFraction hom).f ≫
        inv
          (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
            (TraceAnalyticDMgmComparisonSource
              .normalizedLeftFraction hom).s) :=
  (TraceAnalyticDMgmComparisonSource
    .exists_leftFraction_with_normalized_map hom).choose_spec.left

/-- The denominator of the chosen normalized roof becomes an isomorphism after
passing to the comparison source. -/
theorem normalizedLeftFraction_denominator_isIso
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom :
      TraceAnalyticDMgmComparisonSource.objectOf source ⟶
        TraceAnalyticDMgmComparisonSource.objectOf target) :
    IsIso
      (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
        (TraceAnalyticDMgmComparisonSource
          .normalizedLeftFraction hom).s) :=
  (TraceAnalyticDMgmComparisonSource
    .exists_leftFraction_with_normalized_map hom).choose_spec.right

/-- The denominator of the chosen normalized roof belongs to the analytic
Verdier inverted class. -/
theorem normalizedLeftFraction_denominator_mem
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom :
      TraceAnalyticDMgmComparisonSource.objectOf source ⟶
        TraceAnalyticDMgmComparisonSource.objectOf target) :
    TraceAnalyticStableNullSubcategory.invertedMorphisms
      (TraceAnalyticDMgmComparisonSource.normalizedLeftFraction hom).s :=
  (TraceAnalyticDMgmComparisonSource.normalizedLeftFraction hom).hs

end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
