import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.Fractions.Projections.Owner

/-!
# Chosen normalized analytic Verdier roofs

This file packages the normalized roof supplied by the analytic Verdier
left-fraction calculus for a stable morphism between quotient-represented
additive homotopy objects, together with direct projections of its fraction,
normalization equation, and denominator-isomorphism certificate.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticStableMotiveCategory

/-- A chosen normalized roof representative for a stable morphism between
quotient-represented additive homotopy objects. -/
def normalizedLeftFraction
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom :
      TraceAnalyticStableMotiveCategory.objectOf source ⟶
        TraceAnalyticStableMotiveCategory.objectOf target) :
    TraceAnalyticStableNullSubcategory.invertedMorphisms.LeftFraction
      source
      target :=
  (TraceAnalyticStableMotiveCategory
    .exists_leftFraction_with_normalized_map hom).choose

/-- The chosen normalized roof represents the original stable morphism as its
numerator followed by the inverse denominator. -/
theorem normalizedLeftFraction_map_eq
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom :
      TraceAnalyticStableMotiveCategory.objectOf source ⟶
        TraceAnalyticStableMotiveCategory.objectOf target) :
    hom =
      TraceAnalyticStableMotiveCategory.quotientFunctor.map
          (TraceAnalyticStableMotiveCategory
            .normalizedLeftFraction hom).f ≫
        inv
          (TraceAnalyticStableMotiveCategory.quotientFunctor.map
            (TraceAnalyticStableMotiveCategory
              .normalizedLeftFraction hom).s) :=
  (TraceAnalyticStableMotiveCategory
    .exists_leftFraction_with_normalized_map hom).choose_spec.left

/-- The denominator of the chosen normalized roof becomes an isomorphism after
passing to stable analytic motives. -/
theorem normalizedLeftFraction_denominator_isIso
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom :
      TraceAnalyticStableMotiveCategory.objectOf source ⟶
        TraceAnalyticStableMotiveCategory.objectOf target) :
    IsIso
      (TraceAnalyticStableMotiveCategory.quotientFunctor.map
        (TraceAnalyticStableMotiveCategory
          .normalizedLeftFraction hom).s) :=
  (TraceAnalyticStableMotiveCategory
    .exists_leftFraction_with_normalized_map hom).choose_spec.right

/-- The denominator of the chosen normalized roof belongs to the analytic
Verdier inverted class. -/
theorem normalizedLeftFraction_denominator_mem
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom :
      TraceAnalyticStableMotiveCategory.objectOf source ⟶
        TraceAnalyticStableMotiveCategory.objectOf target) :
    TraceAnalyticStableNullSubcategory.invertedMorphisms
      (TraceAnalyticStableMotiveCategory.normalizedLeftFraction hom).s :=
  (TraceAnalyticStableMotiveCategory.normalizedLeftFraction hom).hs

end TraceAnalyticStableMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
