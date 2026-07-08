import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Source.Fractions.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.Fractions.Projections.Owner

/-!
# Comparison-source projection facts for Verdier roofs

The comparison source is the analytic stable Verdier quotient.  This file
re-exposes the concrete denominator and roof-map projections under comparison
source names, so downstream motivic t-structure files do not have to unfold
the source endpoint back to the stable quotient.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticDMgmComparisonSource

/-- The denominator of a comparison-source left fraction belongs to the
analytic Verdier inverted morphism class. -/
theorem leftFraction_denominator_mem
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (fraction :
      TraceAnalyticStableNullSubcategory.invertedMorphisms.LeftFraction
        source
        target) :
    TraceAnalyticStableNullSubcategory.invertedMorphisms fraction.s :=
  fraction.hs

/-- The denominator of a comparison-source left fraction becomes an isomorphism
after passing to the comparison source. -/
theorem leftFraction_denominator_isIso
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (fraction :
      TraceAnalyticStableNullSubcategory.invertedMorphisms.LeftFraction
        source
        target) :
    IsIso
      (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
        fraction.s) :=
  CategoryTheory.Localization.inverts
    TraceAnalyticDMgmComparisonSource.quotientFunctor
    TraceAnalyticStableNullSubcategory.invertedMorphisms
    fraction.s
    fraction.hs

/-- The comparison-source map represented by a left fraction is the quotient of
its numerator followed by the inverse of the quotient of its denominator. -/
theorem leftFraction_map_eq_numerator_comp_inv_denominator
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (fraction :
      TraceAnalyticStableNullSubcategory.invertedMorphisms.LeftFraction
        source
        target) :
    fraction.map
        TraceAnalyticDMgmComparisonSource.quotientFunctor
        (CategoryTheory.Localization.inverts
          TraceAnalyticDMgmComparisonSource.quotientFunctor
          TraceAnalyticStableNullSubcategory.invertedMorphisms) =
      TraceAnalyticDMgmComparisonSource.quotientFunctor.map fraction.f ≫
        inv
          (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
            fraction.s) :=
  rfl

/-- The identity-denominator roof attached to an additive homotopy morphism
maps to the comparison-source quotient of that morphism. -/
theorem leftFraction_ofHom_map
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom : source ⟶ target) :
    (CategoryTheory.MorphismProperty.LeftFraction.ofHom
        TraceAnalyticStableNullSubcategory.invertedMorphisms
        hom).map
        TraceAnalyticDMgmComparisonSource.quotientFunctor
        (CategoryTheory.Localization.inverts
          TraceAnalyticDMgmComparisonSource.quotientFunctor
          TraceAnalyticStableNullSubcategory.invertedMorphisms) =
      TraceAnalyticDMgmComparisonSource.quotientFunctor.map hom :=
  letI containsIdentities :
      TraceAnalyticStableNullSubcategory
        .invertedMorphisms.ContainsIdentities :=
    TraceAnalyticStableNullSubcategory
      .invertedMorphismsContainsIdentities
  CategoryTheory.MorphismProperty.LeftFraction.map_ofHom
    TraceAnalyticStableNullSubcategory.invertedMorphisms
    hom
    TraceAnalyticDMgmComparisonSource.quotientFunctor
    (CategoryTheory.Localization.inverts
      TraceAnalyticDMgmComparisonSource.quotientFunctor
      TraceAnalyticStableNullSubcategory.invertedMorphisms)

/-- The inverse-denominator roof attached to an inverted morphism composes with
that denominator to the identity after passing to the comparison source. -/
theorem leftFraction_ofInv_map_comp_denominator
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom : target ⟶ source)
    (inverted :
      TraceAnalyticStableNullSubcategory.invertedMorphisms hom) :
    (CategoryTheory.MorphismProperty.LeftFraction.ofInv
        hom
        inverted).map
        TraceAnalyticDMgmComparisonSource.quotientFunctor
        (CategoryTheory.Localization.inverts
          TraceAnalyticDMgmComparisonSource.quotientFunctor
          TraceAnalyticStableNullSubcategory.invertedMorphisms) ≫
      TraceAnalyticDMgmComparisonSource.quotientFunctor.map hom =
        𝟙
          (TraceAnalyticDMgmComparisonSource.quotientFunctor.obj
            target) :=
  CategoryTheory.MorphismProperty.LeftFraction.map_ofInv_hom_id
    hom
    inverted
    TraceAnalyticDMgmComparisonSource.quotientFunctor
    (CategoryTheory.Localization.inverts
      TraceAnalyticDMgmComparisonSource.quotientFunctor
      TraceAnalyticStableNullSubcategory.invertedMorphisms)

/-- Every comparison-source morphism between quotient-represented additive
homotopy objects has a left-fraction representative whose denominator is
inverted by the comparison-source quotient functor. -/
theorem exists_leftFraction_with_denominator_isIso
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom :
      TraceAnalyticDMgmComparisonSource.objectOf source ⟶
        TraceAnalyticDMgmComparisonSource.objectOf target) :
    ∃ fraction :
      TraceAnalyticStableNullSubcategory.invertedMorphisms.LeftFraction
        source
        target,
      hom =
          fraction.map
            TraceAnalyticDMgmComparisonSource.quotientFunctor
            (CategoryTheory.Localization.inverts
              TraceAnalyticDMgmComparisonSource.quotientFunctor
              TraceAnalyticStableNullSubcategory.invertedMorphisms) ∧
        IsIso
          (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
            fraction.s) :=
  match TraceAnalyticDMgmComparisonSource.exists_leftFraction hom with
  | ⟨fraction, fraction_eq⟩ =>
      ⟨fraction,
        And.intro
          fraction_eq
          (TraceAnalyticDMgmComparisonSource
            .leftFraction_denominator_isIso fraction)⟩

/-- Every comparison-source morphism between quotient-represented additive
homotopy objects has a left-fraction representative whose displayed map is
explicitly the numerator followed by the inverse denominator. -/
theorem exists_leftFraction_with_normalized_map
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom :
      TraceAnalyticDMgmComparisonSource.objectOf source ⟶
        TraceAnalyticDMgmComparisonSource.objectOf target) :
    ∃ fraction :
      TraceAnalyticStableNullSubcategory.invertedMorphisms.LeftFraction
        source
        target,
      hom =
          TraceAnalyticDMgmComparisonSource.quotientFunctor.map
              fraction.f ≫
            inv
              (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
                fraction.s) ∧
        IsIso
          (TraceAnalyticDMgmComparisonSource.quotientFunctor.map
            fraction.s) :=
  match
    TraceAnalyticDMgmComparisonSource
      .exists_leftFraction_with_denominator_isIso hom with
  | ⟨fraction, fraction_eq, denominator_isIso⟩ =>
      ⟨fraction,
        And.intro
          (Eq.trans
            fraction_eq
            (TraceAnalyticDMgmComparisonSource
              .leftFraction_map_eq_numerator_comp_inv_denominator
                fraction))
          denominator_isIso⟩

end TraceAnalyticDMgmComparisonSource

end AnalyticMotives
end LFunctions
end Boundary
