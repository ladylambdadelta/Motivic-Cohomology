import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.Fractions.Owner

/-!
# Projection facts for analytic Verdier fractions

This file records the concrete denominator and map projections for roofs in the
analytic Verdier quotient.  The Gabriel-Zisman calculus is owned one level up;
this file only exposes the roof data that downstream t-structure and
orthogonality files repeatedly consume.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticStableMotiveCategory

/-- The denominator of an analytic Verdier left fraction belongs to the
inverted morphism class. -/
theorem leftFraction_denominator_mem
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (fraction :
      TraceAnalyticStableNullSubcategory.invertedMorphisms.LeftFraction
        source
        target) :
    TraceAnalyticStableNullSubcategory.invertedMorphisms fraction.s :=
  fraction.hs

/-- The denominator of an analytic Verdier left fraction becomes an isomorphism
after passing to stable analytic motives. -/
theorem leftFraction_denominator_isIso
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (fraction :
      TraceAnalyticStableNullSubcategory.invertedMorphisms.LeftFraction
        source
        target) :
    IsIso
      (TraceAnalyticStableMotiveCategory.quotientFunctor.map fraction.s) :=
  CategoryTheory.Localization.inverts
    TraceAnalyticStableMotiveCategory.quotientFunctor
    TraceAnalyticStableNullSubcategory.invertedMorphisms
    fraction.s
    fraction.hs

/-- The map represented by an analytic Verdier left fraction is the quotient
of its numerator followed by the inverse of the quotient of its denominator. -/
theorem leftFraction_map_eq_numerator_comp_inv_denominator
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (fraction :
      TraceAnalyticStableNullSubcategory.invertedMorphisms.LeftFraction
        source
        target) :
    fraction.map
        TraceAnalyticStableMotiveCategory.quotientFunctor
        (CategoryTheory.Localization.inverts
          TraceAnalyticStableMotiveCategory.quotientFunctor
          TraceAnalyticStableNullSubcategory.invertedMorphisms) =
      TraceAnalyticStableMotiveCategory.quotientFunctor.map fraction.f ≫
        inv
          (TraceAnalyticStableMotiveCategory.quotientFunctor.map
            fraction.s) :=
  rfl

/-- The identity-denominator roof attached to an additive homotopy morphism
maps to the quotient of that morphism. -/
theorem leftFraction_ofHom_map
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom : source ⟶ target) :
    (CategoryTheory.MorphismProperty.LeftFraction.ofHom
        TraceAnalyticStableNullSubcategory.invertedMorphisms
        hom).map
        TraceAnalyticStableMotiveCategory.quotientFunctor
        (CategoryTheory.Localization.inverts
          TraceAnalyticStableMotiveCategory.quotientFunctor
          TraceAnalyticStableNullSubcategory.invertedMorphisms) =
      TraceAnalyticStableMotiveCategory.quotientFunctor.map hom :=
  letI containsIdentities :
      TraceAnalyticStableNullSubcategory
        .invertedMorphisms.ContainsIdentities :=
    TraceAnalyticStableNullSubcategory
      .invertedMorphismsContainsIdentities
  CategoryTheory.MorphismProperty.LeftFraction.map_ofHom
    TraceAnalyticStableNullSubcategory.invertedMorphisms
    hom
    TraceAnalyticStableMotiveCategory.quotientFunctor
    (CategoryTheory.Localization.inverts
      TraceAnalyticStableMotiveCategory.quotientFunctor
      TraceAnalyticStableNullSubcategory.invertedMorphisms)

/-- The inverse-denominator roof attached to an inverted morphism composes with
that denominator to the identity after quotienting. -/
theorem leftFraction_ofInv_map_comp_denominator
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom : target ⟶ source)
    (inverted :
      TraceAnalyticStableNullSubcategory.invertedMorphisms hom) :
    (CategoryTheory.MorphismProperty.LeftFraction.ofInv
        hom
        inverted).map
        TraceAnalyticStableMotiveCategory.quotientFunctor
        (CategoryTheory.Localization.inverts
          TraceAnalyticStableMotiveCategory.quotientFunctor
          TraceAnalyticStableNullSubcategory.invertedMorphisms) ≫
      TraceAnalyticStableMotiveCategory.quotientFunctor.map hom =
        𝟙
          (TraceAnalyticStableMotiveCategory.quotientFunctor.obj
            target) :=
  CategoryTheory.MorphismProperty.LeftFraction.map_ofInv_hom_id
    hom
    inverted
    TraceAnalyticStableMotiveCategory.quotientFunctor
    (CategoryTheory.Localization.inverts
      TraceAnalyticStableMotiveCategory.quotientFunctor
      TraceAnalyticStableNullSubcategory.invertedMorphisms)

/-- Every stable morphism between quotient-represented additive homotopy
objects has a left-fraction representative whose denominator is inverted by
the quotient functor. -/
theorem exists_leftFraction_with_denominator_isIso
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom :
      TraceAnalyticStableMotiveCategory.objectOf source ⟶
        TraceAnalyticStableMotiveCategory.objectOf target) :
    ∃ fraction :
      TraceAnalyticStableNullSubcategory.invertedMorphisms.LeftFraction
        source
        target,
      hom =
          fraction.map
            TraceAnalyticStableMotiveCategory.quotientFunctor
            (CategoryTheory.Localization.inverts
              TraceAnalyticStableMotiveCategory.quotientFunctor
              TraceAnalyticStableNullSubcategory.invertedMorphisms) ∧
        IsIso
          (TraceAnalyticStableMotiveCategory.quotientFunctor.map
            fraction.s) :=
  match TraceAnalyticStableMotiveCategory.exists_leftFraction hom with
  | ⟨fraction, fraction_eq⟩ =>
      ⟨fraction,
        And.intro
          fraction_eq
          (TraceAnalyticStableMotiveCategory
            .leftFraction_denominator_isIso fraction)⟩

/-- Every stable morphism between quotient-represented additive homotopy
objects has a left-fraction representative whose displayed map is explicitly
the numerator followed by the inverse denominator. -/
theorem exists_leftFraction_with_normalized_map
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (hom :
      TraceAnalyticStableMotiveCategory.objectOf source ⟶
        TraceAnalyticStableMotiveCategory.objectOf target) :
    ∃ fraction :
      TraceAnalyticStableNullSubcategory.invertedMorphisms.LeftFraction
        source
        target,
      hom =
          TraceAnalyticStableMotiveCategory.quotientFunctor.map
              fraction.f ≫
            inv
              (TraceAnalyticStableMotiveCategory.quotientFunctor.map
                fraction.s) ∧
        IsIso
          (TraceAnalyticStableMotiveCategory.quotientFunctor.map
            fraction.s) :=
  match
    TraceAnalyticStableMotiveCategory
      .exists_leftFraction_with_denominator_isIso hom with
  | ⟨fraction, fraction_eq, denominator_isIso⟩ =>
      ⟨fraction,
        And.intro
          (Eq.trans
            fraction_eq
            (TraceAnalyticStableMotiveCategory
              .leftFraction_map_eq_numerator_comp_inv_denominator
                fraction))
          denominator_isIso⟩

end TraceAnalyticStableMotiveCategory

end AnalyticMotives
end LFunctions
end Boundary
