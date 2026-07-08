import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.Owner

/-!
# Universal property of the analytic Verdier quotient

This file specializes Mathlib's localization universal property to the stable
analytic motive category.  A functor out of the additive analytic homotopy
category descends to stable analytic motives exactly when it inverts the
morphisms whose cones belong to the stable null subcategory.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The morphism property inverted by the stable analytic motive quotient. -/
def TraceAnalyticStableMotiveCategory.invertedMorphisms :
    CategoryTheory.MorphismProperty
      TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticStableNullSubcategory.invertedMorphisms

/-- The quotient functor is a localization at the stable null morphisms. -/
def TraceAnalyticStableMotiveCategory.isLocalization :
    TraceAnalyticStableMotiveCategory.quotientFunctor.IsLocalization
      TraceAnalyticStableMotiveCategory.invertedMorphisms :=
  CategoryTheory.Functor.q_isLocalization

/-- The analytic localization theorem is Mathlib's constructed quotient
localization for the Verdier morphism property. -/
theorem TraceAnalyticStableMotiveCategory.isLocalization_eq_q :
    TraceAnalyticStableMotiveCategory.isLocalization =
      CategoryTheory.Functor.q_isLocalization :=
  rfl

/-- Functors out of stable analytic motives are equivalent to additive homotopy
functors that invert the stable null morphisms. -/
def TraceAnalyticStableMotiveCategory.functorEquivalence
    (target : Type*) [CategoryTheory.Category target] :
    (TraceAnalyticStableMotiveCategory ⥤ target) ≌
      TraceAnalyticStableMotiveCategory.invertedMorphisms.FunctorsInverting target :=
  CategoryTheory.Localization.functorEquivalence
    TraceAnalyticStableMotiveCategory.quotientFunctor
    TraceAnalyticStableMotiveCategory.invertedMorphisms
    target

/-- Descend a functor that inverts the stable null morphisms to stable analytic motives. -/
def TraceAnalyticStableMotiveCategory.lift
    {target : Type*} [CategoryTheory.Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableMotiveCategory.invertedMorphisms.IsInvertedBy functor) :
    TraceAnalyticStableMotiveCategory ⥤ target :=
  CategoryTheory.Localization.lift
    functor
    inverts
    TraceAnalyticStableMotiveCategory.quotientFunctor

/-- The descended functor composed with the quotient recovers the original functor. -/
def TraceAnalyticStableMotiveCategory.liftFac
    {target : Type*} [CategoryTheory.Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableMotiveCategory.invertedMorphisms.IsInvertedBy functor) :
    TraceAnalyticStableMotiveCategory.quotientFunctor ⋙
      TraceAnalyticStableMotiveCategory.lift functor inverts ≅ functor :=
  CategoryTheory.Localization.fac
    functor
    inverts
    TraceAnalyticStableMotiveCategory.quotientFunctor

/-- The lift is Mathlib's localization lift specialized to the analytic quotient. -/
theorem TraceAnalyticStableMotiveCategory.lift_eq
    {target : Type*} [CategoryTheory.Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableMotiveCategory.invertedMorphisms.IsInvertedBy functor) :
    TraceAnalyticStableMotiveCategory.lift functor inverts =
      CategoryTheory.Localization.lift
        functor
        inverts
        TraceAnalyticStableMotiveCategory.quotientFunctor :=
  rfl

/-- The factorization is Mathlib's localization factorization specialized to the quotient. -/
theorem TraceAnalyticStableMotiveCategory.liftFac_eq
    {target : Type*} [CategoryTheory.Category target]
    (functor : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (inverts :
      TraceAnalyticStableMotiveCategory.invertedMorphisms.IsInvertedBy functor) :
    TraceAnalyticStableMotiveCategory.liftFac functor inverts =
      CategoryTheory.Localization.fac
        functor
        inverts
        TraceAnalyticStableMotiveCategory.quotientFunctor :=
  rfl

/-- A natural transformation between invertible functors descends across the quotient. -/
def TraceAnalyticStableMotiveCategory.liftNatTrans
    {target : Type*} [CategoryTheory.Category target]
    (first second : TraceAnalyticAdditiveHomotopyCategory ⥤ target)
    (firstLift secondLift : TraceAnalyticStableMotiveCategory ⥤ target)
    [CategoryTheory.Localization.Lifting
      TraceAnalyticStableMotiveCategory.quotientFunctor
      TraceAnalyticStableMotiveCategory.invertedMorphisms
      first
      firstLift]
    [CategoryTheory.Localization.Lifting
      TraceAnalyticStableMotiveCategory.quotientFunctor
      TraceAnalyticStableMotiveCategory.invertedMorphisms
      second
      secondLift]
    (transformation : first ⟶ second) :
    firstLift ⟶ secondLift :=
  CategoryTheory.Localization.liftNatTrans
    TraceAnalyticStableMotiveCategory.quotientFunctor
    TraceAnalyticStableMotiveCategory.invertedMorphisms
    first
    second
    firstLift
    secondLift
    transformation

end AnalyticMotives
end LFunctions
end Boundary
