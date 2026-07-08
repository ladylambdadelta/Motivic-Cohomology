import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.Owner

/-!
# Categorical shifts in the analytic Verdier quotient

This file exposes the Mathlib localization shift structure for the analytic
Verdier quotient.  The null subcategory is a genuine triangulated subcategory,
so its inverted morphisms are compatible with integer shifts, and the quotient
functor commutes with those shifts.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The analytic Verdier inverted morphisms are compatible with integer
shifts. -/
def TraceAnalyticStableNullSubcategory.invertedMorphisms_isCompatibleWithShift :
    TraceAnalyticStableNullSubcategory.invertedMorphisms.IsCompatibleWithShift
      ℤ :=
  { condition :=
      fun degree =>
        CategoryTheory.MorphismProperty.ext
          (TraceAnalyticStableNullSubcategory.invertedMorphisms.inverseImage
            (CategoryTheory.shiftFunctor
              TraceAnalyticAdditiveHomotopyCategory
              degree))
          TraceAnalyticStableNullSubcategory.invertedMorphisms
          (fun morphism =>
            Iff.intro
              (fun shifted =>
                TraceAnalyticStableNullSubcategory.W.unshift shifted)
              (fun base =>
                TraceAnalyticStableNullSubcategory.W.shift
                  base
                  degree)) }

/-- The stable analytic quotient functor commutes with integer shifts. -/
def TraceAnalyticStableMotiveCategory.quotientFunctorCommShift
    :
    TraceAnalyticStableMotiveCategory.quotientFunctor.CommShift ℤ :=
  CategoryTheory.MorphismProperty.commShift_Q

/-- The quotient-functor commutation isomorphism for integer shifts. -/
def TraceAnalyticStableMotiveCategory.quotientFunctorCommShiftIso
    (degree : ℤ) :
    CategoryTheory.shiftFunctor
          TraceAnalyticAdditiveHomotopyCategory
          degree ⋙
        TraceAnalyticStableMotiveCategory.quotientFunctor ≅
      TraceAnalyticStableMotiveCategory.quotientFunctor ⋙
        CategoryTheory.shiftFunctor
          TraceAnalyticStableMotiveCategory
          degree :=
  TraceAnalyticStableMotiveCategory.quotientFunctor.commShiftIso degree

/-- Stable analytic integer shifts are additive functors. -/
def TraceAnalyticStableMotiveCategory.shiftFunctorAdditive
    (degree : ℤ) :
    (CategoryTheory.shiftFunctor
      TraceAnalyticStableMotiveCategory
      degree).Additive :=
  CategoryTheory.Triangulated.Localization.instAdditiveShiftFunctorLocalization
    TraceAnalyticStableNullSubcategory.invertedMorphisms
    degree

/-- The quotient image of a shifted additive homotopy object is isomorphic to
the categorical shift of its quotient image. -/
def TraceAnalyticStableMotiveCategory.objectOfShiftIso
    (object : TraceAnalyticAdditiveHomotopyCategory)
    (degree : ℤ) :
    TraceAnalyticStableMotiveCategory.objectOf (object⟦degree⟧) ≅
      (TraceAnalyticStableMotiveCategory.objectOf object)⟦degree⟧ :=
  (TraceAnalyticStableMotiveCategory.quotientFunctorCommShiftIso
    degree).app object

/-- The object-level quotient shift isomorphism is the quotient functor's
commutation isomorphism at that object. -/
theorem TraceAnalyticStableMotiveCategory.objectOfShiftIso_eq
    (object : TraceAnalyticAdditiveHomotopyCategory)
    (degree : ℤ) :
    TraceAnalyticStableMotiveCategory.objectOfShiftIso object degree =
      (TraceAnalyticStableMotiveCategory.quotientFunctor.commShiftIso
        degree).app object :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
