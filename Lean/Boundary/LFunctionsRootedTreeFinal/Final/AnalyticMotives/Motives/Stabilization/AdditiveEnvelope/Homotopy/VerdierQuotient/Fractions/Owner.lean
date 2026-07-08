import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.Owner

/-!
# Fraction calculus for the analytic Verdier quotient

The analytic stable motive category is the Verdier localization of the
additive analytic homotopy category at the morphisms whose cones lie in the
stable null subcategory.  Mathlib proves the Gabriel-Zisman left-fraction
calculus for this Verdier class from the triangulated-subcategory
construction; this file exposes that proved calculus under analytic names.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The analytic Verdier inverted class contains identities. -/
def TraceAnalyticStableNullSubcategory.invertedMorphismsContainsIdentities :
    TraceAnalyticStableNullSubcategory.invertedMorphisms.ContainsIdentities :=
  inferInstance

/-- The analytic Verdier inverted class is multiplicative. -/
def TraceAnalyticStableNullSubcategory.invertedMorphismsMultiplicative :
    TraceAnalyticStableNullSubcategory.invertedMorphisms.IsMultiplicative :=
  inferInstance

/-- The analytic Verdier inverted class has Gabriel-Zisman left fractions. -/
def TraceAnalyticStableNullSubcategory.invertedMorphismsLeftFractions :
    CategoryTheory.MorphismProperty.HasLeftCalculusOfFractions
      TraceAnalyticStableNullSubcategory.invertedMorphisms :=
  inferInstance

/-- The analytic Verdier inverted class is compatible with the triangulation. -/
def TraceAnalyticStableNullSubcategory.invertedMorphismsCompatibleWithTriangulation :
    CategoryTheory.MorphismProperty.IsCompatibleWithTriangulation
      TraceAnalyticStableNullSubcategory.invertedMorphisms :=
  inferInstance

/-- Every stable analytic morphism between quotient-represented additive
homotopy objects is represented by a Verdier left fraction. -/
theorem TraceAnalyticStableMotiveCategory.exists_leftFraction
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
            TraceAnalyticStableNullSubcategory.invertedMorphisms) :=
  CategoryTheory.Localization.exists_leftFraction
    TraceAnalyticStableMotiveCategory.quotientFunctor
    TraceAnalyticStableNullSubcategory.invertedMorphisms
    hom

/-- A stable analytic left fraction becomes its numerator after postcomposing
with the localized denominator. -/
theorem TraceAnalyticStableMotiveCategory.leftFraction_map_comp_denominator
    {source target : TraceAnalyticAdditiveHomotopyCategory}
    (fraction :
      TraceAnalyticStableNullSubcategory.invertedMorphisms.LeftFraction
        source
        target) :
    fraction.map
        TraceAnalyticStableMotiveCategory.quotientFunctor
        (CategoryTheory.Localization.inverts
          TraceAnalyticStableMotiveCategory.quotientFunctor
          TraceAnalyticStableNullSubcategory.invertedMorphisms) ≫
      TraceAnalyticStableMotiveCategory.quotientFunctor.map fraction.s =
        TraceAnalyticStableMotiveCategory.quotientFunctor.map fraction.f :=
  CategoryTheory.MorphismProperty.LeftFraction.map_comp_map_s
    fraction
    TraceAnalyticStableMotiveCategory.quotientFunctor
    (CategoryTheory.Localization.inverts
      TraceAnalyticStableMotiveCategory.quotientFunctor
      TraceAnalyticStableNullSubcategory.invertedMorphisms)

end AnalyticMotives
end LFunctions
end Boundary
