import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.StableCategory.Core.Construction.Owner

/-!
# Homotopy category of the stable analytic motive infinity category

The concrete stable-infinity object in this lane is presented by the nerve of
the Verdier-localized analytic stable motive category.  This file exposes the
homotopy-category shadow of that presentation without introducing a parallel
abstract interface.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

namespace TraceAnalyticStableInfinityCategory

/-- The homotopy category presented by the stable analytic motive
infinity-category model. -/
abbrev HomotopyCategory :=
  StableInfinityOwner.PresentedCategory

/-- The homotopy category of the stable analytic motive infinity category is
the Verdier quotient category of analytic motives. -/
theorem homotopyCategory_eq_stableMotiveCategory :
    TraceAnalyticStableInfinityCategory.HomotopyCategory =
      TraceAnalyticStableMotiveCategory :=
  rfl

/-- The stable analytic motive quasicategory is the nerve of its homotopy
category presentation. -/
theorem presentedQuasicategory_eq_nerve_homotopyCategory :
    TraceAnalyticStableMotiveQuasicategory =
      CategoryTheory.nerve
        TraceAnalyticStableInfinityCategory.HomotopyCategory :=
  rfl

/-- The quotient functor into the homotopy category of the stable analytic
infinity category is the analytic Verdier quotient functor. -/
def homotopyQuotientFunctor :
    TraceAnalyticAdditiveHomotopyCategory ⥤
      TraceAnalyticStableInfinityCategory.HomotopyCategory :=
  TraceAnalyticStableMotiveQuasicategory.quotientFunctor

/-- The homotopy quotient functor is definitionally the stable analytic
Verdier quotient functor. -/
theorem homotopyQuotientFunctor_eq_stable :
    TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor =
      TraceAnalyticStableMotiveCategory.quotientFunctor :=
  rfl

/-- The homotopy category localization structure is the Verdier localization
structure already owned by the stable analytic motive category. -/
def homotopyCategoryLocalization :
    (TraceAnalyticStableInfinityCategory.homotopyQuotientFunctor)
      .IsLocalization
        TraceAnalyticStableNullSubcategory.invertedMorphisms :=
  TraceAnalyticStableMotiveQuasicategory.isLocalization

/-- The homotopy-category localization field is the stable presentation's
localization field. -/
theorem homotopyCategoryLocalization_eq_presented :
    TraceAnalyticStableInfinityCategory.homotopyCategoryLocalization =
      TraceAnalyticStableMotiveQuasicategory.isLocalization :=
  rfl

/-- The homotopy category carries the same shift structure as the stable
analytic Verdier quotient. -/
def homotopyCategoryShift :
    HasShift TraceAnalyticStableInfinityCategory.HomotopyCategory ℤ :=
  TraceAnalyticStableMotiveQuasicategory.hasShiftStructure

/-- The homotopy-category shift structure is the stable motive shift
structure. -/
theorem homotopyCategoryShift_eq_stable :
    TraceAnalyticStableInfinityCategory.homotopyCategoryShift =
      TraceAnalyticStableMotiveCategory.hasShiftStructure :=
  rfl

/-- The homotopy category carries the same pretriangulated structure as the
stable analytic Verdier quotient. -/
def homotopyCategoryPretriangulated :
    Pretriangulated TraceAnalyticStableInfinityCategory.HomotopyCategory :=
  TraceAnalyticStableMotiveQuasicategory.pretriangulatedStructure

/-- The homotopy-category pretriangulated structure is the stable motive
pretriangulated structure. -/
theorem homotopyCategoryPretriangulated_eq_stable :
    TraceAnalyticStableInfinityCategory.homotopyCategoryPretriangulated =
      TraceAnalyticStableMotiveCategory.pretriangulatedStructure :=
  rfl

/-- The homotopy category carries the same triangulated structure as the
stable analytic Verdier quotient. -/
def homotopyCategoryTriangulated :
    IsTriangulated TraceAnalyticStableInfinityCategory.HomotopyCategory :=
  TraceAnalyticStableMotiveQuasicategory.triangulatedStructure

/-- The homotopy-category triangulated structure is the stable motive
triangulated structure. -/
theorem homotopyCategoryTriangulated_eq_stable :
    TraceAnalyticStableInfinityCategory.homotopyCategoryTriangulated =
      TraceAnalyticStableMotiveCategory.triangulatedStructure :=
  rfl

/-- Distinguished triangles in the homotopy category of the stable analytic
infinity category. -/
def homotopyCategoryDistinguishedTriangles :
    Set
      (Pretriangulated.Triangle
        TraceAnalyticStableInfinityCategory.HomotopyCategory) :=
  TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles

/-- The homotopy-category distinguished triangles are the stable motive
distinguished triangles. -/
theorem homotopyCategoryDistinguishedTriangles_eq_stable :
    TraceAnalyticStableInfinityCategory
        .homotopyCategoryDistinguishedTriangles =
      TraceAnalyticStableMotiveCategory.distinguishedTriangles :=
  rfl

end TraceAnalyticStableInfinityCategory

end AnalyticMotives
end LFunctions
end Boundary
