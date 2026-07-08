import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Infinity.Quasicategory.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.VerdierQuotient.UniversalProperty.Owner

/-!
# Stable presentation of analytic motives

This file records the exact stable presentation currently constructed in the
analytic motives lane.  The infinity-categorical object is the nerve of the
Verdier-localized analytic motive category, and the stable structure visible in
this checkout is the localization, shift, triangulated, and distinguished
triangle structure on that Verdier quotient.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The ordinary category presented by the stable analytic motive
quasicategory. -/
abbrev TraceAnalyticStableMotiveQuasicategory.presentedCategory :=
  TraceAnalyticStableMotiveCategory

/-- The stable analytic motive quasicategory is the nerve of its presented
Verdier-localized category. -/
theorem TraceAnalyticStableMotiveQuasicategory_eq_nerve_presentedCategory :
    TraceAnalyticStableMotiveQuasicategory =
      CategoryTheory.nerve
        TraceAnalyticStableMotiveQuasicategory.presentedCategory :=
  rfl

/-- The quotient functor whose nerve presents stable analytic motives. -/
def TraceAnalyticStableMotiveQuasicategory.quotientFunctor :
    TraceAnalyticAdditiveHomotopyCategory ⥤
      TraceAnalyticStableMotiveQuasicategory.presentedCategory :=
  TraceAnalyticStableMotiveCategory.quotientFunctor

/-- The presented quotient functor is the Verdier quotient functor. -/
theorem TraceAnalyticStableMotiveQuasicategory.quotientFunctor_eq_stable :
    TraceAnalyticStableMotiveQuasicategory.quotientFunctor =
      TraceAnalyticStableMotiveCategory.quotientFunctor :=
  rfl

/-- The morphism property inverted by the stable presentation. -/
def TraceAnalyticStableMotiveQuasicategory.invertedMorphisms :
    MorphismProperty TraceAnalyticAdditiveHomotopyCategory :=
  TraceAnalyticStableMotiveCategory.invertedMorphisms

/-- The stable-presentation inverted morphisms are the Verdier quotient
inverted morphisms. -/
theorem TraceAnalyticStableMotiveQuasicategory.invertedMorphisms_eq_stable :
    TraceAnalyticStableMotiveQuasicategory.invertedMorphisms =
      TraceAnalyticStableMotiveCategory.invertedMorphisms :=
  rfl

/-- The presented quotient functor is the localization at the stable null
morphisms. -/
def TraceAnalyticStableMotiveQuasicategory.isLocalization :
    TraceAnalyticStableMotiveQuasicategory.quotientFunctor.IsLocalization
      TraceAnalyticStableMotiveQuasicategory.invertedMorphisms :=
  TraceAnalyticStableMotiveCategory.isLocalization

/-- The stable-presentation localization structure is the Verdier quotient
localization structure. -/
theorem TraceAnalyticStableMotiveQuasicategory.isLocalization_eq_stable :
    TraceAnalyticStableMotiveQuasicategory.isLocalization =
      TraceAnalyticStableMotiveCategory.isLocalization :=
  rfl

/-- The presented category has the Verdier-localized integer shift structure. -/
def TraceAnalyticStableMotiveQuasicategory.hasShiftStructure :
    HasShift TraceAnalyticStableMotiveQuasicategory.presentedCategory ℤ :=
  TraceAnalyticStableMotiveCategory.hasShiftStructure

/-- The stable-presentation shift structure is the stable motive shift
structure. -/
theorem TraceAnalyticStableMotiveQuasicategory.hasShiftStructure_eq_stable :
    TraceAnalyticStableMotiveQuasicategory.hasShiftStructure =
      TraceAnalyticStableMotiveCategory.hasShiftStructure :=
  rfl

/-- The presented category has the Verdier-localized pretriangulated
structure. -/
def TraceAnalyticStableMotiveQuasicategory.pretriangulatedStructure :
    Pretriangulated TraceAnalyticStableMotiveQuasicategory.presentedCategory :=
  TraceAnalyticStableMotiveCategory.pretriangulatedStructure

/-- The stable-presentation pretriangulated structure is the stable motive
pretriangulated structure. -/
theorem TraceAnalyticStableMotiveQuasicategory.pretriangulatedStructure_eq_stable :
    TraceAnalyticStableMotiveQuasicategory.pretriangulatedStructure =
      TraceAnalyticStableMotiveCategory.pretriangulatedStructure :=
  rfl

/-- The presented category has the Verdier-localized triangulated structure. -/
def TraceAnalyticStableMotiveQuasicategory.triangulatedStructure :
    IsTriangulated TraceAnalyticStableMotiveQuasicategory.presentedCategory :=
  TraceAnalyticStableMotiveCategory.triangulatedStructure

/-- The stable-presentation triangulated structure is the stable motive
triangulated structure. -/
theorem TraceAnalyticStableMotiveQuasicategory.triangulatedStructure_eq_stable :
    TraceAnalyticStableMotiveQuasicategory.triangulatedStructure =
      TraceAnalyticStableMotiveCategory.triangulatedStructure :=
  rfl

/-- Distinguished triangles in the category presented by the stable analytic
motive quasicategory. -/
def TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles :
    Set
      (Pretriangulated.Triangle
        TraceAnalyticStableMotiveQuasicategory.presentedCategory) :=
  TraceAnalyticStableMotiveCategory.distinguishedTriangles

/-- The stable-presentation distinguished triangles are the stable motive
distinguished triangles. -/
theorem TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles_eq_stable :
    TraceAnalyticStableMotiveQuasicategory.distinguishedTriangles =
      TraceAnalyticStableMotiveCategory.distinguishedTriangles :=
  rfl

/-- Functors out of the presented stable category are exactly functors out of
the additive homotopy category that invert stable null morphisms. -/
def TraceAnalyticStableMotiveQuasicategory.functorEquivalence
    (target : Type*) [Category target] :
    (TraceAnalyticStableMotiveQuasicategory.presentedCategory ⥤ target) ≌
      TraceAnalyticStableMotiveQuasicategory.invertedMorphisms.FunctorsInverting
        target :=
  TraceAnalyticStableMotiveCategory.functorEquivalence target

/-- The stable-presentation functor equivalence is the Verdier quotient
universal property. -/
theorem TraceAnalyticStableMotiveQuasicategory.functorEquivalence_eq_stable
    (target : Type*) [Category target] :
    TraceAnalyticStableMotiveQuasicategory.functorEquivalence target =
      TraceAnalyticStableMotiveCategory.functorEquivalence target :=
  rfl

end AnalyticMotives
end LFunctions
end Boundary
