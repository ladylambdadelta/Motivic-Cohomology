import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.DMgmFunctor.Descent.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.DMgmFunctor.HomotopyRestriction.AdditiveObjects.Owner

/-!
# Stable additive-object restriction of descended recognition functors

This file records the finite-family source functor obtained by sending an
additive trace family to a degree-zero complex, then to additive homotopy, then
to the stable comparison source.  A descended recognition functor restricted
along this source functor compares objectwise with the original homotopy-level
additive restriction.
-/

universe u

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

variable {k : Type u} [Field k] [PerfectField k]

variable (composition : Boundary.CanonicalCompositionData (k := k))
variable [FiniteCorrespondence.CanonicalExternalProductFamily (k := k)]
variable [Abelian (LinearPST (Boundary.canonicalCategory composition))]
variable [HasDerivedCategory (LinearPST (Boundary.canonicalCategory composition))]
variable [Abelian (canonicalA1NisLocalization composition)]
variable [HasDerivedCategory (canonicalA1NisLocalization composition)]
variable [(canonicalA1NisLocalizationFunctor composition).Additive]
variable [Limits.PreservesFiniteLimits (canonicalA1NisLocalizationFunctor composition)]
variable [Limits.PreservesFiniteColimits (canonicalA1NisLocalizationFunctor composition)]

/-- The stable comparison-source functor represented by additive finite trace
families concentrated in degree zero. -/
def TraceAnalyticMotiveRecognition.stableAdditiveSourceFunctor :
    TraceAnalyticAdditiveCategoryObject ⥤
      TraceAnalyticDMgmComparisonSource :=
  CochainComplex.singleFunctor TraceAnalyticAdditiveCategoryObject (0 : ℤ) ⋙
    TraceAnalyticAdditiveHomotopyCategory.quotientFunctor ⋙
      TraceAnalyticDMgmComparisonSource.quotientFunctor

/-- The stable additive source functor is the degree-zero complex embedding,
homotopy quotient, and stable comparison-source quotient. -/
theorem TraceAnalyticMotiveRecognition.stableAdditiveSourceFunctor_eq_comp :
    TraceAnalyticMotiveRecognition.stableAdditiveSourceFunctor =
      CochainComplex.singleFunctor TraceAnalyticAdditiveCategoryObject
          (0 : ℤ) ⋙
        TraceAnalyticAdditiveHomotopyCategory.quotientFunctor ⋙
          TraceAnalyticDMgmComparisonSource.quotientFunctor :=
  rfl

/-- Object formula for the stable additive source functor. -/
theorem TraceAnalyticMotiveRecognition.stableAdditiveSourceFunctor_obj
    (object : TraceAnalyticAdditiveCategoryObject) :
    TraceAnalyticMotiveRecognition.stableAdditiveSourceFunctor.obj object =
      TraceAnalyticDMgmComparisonSource.objectOf
        (TraceAnalyticAdditiveHomotopyCategory.objectOf
          ((CochainComplex.singleFunctor TraceAnalyticAdditiveCategoryObject
            (0 : ℤ)).obj object)) :=
  rfl

/-- Map formula for the stable additive source functor. -/
theorem TraceAnalyticMotiveRecognition.stableAdditiveSourceFunctor_map
    {source target : TraceAnalyticAdditiveCategoryObject}
    (hom : source ⟶ target) :
    TraceAnalyticMotiveRecognition.stableAdditiveSourceFunctor.map hom =
      TraceAnalyticDMgmComparisonSource.mapOf
        (TraceAnalyticAdditiveHomotopyCategory.mapOf
          ((CochainComplex.singleFunctor TraceAnalyticAdditiveCategoryObject
            (0 : ℤ)).map hom)) :=
  rfl

/-- The descended recognition functor restricted to stable additive finite
families. -/
def TraceAnalyticMotiveRecognition.descendedAdditiveObjectRestrictionFunctor
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor) :
    TraceAnalyticAdditiveCategoryObject ⥤
      TraceAnalyticDMgmComparisonTarget (composition := composition) :=
  TraceAnalyticMotiveRecognition.stableAdditiveSourceFunctor ⋙
    TraceAnalyticMotiveRecognition.descendedDMgmFunctor
      (composition := composition)
      homotopyFunctor
      inverts

/-- The descended additive restriction is stable additive source followed by
the descended recognition functor. -/
theorem TraceAnalyticMotiveRecognition.descendedAdditiveObjectRestrictionFunctor_eq_comp
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor) :
    TraceAnalyticMotiveRecognition.descendedAdditiveObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor
        inverts =
      TraceAnalyticMotiveRecognition.stableAdditiveSourceFunctor ⋙
        TraceAnalyticMotiveRecognition.descendedDMgmFunctor
          (composition := composition)
          homotopyFunctor
          inverts :=
  rfl

/-- Object formula for the descended additive finite-family restriction. -/
theorem TraceAnalyticMotiveRecognition.descendedAdditiveObjectRestrictionFunctor_obj
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (object : TraceAnalyticAdditiveCategoryObject) :
    (TraceAnalyticMotiveRecognition.descendedAdditiveObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor
        inverts).obj object =
      (TraceAnalyticMotiveRecognition.descendedDMgmFunctor
        (composition := composition)
        homotopyFunctor
        inverts).obj
        (TraceAnalyticMotiveRecognition.stableAdditiveSourceFunctor.obj
          object) :=
  rfl

/-- The descended stable additive restriction compares objectwise with the
homotopy-level additive restriction. -/
def TraceAnalyticMotiveRecognition.descendedAdditiveObjectRestrictionObjectIso
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (object : TraceAnalyticAdditiveCategoryObject) :
    (TraceAnalyticMotiveRecognition.descendedAdditiveObjectRestrictionFunctor
      (composition := composition)
      homotopyFunctor
      inverts).obj object ≅
      (TraceAnalyticMotiveRecognition.additiveObjectRestrictionFunctor
        (composition := composition)
        homotopyFunctor).obj object :=
  TraceAnalyticMotiveRecognition.descendedDMgmFunctorObjectIso
    (composition := composition)
    homotopyFunctor
    inverts
    (TraceAnalyticAdditiveHomotopyCategory.objectOf
      ((CochainComplex.singleFunctor TraceAnalyticAdditiveCategoryObject
        (0 : ℤ)).obj object))

end AnalyticMotives
end LFunctions
end Boundary
