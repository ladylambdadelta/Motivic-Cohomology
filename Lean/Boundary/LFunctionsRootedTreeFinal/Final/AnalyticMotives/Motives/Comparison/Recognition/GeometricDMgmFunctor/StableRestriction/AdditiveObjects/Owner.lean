import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.DMgmFunctor.StableRestriction.AdditiveObjects.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.Descent.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.Recognition.GeometricDMgmFunctor.HomotopyRestriction.AdditiveObjects.Owner

/-!
# Stable additive-object restriction of descended geometric recognition functors

This file restricts a descended geometric recognition functor to additive
finite trace families through the existing stable additive source functor.
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

variable (twistData :
  TraceAnalyticDMgmComparisonTarget.GeometricTateTwistData
    (composition := composition))

/-- The descended geometric recognition functor restricted to stable additive
finite trace families. -/
def TraceAnalyticMotiveRecognition.descendedGeometricAdditiveObjectRestrictionFunctor
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor) :
    TraceAnalyticAdditiveCategoryObject ⥤
      TraceAnalyticDMgmComparisonTarget.geometricMotives
        (composition := composition) twistData :=
  TraceAnalyticMotiveRecognition.stableAdditiveSourceFunctor ⋙
    TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor
      (composition := composition)
      twistData
      homotopyFunctor
      inverts

/-- The descended geometric additive restriction is stable additive source
followed by the descended geometric recognition functor. -/
theorem TraceAnalyticMotiveRecognition.descendedGeometricAdditiveObjectRestrictionFunctor_eq_comp
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor) :
    TraceAnalyticMotiveRecognition.descendedGeometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor
        inverts =
      TraceAnalyticMotiveRecognition.stableAdditiveSourceFunctor ⋙
        TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor
          (composition := composition)
          twistData
          homotopyFunctor
          inverts :=
  rfl

/-- Object formula for the descended geometric additive finite-family
restriction. -/
theorem TraceAnalyticMotiveRecognition.descendedGeometricAdditiveObjectRestrictionFunctor_obj
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (object : TraceAnalyticAdditiveCategoryObject) :
    (TraceAnalyticMotiveRecognition.descendedGeometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor
        inverts).obj object =
      (TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctor
        (composition := composition)
        twistData
        homotopyFunctor
        inverts).obj
        (TraceAnalyticMotiveRecognition.stableAdditiveSourceFunctor.obj
          object) :=
  rfl

/-- The descended stable geometric additive restriction compares objectwise
with the homotopy-level geometric additive restriction. -/
def TraceAnalyticMotiveRecognition.descendedGeometricAdditiveObjectRestrictionObjectIso
    (homotopyFunctor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        homotopyFunctor)
    (object : TraceAnalyticAdditiveCategoryObject) :
    (TraceAnalyticMotiveRecognition.descendedGeometricAdditiveObjectRestrictionFunctor
      (composition := composition)
      twistData
      homotopyFunctor
      inverts).obj object ≅
      (TraceAnalyticMotiveRecognition.geometricAdditiveObjectRestrictionFunctor
        (composition := composition)
        twistData
        homotopyFunctor).obj object :=
  TraceAnalyticMotiveRecognition.descendedGeometricDMgmFunctorObjectIso
    (composition := composition)
    twistData
    homotopyFunctor
    inverts
    (TraceAnalyticAdditiveHomotopyCategory.objectOf
      ((CochainComplex.singleFunctor TraceAnalyticAdditiveCategoryObject
        (0 : ℤ)).obj object))

end AnalyticMotives
end LFunctions
end Boundary
