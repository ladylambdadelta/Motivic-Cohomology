import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Descent.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.LocalizationInput.Owner

/-!
# Localization-input projection formulas for Boundary DMgm descent

This file specializes the Boundary-DMgm descent projection formula to the
stable maps attached to concrete analytic localization inputs.
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

/-- Boundary-DMgm descent projection formula for a localization-input stable map. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_localizationInput_stableMap_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (input : TraceLocalizationInput) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      functor
      inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf input.stableMap) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        input.stableTarget).hom =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        input.stableSource).hom ≫
        functor.map input.stableMap :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_mapOf_naturality
    (composition := composition)
    functor
    inverts
    input.stableMap

/-- Boundary-DMgm descent projection formula for descent-channel stable maps. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_descentChannel_stableMap_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      functor
      inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf
          (TraceLocalizationInput.descentChannel source target).stableMap) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        (TraceLocalizationInput.descentChannel source target).stableTarget).hom =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        (TraceLocalizationInput.descentChannel source target).stableSource).hom ≫
        functor.map
          (TraceLocalizationInput.descentChannel source target).stableMap :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_localizationInput_stableMap_naturality
    (composition := composition)
    functor
    inverts
    (TraceLocalizationInput.descentChannel source target)

/-- Boundary-DMgm descent projection formula for descent-refinement stable maps. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_descentRefinement_stableMap_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      functor
      inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf
          (TraceLocalizationInput.descentRefinement source target).stableMap) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        (TraceLocalizationInput.descentRefinement source target).stableTarget).hom =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        (TraceLocalizationInput.descentRefinement source target).stableSource).hom ≫
        functor.map
          (TraceLocalizationInput.descentRefinement source target).stableMap :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_localizationInput_stableMap_naturality
    (composition := composition)
    functor
    inverts
    (TraceLocalizationInput.descentRefinement source target)

/-- Boundary-DMgm descent projection formula for descent-schedule stable maps. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_descentSchedule_stableMap_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      functor
      inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf
          (TraceLocalizationInput.descentSchedule source target).stableMap) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        (TraceLocalizationInput.descentSchedule source target).stableTarget).hom =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        (TraceLocalizationInput.descentSchedule source target).stableSource).hom ≫
        functor.map
          (TraceLocalizationInput.descentSchedule source target).stableMap :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_localizationInput_stableMap_naturality
    (composition := composition)
    functor
    inverts
    (TraceLocalizationInput.descentSchedule source target)

/-- Boundary-DMgm descent projection formula for interval-Stokes stable maps. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_intervalStokes_stableMap_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      functor
      inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf
          (TraceLocalizationInput.intervalStokes source target).stableMap) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        (TraceLocalizationInput.intervalStokes source target).stableTarget).hom =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        (TraceLocalizationInput.intervalStokes source target).stableSource).hom ≫
        functor.map
          (TraceLocalizationInput.intervalStokes source target).stableMap :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_localizationInput_stableMap_naturality
    (composition := composition)
    functor
    inverts
    (TraceLocalizationInput.intervalStokes source target)

/-- Boundary-DMgm descent projection formula for interval-Fubini stable maps. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_intervalFubini_stableMap_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      functor
      inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf
          (TraceLocalizationInput.intervalFubini source target).stableMap) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        (TraceLocalizationInput.intervalFubini source target).stableTarget).hom =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        (TraceLocalizationInput.intervalFubini source target).stableSource).hom ≫
        functor.map
          (TraceLocalizationInput.intervalFubini source target).stableMap :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_localizationInput_stableMap_naturality
    (composition := composition)
    functor
    inverts
    (TraceLocalizationInput.intervalFubini source target)

/-- Boundary-DMgm descent projection formula for Tate-weight-drop stable maps. -/
theorem TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_tateWeightDrop_stableMap_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget (composition := composition))
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor
      (composition := composition)
      functor
      inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf
          (TraceLocalizationInput.tateWeightDrop source target).stableMap) ≫
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        (TraceLocalizationInput.tateWeightDrop source target).stableTarget).hom =
      (TraceAnalyticDMgmComparisonTarget.descendInvertingFunctorObjectIso
        (composition := composition)
        functor
        inverts
        (TraceLocalizationInput.tateWeightDrop source target).stableSource).hom ≫
        functor.map
          (TraceLocalizationInput.tateWeightDrop source target).stableMap :=
  TraceAnalyticDMgmComparisonTarget.descendInvertingFunctor_localizationInput_stableMap_naturality
    (composition := composition)
    functor
    inverts
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
