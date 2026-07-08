import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Comparison.DMgmTarget.Geometric.Descent.Projections.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Stabilization.AdditiveEnvelope.Homotopy.LocalizationInput.Owner

/-!
# Localization-input projection formulas for geometric Boundary DMgm descent

This file specializes the geometric Boundary-DMgm descent projection formula
to stable maps attached to concrete analytic localization inputs.
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

/-- Geometric Boundary-DMgm descent projection formula for a localization-input
stable map. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor_localizationInput_stableMap_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (input : TraceLocalizationInput) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
      (composition := composition)
      twistData
      functor
      inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf input.stableMap) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        input.stableTarget).hom =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        input.stableSource).hom ≫
        functor.map input.stableMap :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor_mapOf_naturality
    (composition := composition)
    twistData
    functor
    inverts
    input.stableMap

/-- Geometric Boundary-DMgm descent projection formula for descent-channel
stable maps. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor_descentChannel_stableMap_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
      (composition := composition)
      twistData
      functor
      inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf
          (TraceLocalizationInput.descentChannel source target).stableMap) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        (TraceLocalizationInput.descentChannel source target).stableTarget).hom =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        (TraceLocalizationInput.descentChannel source target).stableSource).hom ≫
        functor.map
          (TraceLocalizationInput.descentChannel source target).stableMap :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor_localizationInput_stableMap_naturality
    (composition := composition)
    twistData
    functor
    inverts
    (TraceLocalizationInput.descentChannel source target)

/-- Geometric Boundary-DMgm descent projection formula for descent-refinement
stable maps. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor_descentRefinement_stableMap_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
      (composition := composition)
      twistData
      functor
      inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf
          (TraceLocalizationInput.descentRefinement source target).stableMap) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        (TraceLocalizationInput.descentRefinement source target).stableTarget).hom =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        (TraceLocalizationInput.descentRefinement source target).stableSource).hom ≫
        functor.map
          (TraceLocalizationInput.descentRefinement source target).stableMap :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor_localizationInput_stableMap_naturality
    (composition := composition)
    twistData
    functor
    inverts
    (TraceLocalizationInput.descentRefinement source target)

/-- Geometric Boundary-DMgm descent projection formula for descent-schedule
stable maps. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor_descentSchedule_stableMap_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
      (composition := composition)
      twistData
      functor
      inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf
          (TraceLocalizationInput.descentSchedule source target).stableMap) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        (TraceLocalizationInput.descentSchedule source target).stableTarget).hom =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        (TraceLocalizationInput.descentSchedule source target).stableSource).hom ≫
        functor.map
          (TraceLocalizationInput.descentSchedule source target).stableMap :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor_localizationInput_stableMap_naturality
    (composition := composition)
    twistData
    functor
    inverts
    (TraceLocalizationInput.descentSchedule source target)

/-- Geometric Boundary-DMgm descent projection formula for interval-Stokes
stable maps. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor_intervalStokes_stableMap_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
      (composition := composition)
      twistData
      functor
      inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf
          (TraceLocalizationInput.intervalStokes source target).stableMap) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        (TraceLocalizationInput.intervalStokes source target).stableTarget).hom =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        (TraceLocalizationInput.intervalStokes source target).stableSource).hom ≫
        functor.map
          (TraceLocalizationInput.intervalStokes source target).stableMap :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor_localizationInput_stableMap_naturality
    (composition := composition)
    twistData
    functor
    inverts
    (TraceLocalizationInput.intervalStokes source target)

/-- Geometric Boundary-DMgm descent projection formula for interval-Fubini
stable maps. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor_intervalFubini_stableMap_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
      (composition := composition)
      twistData
      functor
      inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf
          (TraceLocalizationInput.intervalFubini source target).stableMap) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        (TraceLocalizationInput.intervalFubini source target).stableTarget).hom =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        (TraceLocalizationInput.intervalFubini source target).stableSource).hom ≫
        functor.map
          (TraceLocalizationInput.intervalFubini source target).stableMap :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor_localizationInput_stableMap_naturality
    (composition := composition)
    twistData
    functor
    inverts
    (TraceLocalizationInput.intervalFubini source target)

/-- Geometric Boundary-DMgm descent projection formula for Tate-weight-drop
stable maps. -/
theorem TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor_tateWeightDrop_stableMap_naturality
    (functor :
      TraceAnalyticAdditiveHomotopyCategory ⥤
        TraceAnalyticDMgmComparisonTarget.geometricMotives
          (composition := composition) twistData)
    (inverts :
      TraceAnalyticStableHomotopyComparisonSource.invertedMorphisms.IsInvertedBy
        functor)
    (source target : QTraceExpression) :
    (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor
      (composition := composition)
      twistData
      functor
      inverts).map
        (TraceAnalyticStableHomotopyComparisonSource.mapOf
          (TraceLocalizationInput.tateWeightDrop source target).stableMap) ≫
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        (TraceLocalizationInput.tateWeightDrop source target).stableTarget).hom =
      (TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctorObjectIso
        (composition := composition)
        twistData
        functor
        inverts
        (TraceLocalizationInput.tateWeightDrop source target).stableSource).hom ≫
        functor.map
          (TraceLocalizationInput.tateWeightDrop source target).stableMap :=
  TraceAnalyticDMgmComparisonTarget.Geometric.descendInvertingFunctor_localizationInput_stableMap_naturality
    (composition := composition)
    twistData
    functor
    inverts
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
