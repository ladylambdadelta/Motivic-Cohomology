import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Localization.SummaryRepresentatives.Owner

/-!
# Motive-root localization cancellation laws

This file exposes the two-sided cancellation laws for the six calculus
localization isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Channel descent hom followed by inverse is identity in the motive root. -/
theorem TraceAnalyticMotive.descentChannelIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceCalculusLocalization.descentChannelIso source target).hom
        (TraceCalculusLocalization.descentChannelIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentChannel source target).sourceObject :=
  TraceCalculusLocalization.descentChannelIso_hom_comp_inv
    source
    target

/-- Channel descent inverse followed by hom is identity in the motive root. -/
theorem TraceAnalyticMotive.descentChannelIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceCalculusLocalization.descentChannelIso source target).inv
        (TraceCalculusLocalization.descentChannelIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentChannel source target).targetObject :=
  TraceCalculusLocalization.descentChannelIso_inv_comp_hom
    source
    target

/-- Channel descent hom followed by inverse is categorical identity in the motive root. -/
theorem TraceAnalyticMotive.descentChannelIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.descentChannelIso source target).hom ≫
        (TraceCalculusLocalization.descentChannelIso source target).inv =
      (𝟙 (TraceLocalizationInput.descentChannel source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentChannel source target).localizedSourceObject
          (TraceLocalizationInput.descentChannel source target).localizedSourceObject) :=
  TraceCalculusLocalization.descentChannelIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- Channel descent inverse followed by hom is categorical identity in the motive root. -/
theorem TraceAnalyticMotive.descentChannelIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.descentChannelIso source target).inv ≫
        (TraceCalculusLocalization.descentChannelIso source target).hom =
      (𝟙 (TraceLocalizationInput.descentChannel source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentChannel source target).localizedTargetObject
          (TraceLocalizationInput.descentChannel source target).localizedTargetObject) :=
  TraceCalculusLocalization.descentChannelIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- Refinement descent hom followed by inverse is identity in the motive root. -/
theorem TraceAnalyticMotive.descentRefinementIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceCalculusLocalization.descentRefinementIso source target).hom
        (TraceCalculusLocalization.descentRefinementIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentRefinement source target).sourceObject :=
  TraceCalculusLocalization.descentRefinementIso_hom_comp_inv
    source
    target

/-- Refinement descent inverse followed by hom is identity in the motive root. -/
theorem TraceAnalyticMotive.descentRefinementIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceCalculusLocalization.descentRefinementIso source target).inv
        (TraceCalculusLocalization.descentRefinementIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentRefinement source target).targetObject :=
  TraceCalculusLocalization.descentRefinementIso_inv_comp_hom
    source
    target

/-- Refinement descent hom followed by inverse is categorical identity in the motive root. -/
theorem TraceAnalyticMotive.descentRefinementIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.descentRefinementIso source target).hom ≫
        (TraceCalculusLocalization.descentRefinementIso source target).inv =
      (𝟙 (TraceLocalizationInput.descentRefinement source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentRefinement source target).localizedSourceObject
          (TraceLocalizationInput.descentRefinement source target).localizedSourceObject) :=
  TraceCalculusLocalization.descentRefinementIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- Refinement descent inverse followed by hom is categorical identity in the motive root. -/
theorem TraceAnalyticMotive.descentRefinementIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.descentRefinementIso source target).inv ≫
        (TraceCalculusLocalization.descentRefinementIso source target).hom =
      (𝟙 (TraceLocalizationInput.descentRefinement source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentRefinement source target).localizedTargetObject
          (TraceLocalizationInput.descentRefinement source target).localizedTargetObject) :=
  TraceCalculusLocalization.descentRefinementIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- Schedule descent hom followed by inverse is identity in the motive root. -/
theorem TraceAnalyticMotive.descentScheduleIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceCalculusLocalization.descentScheduleIso source target).hom
        (TraceCalculusLocalization.descentScheduleIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentSchedule source target).sourceObject :=
  TraceCalculusLocalization.descentScheduleIso_hom_comp_inv
    source
    target

/-- Schedule descent inverse followed by hom is identity in the motive root. -/
theorem TraceAnalyticMotive.descentScheduleIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceCalculusLocalization.descentScheduleIso source target).inv
        (TraceCalculusLocalization.descentScheduleIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentSchedule source target).targetObject :=
  TraceCalculusLocalization.descentScheduleIso_inv_comp_hom
    source
    target

/-- Schedule descent hom followed by inverse is categorical identity in the motive root. -/
theorem TraceAnalyticMotive.descentScheduleIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.descentScheduleIso source target).hom ≫
        (TraceCalculusLocalization.descentScheduleIso source target).inv =
      (𝟙 (TraceLocalizationInput.descentSchedule source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentSchedule source target).localizedSourceObject
          (TraceLocalizationInput.descentSchedule source target).localizedSourceObject) :=
  TraceCalculusLocalization.descentScheduleIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- Schedule descent inverse followed by hom is categorical identity in the motive root. -/
theorem TraceAnalyticMotive.descentScheduleIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.descentScheduleIso source target).inv ≫
        (TraceCalculusLocalization.descentScheduleIso source target).hom =
      (𝟙 (TraceLocalizationInput.descentSchedule source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentSchedule source target).localizedTargetObject
          (TraceLocalizationInput.descentSchedule source target).localizedTargetObject) :=
  TraceCalculusLocalization.descentScheduleIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- Interval Stokes hom followed by inverse is identity in the motive root. -/
theorem TraceAnalyticMotive.intervalStokesIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceCalculusLocalization.intervalStokesIso source target).hom
        (TraceCalculusLocalization.intervalStokesIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalStokes source target).sourceObject :=
  TraceCalculusLocalization.intervalStokesIso_hom_comp_inv
    source
    target

/-- Interval Stokes inverse followed by hom is identity in the motive root. -/
theorem TraceAnalyticMotive.intervalStokesIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceCalculusLocalization.intervalStokesIso source target).inv
        (TraceCalculusLocalization.intervalStokesIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalStokes source target).targetObject :=
  TraceCalculusLocalization.intervalStokesIso_inv_comp_hom
    source
    target

/-- Interval Stokes hom followed by inverse is categorical identity in the motive root. -/
theorem TraceAnalyticMotive.intervalStokesIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.intervalStokesIso source target).hom ≫
        (TraceCalculusLocalization.intervalStokesIso source target).inv =
      (𝟙 (TraceLocalizationInput.intervalStokes source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.intervalStokes source target).localizedSourceObject
          (TraceLocalizationInput.intervalStokes source target).localizedSourceObject) :=
  TraceCalculusLocalization.intervalStokesIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- Interval Stokes inverse followed by hom is categorical identity in the motive root. -/
theorem TraceAnalyticMotive.intervalStokesIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.intervalStokesIso source target).inv ≫
        (TraceCalculusLocalization.intervalStokesIso source target).hom =
      (𝟙 (TraceLocalizationInput.intervalStokes source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.intervalStokes source target).localizedTargetObject
          (TraceLocalizationInput.intervalStokes source target).localizedTargetObject) :=
  TraceCalculusLocalization.intervalStokesIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- Interval Fubini hom followed by inverse is identity in the motive root. -/
theorem TraceAnalyticMotive.intervalFubiniIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceCalculusLocalization.intervalFubiniIso source target).hom
        (TraceCalculusLocalization.intervalFubiniIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalFubini source target).sourceObject :=
  TraceCalculusLocalization.intervalFubiniIso_hom_comp_inv
    source
    target

/-- Interval Fubini inverse followed by hom is identity in the motive root. -/
theorem TraceAnalyticMotive.intervalFubiniIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceCalculusLocalization.intervalFubiniIso source target).inv
        (TraceCalculusLocalization.intervalFubiniIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalFubini source target).targetObject :=
  TraceCalculusLocalization.intervalFubiniIso_inv_comp_hom
    source
    target

/-- Interval Fubini hom followed by inverse is categorical identity in the motive root. -/
theorem TraceAnalyticMotive.intervalFubiniIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.intervalFubiniIso source target).hom ≫
        (TraceCalculusLocalization.intervalFubiniIso source target).inv =
      (𝟙 (TraceLocalizationInput.intervalFubini source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.intervalFubini source target).localizedSourceObject
          (TraceLocalizationInput.intervalFubini source target).localizedSourceObject) :=
  TraceCalculusLocalization.intervalFubiniIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- Interval Fubini inverse followed by hom is categorical identity in the motive root. -/
theorem TraceAnalyticMotive.intervalFubiniIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.intervalFubiniIso source target).inv ≫
        (TraceCalculusLocalization.intervalFubiniIso source target).hom =
      (𝟙 (TraceLocalizationInput.intervalFubini source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.intervalFubini source target).localizedTargetObject
          (TraceLocalizationInput.intervalFubini source target).localizedTargetObject) :=
  TraceCalculusLocalization.intervalFubiniIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- Tate weight-drop hom followed by inverse is identity in the motive root. -/
theorem TraceAnalyticMotive.tateWeightDropIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceCalculusLocalization.tateWeightDropIso source target).hom
        (TraceCalculusLocalization.tateWeightDropIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject :=
  TraceCalculusLocalization.tateWeightDropIso_hom_comp_inv
    source
    target

/-- Tate weight-drop inverse followed by hom is identity in the motive root. -/
theorem TraceAnalyticMotive.tateWeightDropIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceCalculusLocalization.tateWeightDropIso source target).inv
        (TraceCalculusLocalization.tateWeightDropIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.tateWeightDrop source target).targetObject :=
  TraceCalculusLocalization.tateWeightDropIso_inv_comp_hom
    source
    target

/-- Tate weight-drop hom followed by inverse is categorical identity in the motive root. -/
theorem TraceAnalyticMotive.tateWeightDropIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.tateWeightDropIso source target).hom ≫
        (TraceCalculusLocalization.tateWeightDropIso source target).inv =
      (𝟙 (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject
          (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject) :=
  TraceCalculusLocalization.tateWeightDropIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- Tate weight-drop inverse followed by hom is categorical identity in the motive root. -/
theorem TraceAnalyticMotive.tateWeightDropIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.tateWeightDropIso source target).inv ≫
        (TraceCalculusLocalization.tateWeightDropIso source target).hom =
      (𝟙 (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject
          (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject) :=
  TraceCalculusLocalization.tateWeightDropIso_inv_comp_hom_eq_categoryIdentity
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
