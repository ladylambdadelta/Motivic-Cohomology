import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Cancellation.Owner

/-!
# By-kind unstable localization cancellation

This file exposes cancellation laws for the six named unstable analytic-motive
localization isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel unstable hom followed by inverse is identity. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentChannel source target).sourceObject :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv
    source
    target

/-- Descent-channel unstable inverse followed by hom is identity. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentChannel source target).targetObject :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom
    source
    target

/-- Descent-channel unstable hom followed by inverse is categorical identity. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom ≫
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv =
      (𝟙 (TraceLocalizationInput.descentChannel source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentChannel source target).localizedSourceObject
          (TraceLocalizationInput.descentChannel source target).localizedSourceObject) :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- Descent-channel unstable inverse followed by hom is categorical identity. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv ≫
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom =
      (𝟙 (TraceLocalizationInput.descentChannel source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentChannel source target).localizedTargetObject
          (TraceLocalizationInput.descentChannel source target).localizedTargetObject) :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- Descent-refinement unstable hom followed by inverse is identity. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentRefinement source target).sourceObject :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv
    source
    target

/-- Descent-refinement unstable inverse followed by hom is identity. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentRefinement source target).targetObject :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom
    source
    target

/-- Descent-refinement unstable hom followed by inverse is categorical identity. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom ≫
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv =
      (𝟙 (TraceLocalizationInput.descentRefinement source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentRefinement source target).localizedSourceObject
          (TraceLocalizationInput.descentRefinement source target).localizedSourceObject) :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- Descent-refinement unstable inverse followed by hom is categorical identity. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv ≫
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom =
      (𝟙 (TraceLocalizationInput.descentRefinement source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentRefinement source target).localizedTargetObject
          (TraceLocalizationInput.descentRefinement source target).localizedTargetObject) :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- Descent-schedule unstable hom followed by inverse is identity. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentSchedule source target).sourceObject :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv
    source
    target

/-- Descent-schedule unstable inverse followed by hom is identity. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentSchedule source target).targetObject :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom
    source
    target

/-- Descent-schedule unstable hom followed by inverse is categorical identity. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom ≫
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv =
      (𝟙 (TraceLocalizationInput.descentSchedule source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentSchedule source target).localizedSourceObject
          (TraceLocalizationInput.descentSchedule source target).localizedSourceObject) :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- Descent-schedule unstable inverse followed by hom is categorical identity. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv ≫
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom =
      (𝟙 (TraceLocalizationInput.descentSchedule source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentSchedule source target).localizedTargetObject
          (TraceLocalizationInput.descentSchedule source target).localizedTargetObject) :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- Interval-Stokes unstable hom followed by inverse is identity. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalStokes source target).sourceObject :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv
    source
    target

/-- Interval-Stokes unstable inverse followed by hom is identity. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalStokes source target).targetObject :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom
    source
    target

/-- Interval-Stokes unstable hom followed by inverse is categorical identity. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom ≫
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv =
      (𝟙 (TraceLocalizationInput.intervalStokes source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.intervalStokes source target).localizedSourceObject
          (TraceLocalizationInput.intervalStokes source target).localizedSourceObject) :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- Interval-Stokes unstable inverse followed by hom is categorical identity. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv ≫
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom =
      (𝟙 (TraceLocalizationInput.intervalStokes source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.intervalStokes source target).localizedTargetObject
          (TraceLocalizationInput.intervalStokes source target).localizedTargetObject) :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- Interval-Fubini unstable hom followed by inverse is identity. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalFubini source target).sourceObject :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv
    source
    target

/-- Interval-Fubini unstable inverse followed by hom is identity. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalFubini source target).targetObject :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom
    source
    target

/-- Interval-Fubini unstable hom followed by inverse is categorical identity. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom ≫
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv =
      (𝟙 (TraceLocalizationInput.intervalFubini source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.intervalFubini source target).localizedSourceObject
          (TraceLocalizationInput.intervalFubini source target).localizedSourceObject) :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- Interval-Fubini unstable inverse followed by hom is categorical identity. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv ≫
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom =
      (𝟙 (TraceLocalizationInput.intervalFubini source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.intervalFubini source target).localizedTargetObject
          (TraceLocalizationInput.intervalFubini source target).localizedTargetObject) :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- Tate-weight-drop unstable hom followed by inverse is identity. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv
    source
    target

/-- Tate-weight-drop unstable inverse followed by hom is identity. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.tateWeightDrop source target).targetObject :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom
    source
    target

/-- Tate-weight-drop unstable hom followed by inverse is categorical identity. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom ≫
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv =
      (𝟙 (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject
          (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject) :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- Tate-weight-drop unstable inverse followed by hom is categorical identity. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv ≫
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom =
      (𝟙 (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject
          (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject) :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_eq_categoryIdentity
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
