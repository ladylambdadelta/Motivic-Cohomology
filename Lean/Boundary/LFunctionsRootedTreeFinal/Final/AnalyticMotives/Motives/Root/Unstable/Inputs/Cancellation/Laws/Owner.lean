import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Cancellation.Owner

/-!
# Motive-root all-kind unstable cancellation laws
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- By-kind descent-channel unstable hom followed by inverse is identity. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentChannel source target).sourceObject :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_comp_inv
    source
    target

/-- By-kind descent-channel unstable inverse followed by hom is identity. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentChannel source target).targetObject :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_comp_hom
    source
    target

/-- By-kind descent-channel unstable hom followed by inverse is categorical identity. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom ≫
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv =
      (𝟙 (TraceLocalizationInput.descentChannel source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentChannel source target).localizedSourceObject
          (TraceLocalizationInput.descentChannel source target).localizedSourceObject) :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- By-kind descent-channel unstable inverse followed by hom is categorical identity. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv ≫
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom =
      (𝟙 (TraceLocalizationInput.descentChannel source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentChannel source target).localizedTargetObject
          (TraceLocalizationInput.descentChannel source target).localizedTargetObject) :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- By-kind descent-refinement unstable hom followed by inverse is identity. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentRefinement source target).sourceObject :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_comp_inv
    source
    target

/-- By-kind descent-refinement unstable inverse followed by hom is identity. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentRefinement source target).targetObject :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_comp_hom
    source
    target

/-- By-kind descent-refinement unstable hom followed by inverse is categorical identity. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom ≫
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv =
      (𝟙 (TraceLocalizationInput.descentRefinement source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentRefinement source target).localizedSourceObject
          (TraceLocalizationInput.descentRefinement source target).localizedSourceObject) :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- By-kind descent-refinement unstable inverse followed by hom is categorical identity. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv ≫
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom =
      (𝟙 (TraceLocalizationInput.descentRefinement source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentRefinement source target).localizedTargetObject
          (TraceLocalizationInput.descentRefinement source target).localizedTargetObject) :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- By-kind descent-schedule unstable hom followed by inverse is identity. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentSchedule source target).sourceObject :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_comp_inv
    source
    target

/-- By-kind descent-schedule unstable inverse followed by hom is identity. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentSchedule source target).targetObject :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_comp_hom
    source
    target

/-- By-kind descent-schedule unstable hom followed by inverse is categorical identity. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom ≫
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv =
      (𝟙 (TraceLocalizationInput.descentSchedule source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentSchedule source target).localizedSourceObject
          (TraceLocalizationInput.descentSchedule source target).localizedSourceObject) :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- By-kind descent-schedule unstable inverse followed by hom is categorical identity. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv ≫
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom =
      (𝟙 (TraceLocalizationInput.descentSchedule source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentSchedule source target).localizedTargetObject
          (TraceLocalizationInput.descentSchedule source target).localizedTargetObject) :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- By-kind interval-Stokes unstable hom followed by inverse is identity. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalStokes source target).sourceObject :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_comp_inv
    source
    target

/-- By-kind interval-Stokes unstable inverse followed by hom is identity. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalStokes source target).targetObject :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_comp_hom
    source
    target

/-- By-kind interval-Stokes unstable hom followed by inverse is categorical identity. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom ≫
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv =
      (𝟙 (TraceLocalizationInput.intervalStokes source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.intervalStokes source target).localizedSourceObject
          (TraceLocalizationInput.intervalStokes source target).localizedSourceObject) :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- By-kind interval-Stokes unstable inverse followed by hom is categorical identity. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv ≫
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom =
      (𝟙 (TraceLocalizationInput.intervalStokes source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.intervalStokes source target).localizedTargetObject
          (TraceLocalizationInput.intervalStokes source target).localizedTargetObject) :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- By-kind interval-Fubini unstable hom followed by inverse is identity. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalFubini source target).sourceObject :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_comp_inv
    source
    target

/-- By-kind interval-Fubini unstable inverse followed by hom is identity. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalFubini source target).targetObject :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_comp_hom
    source
    target

/-- By-kind interval-Fubini unstable hom followed by inverse is categorical identity. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom ≫
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv =
      (𝟙 (TraceLocalizationInput.intervalFubini source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.intervalFubini source target).localizedSourceObject
          (TraceLocalizationInput.intervalFubini source target).localizedSourceObject) :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- By-kind interval-Fubini unstable inverse followed by hom is categorical identity. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv ≫
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom =
      (𝟙 (TraceLocalizationInput.intervalFubini source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.intervalFubini source target).localizedTargetObject
          (TraceLocalizationInput.intervalFubini source target).localizedTargetObject) :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- By-kind Tate-weight-drop unstable hom followed by inverse is identity. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_comp_inv
    source
    target

/-- By-kind Tate-weight-drop unstable inverse followed by hom is identity. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.tateWeightDrop source target).targetObject :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_comp_hom
    source
    target

/-- By-kind Tate-weight-drop unstable hom followed by inverse is categorical identity. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom ≫
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv =
      (𝟙 (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject
          (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject) :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- By-kind Tate-weight-drop unstable inverse followed by hom is categorical identity. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv ≫
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom =
      (𝟙 (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject
          (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject) :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_comp_hom_eq_categoryIdentity
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
