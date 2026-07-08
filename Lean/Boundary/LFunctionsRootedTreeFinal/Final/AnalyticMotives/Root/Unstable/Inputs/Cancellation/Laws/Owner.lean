import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.Cancellation.Owner

/-!
# Top-root all-kind unstable cancellation laws
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The root exposes by-kind descent-channel hom-inverse cancellation. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentChannel source target).sourceObject :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_comp_inv
    source
    target

/-- The root exposes by-kind descent-channel inverse-hom cancellation. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentChannel source target).targetObject :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_comp_hom
    source
    target

/-- The root exposes by-kind descent-channel categorical hom-inverse cancellation. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom ≫
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv =
      (𝟙 (TraceLocalizationInput.descentChannel source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentChannel source target).localizedSourceObject
          (TraceLocalizationInput.descentChannel source target).localizedSourceObject) :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- The root exposes by-kind descent-channel categorical inverse-hom cancellation. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv ≫
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom =
      (𝟙 (TraceLocalizationInput.descentChannel source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentChannel source target).localizedTargetObject
          (TraceLocalizationInput.descentChannel source target).localizedTargetObject) :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- The root exposes by-kind descent-refinement hom-inverse cancellation. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentRefinement source target).sourceObject :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_comp_inv
    source
    target

/-- The root exposes by-kind descent-refinement inverse-hom cancellation. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentRefinement source target).targetObject :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_comp_hom
    source
    target

/-- The root exposes by-kind descent-refinement categorical hom-inverse cancellation. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom ≫
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv =
      (𝟙 (TraceLocalizationInput.descentRefinement source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentRefinement source target).localizedSourceObject
          (TraceLocalizationInput.descentRefinement source target).localizedSourceObject) :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- The root exposes by-kind descent-refinement categorical inverse-hom cancellation. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv ≫
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom =
      (𝟙 (TraceLocalizationInput.descentRefinement source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentRefinement source target).localizedTargetObject
          (TraceLocalizationInput.descentRefinement source target).localizedTargetObject) :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- The root exposes by-kind descent-schedule hom-inverse cancellation. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentSchedule source target).sourceObject :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_comp_inv
    source
    target

/-- The root exposes by-kind descent-schedule inverse-hom cancellation. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentSchedule source target).targetObject :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_comp_hom
    source
    target

/-- The root exposes by-kind descent-schedule categorical hom-inverse cancellation. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom ≫
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv =
      (𝟙 (TraceLocalizationInput.descentSchedule source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentSchedule source target).localizedSourceObject
          (TraceLocalizationInput.descentSchedule source target).localizedSourceObject) :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- The root exposes by-kind descent-schedule categorical inverse-hom cancellation. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv ≫
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom =
      (𝟙 (TraceLocalizationInput.descentSchedule source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentSchedule source target).localizedTargetObject
          (TraceLocalizationInput.descentSchedule source target).localizedTargetObject) :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- The root exposes by-kind interval-Stokes hom-inverse cancellation. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalStokes source target).sourceObject :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_comp_inv
    source
    target

/-- The root exposes by-kind interval-Stokes inverse-hom cancellation. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalStokes source target).targetObject :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_comp_hom
    source
    target

/-- The root exposes by-kind interval-Stokes categorical hom-inverse cancellation. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom ≫
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv =
      (𝟙 (TraceLocalizationInput.intervalStokes source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.intervalStokes source target).localizedSourceObject
          (TraceLocalizationInput.intervalStokes source target).localizedSourceObject) :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- The root exposes by-kind interval-Stokes categorical inverse-hom cancellation. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv ≫
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom =
      (𝟙 (TraceLocalizationInput.intervalStokes source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.intervalStokes source target).localizedTargetObject
          (TraceLocalizationInput.intervalStokes source target).localizedTargetObject) :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- The root exposes by-kind interval-Fubini hom-inverse cancellation. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalFubini source target).sourceObject :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_comp_inv
    source
    target

/-- The root exposes by-kind interval-Fubini inverse-hom cancellation. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalFubini source target).targetObject :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_comp_hom
    source
    target

/-- The root exposes by-kind interval-Fubini categorical hom-inverse cancellation. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom ≫
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv =
      (𝟙 (TraceLocalizationInput.intervalFubini source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.intervalFubini source target).localizedSourceObject
          (TraceLocalizationInput.intervalFubini source target).localizedSourceObject) :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- The root exposes by-kind interval-Fubini categorical inverse-hom cancellation. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv ≫
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom =
      (𝟙 (TraceLocalizationInput.intervalFubini source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.intervalFubini source target).localizedTargetObject
          (TraceLocalizationInput.intervalFubini source target).localizedTargetObject) :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- The root exposes by-kind Tate-weight-drop hom-inverse cancellation. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_comp_inv
    source
    target

/-- The root exposes by-kind Tate-weight-drop inverse-hom cancellation. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.tateWeightDrop source target).targetObject :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_comp_hom
    source
    target

/-- The root exposes by-kind Tate-weight-drop categorical hom-inverse cancellation. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom ≫
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv =
      (𝟙 (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject
          (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject) :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- The root exposes by-kind Tate-weight-drop categorical inverse-hom cancellation. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv ≫
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom =
      (𝟙 (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject
          (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject) :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_comp_hom_eq_categoryIdentity
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
