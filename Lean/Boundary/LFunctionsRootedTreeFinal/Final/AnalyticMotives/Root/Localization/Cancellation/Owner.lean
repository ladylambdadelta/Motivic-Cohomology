import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Localization.Cancellation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Localization.SummaryRepresentatives.Owner

/-!
# Top-root localization cancellation laws

This file exposes the two-sided word-class and categorical cancellation laws
for the six calculus localization isomorphisms at the public root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The analytic-motives root exposes channel descent hom-inverse cancellation. -/
theorem AnalyticMotivesRoot.descentChannelIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceCalculusLocalization.descentChannelIso source target).hom
        (TraceCalculusLocalization.descentChannelIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentChannel source target).sourceObject :=
  TraceAnalyticMotive.descentChannelIso_hom_comp_inv
    source
    target

/-- The analytic-motives root exposes channel descent inverse-hom cancellation. -/
theorem AnalyticMotivesRoot.descentChannelIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceCalculusLocalization.descentChannelIso source target).inv
        (TraceCalculusLocalization.descentChannelIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentChannel source target).targetObject :=
  TraceAnalyticMotive.descentChannelIso_inv_comp_hom
    source
    target

/-- The analytic-motives root exposes channel descent categorical hom-inverse cancellation. -/
theorem AnalyticMotivesRoot.descentChannelIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.descentChannelIso source target).hom ≫
        (TraceCalculusLocalization.descentChannelIso source target).inv =
      (𝟙 (TraceLocalizationInput.descentChannel source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentChannel source target).localizedSourceObject
          (TraceLocalizationInput.descentChannel source target).localizedSourceObject) :=
  TraceAnalyticMotive.descentChannelIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- The analytic-motives root exposes channel descent categorical inverse-hom cancellation. -/
theorem AnalyticMotivesRoot.descentChannelIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.descentChannelIso source target).inv ≫
        (TraceCalculusLocalization.descentChannelIso source target).hom =
      (𝟙 (TraceLocalizationInput.descentChannel source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentChannel source target).localizedTargetObject
          (TraceLocalizationInput.descentChannel source target).localizedTargetObject) :=
  TraceAnalyticMotive.descentChannelIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- The analytic-motives root exposes refinement descent hom-inverse cancellation. -/
theorem AnalyticMotivesRoot.descentRefinementIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceCalculusLocalization.descentRefinementIso source target).hom
        (TraceCalculusLocalization.descentRefinementIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentRefinement source target).sourceObject :=
  TraceAnalyticMotive.descentRefinementIso_hom_comp_inv
    source
    target

/-- The analytic-motives root exposes refinement descent inverse-hom cancellation. -/
theorem AnalyticMotivesRoot.descentRefinementIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceCalculusLocalization.descentRefinementIso source target).inv
        (TraceCalculusLocalization.descentRefinementIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentRefinement source target).targetObject :=
  TraceAnalyticMotive.descentRefinementIso_inv_comp_hom
    source
    target

/-- The analytic-motives root exposes refinement descent categorical hom-inverse cancellation. -/
theorem AnalyticMotivesRoot.descentRefinementIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.descentRefinementIso source target).hom ≫
        (TraceCalculusLocalization.descentRefinementIso source target).inv =
      (𝟙 (TraceLocalizationInput.descentRefinement source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentRefinement source target).localizedSourceObject
          (TraceLocalizationInput.descentRefinement source target).localizedSourceObject) :=
  TraceAnalyticMotive.descentRefinementIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- The analytic-motives root exposes refinement descent categorical inverse-hom cancellation. -/
theorem AnalyticMotivesRoot.descentRefinementIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.descentRefinementIso source target).inv ≫
        (TraceCalculusLocalization.descentRefinementIso source target).hom =
      (𝟙 (TraceLocalizationInput.descentRefinement source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentRefinement source target).localizedTargetObject
          (TraceLocalizationInput.descentRefinement source target).localizedTargetObject) :=
  TraceAnalyticMotive.descentRefinementIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- The analytic-motives root exposes schedule descent hom-inverse cancellation. -/
theorem AnalyticMotivesRoot.descentScheduleIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceCalculusLocalization.descentScheduleIso source target).hom
        (TraceCalculusLocalization.descentScheduleIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentSchedule source target).sourceObject :=
  TraceAnalyticMotive.descentScheduleIso_hom_comp_inv
    source
    target

/-- The analytic-motives root exposes schedule descent inverse-hom cancellation. -/
theorem AnalyticMotivesRoot.descentScheduleIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceCalculusLocalization.descentScheduleIso source target).inv
        (TraceCalculusLocalization.descentScheduleIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.descentSchedule source target).targetObject :=
  TraceAnalyticMotive.descentScheduleIso_inv_comp_hom
    source
    target

/-- The analytic-motives root exposes schedule descent categorical hom-inverse cancellation. -/
theorem AnalyticMotivesRoot.descentScheduleIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.descentScheduleIso source target).hom ≫
        (TraceCalculusLocalization.descentScheduleIso source target).inv =
      (𝟙 (TraceLocalizationInput.descentSchedule source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentSchedule source target).localizedSourceObject
          (TraceLocalizationInput.descentSchedule source target).localizedSourceObject) :=
  TraceAnalyticMotive.descentScheduleIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- The analytic-motives root exposes schedule descent categorical inverse-hom cancellation. -/
theorem AnalyticMotivesRoot.descentScheduleIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.descentScheduleIso source target).inv ≫
        (TraceCalculusLocalization.descentScheduleIso source target).hom =
      (𝟙 (TraceLocalizationInput.descentSchedule source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.descentSchedule source target).localizedTargetObject
          (TraceLocalizationInput.descentSchedule source target).localizedTargetObject) :=
  TraceAnalyticMotive.descentScheduleIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- The analytic-motives root exposes interval Stokes hom-inverse cancellation. -/
theorem AnalyticMotivesRoot.intervalStokesIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceCalculusLocalization.intervalStokesIso source target).hom
        (TraceCalculusLocalization.intervalStokesIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalStokes source target).sourceObject :=
  TraceAnalyticMotive.intervalStokesIso_hom_comp_inv
    source
    target

/-- The analytic-motives root exposes interval Stokes inverse-hom cancellation. -/
theorem AnalyticMotivesRoot.intervalStokesIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceCalculusLocalization.intervalStokesIso source target).inv
        (TraceCalculusLocalization.intervalStokesIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalStokes source target).targetObject :=
  TraceAnalyticMotive.intervalStokesIso_inv_comp_hom
    source
    target

/-- The analytic-motives root exposes interval Stokes categorical hom-inverse cancellation. -/
theorem AnalyticMotivesRoot.intervalStokesIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.intervalStokesIso source target).hom ≫
        (TraceCalculusLocalization.intervalStokesIso source target).inv =
      (𝟙 (TraceLocalizationInput.intervalStokes source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.intervalStokes source target).localizedSourceObject
          (TraceLocalizationInput.intervalStokes source target).localizedSourceObject) :=
  TraceAnalyticMotive.intervalStokesIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- The analytic-motives root exposes interval Stokes categorical inverse-hom cancellation. -/
theorem AnalyticMotivesRoot.intervalStokesIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.intervalStokesIso source target).inv ≫
        (TraceCalculusLocalization.intervalStokesIso source target).hom =
      (𝟙 (TraceLocalizationInput.intervalStokes source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.intervalStokes source target).localizedTargetObject
          (TraceLocalizationInput.intervalStokes source target).localizedTargetObject) :=
  TraceAnalyticMotive.intervalStokesIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- The analytic-motives root exposes interval Fubini hom-inverse cancellation. -/
theorem AnalyticMotivesRoot.intervalFubiniIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceCalculusLocalization.intervalFubiniIso source target).hom
        (TraceCalculusLocalization.intervalFubiniIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalFubini source target).sourceObject :=
  TraceAnalyticMotive.intervalFubiniIso_hom_comp_inv
    source
    target

/-- The analytic-motives root exposes interval Fubini inverse-hom cancellation. -/
theorem AnalyticMotivesRoot.intervalFubiniIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceCalculusLocalization.intervalFubiniIso source target).inv
        (TraceCalculusLocalization.intervalFubiniIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.intervalFubini source target).targetObject :=
  TraceAnalyticMotive.intervalFubiniIso_inv_comp_hom
    source
    target

/-- The analytic-motives root exposes interval Fubini categorical hom-inverse cancellation. -/
theorem AnalyticMotivesRoot.intervalFubiniIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.intervalFubiniIso source target).hom ≫
        (TraceCalculusLocalization.intervalFubiniIso source target).inv =
      (𝟙 (TraceLocalizationInput.intervalFubini source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.intervalFubini source target).localizedSourceObject
          (TraceLocalizationInput.intervalFubini source target).localizedSourceObject) :=
  TraceAnalyticMotive.intervalFubiniIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- The analytic-motives root exposes interval Fubini categorical inverse-hom cancellation. -/
theorem AnalyticMotivesRoot.intervalFubiniIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.intervalFubiniIso source target).inv ≫
        (TraceCalculusLocalization.intervalFubiniIso source target).hom =
      (𝟙 (TraceLocalizationInput.intervalFubini source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.intervalFubini source target).localizedTargetObject
          (TraceLocalizationInput.intervalFubini source target).localizedTargetObject) :=
  TraceAnalyticMotive.intervalFubiniIso_inv_comp_hom_eq_categoryIdentity
    source
    target

/-- The analytic-motives root exposes Tate weight-drop hom-inverse cancellation. -/
theorem AnalyticMotivesRoot.tateWeightDropIso_hom_comp_inv
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceCalculusLocalization.tateWeightDropIso source target).hom
        (TraceCalculusLocalization.tateWeightDropIso source target).inv =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.tateWeightDrop source target).sourceObject :=
  TraceAnalyticMotive.tateWeightDropIso_hom_comp_inv
    source
    target

/-- The analytic-motives root exposes Tate weight-drop inverse-hom cancellation. -/
theorem AnalyticMotivesRoot.tateWeightDropIso_inv_comp_hom
    (source target : QTraceExpression) :
    TraceLocalizationWordClass.comp
        (TraceCalculusLocalization.tateWeightDropIso source target).inv
        (TraceCalculusLocalization.tateWeightDropIso source target).hom =
      TraceLocalizationWordClass.identity
        (TraceLocalizationInput.tateWeightDrop source target).targetObject :=
  TraceAnalyticMotive.tateWeightDropIso_inv_comp_hom
    source
    target

/-- The analytic-motives root exposes Tate weight-drop categorical hom-inverse cancellation. -/
theorem AnalyticMotivesRoot.tateWeightDropIso_hom_comp_inv_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.tateWeightDropIso source target).hom ≫
        (TraceCalculusLocalization.tateWeightDropIso source target).inv =
      (𝟙 (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject
          (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject) :=
  TraceAnalyticMotive.tateWeightDropIso_hom_comp_inv_eq_categoryIdentity
    source
    target

/-- The analytic-motives root exposes Tate weight-drop categorical inverse-hom cancellation. -/
theorem AnalyticMotivesRoot.tateWeightDropIso_inv_comp_hom_eq_categoryIdentity
    (source target : QTraceExpression) :
    (TraceCalculusLocalization.tateWeightDropIso source target).inv ≫
        (TraceCalculusLocalization.tateWeightDropIso source target).hom =
      (𝟙 (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject :
        TraceLocalizedWordHom
          (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject
          (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject) :=
  TraceAnalyticMotive.tateWeightDropIso_inv_comp_hom_eq_categoryIdentity
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
