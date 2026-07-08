import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Cancellation.Payload.TraceCalculus.Counts.RewriteSteps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Cancellation.Payload.TraceCalculus.Counts.RewriteSteps.LedgerCounts.Endpoint.Owner

/-!
# Endpoint rewrite-step ledger counts for unstable cancellation composites

This file exposes endpoint rewrite-step count-as-ledger-count facts for
cancellation composites of the six named unstable analytic-motive localization
isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel unstable hom-inverse cancellation endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Descent-channel unstable inverse-hom cancellation endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement unstable hom-inverse cancellation endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement unstable inverse-hom cancellation endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule unstable hom-inverse cancellation endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule unstable inverse-hom cancellation endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes unstable hom-inverse cancellation endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes unstable inverse-hom cancellation endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini unstable hom-inverse cancellation endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini unstable inverse-hom cancellation endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop unstable hom-inverse cancellation endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop unstable inverse-hom cancellation endpoint rewrite count is counted by its endpoint ledger. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_endpointRewriteStepCount_eq_certificateLedger_count
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
