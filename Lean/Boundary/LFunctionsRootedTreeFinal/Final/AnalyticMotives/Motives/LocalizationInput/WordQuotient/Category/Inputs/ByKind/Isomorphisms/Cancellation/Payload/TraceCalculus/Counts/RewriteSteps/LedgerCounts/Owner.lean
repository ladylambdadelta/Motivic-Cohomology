import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Cancellation.Payload.TraceCalculus.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Cancellation.Payload.TraceCalculus.Counts.RewriteSteps.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Cancellation.Payload.TraceCalculus.Counts.RewriteSteps.LedgerCounts.Endpoint.Owner

/-!
# Ledger-count facts for named cancellation rewrite-step payload

This file specializes the generic input-cancellation ledger-count facts for
source and target rewrite-step counts to the six named localization-input
constructors. Endpoint ledger-count facts are owned by the `Endpoint` child.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel hom-inverse cancellation source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv).sourceRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentChannelLocalizedIso source target).hom
        (TraceLocalizationInput.descentChannelLocalizedIso source target).inv).sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel hom-inverse cancellation target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv).targetRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentChannelLocalizedIso source target).hom
        (TraceLocalizationInput.descentChannelLocalizedIso source target).inv).targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel inverse-hom cancellation source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom).sourceRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentChannelLocalizedIso source target).inv
        (TraceLocalizationInput.descentChannelLocalizedIso source target).hom).sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel inverse-hom cancellation target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom).targetRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentChannelLocalizedIso source target).inv
        (TraceLocalizationInput.descentChannelLocalizedIso source target).hom).targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement hom-inverse cancellation source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv).sourceRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv).sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement hom-inverse cancellation target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv).targetRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv).targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement inverse-hom cancellation source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom).sourceRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom).sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement inverse-hom cancellation target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom).targetRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom).targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule hom-inverse cancellation source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv).sourceRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv).sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule hom-inverse cancellation target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv).targetRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv).targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule inverse-hom cancellation source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom).sourceRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom).sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule inverse-hom cancellation target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom).targetRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom).targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes hom-inverse cancellation source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv).sourceRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv).sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes hom-inverse cancellation target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv).targetRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv).targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes inverse-hom cancellation source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom).sourceRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom).sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes inverse-hom cancellation target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom).targetRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom).targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini hom-inverse cancellation source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv).sourceRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv).sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini hom-inverse cancellation target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv).targetRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv).targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini inverse-hom cancellation source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom).sourceRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom).sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini inverse-hom cancellation target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom).targetRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom).targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop hom-inverse cancellation source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv).sourceRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv).sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop hom-inverse cancellation target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv).targetRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv).targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop inverse-hom cancellation source rewrite steps are counted by its source ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_sourceRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom).sourceRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom).sourceCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop inverse-hom cancellation target rewrite steps are counted by its target ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_targetRewriteStepCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom).targetRewriteStepCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom).targetCertificateLedger.rewriteStepCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetRewriteStepCount_eq_certificateLedger_count
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
