import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.Cancellation.TraceCalculus.CertificateLedgers.Owner

/-!
# Top-root cancellation certificate ledgers

This file mirrors the motive-root trace-calculus certificate-ledger boundary at
the public analytic-motives root.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root descent-channel hom-inverse cancellation source ledger. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_comp_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).sourceCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_comp_inv_sourceCertificateLedger
    source
    target

/-- Top-root descent-channel hom-inverse cancellation target ledger. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_comp_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).targetCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_comp_inv_targetCertificateLedger
    source
    target

/-- Top-root descent-channel inverse-hom cancellation source ledger. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_comp_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).sourceCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_comp_hom_sourceCertificateLedger
    source
    target

/-- Top-root descent-channel inverse-hom cancellation target ledger. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_comp_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).targetCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_comp_hom_targetCertificateLedger
    source
    target

/-- Top-root descent-refinement hom-inverse cancellation source ledger. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_comp_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).sourceCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_comp_inv_sourceCertificateLedger
    source
    target

/-- Top-root descent-refinement hom-inverse cancellation target ledger. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_comp_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).targetCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_comp_inv_targetCertificateLedger
    source
    target

/-- Top-root descent-refinement inverse-hom cancellation source ledger. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_comp_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).sourceCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_comp_hom_sourceCertificateLedger
    source
    target

/-- Top-root descent-refinement inverse-hom cancellation target ledger. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_comp_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).targetCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_comp_hom_targetCertificateLedger
    source
    target

/-- Top-root descent-schedule hom-inverse cancellation source ledger. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_comp_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).sourceCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_comp_inv_sourceCertificateLedger
    source
    target

/-- Top-root descent-schedule hom-inverse cancellation target ledger. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_comp_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).targetCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_comp_inv_targetCertificateLedger
    source
    target

/-- Top-root descent-schedule inverse-hom cancellation source ledger. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_comp_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).sourceCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_comp_hom_sourceCertificateLedger
    source
    target

/-- Top-root descent-schedule inverse-hom cancellation target ledger. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_comp_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).targetCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_comp_hom_targetCertificateLedger
    source
    target

/-- Top-root interval-Stokes hom-inverse cancellation source ledger. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_comp_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).sourceCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_comp_inv_sourceCertificateLedger
    source
    target

/-- Top-root interval-Stokes hom-inverse cancellation target ledger. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_comp_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).targetCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_comp_inv_targetCertificateLedger
    source
    target

/-- Top-root interval-Stokes inverse-hom cancellation source ledger. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_comp_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).sourceCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_comp_hom_sourceCertificateLedger
    source
    target

/-- Top-root interval-Stokes inverse-hom cancellation target ledger. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_comp_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).targetCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_comp_hom_targetCertificateLedger
    source
    target

/-- Top-root interval-Fubini hom-inverse cancellation source ledger. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_comp_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).sourceCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_comp_inv_sourceCertificateLedger
    source
    target

/-- Top-root interval-Fubini hom-inverse cancellation target ledger. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_comp_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).targetCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_comp_inv_targetCertificateLedger
    source
    target

/-- Top-root interval-Fubini inverse-hom cancellation source ledger. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_comp_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).sourceCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_comp_hom_sourceCertificateLedger
    source
    target

/-- Top-root interval-Fubini inverse-hom cancellation target ledger. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_comp_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).targetCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_comp_hom_targetCertificateLedger
    source
    target

/-- Top-root Tate-weight-drop hom-inverse cancellation source ledger. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_comp_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).sourceCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_comp_inv_sourceCertificateLedger
    source
    target

/-- Top-root Tate-weight-drop hom-inverse cancellation target ledger. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_comp_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).targetCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_comp_inv_targetCertificateLedger
    source
    target

/-- Top-root Tate-weight-drop inverse-hom cancellation source ledger. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_comp_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).sourceCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_comp_hom_sourceCertificateLedger
    source
    target

/-- Top-root Tate-weight-drop inverse-hom cancellation target ledger. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_comp_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).targetCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_comp_hom_targetCertificateLedger
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
