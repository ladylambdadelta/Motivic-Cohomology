import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Cancellation.Payload.TraceCalculus.CertificateLedgers.Endpoints.Owner

/-!
# Motive-root cancellation certificate ledgers

This file is the motive-root boundary for trace-calculus certificate-ledger
payload carried by the six by-kind unstable cancellation composites.

The imported owner proves the concrete source and target certificate-ledger
identities for hom-inverse and inverse-hom cancellation composites.  This file
keeps those facts available from the motive-root cancellation payload tree
without duplicating the lower analytic proofs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root descent-channel hom-inverse cancellation source ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_comp_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).sourceCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.certificateLedger :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_comp_inv_sourceCertificateLedger
    source
    target

/-- Motive-root descent-channel hom-inverse cancellation target ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_comp_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).targetCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.certificateLedger :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_comp_inv_targetCertificateLedger
    source
    target

/-- Motive-root descent-channel inverse-hom cancellation source ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_comp_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).sourceCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.certificateLedger :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_comp_hom_sourceCertificateLedger
    source
    target

/-- Motive-root descent-channel inverse-hom cancellation target ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_comp_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).targetCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.certificateLedger :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_comp_hom_targetCertificateLedger
    source
    target

/-- Motive-root descent-refinement hom-inverse cancellation source ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_comp_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).sourceCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.certificateLedger :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_comp_inv_sourceCertificateLedger
    source
    target

/-- Motive-root descent-refinement hom-inverse cancellation target ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_comp_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).targetCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.certificateLedger :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_comp_inv_targetCertificateLedger
    source
    target

/-- Motive-root descent-refinement inverse-hom cancellation source ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_comp_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).sourceCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.certificateLedger :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_comp_hom_sourceCertificateLedger
    source
    target

/-- Motive-root descent-refinement inverse-hom cancellation target ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_comp_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).targetCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.certificateLedger :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_comp_hom_targetCertificateLedger
    source
    target

/-- Motive-root descent-schedule hom-inverse cancellation source ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_comp_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).sourceCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.certificateLedger :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_comp_inv_sourceCertificateLedger
    source
    target

/-- Motive-root descent-schedule hom-inverse cancellation target ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_comp_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).targetCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.certificateLedger :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_comp_inv_targetCertificateLedger
    source
    target

/-- Motive-root descent-schedule inverse-hom cancellation source ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_comp_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).sourceCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.certificateLedger :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_comp_hom_sourceCertificateLedger
    source
    target

/-- Motive-root descent-schedule inverse-hom cancellation target ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_comp_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).targetCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.certificateLedger :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_comp_hom_targetCertificateLedger
    source
    target

/-- Motive-root interval-Stokes hom-inverse cancellation source ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_comp_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).sourceCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.certificateLedger :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_comp_inv_sourceCertificateLedger
    source
    target

/-- Motive-root interval-Stokes hom-inverse cancellation target ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_comp_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).targetCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.certificateLedger :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_comp_inv_targetCertificateLedger
    source
    target

/-- Motive-root interval-Stokes inverse-hom cancellation source ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_comp_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).sourceCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.certificateLedger :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_comp_hom_sourceCertificateLedger
    source
    target

/-- Motive-root interval-Stokes inverse-hom cancellation target ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_comp_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).targetCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.certificateLedger :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_comp_hom_targetCertificateLedger
    source
    target

/-- Motive-root interval-Fubini hom-inverse cancellation source ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_comp_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).sourceCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.certificateLedger :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_comp_inv_sourceCertificateLedger
    source
    target

/-- Motive-root interval-Fubini hom-inverse cancellation target ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_comp_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).targetCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.certificateLedger :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_comp_inv_targetCertificateLedger
    source
    target

/-- Motive-root interval-Fubini inverse-hom cancellation source ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_comp_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).sourceCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.certificateLedger :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_comp_hom_sourceCertificateLedger
    source
    target

/-- Motive-root interval-Fubini inverse-hom cancellation target ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_comp_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).targetCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.certificateLedger :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_comp_hom_targetCertificateLedger
    source
    target

/-- Motive-root Tate-weight-drop hom-inverse cancellation source ledger. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_comp_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).sourceCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.certificateLedger :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_comp_inv_sourceCertificateLedger
    source
    target

/-- Motive-root Tate-weight-drop hom-inverse cancellation target ledger. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_comp_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).targetCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.certificateLedger :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_comp_inv_targetCertificateLedger
    source
    target

/-- Motive-root Tate-weight-drop inverse-hom cancellation source ledger. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_comp_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).sourceCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.certificateLedger :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_comp_hom_sourceCertificateLedger
    source
    target

/-- Motive-root Tate-weight-drop inverse-hom cancellation target ledger. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_comp_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).targetCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.certificateLedger :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_comp_hom_targetCertificateLedger
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
