import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.TraceCalculus.ArrowEndpoints.Owner

/-!
# Root all-kind unstable input trace-calculus certificate ledgers

This file exposes source and target certificate-ledger identities for hom and
inverse arrows of all six named unstable localization isomorphisms at the
motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- By-kind descent-channel hom source ledger is the input source ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.sourceCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).sourceObject.certificateLedger :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_sourceCertificateLedger
    source
    target

/-- By-kind descent-channel hom target ledger is the input target ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.targetCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).targetObject.certificateLedger :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_targetCertificateLedger
    source
    target

/-- By-kind descent-channel inverse source ledger is the input target ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.sourceCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).targetObject.certificateLedger :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_sourceCertificateLedger
    source
    target

/-- By-kind descent-channel inverse target ledger is the input source ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.targetCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).sourceObject.certificateLedger :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_targetCertificateLedger
    source
    target

/-- By-kind descent-refinement hom source ledger is the input source ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.sourceCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.certificateLedger :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_sourceCertificateLedger
    source
    target

/-- By-kind descent-refinement hom target ledger is the input target ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.targetCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).targetObject.certificateLedger :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_targetCertificateLedger
    source
    target

/-- By-kind descent-refinement inverse source ledger is the input target ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.sourceCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).targetObject.certificateLedger :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_sourceCertificateLedger
    source
    target

/-- By-kind descent-refinement inverse target ledger is the input source ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.targetCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.certificateLedger :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_targetCertificateLedger
    source
    target

/-- By-kind descent-schedule hom source ledger is the input source ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.sourceCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.certificateLedger :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_sourceCertificateLedger
    source
    target

/-- By-kind descent-schedule hom target ledger is the input target ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.targetCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).targetObject.certificateLedger :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_targetCertificateLedger
    source
    target

/-- By-kind descent-schedule inverse source ledger is the input target ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.sourceCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).targetObject.certificateLedger :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_sourceCertificateLedger
    source
    target

/-- By-kind descent-schedule inverse target ledger is the input source ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.targetCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.certificateLedger :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_targetCertificateLedger
    source
    target

/-- By-kind interval-Stokes hom source ledger is the input source ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.sourceCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.certificateLedger :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_sourceCertificateLedger
    source
    target

/-- By-kind interval-Stokes hom target ledger is the input target ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.targetCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).targetObject.certificateLedger :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_targetCertificateLedger
    source
    target

/-- By-kind interval-Stokes inverse source ledger is the input target ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.sourceCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).targetObject.certificateLedger :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_sourceCertificateLedger
    source
    target

/-- By-kind interval-Stokes inverse target ledger is the input source ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.targetCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.certificateLedger :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_targetCertificateLedger
    source
    target

/-- By-kind interval-Fubini hom source ledger is the input source ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.sourceCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.certificateLedger :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_sourceCertificateLedger
    source
    target

/-- By-kind interval-Fubini hom target ledger is the input target ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.targetCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).targetObject.certificateLedger :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_targetCertificateLedger
    source
    target

/-- By-kind interval-Fubini inverse source ledger is the input target ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.sourceCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).targetObject.certificateLedger :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_sourceCertificateLedger
    source
    target

/-- By-kind interval-Fubini inverse target ledger is the input source ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.targetCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.certificateLedger :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_targetCertificateLedger
    source
    target

/-- By-kind Tate-weight-drop hom source ledger is the input source ledger. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.sourceCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.certificateLedger :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_sourceCertificateLedger
    source
    target

/-- By-kind Tate-weight-drop hom target ledger is the input target ledger. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.targetCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.certificateLedger :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_targetCertificateLedger
    source
    target

/-- By-kind Tate-weight-drop inverse source ledger is the input target ledger. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.sourceCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.certificateLedger :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_sourceCertificateLedger
    source
    target

/-- By-kind Tate-weight-drop inverse target ledger is the input source ledger. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.targetCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.certificateLedger :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_targetCertificateLedger
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
