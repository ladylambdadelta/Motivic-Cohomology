import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.TraceCalculus.CertificateLedgers.Owner

/-!
# Top-root all-kind unstable input trace-calculus certificate ledgers

This file mirrors the motive-root source and target certificate-ledger
identities for hom and inverse arrows of all six named unstable localization
isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The root exposes by-kind descent-channel hom source ledger identity. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.sourceCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).sourceObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_sourceCertificateLedger
    source
    target

/-- The root exposes by-kind descent-channel hom target ledger identity. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.targetCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).targetObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_targetCertificateLedger
    source
    target

/-- The root exposes by-kind descent-channel inverse source ledger identity. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.sourceCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).targetObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_sourceCertificateLedger
    source
    target

/-- The root exposes by-kind descent-channel inverse target ledger identity. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.targetCertificateLedger =
      (TraceLocalizationInput.descentChannel source target).sourceObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_targetCertificateLedger
    source
    target

/-- The root exposes by-kind descent-refinement hom source ledger identity. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.sourceCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_sourceCertificateLedger
    source
    target

/-- The root exposes by-kind descent-refinement hom target ledger identity. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.targetCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).targetObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_targetCertificateLedger
    source
    target

/-- The root exposes by-kind descent-refinement inverse source ledger identity. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.sourceCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).targetObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_sourceCertificateLedger
    source
    target

/-- The root exposes by-kind descent-refinement inverse target ledger identity. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.targetCertificateLedger =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_targetCertificateLedger
    source
    target

/-- The root exposes by-kind descent-schedule hom source ledger identity. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.sourceCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_sourceCertificateLedger
    source
    target

/-- The root exposes by-kind descent-schedule hom target ledger identity. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.targetCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).targetObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_targetCertificateLedger
    source
    target

/-- The root exposes by-kind descent-schedule inverse source ledger identity. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.sourceCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).targetObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_sourceCertificateLedger
    source
    target

/-- The root exposes by-kind descent-schedule inverse target ledger identity. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.targetCertificateLedger =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_targetCertificateLedger
    source
    target

/-- The root exposes by-kind interval-Stokes hom source ledger identity. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.sourceCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_sourceCertificateLedger
    source
    target

/-- The root exposes by-kind interval-Stokes hom target ledger identity. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.targetCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).targetObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_targetCertificateLedger
    source
    target

/-- The root exposes by-kind interval-Stokes inverse source ledger identity. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.sourceCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).targetObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_sourceCertificateLedger
    source
    target

/-- The root exposes by-kind interval-Stokes inverse target ledger identity. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.targetCertificateLedger =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_targetCertificateLedger
    source
    target

/-- The root exposes by-kind interval-Fubini hom source ledger identity. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.sourceCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_sourceCertificateLedger
    source
    target

/-- The root exposes by-kind interval-Fubini hom target ledger identity. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.targetCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).targetObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_targetCertificateLedger
    source
    target

/-- The root exposes by-kind interval-Fubini inverse source ledger identity. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.sourceCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).targetObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_sourceCertificateLedger
    source
    target

/-- The root exposes by-kind interval-Fubini inverse target ledger identity. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.targetCertificateLedger =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_targetCertificateLedger
    source
    target

/-- The root exposes by-kind Tate-weight-drop hom source ledger identity. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.sourceCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_sourceCertificateLedger
    source
    target

/-- The root exposes by-kind Tate-weight-drop hom target ledger identity. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.targetCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_targetCertificateLedger
    source
    target

/-- The root exposes by-kind Tate-weight-drop inverse source ledger identity. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_sourceCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.sourceCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_sourceCertificateLedger
    source
    target

/-- The root exposes by-kind Tate-weight-drop inverse target ledger identity. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_targetCertificateLedger
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.targetCertificateLedger =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.certificateLedger :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_targetCertificateLedger
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
