import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.ImportedRectangles.LedgerCounts.ArrowEndpoints.Owner

/-!
# Root all-kind unstable input imported-rectangle arrow-endpoint ledger counts

This file exposes source and target imported-rectangle
count-as-certificate-ledger-count facts for hom and inverse arrows of all six
named unstable localization isomorphisms at the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- By-kind descent-channel hom source rectangle count is counted by its source ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.sourceCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind descent-channel hom target rectangle count is counted by its target ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.targetCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind descent-channel inverse source rectangle count is counted by its source ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.sourceCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind descent-channel inverse target rectangle count is counted by its target ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.targetCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind descent-refinement hom source rectangle count is counted by its source ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.sourceCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind descent-refinement hom target rectangle count is counted by its target ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.targetCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind descent-refinement inverse source rectangle count is counted by its source ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.sourceCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind descent-refinement inverse target rectangle count is counted by its target ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.targetCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind descent-schedule hom source rectangle count is counted by its source ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.sourceCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind descent-schedule hom target rectangle count is counted by its target ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.targetCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind descent-schedule inverse source rectangle count is counted by its source ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.sourceCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind descent-schedule inverse target rectangle count is counted by its target ledger. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.targetCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind interval-Stokes hom source rectangle count is counted by its source ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.sourceCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind interval-Stokes hom target rectangle count is counted by its target ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.targetCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind interval-Stokes inverse source rectangle count is counted by its source ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.sourceCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind interval-Stokes inverse target rectangle count is counted by its target ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.targetCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind interval-Fubini hom source rectangle count is counted by its source ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.sourceCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind interval-Fubini hom target rectangle count is counted by its target ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.targetCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind interval-Fubini inverse source rectangle count is counted by its source ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.sourceCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind interval-Fubini inverse target rectangle count is counted by its target ledger. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.targetCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind Tate-weight-drop hom source rectangle count is counted by its source ledger. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.sourceCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind Tate-weight-drop hom target rectangle count is counted by its target ledger. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.targetCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind Tate-weight-drop inverse source rectangle count is counted by its source ledger. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.sourceCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- By-kind Tate-weight-drop inverse target rectangle count is counted by its target ledger. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.targetCertificateLedger.importedRectangleCount :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
