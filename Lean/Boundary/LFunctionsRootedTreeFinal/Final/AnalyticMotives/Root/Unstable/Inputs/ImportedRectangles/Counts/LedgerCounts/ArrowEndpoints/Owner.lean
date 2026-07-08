import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ImportedRectangles.Counts.LedgerCounts.ArrowEndpoints.Owner

/-!
# Top-root all-kind unstable input imported-rectangle arrow-endpoint ledger counts

This file mirrors the motive-root source and target imported-rectangle
count-as-certificate-ledger-count surface for hom and inverse arrows of all
six named unstable localization isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The root exposes by-kind descent-channel hom source rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.sourceCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-channel hom target rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.targetCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-channel inverse source rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.sourceCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-channel inverse target rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.targetCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-refinement hom source rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.sourceCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-refinement hom target rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.targetCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-refinement inverse source rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.sourceCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-refinement inverse target rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.targetCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-schedule hom source rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.sourceCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-schedule hom target rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.targetCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-schedule inverse source rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.sourceCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind descent-schedule inverse target rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.targetCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind interval-Stokes hom source rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.sourceCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind interval-Stokes hom target rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.targetCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind interval-Stokes inverse source rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.sourceCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind interval-Stokes inverse target rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.targetCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind interval-Fubini hom source rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.sourceCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind interval-Fubini hom target rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.targetCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind interval-Fubini inverse source rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.sourceCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind interval-Fubini inverse target rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.targetCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind Tate-weight-drop hom source rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.sourceCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind Tate-weight-drop hom target rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.targetCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind Tate-weight-drop inverse source rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.sourceCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- The root exposes by-kind Tate-weight-drop inverse target rectangle count-as-ledger-count. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.targetCertificateLedger.importedRectangleCount :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
