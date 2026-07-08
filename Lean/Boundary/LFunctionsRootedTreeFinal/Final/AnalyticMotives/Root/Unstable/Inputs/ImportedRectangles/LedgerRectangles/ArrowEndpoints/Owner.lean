import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ImportedRectangles.LedgerRectangles.ArrowEndpoints.Owner

/-!
# Top-root all-kind unstable input arrow-endpoint imported-rectangle ledger lists

This file mirrors the motive-root source and target imported-rectangle
list-as-certificate-ledger-list surface for hom and inverse arrows of all six
named unstable localization isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.sourceCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.targetCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.sourceCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.targetCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.sourceCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.targetCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.sourceCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.targetCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.sourceCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.targetCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.sourceCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.targetCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.sourceCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.targetCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.sourceCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.targetCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.sourceCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.targetCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.sourceCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.targetCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.sourceCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.targetCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.sourceCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.targetCertificateLedger.importedRectangles :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
