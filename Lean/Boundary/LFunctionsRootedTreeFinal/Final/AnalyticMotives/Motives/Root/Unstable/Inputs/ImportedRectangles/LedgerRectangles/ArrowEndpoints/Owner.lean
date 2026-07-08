import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.ImportedRectangles.LedgerRectangles.ArrowEndpoints.Owner

/-!
# Root all-kind unstable input arrow-endpoint imported-rectangle ledger lists

This file exposes source and target imported-rectangle
list-as-certificate-ledger-list facts for hom and inverse arrows of all six
named unstable localization isomorphisms at the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.sourceCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.targetCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.sourceCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.targetCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.sourceCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.targetCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.sourceCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.targetCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.sourceCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.targetCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.sourceCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.targetCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.sourceCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.targetCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.sourceCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.targetCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.sourceCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.targetCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.sourceCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.targetCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.sourceCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.targetCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.sourceCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.targetCertificateLedger.importedRectangles :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
