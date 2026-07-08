import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.ImportedRectangles.Counts.ArrowEndpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.ImportedRectangles.LedgerCounts.ArrowEndpoints.Owner

/-!
# By-kind unstable imported-rectangle arrow-endpoint ledger counts

This file exposes source and target imported-rectangle
count-as-certificate-ledger-count facts for the hom and inverse arrows of the
six named unstable analytic-motive isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel unstable hom source rectangle count is counted by its source ledger. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-channel unstable hom target rectangle count is counted by its target ledger. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-channel unstable inverse source rectangle count is counted by its source ledger. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-channel unstable inverse target rectangle count is counted by its target ledger. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement unstable hom source rectangle count is counted by its source ledger. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement unstable hom target rectangle count is counted by its target ledger. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement unstable inverse source rectangle count is counted by its source ledger. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement unstable inverse target rectangle count is counted by its target ledger. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule unstable hom source rectangle count is counted by its source ledger. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule unstable hom target rectangle count is counted by its target ledger. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule unstable inverse source rectangle count is counted by its source ledger. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule unstable inverse target rectangle count is counted by its target ledger. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes unstable hom source rectangle count is counted by its source ledger. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes unstable hom target rectangle count is counted by its target ledger. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes unstable inverse source rectangle count is counted by its source ledger. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes unstable inverse target rectangle count is counted by its target ledger. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini unstable hom source rectangle count is counted by its source ledger. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini unstable hom target rectangle count is counted by its target ledger. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini unstable inverse source rectangle count is counted by its source ledger. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini unstable inverse target rectangle count is counted by its target ledger. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop unstable hom source rectangle count is counted by its source ledger. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop unstable hom target rectangle count is counted by its target ledger. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop unstable inverse source rectangle count is counted by its source ledger. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop unstable inverse target rectangle count is counted by its target ledger. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
