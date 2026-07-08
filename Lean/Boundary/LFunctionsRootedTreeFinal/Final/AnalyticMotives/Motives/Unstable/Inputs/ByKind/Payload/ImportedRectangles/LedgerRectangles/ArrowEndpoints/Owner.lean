import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.ImportedRectangles.ArrowEndpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.ImportedRectangles.LedgerRectangles.ArrowEndpoints.Owner

/-!
# By-kind unstable imported-rectangle arrow-endpoint ledger lists

This file exposes source and target imported-rectangle
list-as-certificate-ledger-list facts for the hom and inverse arrows of the
six named unstable analytic-motive isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel unstable hom source rectangles are extracted from its source ledger. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-channel unstable hom target rectangles are extracted from its target ledger. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-channel unstable inverse source rectangles are extracted from its source ledger. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-channel unstable inverse target rectangles are extracted from its target ledger. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-refinement unstable hom source rectangles are extracted from its source ledger. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-refinement unstable hom target rectangles are extracted from its target ledger. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-refinement unstable inverse source rectangles are extracted from its source ledger. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-refinement unstable inverse target rectangles are extracted from its target ledger. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-schedule unstable hom source rectangles are extracted from its source ledger. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-schedule unstable hom target rectangles are extracted from its target ledger. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-schedule unstable inverse source rectangles are extracted from its source ledger. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-schedule unstable inverse target rectangles are extracted from its target ledger. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Interval-Stokes unstable hom source rectangles are extracted from its source ledger. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Interval-Stokes unstable hom target rectangles are extracted from its target ledger. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Interval-Stokes unstable inverse source rectangles are extracted from its source ledger. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Interval-Stokes unstable inverse target rectangles are extracted from its target ledger. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Interval-Fubini unstable hom source rectangles are extracted from its source ledger. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Interval-Fubini unstable hom target rectangles are extracted from its target ledger. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Interval-Fubini unstable inverse source rectangles are extracted from its source ledger. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Interval-Fubini unstable inverse target rectangles are extracted from its target ledger. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Tate-weight-drop unstable hom source rectangles are extracted from its source ledger. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Tate-weight-drop unstable hom target rectangles are extracted from its target ledger. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Tate-weight-drop unstable inverse source rectangles are extracted from its source ledger. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.sourceImportedRectangles =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Tate-weight-drop unstable inverse target rectangles are extracted from its target ledger. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.targetImportedRectangles =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
