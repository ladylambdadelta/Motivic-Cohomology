import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.ImportedRectangles.Counts.ArrowEndpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Payload.ImportedRectangles.LedgerCounts.ArrowEndpoints.Owner

/-!
# Source and target imported-rectangle ledger counts for named localized isomorphisms

This file specializes the by-kind forward and inverse arrow source/target
count-as-certificate-ledger-count facts to the hom and inverse arrows of the
named localized isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel isomorphism hom source rectangle count is counted by its source ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentChannelLocalizedIso
        source
        target).hom.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentChannelForwardArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-channel isomorphism hom target rectangle count is counted by its target ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.descentChannelLocalizedIso
        source
        target).hom.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentChannelForwardArrow_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-channel isomorphism inverse source rectangle count is counted by its source ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentChannelLocalizedIso
        source
        target).inv.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentChannelInverseArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-channel isomorphism inverse target rectangle count is counted by its target ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.descentChannelLocalizedIso
        source
        target).inv.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentChannelInverseArrow_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement isomorphism hom source rectangle count is counted by its source ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentRefinementLocalizedIso
        source
        target).hom.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentRefinementForwardArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement isomorphism hom target rectangle count is counted by its target ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.descentRefinementLocalizedIso
        source
        target).hom.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentRefinementForwardArrow_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement isomorphism inverse source rectangle count is counted by its source ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentRefinementLocalizedIso
        source
        target).inv.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentRefinementInverseArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement isomorphism inverse target rectangle count is counted by its target ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.descentRefinementLocalizedIso
        source
        target).inv.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentRefinementInverseArrow_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule isomorphism hom source rectangle count is counted by its source ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentScheduleLocalizedIso
        source
        target).hom.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentScheduleForwardArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule isomorphism hom target rectangle count is counted by its target ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.descentScheduleLocalizedIso
        source
        target).hom.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentScheduleForwardArrow_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule isomorphism inverse source rectangle count is counted by its source ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentScheduleLocalizedIso
        source
        target).inv.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentScheduleInverseArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule isomorphism inverse target rectangle count is counted by its target ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.descentScheduleLocalizedIso
        source
        target).inv.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentScheduleInverseArrow_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes isomorphism hom source rectangle count is counted by its source ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalStokesLocalizedIso
        source
        target).hom.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.intervalStokesForwardArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes isomorphism hom target rectangle count is counted by its target ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.intervalStokesLocalizedIso
        source
        target).hom.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.intervalStokesForwardArrow_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes isomorphism inverse source rectangle count is counted by its source ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalStokesLocalizedIso
        source
        target).inv.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.intervalStokesInverseArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes isomorphism inverse target rectangle count is counted by its target ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.intervalStokesLocalizedIso
        source
        target).inv.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.intervalStokesInverseArrow_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini isomorphism hom source rectangle count is counted by its source ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalFubiniLocalizedIso
        source
        target).hom.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.intervalFubiniForwardArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini isomorphism hom target rectangle count is counted by its target ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.intervalFubiniLocalizedIso
        source
        target).hom.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.intervalFubiniForwardArrow_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini isomorphism inverse source rectangle count is counted by its source ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalFubiniLocalizedIso
        source
        target).inv.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.intervalFubiniInverseArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini isomorphism inverse target rectangle count is counted by its target ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.intervalFubiniLocalizedIso
        source
        target).inv.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.intervalFubiniInverseArrow_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop isomorphism hom source rectangle count is counted by its source ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDropLocalizedIso
        source
        target).hom.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.tateWeightDropForwardArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop isomorphism hom target rectangle count is counted by its target ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDropLocalizedIso
        source
        target).hom.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.tateWeightDropForwardArrow_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop isomorphism inverse source rectangle count is counted by its source ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDropLocalizedIso
        source
        target).inv.sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.tateWeightDropInverseArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop isomorphism inverse target rectangle count is counted by its target ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDropLocalizedIso
        source
        target).inv.targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.tateWeightDropInverseArrow_targetImportedRectangleCount_eq_certificateLedger_count
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
