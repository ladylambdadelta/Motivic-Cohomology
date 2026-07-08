import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.ImportedRectangles.ArrowEndpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Payload.ImportedRectangles.LedgerRectangles.ArrowEndpoints.Owner

/-!
# Source and target imported-rectangle ledger lists for named localized isomorphisms

This file specializes the by-kind forward and inverse arrow source/target
list-as-certificate-ledger-list facts to the hom and inverse arrows of the
named localized isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel isomorphism hom source rectangles are extracted from its source ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).hom.sourceImportedRectangles =
      (TraceLocalizationInput.descentChannelLocalizedIso
        source
        target).hom.sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentChannelForwardArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-channel isomorphism hom target rectangles are extracted from its target ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).hom.targetImportedRectangles =
      (TraceLocalizationInput.descentChannelLocalizedIso
        source
        target).hom.targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentChannelForwardArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-channel isomorphism inverse source rectangles are extracted from its source ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).inv.sourceImportedRectangles =
      (TraceLocalizationInput.descentChannelLocalizedIso
        source
        target).inv.sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentChannelInverseArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-channel isomorphism inverse target rectangles are extracted from its target ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).inv.targetImportedRectangles =
      (TraceLocalizationInput.descentChannelLocalizedIso
        source
        target).inv.targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentChannelInverseArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-refinement isomorphism hom source rectangles are extracted from its source ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).hom.sourceImportedRectangles =
      (TraceLocalizationInput.descentRefinementLocalizedIso
        source
        target).hom.sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentRefinementForwardArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-refinement isomorphism hom target rectangles are extracted from its target ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).hom.targetImportedRectangles =
      (TraceLocalizationInput.descentRefinementLocalizedIso
        source
        target).hom.targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentRefinementForwardArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-refinement isomorphism inverse source rectangles are extracted from its source ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).inv.sourceImportedRectangles =
      (TraceLocalizationInput.descentRefinementLocalizedIso
        source
        target).inv.sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentRefinementInverseArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-refinement isomorphism inverse target rectangles are extracted from its target ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).inv.targetImportedRectangles =
      (TraceLocalizationInput.descentRefinementLocalizedIso
        source
        target).inv.targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentRefinementInverseArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-schedule isomorphism hom source rectangles are extracted from its source ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).hom.sourceImportedRectangles =
      (TraceLocalizationInput.descentScheduleLocalizedIso
        source
        target).hom.sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentScheduleForwardArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-schedule isomorphism hom target rectangles are extracted from its target ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).hom.targetImportedRectangles =
      (TraceLocalizationInput.descentScheduleLocalizedIso
        source
        target).hom.targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentScheduleForwardArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-schedule isomorphism inverse source rectangles are extracted from its source ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).inv.sourceImportedRectangles =
      (TraceLocalizationInput.descentScheduleLocalizedIso
        source
        target).inv.sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentScheduleInverseArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-schedule isomorphism inverse target rectangles are extracted from its target ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).inv.targetImportedRectangles =
      (TraceLocalizationInput.descentScheduleLocalizedIso
        source
        target).inv.targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentScheduleInverseArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Interval-Stokes isomorphism hom source rectangles are extracted from its source ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).hom.sourceImportedRectangles =
      (TraceLocalizationInput.intervalStokesLocalizedIso
        source
        target).hom.sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.intervalStokesForwardArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Interval-Stokes isomorphism hom target rectangles are extracted from its target ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).hom.targetImportedRectangles =
      (TraceLocalizationInput.intervalStokesLocalizedIso
        source
        target).hom.targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.intervalStokesForwardArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Interval-Stokes isomorphism inverse source rectangles are extracted from its source ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).inv.sourceImportedRectangles =
      (TraceLocalizationInput.intervalStokesLocalizedIso
        source
        target).inv.sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.intervalStokesInverseArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Interval-Stokes isomorphism inverse target rectangles are extracted from its target ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).inv.targetImportedRectangles =
      (TraceLocalizationInput.intervalStokesLocalizedIso
        source
        target).inv.targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.intervalStokesInverseArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Interval-Fubini isomorphism hom source rectangles are extracted from its source ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).hom.sourceImportedRectangles =
      (TraceLocalizationInput.intervalFubiniLocalizedIso
        source
        target).hom.sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.intervalFubiniForwardArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Interval-Fubini isomorphism hom target rectangles are extracted from its target ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).hom.targetImportedRectangles =
      (TraceLocalizationInput.intervalFubiniLocalizedIso
        source
        target).hom.targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.intervalFubiniForwardArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Interval-Fubini isomorphism inverse source rectangles are extracted from its source ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).inv.sourceImportedRectangles =
      (TraceLocalizationInput.intervalFubiniLocalizedIso
        source
        target).inv.sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.intervalFubiniInverseArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Interval-Fubini isomorphism inverse target rectangles are extracted from its target ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).inv.targetImportedRectangles =
      (TraceLocalizationInput.intervalFubiniLocalizedIso
        source
        target).inv.targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.intervalFubiniInverseArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Tate-weight-drop isomorphism hom source rectangles are extracted from its source ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).hom.sourceImportedRectangles =
      (TraceLocalizationInput.tateWeightDropLocalizedIso
        source
        target).hom.sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.tateWeightDropForwardArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Tate-weight-drop isomorphism hom target rectangles are extracted from its target ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).hom.targetImportedRectangles =
      (TraceLocalizationInput.tateWeightDropLocalizedIso
        source
        target).hom.targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.tateWeightDropForwardArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Tate-weight-drop isomorphism inverse source rectangles are extracted from its source ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).inv.sourceImportedRectangles =
      (TraceLocalizationInput.tateWeightDropLocalizedIso
        source
        target).inv.sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.tateWeightDropInverseArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Tate-weight-drop isomorphism inverse target rectangles are extracted from its target ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).inv.targetImportedRectangles =
      (TraceLocalizationInput.tateWeightDropLocalizedIso
        source
        target).inv.targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.tateWeightDropInverseArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
