import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.ImportedRectangles.Counts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.ImportedRectangles.LedgerCounts.ArrowEndpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Payload.ImportedRectangles.LedgerCounts.Owner

/-!
# Ledger facts for localized-isomorphism imported rectangles

This file specializes the by-kind forward and inverse arrow endpoint
certificate-ledger facts to the hom and inverse arrows of the named localized
isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel isomorphism hom endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.descentChannelLocalizedIso
        source
        target).hom.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentChannelForwardArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-channel isomorphism inverse endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).inv.endpointImportedRectangles =
      (TraceLocalizationInput.descentChannelLocalizedIso
        source
        target).inv.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentChannelInverseArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-refinement isomorphism hom endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.descentRefinementLocalizedIso
        source
        target).hom.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentRefinementForwardArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-refinement isomorphism inverse endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).inv.endpointImportedRectangles =
      (TraceLocalizationInput.descentRefinementLocalizedIso
        source
        target).inv.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentRefinementInverseArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-schedule isomorphism hom endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.descentScheduleLocalizedIso
        source
        target).hom.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentScheduleForwardArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-schedule isomorphism inverse endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).inv.endpointImportedRectangles =
      (TraceLocalizationInput.descentScheduleLocalizedIso
        source
        target).inv.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.descentScheduleInverseArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Interval-Stokes isomorphism hom endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.intervalStokesLocalizedIso
        source
        target).hom.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.intervalStokesForwardArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Interval-Stokes isomorphism inverse endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).inv.endpointImportedRectangles =
      (TraceLocalizationInput.intervalStokesLocalizedIso
        source
        target).inv.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.intervalStokesInverseArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Interval-Fubini isomorphism hom endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.intervalFubiniLocalizedIso
        source
        target).hom.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.intervalFubiniForwardArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Interval-Fubini isomorphism inverse endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).inv.endpointImportedRectangles =
      (TraceLocalizationInput.intervalFubiniLocalizedIso
        source
        target).inv.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.intervalFubiniInverseArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Tate-weight-drop isomorphism hom endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).hom.endpointImportedRectangles =
      (TraceLocalizationInput.tateWeightDropLocalizedIso
        source
        target).hom.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.tateWeightDropForwardArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Tate-weight-drop isomorphism inverse endpoint rectangles are extracted from its endpoint ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).inv.endpointImportedRectangles =
      (TraceLocalizationInput.tateWeightDropLocalizedIso
        source
        target).inv.endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.tateWeightDropInverseArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    source
    target

/-- Descent-channel isomorphism hom endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentChannelLocalizedIso
        source
        target).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentChannelForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-channel isomorphism inverse endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentChannelLocalizedIso
        source
        target).inv.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentChannelInverseArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement isomorphism hom endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentRefinementLocalizedIso
        source
        target).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentRefinementForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-refinement isomorphism inverse endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentRefinementLocalizedIso
        source
        target).inv.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentRefinementInverseArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule isomorphism hom endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentScheduleLocalizedIso
        source
        target).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentScheduleForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Descent-schedule isomorphism inverse endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentScheduleLocalizedIso
        source
        target).inv.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.descentScheduleInverseArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes isomorphism hom endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalStokesLocalizedIso
        source
        target).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.intervalStokesForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Interval-Stokes isomorphism inverse endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalStokesLocalizedIso
        source
        target).inv.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.intervalStokesInverseArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini isomorphism hom endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalFubiniLocalizedIso
        source
        target).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.intervalFubiniForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Interval-Fubini isomorphism inverse endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalFubiniLocalizedIso
        source
        target).inv.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.intervalFubiniInverseArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop isomorphism hom endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDropLocalizedIso
        source
        target).hom.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.tateWeightDropForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

/-- Tate-weight-drop isomorphism inverse endpoint rectangle count is counted by its endpoint ledger. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDropLocalizedIso
        source
        target).inv.endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.tateWeightDropInverseArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
