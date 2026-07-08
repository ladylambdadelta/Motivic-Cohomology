import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Payload.ImportedRectangles.ArrowEndpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Payload.ImportedRectangles.LedgerRectangles.Owner

/-!
# Source and target imported-rectangle ledger lists for named input arrows

This file gives by-kind names to the source and target imported-rectangle
list-as-certificate-ledger-list facts carried by forward and inverse arrows
attached to localization inputs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel forward source rectangles are extracted from the source ledger. -/
theorem TraceLocalizationInput.descentChannelForwardArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelForwardArrow
      source
      target).sourceImportedRectangles =
      (TraceLocalizationInput.descentChannelForwardArrow
        source
        target).sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement forward source rectangles are extracted from the source ledger. -/
theorem TraceLocalizationInput.descentRefinementForwardArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementForwardArrow
      source
      target).sourceImportedRectangles =
      (TraceLocalizationInput.descentRefinementForwardArrow
        source
        target).sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule forward source rectangles are extracted from the source ledger. -/
theorem TraceLocalizationInput.descentScheduleForwardArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleForwardArrow
      source
      target).sourceImportedRectangles =
      (TraceLocalizationInput.descentScheduleForwardArrow
        source
        target).sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes forward source rectangles are extracted from the source ledger. -/
theorem TraceLocalizationInput.intervalStokesForwardArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesForwardArrow
      source
      target).sourceImportedRectangles =
      (TraceLocalizationInput.intervalStokesForwardArrow
        source
        target).sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini forward source rectangles are extracted from the source ledger. -/
theorem TraceLocalizationInput.intervalFubiniForwardArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniForwardArrow
      source
      target).sourceImportedRectangles =
      (TraceLocalizationInput.intervalFubiniForwardArrow
        source
        target).sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop forward source rectangles are extracted from the source ledger. -/
theorem TraceLocalizationInput.tateWeightDropForwardArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropForwardArrow
      source
      target).sourceImportedRectangles =
      (TraceLocalizationInput.tateWeightDropForwardArrow
        source
        target).sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Descent-channel forward target rectangles are extracted from the target ledger. -/
theorem TraceLocalizationInput.descentChannelForwardArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelForwardArrow
      source
      target).targetImportedRectangles =
      (TraceLocalizationInput.descentChannelForwardArrow
        source
        target).targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement forward target rectangles are extracted from the target ledger. -/
theorem TraceLocalizationInput.descentRefinementForwardArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementForwardArrow
      source
      target).targetImportedRectangles =
      (TraceLocalizationInput.descentRefinementForwardArrow
        source
        target).targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule forward target rectangles are extracted from the target ledger. -/
theorem TraceLocalizationInput.descentScheduleForwardArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleForwardArrow
      source
      target).targetImportedRectangles =
      (TraceLocalizationInput.descentScheduleForwardArrow
        source
        target).targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes forward target rectangles are extracted from the target ledger. -/
theorem TraceLocalizationInput.intervalStokesForwardArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesForwardArrow
      source
      target).targetImportedRectangles =
      (TraceLocalizationInput.intervalStokesForwardArrow
        source
        target).targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini forward target rectangles are extracted from the target ledger. -/
theorem TraceLocalizationInput.intervalFubiniForwardArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniForwardArrow
      source
      target).targetImportedRectangles =
      (TraceLocalizationInput.intervalFubiniForwardArrow
        source
        target).targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop forward target rectangles are extracted from the target ledger. -/
theorem TraceLocalizationInput.tateWeightDropForwardArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropForwardArrow
      source
      target).targetImportedRectangles =
      (TraceLocalizationInput.tateWeightDropForwardArrow
        source
        target).targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Descent-channel inverse source rectangles are extracted from the source ledger. -/
theorem TraceLocalizationInput.descentChannelInverseArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelInverseArrow
      source
      target).sourceImportedRectangles =
      (TraceLocalizationInput.descentChannelInverseArrow
        source
        target).sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement inverse source rectangles are extracted from the source ledger. -/
theorem TraceLocalizationInput.descentRefinementInverseArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementInverseArrow
      source
      target).sourceImportedRectangles =
      (TraceLocalizationInput.descentRefinementInverseArrow
        source
        target).sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule inverse source rectangles are extracted from the source ledger. -/
theorem TraceLocalizationInput.descentScheduleInverseArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleInverseArrow
      source
      target).sourceImportedRectangles =
      (TraceLocalizationInput.descentScheduleInverseArrow
        source
        target).sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes inverse source rectangles are extracted from the source ledger. -/
theorem TraceLocalizationInput.intervalStokesInverseArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesInverseArrow
      source
      target).sourceImportedRectangles =
      (TraceLocalizationInput.intervalStokesInverseArrow
        source
        target).sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini inverse source rectangles are extracted from the source ledger. -/
theorem TraceLocalizationInput.intervalFubiniInverseArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniInverseArrow
      source
      target).sourceImportedRectangles =
      (TraceLocalizationInput.intervalFubiniInverseArrow
        source
        target).sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop inverse source rectangles are extracted from the source ledger. -/
theorem TraceLocalizationInput.tateWeightDropInverseArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropInverseArrow
      source
      target).sourceImportedRectangles =
      (TraceLocalizationInput.tateWeightDropInverseArrow
        source
        target).sourceCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Descent-channel inverse target rectangles are extracted from the target ledger. -/
theorem TraceLocalizationInput.descentChannelInverseArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelInverseArrow
      source
      target).targetImportedRectangles =
      (TraceLocalizationInput.descentChannelInverseArrow
        source
        target).targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement inverse target rectangles are extracted from the target ledger. -/
theorem TraceLocalizationInput.descentRefinementInverseArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementInverseArrow
      source
      target).targetImportedRectangles =
      (TraceLocalizationInput.descentRefinementInverseArrow
        source
        target).targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule inverse target rectangles are extracted from the target ledger. -/
theorem TraceLocalizationInput.descentScheduleInverseArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleInverseArrow
      source
      target).targetImportedRectangles =
      (TraceLocalizationInput.descentScheduleInverseArrow
        source
        target).targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes inverse target rectangles are extracted from the target ledger. -/
theorem TraceLocalizationInput.intervalStokesInverseArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesInverseArrow
      source
      target).targetImportedRectangles =
      (TraceLocalizationInput.intervalStokesInverseArrow
        source
        target).targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini inverse target rectangles are extracted from the target ledger. -/
theorem TraceLocalizationInput.intervalFubiniInverseArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniInverseArrow
      source
      target).targetImportedRectangles =
      (TraceLocalizationInput.intervalFubiniInverseArrow
        source
        target).targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop inverse target rectangles are extracted from the target ledger. -/
theorem TraceLocalizationInput.tateWeightDropInverseArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropInverseArrow
      source
      target).targetImportedRectangles =
      (TraceLocalizationInput.tateWeightDropInverseArrow
        source
        target).targetCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
