import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Payload.ImportedRectangles.Counts.ArrowEndpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Payload.ImportedRectangles.LedgerCounts.Owner

/-!
# Source and target imported-rectangle ledger counts for named input arrows

This file gives by-kind names to the source and target imported-rectangle
count-as-certificate-ledger-count facts carried by forward and inverse arrows
attached to localization inputs.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel forward source rectangle count is counted by the source ledger. -/
theorem TraceLocalizationInput.descentChannelForwardArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelForwardArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.descentChannelForwardArrow
        source
        target).sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement forward source rectangle count is counted by the source ledger. -/
theorem TraceLocalizationInput.descentRefinementForwardArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementForwardArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.descentRefinementForwardArrow
        source
        target).sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule forward source rectangle count is counted by the source ledger. -/
theorem TraceLocalizationInput.descentScheduleForwardArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleForwardArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.descentScheduleForwardArrow
        source
        target).sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes forward source rectangle count is counted by the source ledger. -/
theorem TraceLocalizationInput.intervalStokesForwardArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesForwardArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalStokesForwardArrow
        source
        target).sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini forward source rectangle count is counted by the source ledger. -/
theorem TraceLocalizationInput.intervalFubiniForwardArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniForwardArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalFubiniForwardArrow
        source
        target).sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop forward source rectangle count is counted by the source ledger. -/
theorem TraceLocalizationInput.tateWeightDropForwardArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropForwardArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDropForwardArrow
        source
        target).sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Descent-channel forward target rectangle count is counted by the target ledger. -/
theorem TraceLocalizationInput.descentChannelForwardArrow_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelForwardArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.descentChannelForwardArrow
        source
        target).targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement forward target rectangle count is counted by the target ledger. -/
theorem TraceLocalizationInput.descentRefinementForwardArrow_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementForwardArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.descentRefinementForwardArrow
        source
        target).targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule forward target rectangle count is counted by the target ledger. -/
theorem TraceLocalizationInput.descentScheduleForwardArrow_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleForwardArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.descentScheduleForwardArrow
        source
        target).targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes forward target rectangle count is counted by the target ledger. -/
theorem TraceLocalizationInput.intervalStokesForwardArrow_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesForwardArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.intervalStokesForwardArrow
        source
        target).targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini forward target rectangle count is counted by the target ledger. -/
theorem TraceLocalizationInput.intervalFubiniForwardArrow_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniForwardArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.intervalFubiniForwardArrow
        source
        target).targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop forward target rectangle count is counted by the target ledger. -/
theorem TraceLocalizationInput.tateWeightDropForwardArrow_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropForwardArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDropForwardArrow
        source
        target).targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Descent-channel inverse source rectangle count is counted by the source ledger. -/
theorem TraceLocalizationInput.descentChannelInverseArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelInverseArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.descentChannelInverseArrow
        source
        target).sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement inverse source rectangle count is counted by the source ledger. -/
theorem TraceLocalizationInput.descentRefinementInverseArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementInverseArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.descentRefinementInverseArrow
        source
        target).sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule inverse source rectangle count is counted by the source ledger. -/
theorem TraceLocalizationInput.descentScheduleInverseArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleInverseArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.descentScheduleInverseArrow
        source
        target).sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes inverse source rectangle count is counted by the source ledger. -/
theorem TraceLocalizationInput.intervalStokesInverseArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesInverseArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalStokesInverseArrow
        source
        target).sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini inverse source rectangle count is counted by the source ledger. -/
theorem TraceLocalizationInput.intervalFubiniInverseArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniInverseArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalFubiniInverseArrow
        source
        target).sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop inverse source rectangle count is counted by the source ledger. -/
theorem TraceLocalizationInput.tateWeightDropInverseArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropInverseArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDropInverseArrow
        source
        target).sourceCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Descent-channel inverse target rectangle count is counted by the target ledger. -/
theorem TraceLocalizationInput.descentChannelInverseArrow_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelInverseArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.descentChannelInverseArrow
        source
        target).targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement inverse target rectangle count is counted by the target ledger. -/
theorem TraceLocalizationInput.descentRefinementInverseArrow_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementInverseArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.descentRefinementInverseArrow
        source
        target).targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule inverse target rectangle count is counted by the target ledger. -/
theorem TraceLocalizationInput.descentScheduleInverseArrow_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleInverseArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.descentScheduleInverseArrow
        source
        target).targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes inverse target rectangle count is counted by the target ledger. -/
theorem TraceLocalizationInput.intervalStokesInverseArrow_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesInverseArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.intervalStokesInverseArrow
        source
        target).targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini inverse target rectangle count is counted by the target ledger. -/
theorem TraceLocalizationInput.intervalFubiniInverseArrow_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniInverseArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.intervalFubiniInverseArrow
        source
        target).targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop inverse target rectangle count is counted by the target ledger. -/
theorem TraceLocalizationInput.tateWeightDropInverseArrow_targetImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropInverseArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDropInverseArrow
        source
        target).targetCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
