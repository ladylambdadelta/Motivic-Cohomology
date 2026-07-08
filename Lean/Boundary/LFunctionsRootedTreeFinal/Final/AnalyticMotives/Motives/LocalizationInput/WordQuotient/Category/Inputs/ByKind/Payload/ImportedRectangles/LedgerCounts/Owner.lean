import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Payload.ImportedRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Payload.ImportedRectangles.Counts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Payload.ImportedRectangles.LedgerCounts.ArrowEndpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Payload.ImportedRectangles.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Payload.ImportedRectangles.LedgerCounts.Owner

/-!
# Imported finite-rectangle ledger facts for named input arrows by kind

This file gives by-kind names to the endpoint facts that imported finite
rectangles are extracted from, and counted by, endpoint certificate ledgers.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel forward endpoint rectangles are extracted from the endpoint ledger. -/
theorem TraceLocalizationInput.descentChannelForwardArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelForwardArrow
      source
      target).endpointImportedRectangles =
      (TraceLocalizationInput.descentChannelForwardArrow
        source
        target).endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement forward endpoint rectangles are extracted from the endpoint ledger. -/
theorem TraceLocalizationInput.descentRefinementForwardArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementForwardArrow
      source
      target).endpointImportedRectangles =
      (TraceLocalizationInput.descentRefinementForwardArrow
        source
        target).endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule forward endpoint rectangles are extracted from the endpoint ledger. -/
theorem TraceLocalizationInput.descentScheduleForwardArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleForwardArrow
      source
      target).endpointImportedRectangles =
      (TraceLocalizationInput.descentScheduleForwardArrow
        source
        target).endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes forward endpoint rectangles are extracted from the endpoint ledger. -/
theorem TraceLocalizationInput.intervalStokesForwardArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesForwardArrow
      source
      target).endpointImportedRectangles =
      (TraceLocalizationInput.intervalStokesForwardArrow
        source
        target).endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini forward endpoint rectangles are extracted from the endpoint ledger. -/
theorem TraceLocalizationInput.intervalFubiniForwardArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniForwardArrow
      source
      target).endpointImportedRectangles =
      (TraceLocalizationInput.intervalFubiniForwardArrow
        source
        target).endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop forward endpoint rectangles are extracted from the endpoint ledger. -/
theorem TraceLocalizationInput.tateWeightDropForwardArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropForwardArrow
      source
      target).endpointImportedRectangles =
      (TraceLocalizationInput.tateWeightDropForwardArrow
        source
        target).endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Descent-channel inverse endpoint rectangles are extracted from the endpoint ledger. -/
theorem TraceLocalizationInput.descentChannelInverseArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelInverseArrow
      source
      target).endpointImportedRectangles =
      (TraceLocalizationInput.descentChannelInverseArrow
        source
        target).endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement inverse endpoint rectangles are extracted from the endpoint ledger. -/
theorem TraceLocalizationInput.descentRefinementInverseArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementInverseArrow
      source
      target).endpointImportedRectangles =
      (TraceLocalizationInput.descentRefinementInverseArrow
        source
        target).endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule inverse endpoint rectangles are extracted from the endpoint ledger. -/
theorem TraceLocalizationInput.descentScheduleInverseArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleInverseArrow
      source
      target).endpointImportedRectangles =
      (TraceLocalizationInput.descentScheduleInverseArrow
        source
        target).endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes inverse endpoint rectangles are extracted from the endpoint ledger. -/
theorem TraceLocalizationInput.intervalStokesInverseArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesInverseArrow
      source
      target).endpointImportedRectangles =
      (TraceLocalizationInput.intervalStokesInverseArrow
        source
        target).endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini inverse endpoint rectangles are extracted from the endpoint ledger. -/
theorem TraceLocalizationInput.intervalFubiniInverseArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniInverseArrow
      source
      target).endpointImportedRectangles =
      (TraceLocalizationInput.intervalFubiniInverseArrow
        source
        target).endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop inverse endpoint rectangles are extracted from the endpoint ledger. -/
theorem TraceLocalizationInput.tateWeightDropInverseArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropInverseArrow
      source
      target).endpointImportedRectangles =
      (TraceLocalizationInput.tateWeightDropInverseArrow
        source
        target).endpointCertificateLedger.importedRectangles :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangles_eq_certificateLedger_rectangles
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Descent-channel forward endpoint imported count is counted by the endpoint ledger. -/
theorem TraceLocalizationInput.descentChannelForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelForwardArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentChannelForwardArrow
        source
        target).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement forward endpoint imported count is counted by the endpoint ledger. -/
theorem TraceLocalizationInput.descentRefinementForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementForwardArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentRefinementForwardArrow
        source
        target).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule forward endpoint imported count is counted by the endpoint ledger. -/
theorem TraceLocalizationInput.descentScheduleForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleForwardArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentScheduleForwardArrow
        source
        target).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes forward endpoint imported count is counted by the endpoint ledger. -/
theorem TraceLocalizationInput.intervalStokesForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesForwardArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalStokesForwardArrow
        source
        target).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini forward endpoint imported count is counted by the endpoint ledger. -/
theorem TraceLocalizationInput.intervalFubiniForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniForwardArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalFubiniForwardArrow
        source
        target).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop forward endpoint imported count is counted by the endpoint ledger. -/
theorem TraceLocalizationInput.tateWeightDropForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropForwardArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDropForwardArrow
        source
        target).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedForwardArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Descent-channel inverse endpoint imported count is counted by the endpoint ledger. -/
theorem TraceLocalizationInput.descentChannelInverseArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelInverseArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentChannelInverseArrow
        source
        target).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement inverse endpoint imported count is counted by the endpoint ledger. -/
theorem TraceLocalizationInput.descentRefinementInverseArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementInverseArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentRefinementInverseArrow
        source
        target).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule inverse endpoint imported count is counted by the endpoint ledger. -/
theorem TraceLocalizationInput.descentScheduleInverseArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleInverseArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentScheduleInverseArrow
        source
        target).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes inverse endpoint imported count is counted by the endpoint ledger. -/
theorem TraceLocalizationInput.intervalStokesInverseArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesInverseArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalStokesInverseArrow
        source
        target).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini inverse endpoint imported count is counted by the endpoint ledger. -/
theorem TraceLocalizationInput.intervalFubiniInverseArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniInverseArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalFubiniInverseArrow
        source
        target).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop inverse endpoint imported count is counted by the endpoint ledger. -/
theorem TraceLocalizationInput.tateWeightDropInverseArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropInverseArrow
      source
      target).endpointImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDropInverseArrow
        source
        target).endpointCertificateLedger.importedRectangleCount :=
  TraceLocalizationInput.localizedInverseArrow_endpointImportedRectangleCount_eq_certificateLedger_count
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
