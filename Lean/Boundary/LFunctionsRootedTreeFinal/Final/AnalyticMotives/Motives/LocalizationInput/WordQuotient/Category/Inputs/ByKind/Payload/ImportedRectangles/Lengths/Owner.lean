import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Payload.ImportedRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Payload.ImportedRectangles.Counts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Payload.ImportedRectangles.Lengths.Endpoint.Owner

/-!
# Length facts for named imported finite-rectangle payload

This file gives by-kind names to source and target imported finite-rectangle
count/length facts for named localization arrows. Endpoint length facts are
owned by the `Endpoint` child.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel forward source rectangle count is its source rectangle-list length. -/
theorem TraceLocalizationInput.descentChannelForwardArrow_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelForwardArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.descentChannelForwardArrow
        source
        target).sourceImportedRectangles.length :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangleCount_eq_length
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement forward source rectangle count is its source rectangle-list length. -/
theorem TraceLocalizationInput.descentRefinementForwardArrow_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementForwardArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.descentRefinementForwardArrow
        source
        target).sourceImportedRectangles.length :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangleCount_eq_length
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule forward source rectangle count is its source rectangle-list length. -/
theorem TraceLocalizationInput.descentScheduleForwardArrow_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleForwardArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.descentScheduleForwardArrow
        source
        target).sourceImportedRectangles.length :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangleCount_eq_length
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes forward source rectangle count is its source rectangle-list length. -/
theorem TraceLocalizationInput.intervalStokesForwardArrow_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesForwardArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalStokesForwardArrow
        source
        target).sourceImportedRectangles.length :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangleCount_eq_length
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini forward source rectangle count is its source rectangle-list length. -/
theorem TraceLocalizationInput.intervalFubiniForwardArrow_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniForwardArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalFubiniForwardArrow
        source
        target).sourceImportedRectangles.length :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangleCount_eq_length
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop forward source rectangle count is its source rectangle-list length. -/
theorem TraceLocalizationInput.tateWeightDropForwardArrow_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropForwardArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDropForwardArrow
        source
        target).sourceImportedRectangles.length :=
  TraceLocalizationInput.localizedForwardArrow_sourceImportedRectangleCount_eq_length
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Descent-channel forward target rectangle count is its target rectangle-list length. -/
theorem TraceLocalizationInput.descentChannelForwardArrow_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelForwardArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.descentChannelForwardArrow
        source
        target).targetImportedRectangles.length :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangleCount_eq_length
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement forward target rectangle count is its target rectangle-list length. -/
theorem TraceLocalizationInput.descentRefinementForwardArrow_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementForwardArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.descentRefinementForwardArrow
        source
        target).targetImportedRectangles.length :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangleCount_eq_length
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule forward target rectangle count is its target rectangle-list length. -/
theorem TraceLocalizationInput.descentScheduleForwardArrow_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleForwardArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.descentScheduleForwardArrow
        source
        target).targetImportedRectangles.length :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangleCount_eq_length
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes forward target rectangle count is its target rectangle-list length. -/
theorem TraceLocalizationInput.intervalStokesForwardArrow_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesForwardArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.intervalStokesForwardArrow
        source
        target).targetImportedRectangles.length :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangleCount_eq_length
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini forward target rectangle count is its target rectangle-list length. -/
theorem TraceLocalizationInput.intervalFubiniForwardArrow_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniForwardArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.intervalFubiniForwardArrow
        source
        target).targetImportedRectangles.length :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangleCount_eq_length
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop forward target rectangle count is its target rectangle-list length. -/
theorem TraceLocalizationInput.tateWeightDropForwardArrow_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropForwardArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDropForwardArrow
        source
        target).targetImportedRectangles.length :=
  TraceLocalizationInput.localizedForwardArrow_targetImportedRectangleCount_eq_length
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Descent-channel inverse source rectangle count is its source rectangle-list length. -/
theorem TraceLocalizationInput.descentChannelInverseArrow_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelInverseArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.descentChannelInverseArrow
        source
        target).sourceImportedRectangles.length :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangleCount_eq_length
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement inverse source rectangle count is its source rectangle-list length. -/
theorem TraceLocalizationInput.descentRefinementInverseArrow_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementInverseArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.descentRefinementInverseArrow
        source
        target).sourceImportedRectangles.length :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangleCount_eq_length
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule inverse source rectangle count is its source rectangle-list length. -/
theorem TraceLocalizationInput.descentScheduleInverseArrow_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleInverseArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.descentScheduleInverseArrow
        source
        target).sourceImportedRectangles.length :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangleCount_eq_length
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes inverse source rectangle count is its source rectangle-list length. -/
theorem TraceLocalizationInput.intervalStokesInverseArrow_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesInverseArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalStokesInverseArrow
        source
        target).sourceImportedRectangles.length :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangleCount_eq_length
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini inverse source rectangle count is its source rectangle-list length. -/
theorem TraceLocalizationInput.intervalFubiniInverseArrow_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniInverseArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalFubiniInverseArrow
        source
        target).sourceImportedRectangles.length :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangleCount_eq_length
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop inverse source rectangle count is its source rectangle-list length. -/
theorem TraceLocalizationInput.tateWeightDropInverseArrow_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropInverseArrow
      source
      target).sourceImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDropInverseArrow
        source
        target).sourceImportedRectangles.length :=
  TraceLocalizationInput.localizedInverseArrow_sourceImportedRectangleCount_eq_length
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Descent-channel inverse target rectangle count is its target rectangle-list length. -/
theorem TraceLocalizationInput.descentChannelInverseArrow_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelInverseArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.descentChannelInverseArrow
        source
        target).targetImportedRectangles.length :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangleCount_eq_length
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement inverse target rectangle count is its target rectangle-list length. -/
theorem TraceLocalizationInput.descentRefinementInverseArrow_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementInverseArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.descentRefinementInverseArrow
        source
        target).targetImportedRectangles.length :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangleCount_eq_length
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule inverse target rectangle count is its target rectangle-list length. -/
theorem TraceLocalizationInput.descentScheduleInverseArrow_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleInverseArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.descentScheduleInverseArrow
        source
        target).targetImportedRectangles.length :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangleCount_eq_length
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes inverse target rectangle count is its target rectangle-list length. -/
theorem TraceLocalizationInput.intervalStokesInverseArrow_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesInverseArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.intervalStokesInverseArrow
        source
        target).targetImportedRectangles.length :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangleCount_eq_length
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini inverse target rectangle count is its target rectangle-list length. -/
theorem TraceLocalizationInput.intervalFubiniInverseArrow_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniInverseArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.intervalFubiniInverseArrow
        source
        target).targetImportedRectangles.length :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangleCount_eq_length
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop inverse target rectangle count is its target rectangle-list length. -/
theorem TraceLocalizationInput.tateWeightDropInverseArrow_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropInverseArrow
      source
      target).targetImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDropInverseArrow
        source
        target).targetImportedRectangles.length :=
  TraceLocalizationInput.localizedInverseArrow_targetImportedRectangleCount_eq_length
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
