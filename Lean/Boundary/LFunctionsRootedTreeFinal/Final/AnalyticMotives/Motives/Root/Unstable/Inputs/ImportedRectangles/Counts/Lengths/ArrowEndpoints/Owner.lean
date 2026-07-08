import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.ImportedRectangles.Lengths.ArrowEndpoints.Owner

/-!
# Root all-kind unstable input imported-rectangle arrow-endpoint count lengths

This file exposes source and target imported-rectangle count-as-list-length
facts for hom and inverse arrows of all six named unstable localization
isomorphisms at the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- By-kind descent-channel hom source count is its source rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.sourceImportedRectangles.length :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_sourceImportedRectangleCount_eq_length
    source
    target

/-- By-kind descent-channel hom target count is its target rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.targetImportedRectangles.length :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_targetImportedRectangleCount_eq_length
    source
    target

/-- By-kind descent-channel inverse source count is its source rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.sourceImportedRectangles.length :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_sourceImportedRectangleCount_eq_length
    source
    target

/-- By-kind descent-channel inverse target count is its target rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.targetImportedRectangles.length :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_targetImportedRectangleCount_eq_length
    source
    target

/-- By-kind descent-refinement hom source count is its source rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.sourceImportedRectangles.length :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_sourceImportedRectangleCount_eq_length
    source
    target

/-- By-kind descent-refinement hom target count is its target rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.targetImportedRectangles.length :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_targetImportedRectangleCount_eq_length
    source
    target

/-- By-kind descent-refinement inverse source count is its source rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.sourceImportedRectangles.length :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_sourceImportedRectangleCount_eq_length
    source
    target

/-- By-kind descent-refinement inverse target count is its target rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.targetImportedRectangles.length :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_targetImportedRectangleCount_eq_length
    source
    target

/-- By-kind descent-schedule hom source count is its source rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.sourceImportedRectangles.length :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_sourceImportedRectangleCount_eq_length
    source
    target

/-- By-kind descent-schedule hom target count is its target rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.targetImportedRectangles.length :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_targetImportedRectangleCount_eq_length
    source
    target

/-- By-kind descent-schedule inverse source count is its source rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.sourceImportedRectangles.length :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_sourceImportedRectangleCount_eq_length
    source
    target

/-- By-kind descent-schedule inverse target count is its target rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.targetImportedRectangles.length :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_targetImportedRectangleCount_eq_length
    source
    target

/-- By-kind interval-Stokes hom source count is its source rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.sourceImportedRectangles.length :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_sourceImportedRectangleCount_eq_length
    source
    target

/-- By-kind interval-Stokes hom target count is its target rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.targetImportedRectangles.length :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_targetImportedRectangleCount_eq_length
    source
    target

/-- By-kind interval-Stokes inverse source count is its source rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.sourceImportedRectangles.length :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_sourceImportedRectangleCount_eq_length
    source
    target

/-- By-kind interval-Stokes inverse target count is its target rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.targetImportedRectangles.length :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_targetImportedRectangleCount_eq_length
    source
    target

/-- By-kind interval-Fubini hom source count is its source rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.sourceImportedRectangles.length :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_sourceImportedRectangleCount_eq_length
    source
    target

/-- By-kind interval-Fubini hom target count is its target rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.targetImportedRectangles.length :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_targetImportedRectangleCount_eq_length
    source
    target

/-- By-kind interval-Fubini inverse source count is its source rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.sourceImportedRectangles.length :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_sourceImportedRectangleCount_eq_length
    source
    target

/-- By-kind interval-Fubini inverse target count is its target rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.targetImportedRectangles.length :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_targetImportedRectangleCount_eq_length
    source
    target

/-- By-kind Tate-weight-drop hom source count is its source rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.sourceImportedRectangles.length :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_sourceImportedRectangleCount_eq_length
    source
    target

/-- By-kind Tate-weight-drop hom target count is its target rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.targetImportedRectangles.length :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_targetImportedRectangleCount_eq_length
    source
    target

/-- By-kind Tate-weight-drop inverse source count is its source rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.sourceImportedRectangles.length :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_sourceImportedRectangleCount_eq_length
    source
    target

/-- By-kind Tate-weight-drop inverse target count is its target rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.targetImportedRectangles.length :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_targetImportedRectangleCount_eq_length
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
