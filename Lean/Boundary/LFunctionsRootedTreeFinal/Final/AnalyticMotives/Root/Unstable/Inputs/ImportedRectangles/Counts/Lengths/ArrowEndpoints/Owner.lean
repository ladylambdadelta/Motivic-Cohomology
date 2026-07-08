import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ImportedRectangles.Counts.Lengths.ArrowEndpoints.Owner

/-!
# Top-root all-kind unstable input imported-rectangle arrow-endpoint count lengths

This file mirrors the motive-root source and target imported-rectangle
count-as-list-length surface for hom and inverse arrows of all six named
unstable localization isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The root exposes by-kind descent-channel hom source count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.sourceImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_sourceImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind descent-channel hom target count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.targetImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_targetImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind descent-channel inverse source count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.sourceImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_sourceImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind descent-channel inverse target count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.targetImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_targetImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind descent-refinement hom source count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.sourceImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_sourceImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind descent-refinement hom target count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.targetImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_targetImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind descent-refinement inverse source count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.sourceImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_sourceImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind descent-refinement inverse target count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.targetImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_targetImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind descent-schedule hom source count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.sourceImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_sourceImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind descent-schedule hom target count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.targetImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_targetImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind descent-schedule inverse source count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.sourceImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_sourceImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind descent-schedule inverse target count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.targetImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_targetImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind interval-Stokes hom source count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.sourceImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_sourceImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind interval-Stokes hom target count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.targetImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_targetImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind interval-Stokes inverse source count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.sourceImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_sourceImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind interval-Stokes inverse target count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.targetImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_targetImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind interval-Fubini hom source count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.sourceImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_sourceImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind interval-Fubini hom target count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.targetImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_targetImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind interval-Fubini inverse source count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.sourceImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_sourceImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind interval-Fubini inverse target count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.targetImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_targetImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind Tate-weight-drop hom source count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.sourceImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_sourceImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind Tate-weight-drop hom target count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.targetImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_targetImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind Tate-weight-drop inverse source count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.sourceImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_sourceImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind Tate-weight-drop inverse target count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.targetImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_targetImportedRectangleCount_eq_length
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
