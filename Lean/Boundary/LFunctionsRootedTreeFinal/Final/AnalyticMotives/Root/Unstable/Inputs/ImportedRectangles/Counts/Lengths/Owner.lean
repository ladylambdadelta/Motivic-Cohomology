import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ImportedRectangles.Counts.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Unstable.Inputs.ImportedRectangles.Counts.Lengths.ArrowEndpoints.Owner

/-!
# Top-root all-kind unstable input imported-rectangle count lengths

This file mirrors the motive-root endpoint imported-rectangle count-as-list-
length surface for hom and inverse arrows of all six named unstable
localization isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The root exposes by-kind descent-channel hom endpoint count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).hom.endpointImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind descent-channel inverse endpoint count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).inv.endpointImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_endpointImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind descent-refinement hom endpoint count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).hom.endpointImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind descent-refinement inverse endpoint count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).inv.endpointImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_endpointImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind descent-schedule hom endpoint count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).hom.endpointImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind descent-schedule inverse endpoint count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).inv.endpointImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_endpointImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind interval-Stokes hom endpoint count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).hom.endpointImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind interval-Stokes inverse endpoint count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).inv.endpointImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_endpointImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind interval-Fubini hom endpoint count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).hom.endpointImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind interval-Fubini inverse endpoint count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).inv.endpointImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_endpointImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind Tate-weight-drop hom endpoint count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).hom.endpointImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind Tate-weight-drop inverse endpoint count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).inv.endpointImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_endpointImportedRectangleCount_eq_length
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
