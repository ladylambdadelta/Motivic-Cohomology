import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.ImportedRectangles.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.ImportedRectangles.Counts.Lengths.ArrowEndpoints.Owner

/-!
# Root all-kind unstable input imported-rectangle count lengths

This file exposes endpoint imported-rectangle count-as-list-length facts for
hom and inverse arrows of all six named unstable localization isomorphisms at
the motive-root namespace.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- By-kind descent-channel hom endpoint count is its endpoint rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).hom.endpointImportedRectangles.length :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- By-kind descent-channel inverse endpoint count is its endpoint rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).inv.endpointImportedRectangles.length :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_endpointImportedRectangleCount_eq_length
    source
    target

/-- By-kind descent-refinement hom endpoint count is its endpoint rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).hom.endpointImportedRectangles.length :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- By-kind descent-refinement inverse endpoint count is its endpoint rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).inv.endpointImportedRectangles.length :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_endpointImportedRectangleCount_eq_length
    source
    target

/-- By-kind descent-schedule hom endpoint count is its endpoint rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).hom.endpointImportedRectangles.length :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- By-kind descent-schedule inverse endpoint count is its endpoint rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).inv.endpointImportedRectangles.length :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_endpointImportedRectangleCount_eq_length
    source
    target

/-- By-kind interval-Stokes hom endpoint count is its endpoint rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).hom.endpointImportedRectangles.length :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- By-kind interval-Stokes inverse endpoint count is its endpoint rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).inv.endpointImportedRectangles.length :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_endpointImportedRectangleCount_eq_length
    source
    target

/-- By-kind interval-Fubini hom endpoint count is its endpoint rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).hom.endpointImportedRectangles.length :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- By-kind interval-Fubini inverse endpoint count is its endpoint rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).inv.endpointImportedRectangles.length :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_endpointImportedRectangleCount_eq_length
    source
    target

/-- By-kind Tate-weight-drop hom endpoint count is its endpoint rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).hom.endpointImportedRectangles.length :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- By-kind Tate-weight-drop inverse endpoint count is its endpoint rectangle-list length. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).inv.endpointImportedRectangles.length :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_endpointImportedRectangleCount_eq_length
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
