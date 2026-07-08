import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.ImportedRectangles.Lengths.ArrowEndpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.ImportedRectangles.Counts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.ImportedRectangles.Lengths.Endpoint.Owner

/-!
# By-kind unstable imported-rectangle length facts

This file exposes endpoint imported-rectangle count-as-length facts for the
six named unstable analytic-motive isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel unstable hom endpoint count is its endpoint rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).hom.endpointImportedRectangles.length :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- Descent-channel unstable inverse endpoint count is its endpoint rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso
        source
        target).inv.endpointImportedRectangles.length :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_endpointImportedRectangleCount_eq_length
    source
    target

/-- Descent-refinement unstable hom endpoint count is its endpoint rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).hom.endpointImportedRectangles.length :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- Descent-refinement unstable inverse endpoint count is its endpoint rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso
        source
        target).inv.endpointImportedRectangles.length :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_endpointImportedRectangleCount_eq_length
    source
    target

/-- Descent-schedule unstable hom endpoint count is its endpoint rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).hom.endpointImportedRectangles.length :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- Descent-schedule unstable inverse endpoint count is its endpoint rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso
        source
        target).inv.endpointImportedRectangles.length :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_endpointImportedRectangleCount_eq_length
    source
    target

/-- Interval-Stokes unstable hom endpoint count is its endpoint rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).hom.endpointImportedRectangles.length :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- Interval-Stokes unstable inverse endpoint count is its endpoint rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso
        source
        target).inv.endpointImportedRectangles.length :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_endpointImportedRectangleCount_eq_length
    source
    target

/-- Interval-Fubini unstable hom endpoint count is its endpoint rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).hom.endpointImportedRectangles.length :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- Interval-Fubini unstable inverse endpoint count is its endpoint rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso
        source
        target).inv.endpointImportedRectangles.length :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_endpointImportedRectangleCount_eq_length
    source
    target

/-- Tate-weight-drop unstable hom endpoint count is its endpoint rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).hom.endpointImportedRectangles.length :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- Tate-weight-drop unstable inverse endpoint count is its endpoint rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso
        source
        target).inv.endpointImportedRectangles.length :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_endpointImportedRectangleCount_eq_length
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
