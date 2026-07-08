import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.ImportedRectangles.Counts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Payload.ImportedRectangles.Lengths.Owner

/-!
# Endpoint imported-rectangle length facts for named localized isomorphisms

This file owns endpoint imported-rectangle count-as-length facts for the hom
and inverse arrows of the named localized isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel isomorphism hom endpoint count is its endpoint rectangle-list length. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentChannelLocalizedIso
        source
        target).hom.endpointImportedRectangles.length :=
  TraceLocalizationInput.descentChannelForwardArrow_endpointImportedRectangleCount_eq_length
    source
    target

/-- Descent-channel isomorphism inverse endpoint count is its endpoint rectangle-list length. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentChannelLocalizedIso
        source
        target).inv.endpointImportedRectangles.length :=
  TraceLocalizationInput.descentChannelInverseArrow_endpointImportedRectangleCount_eq_length
    source
    target

/-- Descent-refinement isomorphism hom endpoint count is its endpoint rectangle-list length. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentRefinementLocalizedIso
        source
        target).hom.endpointImportedRectangles.length :=
  TraceLocalizationInput.descentRefinementForwardArrow_endpointImportedRectangleCount_eq_length
    source
    target

/-- Descent-refinement isomorphism inverse endpoint count is its endpoint rectangle-list length. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentRefinementLocalizedIso
        source
        target).inv.endpointImportedRectangles.length :=
  TraceLocalizationInput.descentRefinementInverseArrow_endpointImportedRectangleCount_eq_length
    source
    target

/-- Descent-schedule isomorphism hom endpoint count is its endpoint rectangle-list length. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentScheduleLocalizedIso
        source
        target).hom.endpointImportedRectangles.length :=
  TraceLocalizationInput.descentScheduleForwardArrow_endpointImportedRectangleCount_eq_length
    source
    target

/-- Descent-schedule isomorphism inverse endpoint count is its endpoint rectangle-list length. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.descentScheduleLocalizedIso
        source
        target).inv.endpointImportedRectangles.length :=
  TraceLocalizationInput.descentScheduleInverseArrow_endpointImportedRectangleCount_eq_length
    source
    target

/-- Interval-Stokes isomorphism hom endpoint count is its endpoint rectangle-list length. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalStokesLocalizedIso
        source
        target).hom.endpointImportedRectangles.length :=
  TraceLocalizationInput.intervalStokesForwardArrow_endpointImportedRectangleCount_eq_length
    source
    target

/-- Interval-Stokes isomorphism inverse endpoint count is its endpoint rectangle-list length. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalStokesLocalizedIso
        source
        target).inv.endpointImportedRectangles.length :=
  TraceLocalizationInput.intervalStokesInverseArrow_endpointImportedRectangleCount_eq_length
    source
    target

/-- Interval-Fubini isomorphism hom endpoint count is its endpoint rectangle-list length. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalFubiniLocalizedIso
        source
        target).hom.endpointImportedRectangles.length :=
  TraceLocalizationInput.intervalFubiniForwardArrow_endpointImportedRectangleCount_eq_length
    source
    target

/-- Interval-Fubini isomorphism inverse endpoint count is its endpoint rectangle-list length. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalFubiniLocalizedIso
        source
        target).inv.endpointImportedRectangles.length :=
  TraceLocalizationInput.intervalFubiniInverseArrow_endpointImportedRectangleCount_eq_length
    source
    target

/-- Tate-weight-drop isomorphism hom endpoint count is its endpoint rectangle-list length. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).hom.endpointImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDropLocalizedIso
        source
        target).hom.endpointImportedRectangles.length :=
  TraceLocalizationInput.tateWeightDropForwardArrow_endpointImportedRectangleCount_eq_length
    source
    target

/-- Tate-weight-drop isomorphism inverse endpoint count is its endpoint rectangle-list length. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).inv.endpointImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDropLocalizedIso
        source
        target).inv.endpointImportedRectangles.length :=
  TraceLocalizationInput.tateWeightDropInverseArrow_endpointImportedRectangleCount_eq_length
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
