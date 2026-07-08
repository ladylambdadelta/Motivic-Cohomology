import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Cancellation.Payload.ImportedRectangles.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Cancellation.Owner

/-!
# Endpoint imported-rectangle length facts for named cancellation composites

This file specializes endpoint imported-rectangle count/length facts to the
six named localization-input cancellation isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel hom-inverse cancellation endpoint count is the endpoint rectangle-list length. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentChannelLocalizedIso source target).hom
        (TraceLocalizationInput.descentChannelLocalizedIso source target).inv).endpointImportedRectangles.length :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel inverse-hom cancellation endpoint count is the endpoint rectangle-list length. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentChannelLocalizedIso source target).inv
        (TraceLocalizationInput.descentChannelLocalizedIso source target).hom).endpointImportedRectangles.length :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement hom-inverse cancellation endpoint count is the endpoint rectangle-list length. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv).endpointImportedRectangles.length :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement inverse-hom cancellation endpoint count is the endpoint rectangle-list length. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv
        (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom).endpointImportedRectangles.length :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule hom-inverse cancellation endpoint count is the endpoint rectangle-list length. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv).endpointImportedRectangles.length :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule inverse-hom cancellation endpoint count is the endpoint rectangle-list length. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv
        (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom).endpointImportedRectangles.length :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes hom-inverse cancellation endpoint count is the endpoint rectangle-list length. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv).endpointImportedRectangles.length :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes inverse-hom cancellation endpoint count is the endpoint rectangle-list length. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv
        (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom).endpointImportedRectangles.length :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini hom-inverse cancellation endpoint count is the endpoint rectangle-list length. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv).endpointImportedRectangles.length :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini inverse-hom cancellation endpoint count is the endpoint rectangle-list length. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv
        (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom).endpointImportedRectangles.length :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop hom-inverse cancellation endpoint count is the endpoint rectangle-list length. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv).endpointImportedRectangles.length :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop inverse-hom cancellation endpoint count is the endpoint rectangle-list length. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv
        (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom).endpointImportedRectangles.length :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
