import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Cancellation.Payload.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Cancellation.Payload.ImportedRectangles.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Cancellation.Payload.ImportedRectangles.LedgerCounts.Owner

/-!
# Endpoint imported-rectangle payload for named cancellation composites

This file specializes endpoint imported-rectangle facts for the six named
localization-input cancellation composites.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel hom-inverse cancellation endpoint rectangles are source rectangles twice. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.importedRectangles ++
        (TraceLocalizationInput.descentChannel source target).localizedSourceObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangles
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel inverse-hom cancellation endpoint rectangles are target rectangles twice. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.importedRectangles ++
        (TraceLocalizationInput.descentChannel source target).localizedTargetObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangles
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement hom-inverse cancellation endpoint rectangles are source rectangles twice. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.importedRectangles ++
        (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangles
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement inverse-hom cancellation endpoint rectangles are target rectangles twice. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.importedRectangles ++
        (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangles
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule hom-inverse cancellation endpoint rectangles are source rectangles twice. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.importedRectangles ++
        (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangles
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule inverse-hom cancellation endpoint rectangles are target rectangles twice. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.importedRectangles ++
        (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangles
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes hom-inverse cancellation endpoint rectangles are source rectangles twice. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.importedRectangles ++
        (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangles
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes inverse-hom cancellation endpoint rectangles are target rectangles twice. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.importedRectangles ++
        (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangles
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini hom-inverse cancellation endpoint rectangles are source rectangles twice. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.importedRectangles ++
        (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangles
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini inverse-hom cancellation endpoint rectangles are target rectangles twice. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.importedRectangles ++
        (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangles
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop hom-inverse cancellation endpoint rectangles are source rectangles twice. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv).endpointImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.importedRectangles ++
        (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangles
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop inverse-hom cancellation endpoint rectangles are target rectangles twice. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_endpointImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom).endpointImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.importedRectangles ++
        (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangles
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Descent-channel hom-inverse cancellation endpoint count is source count twice. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.importedRectangleCount +
        (TraceLocalizationInput.descentChannel source target).localizedSourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangleCount
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel inverse-hom cancellation endpoint count is target count twice. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.importedRectangleCount +
        (TraceLocalizationInput.descentChannel source target).localizedTargetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangleCount
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement hom-inverse cancellation endpoint count is source count twice. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.importedRectangleCount +
        (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangleCount
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement inverse-hom cancellation endpoint count is target count twice. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.importedRectangleCount +
        (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangleCount
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule hom-inverse cancellation endpoint count is source count twice. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.importedRectangleCount +
        (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangleCount
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule inverse-hom cancellation endpoint count is target count twice. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.importedRectangleCount +
        (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangleCount
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes hom-inverse cancellation endpoint count is source count twice. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.importedRectangleCount +
        (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangleCount
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes inverse-hom cancellation endpoint count is target count twice. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.importedRectangleCount +
        (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangleCount
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini hom-inverse cancellation endpoint count is source count twice. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.importedRectangleCount +
        (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangleCount
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini inverse-hom cancellation endpoint count is target count twice. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.importedRectangleCount +
        (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangleCount
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop hom-inverse cancellation endpoint count is source count twice. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.importedRectangleCount +
        (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_endpointImportedRectangleCount
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop inverse-hom cancellation endpoint count is target count twice. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_endpointImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.importedRectangleCount +
        (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_endpointImportedRectangleCount
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
