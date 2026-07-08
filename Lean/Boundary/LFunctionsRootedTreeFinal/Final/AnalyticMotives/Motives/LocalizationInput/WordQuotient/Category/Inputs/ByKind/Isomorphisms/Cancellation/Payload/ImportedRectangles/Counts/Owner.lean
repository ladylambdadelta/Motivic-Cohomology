import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Cancellation.Payload.ImportedRectangles.Endpoint.Owner

/-!
# Imported-rectangle counts for named cancellation composites

This file specializes the generic input-cancellation imported-rectangle count
facts to the six named localization-input constructors.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel hom-inverse cancellation source count is the source endpoint count. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv).sourceImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceImportedRectangleCount
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel hom-inverse cancellation target count is the source endpoint count. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv).targetImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetImportedRectangleCount
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel inverse-hom cancellation source count is the target endpoint count. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom).sourceImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceImportedRectangleCount
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel inverse-hom cancellation target count is the target endpoint count. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom).targetImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetImportedRectangleCount
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement hom-inverse cancellation source count is the source endpoint count. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv).sourceImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceImportedRectangleCount
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement hom-inverse cancellation target count is the source endpoint count. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv).targetImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetImportedRectangleCount
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement inverse-hom cancellation source count is the target endpoint count. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom).sourceImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceImportedRectangleCount
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement inverse-hom cancellation target count is the target endpoint count. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom).targetImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetImportedRectangleCount
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule hom-inverse cancellation source count is the source endpoint count. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv).sourceImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceImportedRectangleCount
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule hom-inverse cancellation target count is the source endpoint count. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv).targetImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetImportedRectangleCount
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule inverse-hom cancellation source count is the target endpoint count. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom).sourceImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceImportedRectangleCount
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule inverse-hom cancellation target count is the target endpoint count. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom).targetImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetImportedRectangleCount
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes hom-inverse cancellation source count is the source endpoint count. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv).sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceImportedRectangleCount
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes hom-inverse cancellation target count is the source endpoint count. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv).targetImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetImportedRectangleCount
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes inverse-hom cancellation source count is the target endpoint count. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom).sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceImportedRectangleCount
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes inverse-hom cancellation target count is the target endpoint count. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom).targetImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetImportedRectangleCount
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini hom-inverse cancellation source count is the source endpoint count. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv).sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceImportedRectangleCount
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini hom-inverse cancellation target count is the source endpoint count. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv).targetImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetImportedRectangleCount
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini inverse-hom cancellation source count is the target endpoint count. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom).sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceImportedRectangleCount
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini inverse-hom cancellation target count is the target endpoint count. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom).targetImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetImportedRectangleCount
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop hom-inverse cancellation source count is the source endpoint count. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv).sourceImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceImportedRectangleCount
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop hom-inverse cancellation target count is the source endpoint count. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv).targetImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetImportedRectangleCount
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop inverse-hom cancellation source count is the target endpoint count. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom).sourceImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceImportedRectangleCount
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop inverse-hom cancellation target count is the target endpoint count. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom).targetImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.importedRectangleCount :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetImportedRectangleCount
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
