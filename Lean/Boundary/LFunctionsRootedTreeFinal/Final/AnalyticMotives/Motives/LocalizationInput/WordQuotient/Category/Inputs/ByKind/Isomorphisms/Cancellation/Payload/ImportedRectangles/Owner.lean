import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.Cancellation.Payload.ImportedRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Cancellation.Payload.ImportedRectangles.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Cancellation.Payload.ImportedRectangles.LedgerCounts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Cancellation.Payload.ImportedRectangles.LedgerRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Cancellation.Payload.ImportedRectangles.Endpoint.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Cancellation.Payload.ImportedRectangles.Counts.Owner

/-!
# Imported-rectangle payload for named cancellation composites

This file specializes the generic input-cancellation imported-rectangle list
facts to the six named localization-input constructors.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel hom-inverse cancellation source rectangles are the source endpoint rectangles. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv).sourceImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceImportedRectangles
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel hom-inverse cancellation target rectangles are the source endpoint rectangles. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_comp_inv_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv).targetImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).localizedSourceObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetImportedRectangles
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel inverse-hom cancellation source rectangles are the target endpoint rectangles. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom).sourceImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceImportedRectangles
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-channel inverse-hom cancellation target rectangles are the target endpoint rectangles. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_comp_hom_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentChannelLocalizedIso source target).inv
      (TraceLocalizationInput.descentChannelLocalizedIso source target).hom).targetImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).localizedTargetObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetImportedRectangles
    (TraceLocalizationInput.descentChannel source target)

/-- Descent-refinement hom-inverse cancellation source rectangles are the source endpoint rectangles. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv).sourceImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceImportedRectangles
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement hom-inverse cancellation target rectangles are the source endpoint rectangles. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_comp_inv_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv).targetImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).localizedSourceObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetImportedRectangles
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement inverse-hom cancellation source rectangles are the target endpoint rectangles. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom).sourceImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceImportedRectangles
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-refinement inverse-hom cancellation target rectangles are the target endpoint rectangles. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_comp_hom_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).inv
      (TraceLocalizationInput.descentRefinementLocalizedIso source target).hom).targetImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).localizedTargetObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetImportedRectangles
    (TraceLocalizationInput.descentRefinement source target)

/-- Descent-schedule hom-inverse cancellation source rectangles are the source endpoint rectangles. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv).sourceImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceImportedRectangles
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule hom-inverse cancellation target rectangles are the source endpoint rectangles. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_comp_inv_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv).targetImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).localizedSourceObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetImportedRectangles
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule inverse-hom cancellation source rectangles are the target endpoint rectangles. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom).sourceImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceImportedRectangles
    (TraceLocalizationInput.descentSchedule source target)

/-- Descent-schedule inverse-hom cancellation target rectangles are the target endpoint rectangles. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_comp_hom_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).inv
      (TraceLocalizationInput.descentScheduleLocalizedIso source target).hom).targetImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).localizedTargetObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetImportedRectangles
    (TraceLocalizationInput.descentSchedule source target)

/-- Interval-Stokes hom-inverse cancellation source rectangles are the source endpoint rectangles. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv).sourceImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceImportedRectangles
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes hom-inverse cancellation target rectangles are the source endpoint rectangles. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_comp_inv_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv).targetImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).localizedSourceObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetImportedRectangles
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes inverse-hom cancellation source rectangles are the target endpoint rectangles. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom).sourceImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceImportedRectangles
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Stokes inverse-hom cancellation target rectangles are the target endpoint rectangles. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_comp_hom_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).inv
      (TraceLocalizationInput.intervalStokesLocalizedIso source target).hom).targetImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).localizedTargetObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetImportedRectangles
    (TraceLocalizationInput.intervalStokes source target)

/-- Interval-Fubini hom-inverse cancellation source rectangles are the source endpoint rectangles. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv).sourceImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceImportedRectangles
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini hom-inverse cancellation target rectangles are the source endpoint rectangles. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_comp_inv_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv).targetImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).localizedSourceObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetImportedRectangles
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini inverse-hom cancellation source rectangles are the target endpoint rectangles. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom).sourceImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceImportedRectangles
    (TraceLocalizationInput.intervalFubini source target)

/-- Interval-Fubini inverse-hom cancellation target rectangles are the target endpoint rectangles. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_comp_hom_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).inv
      (TraceLocalizationInput.intervalFubiniLocalizedIso source target).hom).targetImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).localizedTargetObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetImportedRectangles
    (TraceLocalizationInput.intervalFubini source target)

/-- Tate-weight-drop hom-inverse cancellation source rectangles are the source endpoint rectangles. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv).sourceImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_sourceImportedRectangles
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop hom-inverse cancellation target rectangles are the source endpoint rectangles. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_comp_inv_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv).targetImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).localizedSourceObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_hom_comp_inv_targetImportedRectangles
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop inverse-hom cancellation source rectangles are the target endpoint rectangles. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom).sourceImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_sourceImportedRectangles
    (TraceLocalizationInput.tateWeightDrop source target)

/-- Tate-weight-drop inverse-hom cancellation target rectangles are the target endpoint rectangles. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_comp_hom_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).inv
      (TraceLocalizationInput.tateWeightDropLocalizedIso source target).hom).targetImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).localizedTargetObject.importedRectangles :=
  TraceLocalizationInput.localizedIso_inv_comp_hom_targetImportedRectangles
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
