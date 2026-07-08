import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Arrows.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Payload.ImportedRectangles.Owner

/-!
# Imported finite-rectangle arrow-endpoint payload for named localized isomorphisms

This file exposes the concrete imported finite-rectangle source and target
payload through the hom and inverse arrows of the named by-kind localized
isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel isomorphism hom source rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).hom.sourceImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.descentChannelForwardArrow_sourceImportedRectangles
    source
    target

/-- Descent-channel isomorphism hom target rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).hom.targetImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangles :=
  TraceLocalizationInput.descentChannelForwardArrow_targetImportedRectangles
    source
    target

/-- Descent-channel isomorphism inverse source rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).inv.sourceImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangles :=
  TraceLocalizationInput.descentChannelInverseArrow_sourceImportedRectangles
    source
    target

/-- Descent-channel isomorphism inverse target rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).inv.targetImportedRectangles =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.descentChannelInverseArrow_targetImportedRectangles
    source
    target

/-- Descent-refinement isomorphism hom source rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).hom.sourceImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.descentRefinementForwardArrow_sourceImportedRectangles
    source
    target

/-- Descent-refinement isomorphism hom target rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).hom.targetImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangles :=
  TraceLocalizationInput.descentRefinementForwardArrow_targetImportedRectangles
    source
    target

/-- Descent-refinement isomorphism inverse source rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).inv.sourceImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangles :=
  TraceLocalizationInput.descentRefinementInverseArrow_sourceImportedRectangles
    source
    target

/-- Descent-refinement isomorphism inverse target rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).inv.targetImportedRectangles =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.descentRefinementInverseArrow_targetImportedRectangles
    source
    target

/-- Descent-schedule isomorphism hom source rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).hom.sourceImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.descentScheduleForwardArrow_sourceImportedRectangles
    source
    target

/-- Descent-schedule isomorphism hom target rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).hom.targetImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangles :=
  TraceLocalizationInput.descentScheduleForwardArrow_targetImportedRectangles
    source
    target

/-- Descent-schedule isomorphism inverse source rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).inv.sourceImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangles :=
  TraceLocalizationInput.descentScheduleInverseArrow_sourceImportedRectangles
    source
    target

/-- Descent-schedule isomorphism inverse target rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).inv.targetImportedRectangles =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.descentScheduleInverseArrow_targetImportedRectangles
    source
    target

/-- Interval-Stokes isomorphism hom source rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).hom.sourceImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.intervalStokesForwardArrow_sourceImportedRectangles
    source
    target

/-- Interval-Stokes isomorphism hom target rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).hom.targetImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangles :=
  TraceLocalizationInput.intervalStokesForwardArrow_targetImportedRectangles
    source
    target

/-- Interval-Stokes isomorphism inverse source rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).inv.sourceImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangles :=
  TraceLocalizationInput.intervalStokesInverseArrow_sourceImportedRectangles
    source
    target

/-- Interval-Stokes isomorphism inverse target rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).inv.targetImportedRectangles =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.intervalStokesInverseArrow_targetImportedRectangles
    source
    target

/-- Interval-Fubini isomorphism hom source rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).hom.sourceImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.intervalFubiniForwardArrow_sourceImportedRectangles
    source
    target

/-- Interval-Fubini isomorphism hom target rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).hom.targetImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangles :=
  TraceLocalizationInput.intervalFubiniForwardArrow_targetImportedRectangles
    source
    target

/-- Interval-Fubini isomorphism inverse source rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).inv.sourceImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangles :=
  TraceLocalizationInput.intervalFubiniInverseArrow_sourceImportedRectangles
    source
    target

/-- Interval-Fubini isomorphism inverse target rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).inv.targetImportedRectangles =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.intervalFubiniInverseArrow_targetImportedRectangles
    source
    target

/-- Tate-weight-drop isomorphism hom source rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).hom.sourceImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.tateWeightDropForwardArrow_sourceImportedRectangles
    source
    target

/-- Tate-weight-drop isomorphism hom target rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).hom.targetImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangles :=
  TraceLocalizationInput.tateWeightDropForwardArrow_targetImportedRectangles
    source
    target

/-- Tate-weight-drop isomorphism inverse source rectangles are the input target rectangles. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_sourceImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).inv.sourceImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangles :=
  TraceLocalizationInput.tateWeightDropInverseArrow_sourceImportedRectangles
    source
    target

/-- Tate-weight-drop isomorphism inverse target rectangles are the input source rectangles. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_targetImportedRectangles
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).inv.targetImportedRectangles =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangles :=
  TraceLocalizationInput.tateWeightDropInverseArrow_targetImportedRectangles
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
