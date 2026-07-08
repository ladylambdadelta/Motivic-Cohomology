import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.ImportedRectangles.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Payload.ImportedRectangles.Counts.Owner

/-!
# Imported finite-rectangle arrow-endpoint counts for named localized isomorphisms

This file exposes source and target imported-rectangle counts through the hom
and inverse arrows of the named by-kind localized isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel isomorphism hom source rectangle count is the input source count. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.descentChannelForwardArrow_sourceImportedRectangleCount
    source
    target

/-- Descent-channel isomorphism hom target rectangle count is the input target count. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.descentChannelForwardArrow_targetImportedRectangleCount
    source
    target

/-- Descent-channel isomorphism inverse source rectangle count is the input target count. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.descentChannelInverseArrow_sourceImportedRectangleCount
    source
    target

/-- Descent-channel isomorphism inverse target rectangle count is the input source count. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.descentChannel source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.descentChannelInverseArrow_targetImportedRectangleCount
    source
    target

/-- Descent-refinement isomorphism hom source rectangle count is the input source count. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.descentRefinementForwardArrow_sourceImportedRectangleCount
    source
    target

/-- Descent-refinement isomorphism hom target rectangle count is the input target count. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.descentRefinementForwardArrow_targetImportedRectangleCount
    source
    target

/-- Descent-refinement isomorphism inverse source rectangle count is the input target count. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.descentRefinementInverseArrow_sourceImportedRectangleCount
    source
    target

/-- Descent-refinement isomorphism inverse target rectangle count is the input source count. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.descentRefinement source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.descentRefinementInverseArrow_targetImportedRectangleCount
    source
    target

/-- Descent-schedule isomorphism hom source rectangle count is the input source count. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.descentScheduleForwardArrow_sourceImportedRectangleCount
    source
    target

/-- Descent-schedule isomorphism hom target rectangle count is the input target count. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.descentScheduleForwardArrow_targetImportedRectangleCount
    source
    target

/-- Descent-schedule isomorphism inverse source rectangle count is the input target count. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.descentScheduleInverseArrow_sourceImportedRectangleCount
    source
    target

/-- Descent-schedule isomorphism inverse target rectangle count is the input source count. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.descentSchedule source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.descentScheduleInverseArrow_targetImportedRectangleCount
    source
    target

/-- Interval-Stokes isomorphism hom source rectangle count is the input source count. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.intervalStokesForwardArrow_sourceImportedRectangleCount
    source
    target

/-- Interval-Stokes isomorphism hom target rectangle count is the input target count. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.intervalStokesForwardArrow_targetImportedRectangleCount
    source
    target

/-- Interval-Stokes isomorphism inverse source rectangle count is the input target count. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.intervalStokesInverseArrow_sourceImportedRectangleCount
    source
    target

/-- Interval-Stokes isomorphism inverse target rectangle count is the input source count. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.intervalStokes source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.intervalStokesInverseArrow_targetImportedRectangleCount
    source
    target

/-- Interval-Fubini isomorphism hom source rectangle count is the input source count. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.intervalFubiniForwardArrow_sourceImportedRectangleCount
    source
    target

/-- Interval-Fubini isomorphism hom target rectangle count is the input target count. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.intervalFubiniForwardArrow_targetImportedRectangleCount
    source
    target

/-- Interval-Fubini isomorphism inverse source rectangle count is the input target count. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.intervalFubiniInverseArrow_sourceImportedRectangleCount
    source
    target

/-- Interval-Fubini isomorphism inverse target rectangle count is the input source count. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.intervalFubini source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.intervalFubiniInverseArrow_targetImportedRectangleCount
    source
    target

/-- Tate-weight-drop isomorphism hom source rectangle count is the input source count. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.tateWeightDropForwardArrow_sourceImportedRectangleCount
    source
    target

/-- Tate-weight-drop isomorphism hom target rectangle count is the input target count. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.tateWeightDropForwardArrow_targetImportedRectangleCount
    source
    target

/-- Tate-weight-drop isomorphism inverse source rectangle count is the input target count. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_sourceImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).targetObject.importedRectangleCount :=
  TraceLocalizationInput.tateWeightDropInverseArrow_sourceImportedRectangleCount
    source
    target

/-- Tate-weight-drop isomorphism inverse target rectangle count is the input source count. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_targetImportedRectangleCount
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDrop source target).sourceObject.importedRectangleCount :=
  TraceLocalizationInput.tateWeightDropInverseArrow_targetImportedRectangleCount
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
