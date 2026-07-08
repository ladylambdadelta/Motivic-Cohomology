import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Payload.ImportedRectangles.Counts.ArrowEndpoints.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.ImportedRectangles.Lengths.Owner

/-!
# Imported-rectangle arrow-endpoint length facts for unstable named isomorphisms

This file exposes source and target imported-rectangle count-as-length facts
through the hom and inverse arrows of the six named unstable analytic-motive
localization isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel unstable hom source count is its source rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.sourceImportedRectangles.length :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_sourceImportedRectangleCount_eq_length
    source
    target

/-- Descent-channel unstable hom target count is its target rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_hom_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom.targetImportedRectangles.length :=
  TraceLocalizationInput.descentChannelLocalizedIso_hom_targetImportedRectangleCount_eq_length
    source
    target

/-- Descent-channel unstable inverse source count is its source rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.sourceImportedRectangles.length :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_sourceImportedRectangleCount_eq_length
    source
    target

/-- Descent-channel unstable inverse target count is its target rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.descentChannelIso_inv_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv.targetImportedRectangles.length :=
  TraceLocalizationInput.descentChannelLocalizedIso_inv_targetImportedRectangleCount_eq_length
    source
    target

/-- Descent-refinement unstable hom source count is its source rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.sourceImportedRectangles.length :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_sourceImportedRectangleCount_eq_length
    source
    target

/-- Descent-refinement unstable hom target count is its target rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_hom_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom.targetImportedRectangles.length :=
  TraceLocalizationInput.descentRefinementLocalizedIso_hom_targetImportedRectangleCount_eq_length
    source
    target

/-- Descent-refinement unstable inverse source count is its source rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.sourceImportedRectangles.length :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_sourceImportedRectangleCount_eq_length
    source
    target

/-- Descent-refinement unstable inverse target count is its target rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.descentRefinementIso_inv_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv.targetImportedRectangles.length :=
  TraceLocalizationInput.descentRefinementLocalizedIso_inv_targetImportedRectangleCount_eq_length
    source
    target

/-- Descent-schedule unstable hom source count is its source rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.sourceImportedRectangles.length :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_sourceImportedRectangleCount_eq_length
    source
    target

/-- Descent-schedule unstable hom target count is its target rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_hom_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom.targetImportedRectangles.length :=
  TraceLocalizationInput.descentScheduleLocalizedIso_hom_targetImportedRectangleCount_eq_length
    source
    target

/-- Descent-schedule unstable inverse source count is its source rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.sourceImportedRectangles.length :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_sourceImportedRectangleCount_eq_length
    source
    target

/-- Descent-schedule unstable inverse target count is its target rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.descentScheduleIso_inv_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv.targetImportedRectangles.length :=
  TraceLocalizationInput.descentScheduleLocalizedIso_inv_targetImportedRectangleCount_eq_length
    source
    target

/-- Interval-Stokes unstable hom source count is its source rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.sourceImportedRectangles.length :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_sourceImportedRectangleCount_eq_length
    source
    target

/-- Interval-Stokes unstable hom target count is its target rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_hom_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom.targetImportedRectangles.length :=
  TraceLocalizationInput.intervalStokesLocalizedIso_hom_targetImportedRectangleCount_eq_length
    source
    target

/-- Interval-Stokes unstable inverse source count is its source rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.sourceImportedRectangles.length :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_sourceImportedRectangleCount_eq_length
    source
    target

/-- Interval-Stokes unstable inverse target count is its target rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.intervalStokesIso_inv_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv.targetImportedRectangles.length :=
  TraceLocalizationInput.intervalStokesLocalizedIso_inv_targetImportedRectangleCount_eq_length
    source
    target

/-- Interval-Fubini unstable hom source count is its source rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.sourceImportedRectangles.length :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_sourceImportedRectangleCount_eq_length
    source
    target

/-- Interval-Fubini unstable hom target count is its target rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_hom_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom.targetImportedRectangles.length :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_hom_targetImportedRectangleCount_eq_length
    source
    target

/-- Interval-Fubini unstable inverse source count is its source rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.sourceImportedRectangles.length :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_sourceImportedRectangleCount_eq_length
    source
    target

/-- Interval-Fubini unstable inverse target count is its target rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.intervalFubiniIso_inv_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv.targetImportedRectangles.length :=
  TraceLocalizationInput.intervalFubiniLocalizedIso_inv_targetImportedRectangleCount_eq_length
    source
    target

/-- Tate-weight-drop unstable hom source count is its source rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.sourceImportedRectangles.length :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_sourceImportedRectangleCount_eq_length
    source
    target

/-- Tate-weight-drop unstable hom target count is its target rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_hom_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom.targetImportedRectangles.length :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_hom_targetImportedRectangleCount_eq_length
    source
    target

/-- Tate-weight-drop unstable inverse source count is its source rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.sourceImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.sourceImportedRectangles.length :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_sourceImportedRectangleCount_eq_length
    source
    target

/-- Tate-weight-drop unstable inverse target count is its target rectangle-list length. -/
theorem TraceUnstableAnalyticMotive.tateWeightDropIso_inv_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.targetImportedRectangleCount =
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv.targetImportedRectangles.length :=
  TraceLocalizationInput.tateWeightDropLocalizedIso_inv_targetImportedRectangleCount_eq_length
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
