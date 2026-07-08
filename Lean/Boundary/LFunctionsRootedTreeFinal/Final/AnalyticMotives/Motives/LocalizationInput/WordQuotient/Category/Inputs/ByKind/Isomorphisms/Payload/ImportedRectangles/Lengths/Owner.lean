import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.ImportedRectangles.Counts.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Payload.ImportedRectangles.Lengths.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.LocalizationInput.WordQuotient.Category.Inputs.ByKind.Isomorphisms.Payload.ImportedRectangles.Lengths.Endpoint.Owner

/-!
# Length facts for named localized-isomorphism rectangle payload

This file exposes endpoint count-equals-list-length facts for imported
finite-rectangle payload through the hom and inverse arrows of the named
by-kind localized isomorphisms.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Descent-channel isomorphism hom source count is its source rectangle-list length. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentChannelLocalizedIso
        source
        target).hom.sourceImportedRectangles.length :=
  TraceLocalizationInput.descentChannelForwardArrow_sourceImportedRectangleCount_eq_length
    source
    target

/-- Descent-channel isomorphism hom target count is its target rectangle-list length. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_hom_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.descentChannelLocalizedIso
        source
        target).hom.targetImportedRectangles.length :=
  TraceLocalizationInput.descentChannelForwardArrow_targetImportedRectangleCount_eq_length
    source
    target

/-- Descent-channel isomorphism inverse source count is its source rectangle-list length. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentChannelLocalizedIso
        source
        target).inv.sourceImportedRectangles.length :=
  TraceLocalizationInput.descentChannelInverseArrow_sourceImportedRectangleCount_eq_length
    source
    target

/-- Descent-channel isomorphism inverse target count is its target rectangle-list length. -/
theorem TraceLocalizationInput.descentChannelLocalizedIso_inv_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannelLocalizedIso
      source
      target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.descentChannelLocalizedIso
        source
        target).inv.targetImportedRectangles.length :=
  TraceLocalizationInput.descentChannelInverseArrow_targetImportedRectangleCount_eq_length
    source
    target

/-- Descent-refinement isomorphism hom source count is its source rectangle-list length. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentRefinementLocalizedIso
        source
        target).hom.sourceImportedRectangles.length :=
  TraceLocalizationInput.descentRefinementForwardArrow_sourceImportedRectangleCount_eq_length
    source
    target

/-- Descent-refinement isomorphism hom target count is its target rectangle-list length. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_hom_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.descentRefinementLocalizedIso
        source
        target).hom.targetImportedRectangles.length :=
  TraceLocalizationInput.descentRefinementForwardArrow_targetImportedRectangleCount_eq_length
    source
    target

/-- Descent-refinement isomorphism inverse source count is its source rectangle-list length. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentRefinementLocalizedIso
        source
        target).inv.sourceImportedRectangles.length :=
  TraceLocalizationInput.descentRefinementInverseArrow_sourceImportedRectangleCount_eq_length
    source
    target

/-- Descent-refinement isomorphism inverse target count is its target rectangle-list length. -/
theorem TraceLocalizationInput.descentRefinementLocalizedIso_inv_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinementLocalizedIso
      source
      target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.descentRefinementLocalizedIso
        source
        target).inv.targetImportedRectangles.length :=
  TraceLocalizationInput.descentRefinementInverseArrow_targetImportedRectangleCount_eq_length
    source
    target

/-- Descent-schedule isomorphism hom source count is its source rectangle-list length. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentScheduleLocalizedIso
        source
        target).hom.sourceImportedRectangles.length :=
  TraceLocalizationInput.descentScheduleForwardArrow_sourceImportedRectangleCount_eq_length
    source
    target

/-- Descent-schedule isomorphism hom target count is its target rectangle-list length. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_hom_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.descentScheduleLocalizedIso
        source
        target).hom.targetImportedRectangles.length :=
  TraceLocalizationInput.descentScheduleForwardArrow_targetImportedRectangleCount_eq_length
    source
    target

/-- Descent-schedule isomorphism inverse source count is its source rectangle-list length. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.descentScheduleLocalizedIso
        source
        target).inv.sourceImportedRectangles.length :=
  TraceLocalizationInput.descentScheduleInverseArrow_sourceImportedRectangleCount_eq_length
    source
    target

/-- Descent-schedule isomorphism inverse target count is its target rectangle-list length. -/
theorem TraceLocalizationInput.descentScheduleLocalizedIso_inv_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentScheduleLocalizedIso
      source
      target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.descentScheduleLocalizedIso
        source
        target).inv.targetImportedRectangles.length :=
  TraceLocalizationInput.descentScheduleInverseArrow_targetImportedRectangleCount_eq_length
    source
    target

/-- Interval-Stokes isomorphism hom source count is its source rectangle-list length. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalStokesLocalizedIso
        source
        target).hom.sourceImportedRectangles.length :=
  TraceLocalizationInput.intervalStokesForwardArrow_sourceImportedRectangleCount_eq_length
    source
    target

/-- Interval-Stokes isomorphism hom target count is its target rectangle-list length. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_hom_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.intervalStokesLocalizedIso
        source
        target).hom.targetImportedRectangles.length :=
  TraceLocalizationInput.intervalStokesForwardArrow_targetImportedRectangleCount_eq_length
    source
    target

/-- Interval-Stokes isomorphism inverse source count is its source rectangle-list length. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalStokesLocalizedIso
        source
        target).inv.sourceImportedRectangles.length :=
  TraceLocalizationInput.intervalStokesInverseArrow_sourceImportedRectangleCount_eq_length
    source
    target

/-- Interval-Stokes isomorphism inverse target count is its target rectangle-list length. -/
theorem TraceLocalizationInput.intervalStokesLocalizedIso_inv_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokesLocalizedIso
      source
      target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.intervalStokesLocalizedIso
        source
        target).inv.targetImportedRectangles.length :=
  TraceLocalizationInput.intervalStokesInverseArrow_targetImportedRectangleCount_eq_length
    source
    target

/-- Interval-Fubini isomorphism hom source count is its source rectangle-list length. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalFubiniLocalizedIso
        source
        target).hom.sourceImportedRectangles.length :=
  TraceLocalizationInput.intervalFubiniForwardArrow_sourceImportedRectangleCount_eq_length
    source
    target

/-- Interval-Fubini isomorphism hom target count is its target rectangle-list length. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_hom_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.intervalFubiniLocalizedIso
        source
        target).hom.targetImportedRectangles.length :=
  TraceLocalizationInput.intervalFubiniForwardArrow_targetImportedRectangleCount_eq_length
    source
    target

/-- Interval-Fubini isomorphism inverse source count is its source rectangle-list length. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.intervalFubiniLocalizedIso
        source
        target).inv.sourceImportedRectangles.length :=
  TraceLocalizationInput.intervalFubiniInverseArrow_sourceImportedRectangleCount_eq_length
    source
    target

/-- Interval-Fubini isomorphism inverse target count is its target rectangle-list length. -/
theorem TraceLocalizationInput.intervalFubiniLocalizedIso_inv_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubiniLocalizedIso
      source
      target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.intervalFubiniLocalizedIso
        source
        target).inv.targetImportedRectangles.length :=
  TraceLocalizationInput.intervalFubiniInverseArrow_targetImportedRectangleCount_eq_length
    source
    target

/-- Tate-weight-drop isomorphism hom source count is its source rectangle-list length. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).hom.sourceImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDropLocalizedIso
        source
        target).hom.sourceImportedRectangles.length :=
  TraceLocalizationInput.tateWeightDropForwardArrow_sourceImportedRectangleCount_eq_length
    source
    target

/-- Tate-weight-drop isomorphism hom target count is its target rectangle-list length. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_hom_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).hom.targetImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDropLocalizedIso
        source
        target).hom.targetImportedRectangles.length :=
  TraceLocalizationInput.tateWeightDropForwardArrow_targetImportedRectangleCount_eq_length
    source
    target

/-- Tate-weight-drop isomorphism inverse source count is its source rectangle-list length. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_sourceImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).inv.sourceImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDropLocalizedIso
        source
        target).inv.sourceImportedRectangles.length :=
  TraceLocalizationInput.tateWeightDropInverseArrow_sourceImportedRectangleCount_eq_length
    source
    target

/-- Tate-weight-drop isomorphism inverse target count is its target rectangle-list length. -/
theorem TraceLocalizationInput.tateWeightDropLocalizedIso_inv_targetImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDropLocalizedIso
      source
      target).inv.targetImportedRectangleCount =
      (TraceLocalizationInput.tateWeightDropLocalizedIso
        source
        target).inv.targetImportedRectangles.length :=
  TraceLocalizationInput.tateWeightDropInverseArrow_targetImportedRectangleCount_eq_length
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
