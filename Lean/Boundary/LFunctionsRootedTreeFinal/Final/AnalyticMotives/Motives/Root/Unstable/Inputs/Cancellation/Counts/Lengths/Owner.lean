import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Unstable.Inputs.ByKind.Cancellation.Payload.ImportedRectangles.Lengths.Owner

/-!
# Root all-kind unstable cancellation endpoint count lengths

This file exposes endpoint imported-rectangle count-as-list-length facts for
all six named unstable localization cancellation composites.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- By-kind descent-channel hom-inverse endpoint count is its endpoint list length. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointImportedRectangles.length :=
  TraceUnstableAnalyticMotive.descentChannelIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    source
    target

/-- By-kind descent-channel inverse-hom endpoint count is its endpoint list length. -/
theorem TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointImportedRectangles.length :=
  TraceUnstableAnalyticMotive.descentChannelIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- By-kind descent-refinement hom-inverse endpoint count is its endpoint list length. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointImportedRectangles.length :=
  TraceUnstableAnalyticMotive.descentRefinementIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    source
    target

/-- By-kind descent-refinement inverse-hom endpoint count is its endpoint list length. -/
theorem TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointImportedRectangles.length :=
  TraceUnstableAnalyticMotive.descentRefinementIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- By-kind descent-schedule hom-inverse endpoint count is its endpoint list length. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointImportedRectangles.length :=
  TraceUnstableAnalyticMotive.descentScheduleIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    source
    target

/-- By-kind descent-schedule inverse-hom endpoint count is its endpoint list length. -/
theorem TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointImportedRectangles.length :=
  TraceUnstableAnalyticMotive.descentScheduleIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- By-kind interval-Stokes hom-inverse endpoint count is its endpoint list length. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointImportedRectangles.length :=
  TraceUnstableAnalyticMotive.intervalStokesIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    source
    target

/-- By-kind interval-Stokes inverse-hom endpoint count is its endpoint list length. -/
theorem TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointImportedRectangles.length :=
  TraceUnstableAnalyticMotive.intervalStokesIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- By-kind interval-Fubini hom-inverse endpoint count is its endpoint list length. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointImportedRectangles.length :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    source
    target

/-- By-kind interval-Fubini inverse-hom endpoint count is its endpoint list length. -/
theorem TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointImportedRectangles.length :=
  TraceUnstableAnalyticMotive.intervalFubiniIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- By-kind Tate-weight-drop hom-inverse endpoint count is its endpoint list length. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointImportedRectangles.length :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    source
    target

/-- By-kind Tate-weight-drop inverse-hom endpoint count is its endpoint list length. -/
theorem TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointImportedRectangles.length :=
  TraceUnstableAnalyticMotive.tateWeightDropIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
