import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Unstable.Inputs.Cancellation.Counts.Lengths.Owner

/-!
# Top-root all-kind unstable cancellation endpoint count lengths

This file mirrors endpoint imported-rectangle count-as-list-length facts for
all six named unstable localization cancellation composites.
-/

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The root exposes by-kind descent-channel hom-inverse count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv).endpointImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind descent-channel inverse-hom count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindDescentChannelIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
      (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentChannelIso source target).inv
        (TraceUnstableAnalyticMotive.descentChannelIso source target).hom).endpointImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindDescentChannelIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind descent-refinement hom-inverse count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv).endpointImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind descent-refinement inverse-hom count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindDescentRefinementIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
      (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).inv
        (TraceUnstableAnalyticMotive.descentRefinementIso source target).hom).endpointImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindDescentRefinementIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind descent-schedule hom-inverse count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv).endpointImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind descent-schedule inverse-hom count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindDescentScheduleIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
      (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).inv
        (TraceUnstableAnalyticMotive.descentScheduleIso source target).hom).endpointImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindDescentScheduleIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind interval-Stokes hom-inverse count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv).endpointImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind interval-Stokes inverse-hom count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalStokesIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
      (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).inv
        (TraceUnstableAnalyticMotive.intervalStokesIso source target).hom).endpointImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindIntervalStokesIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind interval-Fubini hom-inverse count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv).endpointImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind interval-Fubini inverse-hom count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindIntervalFubiniIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
      (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).inv
        (TraceUnstableAnalyticMotive.intervalFubiniIso source target).hom).endpointImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindIntervalFubiniIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind Tate-weight-drop hom-inverse count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv).endpointImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_hom_comp_inv_endpointImportedRectangleCount_eq_length
    source
    target

/-- The root exposes by-kind Tate-weight-drop inverse-hom count-as-length. -/
theorem AnalyticMotivesRoot.unstableByKindTateWeightDropIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    (source target : QTraceExpression) :
    (TraceLocalizationWordClass.comp
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
      (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointImportedRectangleCount =
      (TraceLocalizationWordClass.comp
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).inv
        (TraceUnstableAnalyticMotive.tateWeightDropIso source target).hom).endpointImportedRectangles.length :=
  TraceAnalyticMotive.unstableByKindTateWeightDropIso_inv_comp_hom_endpointImportedRectangleCount_eq_length
    source
    target

end AnalyticMotives
end LFunctions
end Boundary
