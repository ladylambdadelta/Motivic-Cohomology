import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Motives.Summary.LocalizationInput.NamedShortComplex.Owner

/-!
# Public named analytic-generator short-complex facade

This file exposes bounded cone short complexes and zero-composite facts for the
six concrete analytic localization generators at the public root surface.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Public root facade: the descent-channel bounded cone short complex. -/
def AnalyticMotivesRoot.rootFacade_descentChannel_boundedMappingConeShortComplex
    (source target : QTraceExpression) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  AnalyticMotivesRoot.rootSummary_descentChannel_boundedMappingConeShortComplex source target

/-- Public root facade: the descent-channel bounded cone short complex has zero composite. -/
theorem AnalyticMotivesRoot.rootFacade_descentChannel_boundedMappingConeShortComplex_zero
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeShortComplex.f ≫
        (TraceLocalizationInput.descentChannel source target).boundedMappingConeShortComplex.g =
      0 :=
  AnalyticMotivesRoot.rootSummary_descentChannel_boundedMappingConeShortComplex_zero source target

/-- Public root facade: the descent-refinement bounded cone short complex. -/
def AnalyticMotivesRoot.rootFacade_descentRefinement_boundedMappingConeShortComplex
    (source target : QTraceExpression) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  AnalyticMotivesRoot.rootSummary_descentRefinement_boundedMappingConeShortComplex source target

/-- Public root facade: the descent-refinement bounded cone short complex has zero composite. -/
theorem AnalyticMotivesRoot.rootFacade_descentRefinement_boundedMappingConeShortComplex_zero
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeShortComplex.f ≫
        (TraceLocalizationInput.descentRefinement source target).boundedMappingConeShortComplex.g =
      0 :=
  AnalyticMotivesRoot.rootSummary_descentRefinement_boundedMappingConeShortComplex_zero source target

/-- Public root facade: the descent-schedule bounded cone short complex. -/
def AnalyticMotivesRoot.rootFacade_descentSchedule_boundedMappingConeShortComplex
    (source target : QTraceExpression) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  AnalyticMotivesRoot.rootSummary_descentSchedule_boundedMappingConeShortComplex source target

/-- Public root facade: the descent-schedule bounded cone short complex has zero composite. -/
theorem AnalyticMotivesRoot.rootFacade_descentSchedule_boundedMappingConeShortComplex_zero
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeShortComplex.f ≫
        (TraceLocalizationInput.descentSchedule source target).boundedMappingConeShortComplex.g =
      0 :=
  AnalyticMotivesRoot.rootSummary_descentSchedule_boundedMappingConeShortComplex_zero source target

/-- Public root facade: the interval-Stokes bounded cone short complex. -/
def AnalyticMotivesRoot.rootFacade_intervalStokes_boundedMappingConeShortComplex
    (source target : QTraceExpression) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  AnalyticMotivesRoot.rootSummary_intervalStokes_boundedMappingConeShortComplex source target

/-- Public root facade: the interval-Stokes bounded cone short complex has zero composite. -/
theorem AnalyticMotivesRoot.rootFacade_intervalStokes_boundedMappingConeShortComplex_zero
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeShortComplex.f ≫
        (TraceLocalizationInput.intervalStokes source target).boundedMappingConeShortComplex.g =
      0 :=
  AnalyticMotivesRoot.rootSummary_intervalStokes_boundedMappingConeShortComplex_zero source target

/-- Public root facade: the interval-Fubini bounded cone short complex. -/
def AnalyticMotivesRoot.rootFacade_intervalFubini_boundedMappingConeShortComplex
    (source target : QTraceExpression) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  AnalyticMotivesRoot.rootSummary_intervalFubini_boundedMappingConeShortComplex source target

/-- Public root facade: the interval-Fubini bounded cone short complex has zero composite. -/
theorem AnalyticMotivesRoot.rootFacade_intervalFubini_boundedMappingConeShortComplex_zero
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeShortComplex.f ≫
        (TraceLocalizationInput.intervalFubini source target).boundedMappingConeShortComplex.g =
      0 :=
  AnalyticMotivesRoot.rootSummary_intervalFubini_boundedMappingConeShortComplex_zero source target

/-- Public root facade: the Tate-weight-drop bounded cone short complex. -/
def AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeShortComplex
    (source target : QTraceExpression) :
    ShortComplex TraceAnalyticAdditiveHomotopyCategory :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeShortComplex source target

/-- Public root facade: the Tate-weight-drop bounded cone short complex has zero composite. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeShortComplex_zero
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeShortComplex.f ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeShortComplex.g =
      0 :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeShortComplex_zero source target

end AnalyticMotives
end LFunctions
end Boundary
