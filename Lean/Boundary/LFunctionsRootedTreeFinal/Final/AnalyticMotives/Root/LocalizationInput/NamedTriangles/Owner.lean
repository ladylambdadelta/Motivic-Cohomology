import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Motives.Summary.LocalizationInput.NamedTriangles.Owner

/-!
# Public named analytic-generator cone triangle facade

This file exposes named analytic-generator bounded cone triangles at the public
root surface.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Public root facade: the descent-channel bounded cone triangle. -/
def AnalyticMotivesRoot.rootFacade_descentChannel_boundedMappingConeTriangle
    (source target : QTraceExpression) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle
      (TraceLocalizationInput.descentChannel source target).additiveComplexCommonWeightBound :=
  AnalyticMotivesRoot.rootSummary_descentChannel_boundedMappingConeTriangle source target

/-- Public root facade: the descent-channel bounded cone triangle is distinguished. -/
theorem AnalyticMotivesRoot.rootFacade_descentChannel_boundedMappingConeTriangle_distinguished
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  AnalyticMotivesRoot.rootSummary_descentChannel_boundedMappingConeTriangle_distinguished source target

/-- Public root facade: the descent-refinement bounded cone triangle. -/
def AnalyticMotivesRoot.rootFacade_descentRefinement_boundedMappingConeTriangle
    (source target : QTraceExpression) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle
      (TraceLocalizationInput.descentRefinement source target).additiveComplexCommonWeightBound :=
  AnalyticMotivesRoot.rootSummary_descentRefinement_boundedMappingConeTriangle source target

/-- Public root facade: the descent-refinement bounded cone triangle is distinguished. -/
theorem AnalyticMotivesRoot.rootFacade_descentRefinement_boundedMappingConeTriangle_distinguished
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  AnalyticMotivesRoot.rootSummary_descentRefinement_boundedMappingConeTriangle_distinguished source target

/-- Public root facade: the descent-schedule bounded cone triangle. -/
def AnalyticMotivesRoot.rootFacade_descentSchedule_boundedMappingConeTriangle
    (source target : QTraceExpression) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle
      (TraceLocalizationInput.descentSchedule source target).additiveComplexCommonWeightBound :=
  AnalyticMotivesRoot.rootSummary_descentSchedule_boundedMappingConeTriangle source target

/-- Public root facade: the descent-schedule bounded cone triangle is distinguished. -/
theorem AnalyticMotivesRoot.rootFacade_descentSchedule_boundedMappingConeTriangle_distinguished
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  AnalyticMotivesRoot.rootSummary_descentSchedule_boundedMappingConeTriangle_distinguished source target

/-- Public root facade: the interval-Stokes bounded cone triangle. -/
def AnalyticMotivesRoot.rootFacade_intervalStokes_boundedMappingConeTriangle
    (source target : QTraceExpression) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle
      (TraceLocalizationInput.intervalStokes source target).additiveComplexCommonWeightBound :=
  AnalyticMotivesRoot.rootSummary_intervalStokes_boundedMappingConeTriangle source target

/-- Public root facade: the interval-Stokes bounded cone triangle is distinguished. -/
theorem AnalyticMotivesRoot.rootFacade_intervalStokes_boundedMappingConeTriangle_distinguished
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  AnalyticMotivesRoot.rootSummary_intervalStokes_boundedMappingConeTriangle_distinguished source target

/-- Public root facade: the interval-Fubini bounded cone triangle. -/
def AnalyticMotivesRoot.rootFacade_intervalFubini_boundedMappingConeTriangle
    (source target : QTraceExpression) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle
      (TraceLocalizationInput.intervalFubini source target).additiveComplexCommonWeightBound :=
  AnalyticMotivesRoot.rootSummary_intervalFubini_boundedMappingConeTriangle source target

/-- Public root facade: the interval-Fubini bounded cone triangle is distinguished. -/
theorem AnalyticMotivesRoot.rootFacade_intervalFubini_boundedMappingConeTriangle_distinguished
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  AnalyticMotivesRoot.rootSummary_intervalFubini_boundedMappingConeTriangle_distinguished source target

/-- Public root facade: the Tate-weight-drop bounded cone triangle. -/
def AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeTriangle
    (source target : QTraceExpression) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle
      (TraceLocalizationInput.tateWeightDrop source target).additiveComplexCommonWeightBound :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeTriangle source target

/-- Public root facade: the Tate-weight-drop bounded cone triangle is distinguished. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeTriangle_distinguished
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeTriangle_distinguished source target

end AnalyticMotives
end LFunctions
end Boundary
