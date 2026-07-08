import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Summary.LocalizationInput.NamedTriangles.Owner

/-!
# Top-root motive summary for named analytic-generator cone triangles

This file forwards named analytic-generator cone triangles from the motive-root
summary namespace to the top-root motive summary namespace.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root motive summary: the descent-channel bounded cone triangle. -/
def AnalyticMotivesRoot.rootSummary_descentChannel_boundedMappingConeTriangle
    (source target : QTraceExpression) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle
      (TraceLocalizationInput.descentChannel source target).additiveComplexCommonWeightBound :=
  TraceAnalyticMotive.rootSummary_descentChannel_boundedMappingConeTriangle source target

/-- Top-root motive summary: the descent-channel bounded cone triangle is distinguished. -/
theorem AnalyticMotivesRoot.rootSummary_descentChannel_boundedMappingConeTriangle_distinguished
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticMotive.rootSummary_descentChannel_boundedMappingConeTriangle_distinguished source target

/-- Top-root motive summary: the descent-refinement bounded cone triangle. -/
def AnalyticMotivesRoot.rootSummary_descentRefinement_boundedMappingConeTriangle
    (source target : QTraceExpression) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle
      (TraceLocalizationInput.descentRefinement source target).additiveComplexCommonWeightBound :=
  TraceAnalyticMotive.rootSummary_descentRefinement_boundedMappingConeTriangle source target

/-- Top-root motive summary: the descent-refinement bounded cone triangle is distinguished. -/
theorem AnalyticMotivesRoot.rootSummary_descentRefinement_boundedMappingConeTriangle_distinguished
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticMotive.rootSummary_descentRefinement_boundedMappingConeTriangle_distinguished source target

/-- Top-root motive summary: the descent-schedule bounded cone triangle. -/
def AnalyticMotivesRoot.rootSummary_descentSchedule_boundedMappingConeTriangle
    (source target : QTraceExpression) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle
      (TraceLocalizationInput.descentSchedule source target).additiveComplexCommonWeightBound :=
  TraceAnalyticMotive.rootSummary_descentSchedule_boundedMappingConeTriangle source target

/-- Top-root motive summary: the descent-schedule bounded cone triangle is distinguished. -/
theorem AnalyticMotivesRoot.rootSummary_descentSchedule_boundedMappingConeTriangle_distinguished
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticMotive.rootSummary_descentSchedule_boundedMappingConeTriangle_distinguished source target

/-- Top-root motive summary: the interval-Stokes bounded cone triangle. -/
def AnalyticMotivesRoot.rootSummary_intervalStokes_boundedMappingConeTriangle
    (source target : QTraceExpression) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle
      (TraceLocalizationInput.intervalStokes source target).additiveComplexCommonWeightBound :=
  TraceAnalyticMotive.rootSummary_intervalStokes_boundedMappingConeTriangle source target

/-- Top-root motive summary: the interval-Stokes bounded cone triangle is distinguished. -/
theorem AnalyticMotivesRoot.rootSummary_intervalStokes_boundedMappingConeTriangle_distinguished
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticMotive.rootSummary_intervalStokes_boundedMappingConeTriangle_distinguished source target

/-- Top-root motive summary: the interval-Fubini bounded cone triangle. -/
def AnalyticMotivesRoot.rootSummary_intervalFubini_boundedMappingConeTriangle
    (source target : QTraceExpression) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle
      (TraceLocalizationInput.intervalFubini source target).additiveComplexCommonWeightBound :=
  TraceAnalyticMotive.rootSummary_intervalFubini_boundedMappingConeTriangle source target

/-- Top-root motive summary: the interval-Fubini bounded cone triangle is distinguished. -/
theorem AnalyticMotivesRoot.rootSummary_intervalFubini_boundedMappingConeTriangle_distinguished
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticMotive.rootSummary_intervalFubini_boundedMappingConeTriangle_distinguished source target

/-- Top-root motive summary: the Tate-weight-drop bounded cone triangle. -/
def AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeTriangle
    (source target : QTraceExpression) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle
      (TraceLocalizationInput.tateWeightDrop source target).additiveComplexCommonWeightBound :=
  TraceAnalyticMotive.rootSummary_tateWeightDrop_boundedMappingConeTriangle source target

/-- Top-root motive summary: the Tate-weight-drop bounded cone triangle is distinguished. -/
theorem AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeTriangle_distinguished
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceAnalyticMotive.rootSummary_tateWeightDrop_boundedMappingConeTriangle_distinguished source target

end AnalyticMotives
end LFunctions
end Boundary
