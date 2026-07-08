import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.Named.Projections.Owner

/-!
# Motive-root named analytic-generator cone triangles

This file exposes the bounded cone triangles attached to the six concrete
analytic localization generators through the motive-root summary namespace.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Motive-root summary: the descent-channel bounded cone triangle. -/
def TraceAnalyticMotive.rootSummary_descentChannel_boundedMappingConeTriangle
    (source target : QTraceExpression) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle
      (TraceLocalizationInput.descentChannel source target).additiveComplexCommonWeightBound :=
  TraceLocalizationInput.descentChannel_boundedMappingConeTriangle source target

/-- Motive-root summary: the descent-channel bounded cone triangle is distinguished. -/
theorem TraceAnalyticMotive.rootSummary_descentChannel_boundedMappingConeTriangle_distinguished
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceLocalizationInput.descentChannel_boundedMappingConeTriangle_distinguished source target

/-- Motive-root summary: the descent-refinement bounded cone triangle. -/
def TraceAnalyticMotive.rootSummary_descentRefinement_boundedMappingConeTriangle
    (source target : QTraceExpression) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle
      (TraceLocalizationInput.descentRefinement source target).additiveComplexCommonWeightBound :=
  TraceLocalizationInput.descentRefinement_boundedMappingConeTriangle source target

/-- Motive-root summary: the descent-refinement bounded cone triangle is distinguished. -/
theorem TraceAnalyticMotive.rootSummary_descentRefinement_boundedMappingConeTriangle_distinguished
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceLocalizationInput.descentRefinement_boundedMappingConeTriangle_distinguished source target

/-- Motive-root summary: the descent-schedule bounded cone triangle. -/
def TraceAnalyticMotive.rootSummary_descentSchedule_boundedMappingConeTriangle
    (source target : QTraceExpression) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle
      (TraceLocalizationInput.descentSchedule source target).additiveComplexCommonWeightBound :=
  TraceLocalizationInput.descentSchedule_boundedMappingConeTriangle source target

/-- Motive-root summary: the descent-schedule bounded cone triangle is distinguished. -/
theorem TraceAnalyticMotive.rootSummary_descentSchedule_boundedMappingConeTriangle_distinguished
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceLocalizationInput.descentSchedule_boundedMappingConeTriangle_distinguished source target

/-- Motive-root summary: the interval-Stokes bounded cone triangle. -/
def TraceAnalyticMotive.rootSummary_intervalStokes_boundedMappingConeTriangle
    (source target : QTraceExpression) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle
      (TraceLocalizationInput.intervalStokes source target).additiveComplexCommonWeightBound :=
  TraceLocalizationInput.intervalStokes_boundedMappingConeTriangle source target

/-- Motive-root summary: the interval-Stokes bounded cone triangle is distinguished. -/
theorem TraceAnalyticMotive.rootSummary_intervalStokes_boundedMappingConeTriangle_distinguished
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceLocalizationInput.intervalStokes_boundedMappingConeTriangle_distinguished source target

/-- Motive-root summary: the interval-Fubini bounded cone triangle. -/
def TraceAnalyticMotive.rootSummary_intervalFubini_boundedMappingConeTriangle
    (source target : QTraceExpression) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle
      (TraceLocalizationInput.intervalFubini source target).additiveComplexCommonWeightBound :=
  TraceLocalizationInput.intervalFubini_boundedMappingConeTriangle source target

/-- Motive-root summary: the interval-Fubini bounded cone triangle is distinguished. -/
theorem TraceAnalyticMotive.rootSummary_intervalFubini_boundedMappingConeTriangle_distinguished
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceLocalizationInput.intervalFubini_boundedMappingConeTriangle_distinguished source target

/-- Motive-root summary: the Tate-weight-drop bounded cone triangle. -/
def TraceAnalyticMotive.rootSummary_tateWeightDrop_boundedMappingConeTriangle
    (source target : QTraceExpression) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle
      (TraceLocalizationInput.tateWeightDrop source target).additiveComplexCommonWeightBound :=
  TraceLocalizationInput.tateWeightDrop_boundedMappingConeTriangle source target

/-- Motive-root summary: the Tate-weight-drop bounded cone triangle is distinguished. -/
theorem TraceAnalyticMotive.rootSummary_tateWeightDrop_boundedMappingConeTriangle_distinguished
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceLocalizationInput.tateWeightDrop_boundedMappingConeTriangle_distinguished source target

end AnalyticMotives
end LFunctions
end Boundary
