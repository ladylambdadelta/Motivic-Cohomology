import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.Exactness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.Rotation.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.ShortComplex.Owner

/-!
# Named analytic-generator bounded cone triangles

This file specializes the localization-input bounded mapping-cone calculus to
the six concrete analytic generators inverted by the analytic-motives
localization: descent channel, descent refinement, descent schedule, interval
Stokes, interval Fubini, and Tate weight drop.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The bounded cone triangle for a descent-channel input. -/
def TraceLocalizationInput.descentChannel_boundedMappingConeTriangle
    (source target : QTraceExpression) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle
      (TraceLocalizationInput.descentChannel source target).additiveComplexCommonWeightBound :=
  (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle

/-- The descent-channel bounded cone triangle is distinguished. -/
theorem TraceLocalizationInput.descentChannel_boundedMappingConeTriangle_distinguished
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceLocalizationInput.boundedMappingConeTriangle_distinguished
    (TraceLocalizationInput.descentChannel source target)

/-- The descent-channel bounded cone triangle has zero first consecutive composite. -/
theorem TraceLocalizationInput.descentChannel_boundedMappingConeTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangle.mor₁ ≫
        (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangle.mor₂ =
      0 :=
  TraceLocalizationInput.boundedMappingConeTriangle_first_comp_second
    (TraceLocalizationInput.descentChannel source target)

/-- The bounded cone triangle for a descent-refinement input. -/
def TraceLocalizationInput.descentRefinement_boundedMappingConeTriangle
    (source target : QTraceExpression) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle
      (TraceLocalizationInput.descentRefinement source target).additiveComplexCommonWeightBound :=
  (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle

/-- The descent-refinement bounded cone triangle is distinguished. -/
theorem TraceLocalizationInput.descentRefinement_boundedMappingConeTriangle_distinguished
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceLocalizationInput.boundedMappingConeTriangle_distinguished
    (TraceLocalizationInput.descentRefinement source target)

/-- The descent-refinement bounded cone triangle has zero first consecutive composite. -/
theorem TraceLocalizationInput.descentRefinement_boundedMappingConeTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangle.mor₁ ≫
        (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangle.mor₂ =
      0 :=
  TraceLocalizationInput.boundedMappingConeTriangle_first_comp_second
    (TraceLocalizationInput.descentRefinement source target)

/-- The bounded cone triangle for a descent-schedule input. -/
def TraceLocalizationInput.descentSchedule_boundedMappingConeTriangle
    (source target : QTraceExpression) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle
      (TraceLocalizationInput.descentSchedule source target).additiveComplexCommonWeightBound :=
  (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle

/-- The descent-schedule bounded cone triangle is distinguished. -/
theorem TraceLocalizationInput.descentSchedule_boundedMappingConeTriangle_distinguished
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceLocalizationInput.boundedMappingConeTriangle_distinguished
    (TraceLocalizationInput.descentSchedule source target)

/-- The descent-schedule bounded cone triangle has zero first consecutive composite. -/
theorem TraceLocalizationInput.descentSchedule_boundedMappingConeTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangle.mor₁ ≫
        (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangle.mor₂ =
      0 :=
  TraceLocalizationInput.boundedMappingConeTriangle_first_comp_second
    (TraceLocalizationInput.descentSchedule source target)

/-- The bounded cone triangle for an interval-Stokes input. -/
def TraceLocalizationInput.intervalStokes_boundedMappingConeTriangle
    (source target : QTraceExpression) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle
      (TraceLocalizationInput.intervalStokes source target).additiveComplexCommonWeightBound :=
  (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle

/-- The interval-Stokes bounded cone triangle is distinguished. -/
theorem TraceLocalizationInput.intervalStokes_boundedMappingConeTriangle_distinguished
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceLocalizationInput.boundedMappingConeTriangle_distinguished
    (TraceLocalizationInput.intervalStokes source target)

/-- The interval-Stokes bounded cone triangle has zero first consecutive composite. -/
theorem TraceLocalizationInput.intervalStokes_boundedMappingConeTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangle.mor₁ ≫
        (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangle.mor₂ =
      0 :=
  TraceLocalizationInput.boundedMappingConeTriangle_first_comp_second
    (TraceLocalizationInput.intervalStokes source target)

/-- The bounded cone triangle for an interval-Fubini input. -/
def TraceLocalizationInput.intervalFubini_boundedMappingConeTriangle
    (source target : QTraceExpression) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle
      (TraceLocalizationInput.intervalFubini source target).additiveComplexCommonWeightBound :=
  (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle

/-- The interval-Fubini bounded cone triangle is distinguished. -/
theorem TraceLocalizationInput.intervalFubini_boundedMappingConeTriangle_distinguished
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceLocalizationInput.boundedMappingConeTriangle_distinguished
    (TraceLocalizationInput.intervalFubini source target)

/-- The interval-Fubini bounded cone triangle has zero first consecutive composite. -/
theorem TraceLocalizationInput.intervalFubini_boundedMappingConeTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangle.mor₁ ≫
        (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangle.mor₂ =
      0 :=
  TraceLocalizationInput.boundedMappingConeTriangle_first_comp_second
    (TraceLocalizationInput.intervalFubini source target)

/-- The bounded cone triangle for a Tate-weight-drop input. -/
def TraceLocalizationInput.tateWeightDrop_boundedMappingConeTriangle
    (source target : QTraceExpression) :
    TraceAnalyticAdditiveHomotopyCategory.BoundedTriangle
      (TraceLocalizationInput.tateWeightDrop source target).additiveComplexCommonWeightBound :=
  (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle

/-- The Tate-weight-drop bounded cone triangle is distinguished. -/
theorem TraceLocalizationInput.tateWeightDrop_boundedMappingConeTriangle_distinguished
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle ∈
      TraceAnalyticAdditiveHomotopyCategory.distinguishedTriangles :=
  TraceLocalizationInput.boundedMappingConeTriangle_distinguished
    (TraceLocalizationInput.tateWeightDrop source target)

/-- The Tate-weight-drop bounded cone triangle has zero first consecutive composite. -/
theorem TraceLocalizationInput.tateWeightDrop_boundedMappingConeTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₁ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₂ =
      0 :=
  TraceLocalizationInput.boundedMappingConeTriangle_first_comp_second
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
