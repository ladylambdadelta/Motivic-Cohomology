import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Summary.LocalizationInput.NamedProjections.Owner

/-!
# Top-root motive summary for named cone projections

This file forwards named analytic-generator unrotated bounded cone projection
facts to the top-root motive summary namespace.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- Top-root motive summary: descent-channel cone source object projection. -/
theorem AnalyticMotivesRoot.rootSummary_descentChannel_boundedMappingConeTriangle_firstObject
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.firstObject =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.descentChannel source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_descentChannel_boundedMappingConeTriangle_firstObject source target

/-- Top-root motive summary: descent-channel cone target object projection. -/
theorem AnalyticMotivesRoot.rootSummary_descentChannel_boundedMappingConeTriangle_secondObject
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.secondObject =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.descentChannel source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_descentChannel_boundedMappingConeTriangle_secondObject source target

/-- Top-root motive summary: descent-channel cone first-map projection. -/
theorem AnalyticMotivesRoot.rootSummary_descentChannel_boundedMappingConeTriangle_firstMap
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.firstMap =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.descentChannel source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_descentChannel_boundedMappingConeTriangle_firstMap source target

/-- Top-root motive summary: descent-channel cone third-vertex projection. -/
theorem AnalyticMotivesRoot.rootSummary_descentChannel_boundedMappingConeTriangle_thirdVertex
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangleThirdVertex =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.triangle
        (TraceLocalizationInput.descentChannel source target).boundedAdditiveComplexHom).obj₃ :=
  TraceAnalyticMotive.rootSummary_descentChannel_boundedMappingConeTriangle_thirdVertex source target

/-- Top-root motive summary: descent-refinement cone source object projection. -/
theorem AnalyticMotivesRoot.rootSummary_descentRefinement_boundedMappingConeTriangle_firstObject
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.firstObject =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.descentRefinement source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_descentRefinement_boundedMappingConeTriangle_firstObject source target

/-- Top-root motive summary: descent-refinement cone target object projection. -/
theorem AnalyticMotivesRoot.rootSummary_descentRefinement_boundedMappingConeTriangle_secondObject
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.secondObject =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.descentRefinement source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_descentRefinement_boundedMappingConeTriangle_secondObject source target

/-- Top-root motive summary: descent-refinement cone first-map projection. -/
theorem AnalyticMotivesRoot.rootSummary_descentRefinement_boundedMappingConeTriangle_firstMap
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.firstMap =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.descentRefinement source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_descentRefinement_boundedMappingConeTriangle_firstMap source target

/-- Top-root motive summary: descent-refinement cone third-vertex projection. -/
theorem AnalyticMotivesRoot.rootSummary_descentRefinement_boundedMappingConeTriangle_thirdVertex
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangleThirdVertex =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.triangle
        (TraceLocalizationInput.descentRefinement source target).boundedAdditiveComplexHom).obj₃ :=
  TraceAnalyticMotive.rootSummary_descentRefinement_boundedMappingConeTriangle_thirdVertex source target

/-- Top-root motive summary: descent-schedule cone source object projection. -/
theorem AnalyticMotivesRoot.rootSummary_descentSchedule_boundedMappingConeTriangle_firstObject
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.firstObject =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.descentSchedule source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_descentSchedule_boundedMappingConeTriangle_firstObject source target

/-- Top-root motive summary: descent-schedule cone target object projection. -/
theorem AnalyticMotivesRoot.rootSummary_descentSchedule_boundedMappingConeTriangle_secondObject
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.secondObject =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.descentSchedule source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_descentSchedule_boundedMappingConeTriangle_secondObject source target

/-- Top-root motive summary: descent-schedule cone first-map projection. -/
theorem AnalyticMotivesRoot.rootSummary_descentSchedule_boundedMappingConeTriangle_firstMap
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.firstMap =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.descentSchedule source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_descentSchedule_boundedMappingConeTriangle_firstMap source target

/-- Top-root motive summary: descent-schedule cone third-vertex projection. -/
theorem AnalyticMotivesRoot.rootSummary_descentSchedule_boundedMappingConeTriangle_thirdVertex
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangleThirdVertex =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.triangle
        (TraceLocalizationInput.descentSchedule source target).boundedAdditiveComplexHom).obj₃ :=
  TraceAnalyticMotive.rootSummary_descentSchedule_boundedMappingConeTriangle_thirdVertex source target

/-- Top-root motive summary: interval-Stokes cone source object projection. -/
theorem AnalyticMotivesRoot.rootSummary_intervalStokes_boundedMappingConeTriangle_firstObject
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.firstObject =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.intervalStokes source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_intervalStokes_boundedMappingConeTriangle_firstObject source target

/-- Top-root motive summary: interval-Stokes cone target object projection. -/
theorem AnalyticMotivesRoot.rootSummary_intervalStokes_boundedMappingConeTriangle_secondObject
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.secondObject =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.intervalStokes source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_intervalStokes_boundedMappingConeTriangle_secondObject source target

/-- Top-root motive summary: interval-Stokes cone first-map projection. -/
theorem AnalyticMotivesRoot.rootSummary_intervalStokes_boundedMappingConeTriangle_firstMap
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.firstMap =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.intervalStokes source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_intervalStokes_boundedMappingConeTriangle_firstMap source target

/-- Top-root motive summary: interval-Stokes cone third-vertex projection. -/
theorem AnalyticMotivesRoot.rootSummary_intervalStokes_boundedMappingConeTriangle_thirdVertex
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangleThirdVertex =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.triangle
        (TraceLocalizationInput.intervalStokes source target).boundedAdditiveComplexHom).obj₃ :=
  TraceAnalyticMotive.rootSummary_intervalStokes_boundedMappingConeTriangle_thirdVertex source target

/-- Top-root motive summary: interval-Fubini cone source object projection. -/
theorem AnalyticMotivesRoot.rootSummary_intervalFubini_boundedMappingConeTriangle_firstObject
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.firstObject =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.intervalFubini source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_intervalFubini_boundedMappingConeTriangle_firstObject source target

/-- Top-root motive summary: interval-Fubini cone target object projection. -/
theorem AnalyticMotivesRoot.rootSummary_intervalFubini_boundedMappingConeTriangle_secondObject
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.secondObject =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.intervalFubini source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_intervalFubini_boundedMappingConeTriangle_secondObject source target

/-- Top-root motive summary: interval-Fubini cone first-map projection. -/
theorem AnalyticMotivesRoot.rootSummary_intervalFubini_boundedMappingConeTriangle_firstMap
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.firstMap =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.intervalFubini source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_intervalFubini_boundedMappingConeTriangle_firstMap source target

/-- Top-root motive summary: interval-Fubini cone third-vertex projection. -/
theorem AnalyticMotivesRoot.rootSummary_intervalFubini_boundedMappingConeTriangle_thirdVertex
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangleThirdVertex =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.triangle
        (TraceLocalizationInput.intervalFubini source target).boundedAdditiveComplexHom).obj₃ :=
  TraceAnalyticMotive.rootSummary_intervalFubini_boundedMappingConeTriangle_thirdVertex source target

/-- Top-root motive summary: Tate-weight-drop cone source object projection. -/
theorem AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeTriangle_firstObject
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.firstObject =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_tateWeightDrop_boundedMappingConeTriangle_firstObject source target

/-- Top-root motive summary: Tate-weight-drop cone target object projection. -/
theorem AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeTriangle_secondObject
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.secondObject =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_tateWeightDrop_boundedMappingConeTriangle_secondObject source target

/-- Top-root motive summary: Tate-weight-drop cone first-map projection. -/
theorem AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeTriangle_firstMap
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.firstMap =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_tateWeightDrop_boundedMappingConeTriangle_firstMap source target

/-- Top-root motive summary: Tate-weight-drop cone third-vertex projection. -/
theorem AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeTriangle_thirdVertex
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangleThirdVertex =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.triangle
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom).obj₃ :=
  TraceAnalyticMotive.rootSummary_tateWeightDrop_boundedMappingConeTriangle_thirdVertex source target

end AnalyticMotives
end LFunctions
end Boundary
