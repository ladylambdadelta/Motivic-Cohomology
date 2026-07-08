import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.Named.Owner

/-!
# Projections of named analytic-generator cone triangles

This file exposes source, target, first-map, and cone-vertex projections for
the bounded cone triangles attached to the six concrete analytic localization
generators.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

/-- The descent-channel cone triangle starts at the bounded source object. -/
theorem TraceLocalizationInput.descentChannel_boundedMappingConeTriangle_firstObject
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.firstObject =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.descentChannel source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeTriangle_firstObject
    (TraceLocalizationInput.descentChannel source target)

/-- The descent-channel cone triangle has the bounded target as second object. -/
theorem TraceLocalizationInput.descentChannel_boundedMappingConeTriangle_secondObject
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.secondObject =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.descentChannel source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeTriangle_secondObject
    (TraceLocalizationInput.descentChannel source target)

/-- The descent-channel cone triangle first map is the bounded localization-input map. -/
theorem TraceLocalizationInput.descentChannel_boundedMappingConeTriangle_firstMap
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.firstMap =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.descentChannel source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeTriangle_firstMap
    (TraceLocalizationInput.descentChannel source target)

/-- The descent-channel cone triangle third vertex is the mapping cone vertex. -/
theorem TraceLocalizationInput.descentChannel_boundedMappingConeTriangle_thirdVertex
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangleThirdVertex =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.triangle
        (TraceLocalizationInput.descentChannel source target).boundedAdditiveComplexHom).obj₃ :=
  TraceLocalizationInput.boundedMappingConeTriangle_thirdVertex
    (TraceLocalizationInput.descentChannel source target)

/-- The descent-refinement cone triangle starts at the bounded source object. -/
theorem TraceLocalizationInput.descentRefinement_boundedMappingConeTriangle_firstObject
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.firstObject =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.descentRefinement source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeTriangle_firstObject
    (TraceLocalizationInput.descentRefinement source target)

/-- The descent-refinement cone triangle has the bounded target as second object. -/
theorem TraceLocalizationInput.descentRefinement_boundedMappingConeTriangle_secondObject
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.secondObject =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.descentRefinement source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeTriangle_secondObject
    (TraceLocalizationInput.descentRefinement source target)

/-- The descent-refinement cone triangle first map is the bounded localization-input map. -/
theorem TraceLocalizationInput.descentRefinement_boundedMappingConeTriangle_firstMap
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.firstMap =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.descentRefinement source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeTriangle_firstMap
    (TraceLocalizationInput.descentRefinement source target)

/-- The descent-refinement cone triangle third vertex is the mapping cone vertex. -/
theorem TraceLocalizationInput.descentRefinement_boundedMappingConeTriangle_thirdVertex
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangleThirdVertex =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.triangle
        (TraceLocalizationInput.descentRefinement source target).boundedAdditiveComplexHom).obj₃ :=
  TraceLocalizationInput.boundedMappingConeTriangle_thirdVertex
    (TraceLocalizationInput.descentRefinement source target)

/-- The descent-schedule cone triangle starts at the bounded source object. -/
theorem TraceLocalizationInput.descentSchedule_boundedMappingConeTriangle_firstObject
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.firstObject =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.descentSchedule source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeTriangle_firstObject
    (TraceLocalizationInput.descentSchedule source target)

/-- The descent-schedule cone triangle has the bounded target as second object. -/
theorem TraceLocalizationInput.descentSchedule_boundedMappingConeTriangle_secondObject
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.secondObject =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.descentSchedule source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeTriangle_secondObject
    (TraceLocalizationInput.descentSchedule source target)

/-- The descent-schedule cone triangle first map is the bounded localization-input map. -/
theorem TraceLocalizationInput.descentSchedule_boundedMappingConeTriangle_firstMap
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.firstMap =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.descentSchedule source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeTriangle_firstMap
    (TraceLocalizationInput.descentSchedule source target)

/-- The descent-schedule cone triangle third vertex is the mapping cone vertex. -/
theorem TraceLocalizationInput.descentSchedule_boundedMappingConeTriangle_thirdVertex
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangleThirdVertex =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.triangle
        (TraceLocalizationInput.descentSchedule source target).boundedAdditiveComplexHom).obj₃ :=
  TraceLocalizationInput.boundedMappingConeTriangle_thirdVertex
    (TraceLocalizationInput.descentSchedule source target)

/-- The interval-Stokes cone triangle starts at the bounded source object. -/
theorem TraceLocalizationInput.intervalStokes_boundedMappingConeTriangle_firstObject
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.firstObject =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.intervalStokes source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeTriangle_firstObject
    (TraceLocalizationInput.intervalStokes source target)

/-- The interval-Stokes cone triangle has the bounded target as second object. -/
theorem TraceLocalizationInput.intervalStokes_boundedMappingConeTriangle_secondObject
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.secondObject =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.intervalStokes source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeTriangle_secondObject
    (TraceLocalizationInput.intervalStokes source target)

/-- The interval-Stokes cone triangle first map is the bounded localization-input map. -/
theorem TraceLocalizationInput.intervalStokes_boundedMappingConeTriangle_firstMap
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.firstMap =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.intervalStokes source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeTriangle_firstMap
    (TraceLocalizationInput.intervalStokes source target)

/-- The interval-Stokes cone triangle third vertex is the mapping cone vertex. -/
theorem TraceLocalizationInput.intervalStokes_boundedMappingConeTriangle_thirdVertex
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangleThirdVertex =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.triangle
        (TraceLocalizationInput.intervalStokes source target).boundedAdditiveComplexHom).obj₃ :=
  TraceLocalizationInput.boundedMappingConeTriangle_thirdVertex
    (TraceLocalizationInput.intervalStokes source target)

/-- The interval-Fubini cone triangle starts at the bounded source object. -/
theorem TraceLocalizationInput.intervalFubini_boundedMappingConeTriangle_firstObject
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.firstObject =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.intervalFubini source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeTriangle_firstObject
    (TraceLocalizationInput.intervalFubini source target)

/-- The interval-Fubini cone triangle has the bounded target as second object. -/
theorem TraceLocalizationInput.intervalFubini_boundedMappingConeTriangle_secondObject
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.secondObject =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.intervalFubini source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeTriangle_secondObject
    (TraceLocalizationInput.intervalFubini source target)

/-- The interval-Fubini cone triangle first map is the bounded localization-input map. -/
theorem TraceLocalizationInput.intervalFubini_boundedMappingConeTriangle_firstMap
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.firstMap =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.intervalFubini source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeTriangle_firstMap
    (TraceLocalizationInput.intervalFubini source target)

/-- The interval-Fubini cone triangle third vertex is the mapping cone vertex. -/
theorem TraceLocalizationInput.intervalFubini_boundedMappingConeTriangle_thirdVertex
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangleThirdVertex =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.triangle
        (TraceLocalizationInput.intervalFubini source target).boundedAdditiveComplexHom).obj₃ :=
  TraceLocalizationInput.boundedMappingConeTriangle_thirdVertex
    (TraceLocalizationInput.intervalFubini source target)

/-- The Tate-weight-drop cone triangle starts at the bounded source object. -/
theorem TraceLocalizationInput.tateWeightDrop_boundedMappingConeTriangle_firstObject
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.firstObject =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeTriangle_firstObject
    (TraceLocalizationInput.tateWeightDrop source target)

/-- The Tate-weight-drop cone triangle has the bounded target as second object. -/
theorem TraceLocalizationInput.tateWeightDrop_boundedMappingConeTriangle_secondObject
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.secondObject =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeTriangle_secondObject
    (TraceLocalizationInput.tateWeightDrop source target)

/-- The Tate-weight-drop cone triangle first map is the bounded localization-input map. -/
theorem TraceLocalizationInput.tateWeightDrop_boundedMappingConeTriangle_firstMap
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.firstMap =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeTriangle_firstMap
    (TraceLocalizationInput.tateWeightDrop source target)

/-- The Tate-weight-drop cone triangle third vertex is the mapping cone vertex. -/
theorem TraceLocalizationInput.tateWeightDrop_boundedMappingConeTriangle_thirdVertex
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangleThirdVertex =
      (TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.triangle
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom).obj₃ :=
  TraceLocalizationInput.boundedMappingConeTriangle_thirdVertex
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
