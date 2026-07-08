import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.Named.RotationExactness.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.Rotation.Projections.Owner

/-!
# Rotation projections for named analytic-generator cone triangles

This file exposes selected rotated and inverse-rotated vertex and morphism
projections for the six concrete analytic localization generators.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The descent-channel rotated triangle starts at the target object. -/
theorem TraceLocalizationInput.descentChannel_boundedMappingConeRotatedTriangle_obj₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeRotatedTriangle.obj₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.descentChannel source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_obj₁
    (TraceLocalizationInput.descentChannel source target)

/-- The descent-channel rotated triangle second morphism is the connecting map. -/
theorem TraceLocalizationInput.descentChannel_boundedMappingConeRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (TraceLocalizationInput.descentChannel source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_mor₂
    (TraceLocalizationInput.descentChannel source target)

/-- The descent-channel inverse-rotated triangle middle vertex is the source object. -/
theorem TraceLocalizationInput.descentChannel_boundedMappingConeInverseRotatedTriangle_obj₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeInverseRotatedTriangle.obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.descentChannel source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_obj₂
    (TraceLocalizationInput.descentChannel source target)

/-- The descent-channel inverse-rotated triangle second morphism is the bounded map. -/
theorem TraceLocalizationInput.descentChannel_boundedMappingConeInverseRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.descentChannel source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_mor₂
    (TraceLocalizationInput.descentChannel source target)

/-- The descent-refinement rotated triangle starts at the target object. -/
theorem TraceLocalizationInput.descentRefinement_boundedMappingConeRotatedTriangle_obj₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeRotatedTriangle.obj₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.descentRefinement source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_obj₁
    (TraceLocalizationInput.descentRefinement source target)

/-- The descent-refinement rotated triangle second morphism is the connecting map. -/
theorem TraceLocalizationInput.descentRefinement_boundedMappingConeRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (TraceLocalizationInput.descentRefinement source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_mor₂
    (TraceLocalizationInput.descentRefinement source target)

/-- The descent-refinement inverse-rotated triangle middle vertex is the source object. -/
theorem TraceLocalizationInput.descentRefinement_boundedMappingConeInverseRotatedTriangle_obj₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeInverseRotatedTriangle.obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.descentRefinement source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_obj₂
    (TraceLocalizationInput.descentRefinement source target)

/-- The descent-refinement inverse-rotated triangle second morphism is the bounded map. -/
theorem TraceLocalizationInput.descentRefinement_boundedMappingConeInverseRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.descentRefinement source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_mor₂
    (TraceLocalizationInput.descentRefinement source target)

/-- The descent-schedule rotated triangle starts at the target object. -/
theorem TraceLocalizationInput.descentSchedule_boundedMappingConeRotatedTriangle_obj₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeRotatedTriangle.obj₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.descentSchedule source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_obj₁
    (TraceLocalizationInput.descentSchedule source target)

/-- The descent-schedule rotated triangle second morphism is the connecting map. -/
theorem TraceLocalizationInput.descentSchedule_boundedMappingConeRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (TraceLocalizationInput.descentSchedule source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_mor₂
    (TraceLocalizationInput.descentSchedule source target)

/-- The descent-schedule inverse-rotated triangle middle vertex is the source object. -/
theorem TraceLocalizationInput.descentSchedule_boundedMappingConeInverseRotatedTriangle_obj₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeInverseRotatedTriangle.obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.descentSchedule source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_obj₂
    (TraceLocalizationInput.descentSchedule source target)

/-- The descent-schedule inverse-rotated triangle second morphism is the bounded map. -/
theorem TraceLocalizationInput.descentSchedule_boundedMappingConeInverseRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.descentSchedule source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_mor₂
    (TraceLocalizationInput.descentSchedule source target)

/-- The interval-Stokes rotated triangle starts at the target object. -/
theorem TraceLocalizationInput.intervalStokes_boundedMappingConeRotatedTriangle_obj₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeRotatedTriangle.obj₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.intervalStokes source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_obj₁
    (TraceLocalizationInput.intervalStokes source target)

/-- The interval-Stokes rotated triangle second morphism is the connecting map. -/
theorem TraceLocalizationInput.intervalStokes_boundedMappingConeRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (TraceLocalizationInput.intervalStokes source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_mor₂
    (TraceLocalizationInput.intervalStokes source target)

/-- The interval-Stokes inverse-rotated triangle middle vertex is the source object. -/
theorem TraceLocalizationInput.intervalStokes_boundedMappingConeInverseRotatedTriangle_obj₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeInverseRotatedTriangle.obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.intervalStokes source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_obj₂
    (TraceLocalizationInput.intervalStokes source target)

/-- The interval-Stokes inverse-rotated triangle second morphism is the bounded map. -/
theorem TraceLocalizationInput.intervalStokes_boundedMappingConeInverseRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.intervalStokes source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_mor₂
    (TraceLocalizationInput.intervalStokes source target)

/-- The interval-Fubini rotated triangle starts at the target object. -/
theorem TraceLocalizationInput.intervalFubini_boundedMappingConeRotatedTriangle_obj₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeRotatedTriangle.obj₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.intervalFubini source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_obj₁
    (TraceLocalizationInput.intervalFubini source target)

/-- The interval-Fubini rotated triangle second morphism is the connecting map. -/
theorem TraceLocalizationInput.intervalFubini_boundedMappingConeRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (TraceLocalizationInput.intervalFubini source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_mor₂
    (TraceLocalizationInput.intervalFubini source target)

/-- The interval-Fubini inverse-rotated triangle middle vertex is the source object. -/
theorem TraceLocalizationInput.intervalFubini_boundedMappingConeInverseRotatedTriangle_obj₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeInverseRotatedTriangle.obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.intervalFubini source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_obj₂
    (TraceLocalizationInput.intervalFubini source target)

/-- The interval-Fubini inverse-rotated triangle second morphism is the bounded map. -/
theorem TraceLocalizationInput.intervalFubini_boundedMappingConeInverseRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.intervalFubini source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_mor₂
    (TraceLocalizationInput.intervalFubini source target)

/-- The Tate-weight-drop rotated triangle starts at the target object. -/
theorem TraceLocalizationInput.tateWeightDrop_boundedMappingConeRotatedTriangle_obj₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.obj₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_obj₁
    (TraceLocalizationInput.tateWeightDrop source target)

/-- The Tate-weight-drop rotated triangle second morphism is the connecting map. -/
theorem TraceLocalizationInput.tateWeightDrop_boundedMappingConeRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_mor₂
    (TraceLocalizationInput.tateWeightDrop source target)

/-- The Tate-weight-drop inverse-rotated triangle middle vertex is the source object. -/
theorem TraceLocalizationInput.tateWeightDrop_boundedMappingConeInverseRotatedTriangle_obj₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_obj₂
    (TraceLocalizationInput.tateWeightDrop source target)

/-- The Tate-weight-drop inverse-rotated triangle second morphism is the bounded map. -/
theorem TraceLocalizationInput.tateWeightDrop_boundedMappingConeInverseRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_mor₂
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
