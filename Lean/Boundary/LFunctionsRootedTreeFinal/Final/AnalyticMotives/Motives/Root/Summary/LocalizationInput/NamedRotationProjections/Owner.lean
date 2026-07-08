import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.Named.RotationProjections.Owner

/-!
# Motive-root named rotated cone projections

This file exposes selected rotated and inverse-rotated bounded cone projection
facts for the six concrete analytic localization generators through the
motive-root summary namespace.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Motive-root summary: descent-channel rotated cone starts at the target object. -/
theorem TraceAnalyticMotive.rootSummary_descentChannel_boundedMappingConeRotatedTriangle_obj₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeRotatedTriangle.obj₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.descentChannel source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.descentChannel_boundedMappingConeRotatedTriangle_obj₁ source target

/-- Motive-root summary: descent-channel rotated cone second morphism is connecting. -/
theorem TraceAnalyticMotive.rootSummary_descentChannel_boundedMappingConeRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (TraceLocalizationInput.descentChannel source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.descentChannel_boundedMappingConeRotatedTriangle_mor₂ source target

/-- Motive-root summary: descent-channel inverse-rotated cone middle vertex is source. -/
theorem TraceAnalyticMotive.rootSummary_descentChannel_boundedMappingConeInverseRotatedTriangle_obj₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeInverseRotatedTriangle.obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.descentChannel source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.descentChannel_boundedMappingConeInverseRotatedTriangle_obj₂ source target

/-- Motive-root summary: descent-channel inverse-rotated cone second morphism is bounded map. -/
theorem TraceAnalyticMotive.rootSummary_descentChannel_boundedMappingConeInverseRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.descentChannel source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.descentChannel_boundedMappingConeInverseRotatedTriangle_mor₂ source target

/-- Motive-root summary: descent-refinement rotated cone starts at the target object. -/
theorem TraceAnalyticMotive.rootSummary_descentRefinement_boundedMappingConeRotatedTriangle_obj₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeRotatedTriangle.obj₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.descentRefinement source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.descentRefinement_boundedMappingConeRotatedTriangle_obj₁ source target

/-- Motive-root summary: descent-refinement rotated cone second morphism is connecting. -/
theorem TraceAnalyticMotive.rootSummary_descentRefinement_boundedMappingConeRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (TraceLocalizationInput.descentRefinement source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.descentRefinement_boundedMappingConeRotatedTriangle_mor₂ source target

/-- Motive-root summary: descent-refinement inverse-rotated cone middle vertex is source. -/
theorem TraceAnalyticMotive.rootSummary_descentRefinement_boundedMappingConeInverseRotatedTriangle_obj₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeInverseRotatedTriangle.obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.descentRefinement source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.descentRefinement_boundedMappingConeInverseRotatedTriangle_obj₂ source target

/-- Motive-root summary: descent-refinement inverse-rotated cone second morphism is bounded map. -/
theorem TraceAnalyticMotive.rootSummary_descentRefinement_boundedMappingConeInverseRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.descentRefinement source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.descentRefinement_boundedMappingConeInverseRotatedTriangle_mor₂ source target

/-- Motive-root summary: descent-schedule rotated cone starts at the target object. -/
theorem TraceAnalyticMotive.rootSummary_descentSchedule_boundedMappingConeRotatedTriangle_obj₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeRotatedTriangle.obj₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.descentSchedule source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.descentSchedule_boundedMappingConeRotatedTriangle_obj₁ source target

/-- Motive-root summary: descent-schedule rotated cone second morphism is connecting. -/
theorem TraceAnalyticMotive.rootSummary_descentSchedule_boundedMappingConeRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (TraceLocalizationInput.descentSchedule source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.descentSchedule_boundedMappingConeRotatedTriangle_mor₂ source target

/-- Motive-root summary: descent-schedule inverse-rotated cone middle vertex is source. -/
theorem TraceAnalyticMotive.rootSummary_descentSchedule_boundedMappingConeInverseRotatedTriangle_obj₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeInverseRotatedTriangle.obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.descentSchedule source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.descentSchedule_boundedMappingConeInverseRotatedTriangle_obj₂ source target

/-- Motive-root summary: descent-schedule inverse-rotated cone second morphism is bounded map. -/
theorem TraceAnalyticMotive.rootSummary_descentSchedule_boundedMappingConeInverseRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.descentSchedule source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.descentSchedule_boundedMappingConeInverseRotatedTriangle_mor₂ source target

/-- Motive-root summary: interval-Stokes rotated cone starts at the target object. -/
theorem TraceAnalyticMotive.rootSummary_intervalStokes_boundedMappingConeRotatedTriangle_obj₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeRotatedTriangle.obj₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.intervalStokes source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.intervalStokes_boundedMappingConeRotatedTriangle_obj₁ source target

/-- Motive-root summary: interval-Stokes rotated cone second morphism is connecting. -/
theorem TraceAnalyticMotive.rootSummary_intervalStokes_boundedMappingConeRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (TraceLocalizationInput.intervalStokes source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.intervalStokes_boundedMappingConeRotatedTriangle_mor₂ source target

/-- Motive-root summary: interval-Stokes inverse-rotated cone middle vertex is source. -/
theorem TraceAnalyticMotive.rootSummary_intervalStokes_boundedMappingConeInverseRotatedTriangle_obj₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeInverseRotatedTriangle.obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.intervalStokes source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.intervalStokes_boundedMappingConeInverseRotatedTriangle_obj₂ source target

/-- Motive-root summary: interval-Stokes inverse-rotated cone second morphism is bounded map. -/
theorem TraceAnalyticMotive.rootSummary_intervalStokes_boundedMappingConeInverseRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.intervalStokes source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.intervalStokes_boundedMappingConeInverseRotatedTriangle_mor₂ source target

/-- Motive-root summary: interval-Fubini rotated cone starts at the target object. -/
theorem TraceAnalyticMotive.rootSummary_intervalFubini_boundedMappingConeRotatedTriangle_obj₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeRotatedTriangle.obj₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.intervalFubini source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.intervalFubini_boundedMappingConeRotatedTriangle_obj₁ source target

/-- Motive-root summary: interval-Fubini rotated cone second morphism is connecting. -/
theorem TraceAnalyticMotive.rootSummary_intervalFubini_boundedMappingConeRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (TraceLocalizationInput.intervalFubini source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.intervalFubini_boundedMappingConeRotatedTriangle_mor₂ source target

/-- Motive-root summary: interval-Fubini inverse-rotated cone middle vertex is source. -/
theorem TraceAnalyticMotive.rootSummary_intervalFubini_boundedMappingConeInverseRotatedTriangle_obj₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeInverseRotatedTriangle.obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.intervalFubini source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.intervalFubini_boundedMappingConeInverseRotatedTriangle_obj₂ source target

/-- Motive-root summary: interval-Fubini inverse-rotated cone second morphism is bounded map. -/
theorem TraceAnalyticMotive.rootSummary_intervalFubini_boundedMappingConeInverseRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.intervalFubini source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.intervalFubini_boundedMappingConeInverseRotatedTriangle_mor₂ source target

/-- Motive-root summary: Tate-weight-drop rotated cone starts at the target object. -/
theorem TraceAnalyticMotive.rootSummary_tateWeightDrop_boundedMappingConeRotatedTriangle_obj₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.obj₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.tateWeightDrop_boundedMappingConeRotatedTriangle_obj₁ source target

/-- Motive-root summary: Tate-weight-drop rotated cone second morphism is connecting. -/
theorem TraceAnalyticMotive.rootSummary_tateWeightDrop_boundedMappingConeRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.tateWeightDrop_boundedMappingConeRotatedTriangle_mor₂ source target

/-- Motive-root summary: Tate-weight-drop inverse-rotated cone middle vertex is source. -/
theorem TraceAnalyticMotive.rootSummary_tateWeightDrop_boundedMappingConeInverseRotatedTriangle_obj₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.tateWeightDrop_boundedMappingConeInverseRotatedTriangle_obj₂ source target

/-- Motive-root summary: Tate-weight-drop inverse-rotated cone second morphism is bounded map. -/
theorem TraceAnalyticMotive.rootSummary_tateWeightDrop_boundedMappingConeInverseRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceLocalizationInput.tateWeightDrop_boundedMappingConeInverseRotatedTriangle_mor₂ source target

end AnalyticMotives
end LFunctions
end Boundary
