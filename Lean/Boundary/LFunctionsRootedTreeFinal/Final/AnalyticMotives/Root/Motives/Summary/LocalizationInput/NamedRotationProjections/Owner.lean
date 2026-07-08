import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Summary.LocalizationInput.NamedRotationProjections.Owner

/-!
# Top-root motive summary for named rotated cone projections

This file forwards selected named analytic-generator rotated and inverse-rotated
bounded cone projection facts to the top-root motive summary namespace.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Top-root motive summary: descent-channel rotated cone starts at the target object. -/
theorem AnalyticMotivesRoot.rootSummary_descentChannel_boundedMappingConeRotatedTriangle_obj₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeRotatedTriangle.obj₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.descentChannel source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_descentChannel_boundedMappingConeRotatedTriangle_obj₁ source target

/-- Top-root motive summary: descent-channel rotated cone second morphism is connecting. -/
theorem AnalyticMotivesRoot.rootSummary_descentChannel_boundedMappingConeRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (TraceLocalizationInput.descentChannel source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_descentChannel_boundedMappingConeRotatedTriangle_mor₂ source target

/-- Top-root motive summary: descent-channel inverse-rotated cone middle vertex is source. -/
theorem AnalyticMotivesRoot.rootSummary_descentChannel_boundedMappingConeInverseRotatedTriangle_obj₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeInverseRotatedTriangle.obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.descentChannel source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_descentChannel_boundedMappingConeInverseRotatedTriangle_obj₂ source target

/-- Top-root motive summary: descent-channel inverse-rotated cone second morphism is bounded map. -/
theorem AnalyticMotivesRoot.rootSummary_descentChannel_boundedMappingConeInverseRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.descentChannel source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_descentChannel_boundedMappingConeInverseRotatedTriangle_mor₂ source target

/-- Top-root motive summary: descent-refinement rotated cone starts at the target object. -/
theorem AnalyticMotivesRoot.rootSummary_descentRefinement_boundedMappingConeRotatedTriangle_obj₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeRotatedTriangle.obj₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.descentRefinement source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_descentRefinement_boundedMappingConeRotatedTriangle_obj₁ source target

/-- Top-root motive summary: descent-refinement rotated cone second morphism is connecting. -/
theorem AnalyticMotivesRoot.rootSummary_descentRefinement_boundedMappingConeRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (TraceLocalizationInput.descentRefinement source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_descentRefinement_boundedMappingConeRotatedTriangle_mor₂ source target

/-- Top-root motive summary: descent-refinement inverse-rotated cone middle vertex is source. -/
theorem AnalyticMotivesRoot.rootSummary_descentRefinement_boundedMappingConeInverseRotatedTriangle_obj₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeInverseRotatedTriangle.obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.descentRefinement source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_descentRefinement_boundedMappingConeInverseRotatedTriangle_obj₂ source target

/-- Top-root motive summary: descent-refinement inverse-rotated cone second morphism is bounded map. -/
theorem AnalyticMotivesRoot.rootSummary_descentRefinement_boundedMappingConeInverseRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.descentRefinement source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_descentRefinement_boundedMappingConeInverseRotatedTriangle_mor₂ source target

/-- Top-root motive summary: descent-schedule rotated cone starts at the target object. -/
theorem AnalyticMotivesRoot.rootSummary_descentSchedule_boundedMappingConeRotatedTriangle_obj₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeRotatedTriangle.obj₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.descentSchedule source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_descentSchedule_boundedMappingConeRotatedTriangle_obj₁ source target

/-- Top-root motive summary: descent-schedule rotated cone second morphism is connecting. -/
theorem AnalyticMotivesRoot.rootSummary_descentSchedule_boundedMappingConeRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (TraceLocalizationInput.descentSchedule source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_descentSchedule_boundedMappingConeRotatedTriangle_mor₂ source target

/-- Top-root motive summary: descent-schedule inverse-rotated cone middle vertex is source. -/
theorem AnalyticMotivesRoot.rootSummary_descentSchedule_boundedMappingConeInverseRotatedTriangle_obj₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeInverseRotatedTriangle.obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.descentSchedule source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_descentSchedule_boundedMappingConeInverseRotatedTriangle_obj₂ source target

/-- Top-root motive summary: descent-schedule inverse-rotated cone second morphism is bounded map. -/
theorem AnalyticMotivesRoot.rootSummary_descentSchedule_boundedMappingConeInverseRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.descentSchedule source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_descentSchedule_boundedMappingConeInverseRotatedTriangle_mor₂ source target

/-- Top-root motive summary: interval-Stokes rotated cone starts at the target object. -/
theorem AnalyticMotivesRoot.rootSummary_intervalStokes_boundedMappingConeRotatedTriangle_obj₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeRotatedTriangle.obj₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.intervalStokes source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_intervalStokes_boundedMappingConeRotatedTriangle_obj₁ source target

/-- Top-root motive summary: interval-Stokes rotated cone second morphism is connecting. -/
theorem AnalyticMotivesRoot.rootSummary_intervalStokes_boundedMappingConeRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (TraceLocalizationInput.intervalStokes source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_intervalStokes_boundedMappingConeRotatedTriangle_mor₂ source target

/-- Top-root motive summary: interval-Stokes inverse-rotated cone middle vertex is source. -/
theorem AnalyticMotivesRoot.rootSummary_intervalStokes_boundedMappingConeInverseRotatedTriangle_obj₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeInverseRotatedTriangle.obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.intervalStokes source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_intervalStokes_boundedMappingConeInverseRotatedTriangle_obj₂ source target

/-- Top-root motive summary: interval-Stokes inverse-rotated cone second morphism is bounded map. -/
theorem AnalyticMotivesRoot.rootSummary_intervalStokes_boundedMappingConeInverseRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.intervalStokes source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_intervalStokes_boundedMappingConeInverseRotatedTriangle_mor₂ source target

/-- Top-root motive summary: interval-Fubini rotated cone starts at the target object. -/
theorem AnalyticMotivesRoot.rootSummary_intervalFubini_boundedMappingConeRotatedTriangle_obj₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeRotatedTriangle.obj₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.intervalFubini source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_intervalFubini_boundedMappingConeRotatedTriangle_obj₁ source target

/-- Top-root motive summary: interval-Fubini rotated cone second morphism is connecting. -/
theorem AnalyticMotivesRoot.rootSummary_intervalFubini_boundedMappingConeRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (TraceLocalizationInput.intervalFubini source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_intervalFubini_boundedMappingConeRotatedTriangle_mor₂ source target

/-- Top-root motive summary: interval-Fubini inverse-rotated cone middle vertex is source. -/
theorem AnalyticMotivesRoot.rootSummary_intervalFubini_boundedMappingConeInverseRotatedTriangle_obj₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeInverseRotatedTriangle.obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.intervalFubini source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_intervalFubini_boundedMappingConeInverseRotatedTriangle_obj₂ source target

/-- Top-root motive summary: interval-Fubini inverse-rotated cone second morphism is bounded map. -/
theorem AnalyticMotivesRoot.rootSummary_intervalFubini_boundedMappingConeInverseRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.intervalFubini source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_intervalFubini_boundedMappingConeInverseRotatedTriangle_mor₂ source target

/-- Top-root motive summary: Tate-weight-drop rotated cone starts at the target object. -/
theorem AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeRotatedTriangle_obj₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.obj₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_tateWeightDrop_boundedMappingConeRotatedTriangle_obj₁ source target

/-- Top-root motive summary: Tate-weight-drop rotated cone second morphism is connecting. -/
theorem AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_tateWeightDrop_boundedMappingConeRotatedTriangle_mor₂ source target

/-- Top-root motive summary: Tate-weight-drop inverse-rotated cone middle vertex is source. -/
theorem AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeInverseRotatedTriangle_obj₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_tateWeightDrop_boundedMappingConeInverseRotatedTriangle_obj₂ source target

/-- Top-root motive summary: Tate-weight-drop inverse-rotated cone second morphism is bounded map. -/
theorem AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeInverseRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  TraceAnalyticMotive.rootSummary_tateWeightDrop_boundedMappingConeInverseRotatedTriangle_mor₂ source target

end AnalyticMotives
end LFunctions
end Boundary
