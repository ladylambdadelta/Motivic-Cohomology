import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Motives.Summary.LocalizationInput.NamedRotationProjections.Owner

/-!
# Public named rotated cone projection facade

This file exposes selected named analytic-generator rotated and inverse-rotated
bounded cone projection facts at the public root surface.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Public root facade: descent-channel rotated cone starts at the target object. -/
theorem AnalyticMotivesRoot.rootFacade_descentChannel_boundedMappingConeRotatedTriangle_obj₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeRotatedTriangle.obj₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.descentChannel source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_descentChannel_boundedMappingConeRotatedTriangle_obj₁ source target

/-- Public root facade: descent-channel rotated cone second morphism is connecting. -/
theorem AnalyticMotivesRoot.rootFacade_descentChannel_boundedMappingConeRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (TraceLocalizationInput.descentChannel source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_descentChannel_boundedMappingConeRotatedTriangle_mor₂ source target

/-- Public root facade: descent-channel inverse-rotated cone middle vertex is source. -/
theorem AnalyticMotivesRoot.rootFacade_descentChannel_boundedMappingConeInverseRotatedTriangle_obj₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeInverseRotatedTriangle.obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.descentChannel source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_descentChannel_boundedMappingConeInverseRotatedTriangle_obj₂ source target

/-- Public root facade: descent-channel inverse-rotated cone second morphism is bounded map. -/
theorem AnalyticMotivesRoot.rootFacade_descentChannel_boundedMappingConeInverseRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.descentChannel source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_descentChannel_boundedMappingConeInverseRotatedTriangle_mor₂ source target

/-- Public root facade: descent-refinement rotated cone starts at the target object. -/
theorem AnalyticMotivesRoot.rootFacade_descentRefinement_boundedMappingConeRotatedTriangle_obj₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeRotatedTriangle.obj₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.descentRefinement source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_descentRefinement_boundedMappingConeRotatedTriangle_obj₁ source target

/-- Public root facade: descent-refinement rotated cone second morphism is connecting. -/
theorem AnalyticMotivesRoot.rootFacade_descentRefinement_boundedMappingConeRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (TraceLocalizationInput.descentRefinement source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_descentRefinement_boundedMappingConeRotatedTriangle_mor₂ source target

/-- Public root facade: descent-refinement inverse-rotated cone middle vertex is source. -/
theorem AnalyticMotivesRoot.rootFacade_descentRefinement_boundedMappingConeInverseRotatedTriangle_obj₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeInverseRotatedTriangle.obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.descentRefinement source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_descentRefinement_boundedMappingConeInverseRotatedTriangle_obj₂ source target

/-- Public root facade: descent-refinement inverse-rotated cone second morphism is bounded map. -/
theorem AnalyticMotivesRoot.rootFacade_descentRefinement_boundedMappingConeInverseRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.descentRefinement source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_descentRefinement_boundedMappingConeInverseRotatedTriangle_mor₂ source target

/-- Public root facade: descent-schedule rotated cone starts at the target object. -/
theorem AnalyticMotivesRoot.rootFacade_descentSchedule_boundedMappingConeRotatedTriangle_obj₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeRotatedTriangle.obj₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.descentSchedule source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_descentSchedule_boundedMappingConeRotatedTriangle_obj₁ source target

/-- Public root facade: descent-schedule rotated cone second morphism is connecting. -/
theorem AnalyticMotivesRoot.rootFacade_descentSchedule_boundedMappingConeRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (TraceLocalizationInput.descentSchedule source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_descentSchedule_boundedMappingConeRotatedTriangle_mor₂ source target

/-- Public root facade: descent-schedule inverse-rotated cone middle vertex is source. -/
theorem AnalyticMotivesRoot.rootFacade_descentSchedule_boundedMappingConeInverseRotatedTriangle_obj₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeInverseRotatedTriangle.obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.descentSchedule source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_descentSchedule_boundedMappingConeInverseRotatedTriangle_obj₂ source target

/-- Public root facade: descent-schedule inverse-rotated cone second morphism is bounded map. -/
theorem AnalyticMotivesRoot.rootFacade_descentSchedule_boundedMappingConeInverseRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.descentSchedule source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_descentSchedule_boundedMappingConeInverseRotatedTriangle_mor₂ source target

/-- Public root facade: interval-Stokes rotated cone starts at the target object. -/
theorem AnalyticMotivesRoot.rootFacade_intervalStokes_boundedMappingConeRotatedTriangle_obj₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeRotatedTriangle.obj₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.intervalStokes source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_intervalStokes_boundedMappingConeRotatedTriangle_obj₁ source target

/-- Public root facade: interval-Stokes rotated cone second morphism is connecting. -/
theorem AnalyticMotivesRoot.rootFacade_intervalStokes_boundedMappingConeRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (TraceLocalizationInput.intervalStokes source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_intervalStokes_boundedMappingConeRotatedTriangle_mor₂ source target

/-- Public root facade: interval-Stokes inverse-rotated cone middle vertex is source. -/
theorem AnalyticMotivesRoot.rootFacade_intervalStokes_boundedMappingConeInverseRotatedTriangle_obj₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeInverseRotatedTriangle.obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.intervalStokes source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_intervalStokes_boundedMappingConeInverseRotatedTriangle_obj₂ source target

/-- Public root facade: interval-Stokes inverse-rotated cone second morphism is bounded map. -/
theorem AnalyticMotivesRoot.rootFacade_intervalStokes_boundedMappingConeInverseRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.intervalStokes source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_intervalStokes_boundedMappingConeInverseRotatedTriangle_mor₂ source target

/-- Public root facade: interval-Fubini rotated cone starts at the target object. -/
theorem AnalyticMotivesRoot.rootFacade_intervalFubini_boundedMappingConeRotatedTriangle_obj₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeRotatedTriangle.obj₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.intervalFubini source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_intervalFubini_boundedMappingConeRotatedTriangle_obj₁ source target

/-- Public root facade: interval-Fubini rotated cone second morphism is connecting. -/
theorem AnalyticMotivesRoot.rootFacade_intervalFubini_boundedMappingConeRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (TraceLocalizationInput.intervalFubini source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_intervalFubini_boundedMappingConeRotatedTriangle_mor₂ source target

/-- Public root facade: interval-Fubini inverse-rotated cone middle vertex is source. -/
theorem AnalyticMotivesRoot.rootFacade_intervalFubini_boundedMappingConeInverseRotatedTriangle_obj₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeInverseRotatedTriangle.obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.intervalFubini source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_intervalFubini_boundedMappingConeInverseRotatedTriangle_obj₂ source target

/-- Public root facade: interval-Fubini inverse-rotated cone second morphism is bounded map. -/
theorem AnalyticMotivesRoot.rootFacade_intervalFubini_boundedMappingConeInverseRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.intervalFubini source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_intervalFubini_boundedMappingConeInverseRotatedTriangle_mor₂ source target

/-- Public root facade: Tate-weight-drop rotated cone starts at the target object. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeRotatedTriangle_obj₁
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.obj₁ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.secondObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeRotatedTriangle_obj₁ source target

/-- Public root facade: Tate-weight-drop rotated cone second morphism is connecting. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.connectingMap
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeRotatedTriangle_mor₂ source target

/-- Public root facade: Tate-weight-drop inverse-rotated cone middle vertex is source. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeInverseRotatedTriangle_obj₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.obj₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstObject
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeInverseRotatedTriangle_obj₂ source target

/-- Public root facade: Tate-weight-drop inverse-rotated cone second morphism is bounded map. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeInverseRotatedTriangle_mor₂
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      TraceAnalyticAdditiveHomotopyCategory.BoundedMappingCone.firstMap
        (TraceLocalizationInput.tateWeightDrop source target).boundedAdditiveComplexHom :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeInverseRotatedTriangle_mor₂ source target

end AnalyticMotives
end LFunctions
end Boundary
