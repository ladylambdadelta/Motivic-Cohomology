import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Motives.Summary.LocalizationInput.NamedRotationExactness.Owner

/-!
# Public named rotated cone exactness facade

This file exposes named analytic-generator rotated and inverse-rotated cone
exactness at the public root surface.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Public root facade: descent-channel rotated second cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_descentChannel_boundedMappingConeRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.descentChannel source target).boundedMappingConeRotatedTriangle.mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_descentChannel_boundedMappingConeRotatedTriangle_second_comp_third source target

/-- Public root facade: descent-channel rotated third shifted cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_descentChannel_boundedMappingConeRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.descentChannel source target).boundedMappingConeRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_descentChannel_boundedMappingConeRotatedTriangle_third_comp_shifted_first source target

/-- Public root facade: descent-channel inverse-rotated second cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_descentChannel_boundedMappingConeInverseRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeInverseRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.descentChannel source target).boundedMappingConeInverseRotatedTriangle.mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_descentChannel_boundedMappingConeInverseRotatedTriangle_second_comp_third source target

/-- Public root facade: descent-channel inverse-rotated third shifted cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_descentChannel_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeInverseRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.descentChannel source target).boundedMappingConeInverseRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_descentChannel_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first source target

/-- Public root facade: descent-refinement rotated second cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_descentRefinement_boundedMappingConeRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.descentRefinement source target).boundedMappingConeRotatedTriangle.mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_descentRefinement_boundedMappingConeRotatedTriangle_second_comp_third source target

/-- Public root facade: descent-refinement rotated third shifted cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_descentRefinement_boundedMappingConeRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.descentRefinement source target).boundedMappingConeRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_descentRefinement_boundedMappingConeRotatedTriangle_third_comp_shifted_first source target

/-- Public root facade: descent-refinement inverse-rotated second cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_descentRefinement_boundedMappingConeInverseRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeInverseRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.descentRefinement source target).boundedMappingConeInverseRotatedTriangle.mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_descentRefinement_boundedMappingConeInverseRotatedTriangle_second_comp_third source target

/-- Public root facade: descent-refinement inverse-rotated third shifted cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_descentRefinement_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeInverseRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.descentRefinement source target).boundedMappingConeInverseRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_descentRefinement_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first source target

/-- Public root facade: descent-schedule rotated second cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_descentSchedule_boundedMappingConeRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.descentSchedule source target).boundedMappingConeRotatedTriangle.mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_descentSchedule_boundedMappingConeRotatedTriangle_second_comp_third source target

/-- Public root facade: descent-schedule rotated third shifted cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_descentSchedule_boundedMappingConeRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.descentSchedule source target).boundedMappingConeRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_descentSchedule_boundedMappingConeRotatedTriangle_third_comp_shifted_first source target

/-- Public root facade: descent-schedule inverse-rotated second cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_descentSchedule_boundedMappingConeInverseRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeInverseRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.descentSchedule source target).boundedMappingConeInverseRotatedTriangle.mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_descentSchedule_boundedMappingConeInverseRotatedTriangle_second_comp_third source target

/-- Public root facade: descent-schedule inverse-rotated third shifted cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_descentSchedule_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeInverseRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.descentSchedule source target).boundedMappingConeInverseRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_descentSchedule_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first source target

/-- Public root facade: interval-Stokes rotated second cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_intervalStokes_boundedMappingConeRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.intervalStokes source target).boundedMappingConeRotatedTriangle.mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_intervalStokes_boundedMappingConeRotatedTriangle_second_comp_third source target

/-- Public root facade: interval-Stokes rotated third shifted cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_intervalStokes_boundedMappingConeRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.intervalStokes source target).boundedMappingConeRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_intervalStokes_boundedMappingConeRotatedTriangle_third_comp_shifted_first source target

/-- Public root facade: interval-Stokes inverse-rotated second cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_intervalStokes_boundedMappingConeInverseRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeInverseRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.intervalStokes source target).boundedMappingConeInverseRotatedTriangle.mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_intervalStokes_boundedMappingConeInverseRotatedTriangle_second_comp_third source target

/-- Public root facade: interval-Stokes inverse-rotated third shifted cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_intervalStokes_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeInverseRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.intervalStokes source target).boundedMappingConeInverseRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_intervalStokes_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first source target

/-- Public root facade: interval-Fubini rotated second cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_intervalFubini_boundedMappingConeRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.intervalFubini source target).boundedMappingConeRotatedTriangle.mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_intervalFubini_boundedMappingConeRotatedTriangle_second_comp_third source target

/-- Public root facade: interval-Fubini rotated third shifted cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_intervalFubini_boundedMappingConeRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.intervalFubini source target).boundedMappingConeRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_intervalFubini_boundedMappingConeRotatedTriangle_third_comp_shifted_first source target

/-- Public root facade: interval-Fubini inverse-rotated second cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_intervalFubini_boundedMappingConeInverseRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeInverseRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.intervalFubini source target).boundedMappingConeInverseRotatedTriangle.mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_intervalFubini_boundedMappingConeInverseRotatedTriangle_second_comp_third source target

/-- Public root facade: interval-Fubini inverse-rotated third shifted cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_intervalFubini_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeInverseRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.intervalFubini source target).boundedMappingConeInverseRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_intervalFubini_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first source target

/-- Public root facade: Tate-weight-drop rotated second cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeRotatedTriangle_second_comp_third source target

/-- Public root facade: Tate-weight-drop rotated third shifted cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeRotatedTriangle_third_comp_shifted_first source target

/-- Public root facade: Tate-weight-drop inverse-rotated second cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeInverseRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeInverseRotatedTriangle_second_comp_third source target

/-- Public root facade: Tate-weight-drop inverse-rotated third shifted cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first source target

end AnalyticMotives
end LFunctions
end Boundary
