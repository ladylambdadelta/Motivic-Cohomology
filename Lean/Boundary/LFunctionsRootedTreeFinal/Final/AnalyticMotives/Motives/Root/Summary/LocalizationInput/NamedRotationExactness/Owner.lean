import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.Named.RotationExactness.Owner

/-!
# Motive-root named analytic-generator rotated cone exactness

This file exposes rotated and inverse-rotated bounded cone exactness for the
six concrete analytic localization generators through the motive-root summary
namespace.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Motive-root summary: descent-channel rotated second cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_descentChannel_boundedMappingConeRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.descentChannel source target).boundedMappingConeRotatedTriangle.mor₃ =
      0 :=
  TraceLocalizationInput.descentChannel_boundedMappingConeRotatedTriangle_second_comp_third source target

/-- Motive-root summary: descent-channel rotated third shifted cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_descentChannel_boundedMappingConeRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.descentChannel source target).boundedMappingConeRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.descentChannel_boundedMappingConeRotatedTriangle_third_comp_shifted_first source target

/-- Motive-root summary: descent-channel inverse-rotated second cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_descentChannel_boundedMappingConeInverseRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeInverseRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.descentChannel source target).boundedMappingConeInverseRotatedTriangle.mor₃ =
      0 :=
  TraceLocalizationInput.descentChannel_boundedMappingConeInverseRotatedTriangle_second_comp_third source target

/-- Motive-root summary: descent-channel inverse-rotated third shifted cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_descentChannel_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeInverseRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.descentChannel source target).boundedMappingConeInverseRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.descentChannel_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first source target

/-- Motive-root summary: descent-refinement rotated second cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_descentRefinement_boundedMappingConeRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.descentRefinement source target).boundedMappingConeRotatedTriangle.mor₃ =
      0 :=
  TraceLocalizationInput.descentRefinement_boundedMappingConeRotatedTriangle_second_comp_third source target

/-- Motive-root summary: descent-refinement rotated third shifted cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_descentRefinement_boundedMappingConeRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.descentRefinement source target).boundedMappingConeRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.descentRefinement_boundedMappingConeRotatedTriangle_third_comp_shifted_first source target

/-- Motive-root summary: descent-refinement inverse-rotated second cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_descentRefinement_boundedMappingConeInverseRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeInverseRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.descentRefinement source target).boundedMappingConeInverseRotatedTriangle.mor₃ =
      0 :=
  TraceLocalizationInput.descentRefinement_boundedMappingConeInverseRotatedTriangle_second_comp_third source target

/-- Motive-root summary: descent-refinement inverse-rotated third shifted cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_descentRefinement_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeInverseRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.descentRefinement source target).boundedMappingConeInverseRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.descentRefinement_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first source target

/-- Motive-root summary: descent-schedule rotated second cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_descentSchedule_boundedMappingConeRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.descentSchedule source target).boundedMappingConeRotatedTriangle.mor₃ =
      0 :=
  TraceLocalizationInput.descentSchedule_boundedMappingConeRotatedTriangle_second_comp_third source target

/-- Motive-root summary: descent-schedule rotated third shifted cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_descentSchedule_boundedMappingConeRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.descentSchedule source target).boundedMappingConeRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.descentSchedule_boundedMappingConeRotatedTriangle_third_comp_shifted_first source target

/-- Motive-root summary: descent-schedule inverse-rotated second cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_descentSchedule_boundedMappingConeInverseRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeInverseRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.descentSchedule source target).boundedMappingConeInverseRotatedTriangle.mor₃ =
      0 :=
  TraceLocalizationInput.descentSchedule_boundedMappingConeInverseRotatedTriangle_second_comp_third source target

/-- Motive-root summary: descent-schedule inverse-rotated third shifted cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_descentSchedule_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeInverseRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.descentSchedule source target).boundedMappingConeInverseRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.descentSchedule_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first source target

/-- Motive-root summary: interval-Stokes rotated second cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_intervalStokes_boundedMappingConeRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.intervalStokes source target).boundedMappingConeRotatedTriangle.mor₃ =
      0 :=
  TraceLocalizationInput.intervalStokes_boundedMappingConeRotatedTriangle_second_comp_third source target

/-- Motive-root summary: interval-Stokes rotated third shifted cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_intervalStokes_boundedMappingConeRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.intervalStokes source target).boundedMappingConeRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.intervalStokes_boundedMappingConeRotatedTriangle_third_comp_shifted_first source target

/-- Motive-root summary: interval-Stokes inverse-rotated second cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_intervalStokes_boundedMappingConeInverseRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeInverseRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.intervalStokes source target).boundedMappingConeInverseRotatedTriangle.mor₃ =
      0 :=
  TraceLocalizationInput.intervalStokes_boundedMappingConeInverseRotatedTriangle_second_comp_third source target

/-- Motive-root summary: interval-Stokes inverse-rotated third shifted cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_intervalStokes_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeInverseRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.intervalStokes source target).boundedMappingConeInverseRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.intervalStokes_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first source target

/-- Motive-root summary: interval-Fubini rotated second cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_intervalFubini_boundedMappingConeRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.intervalFubini source target).boundedMappingConeRotatedTriangle.mor₃ =
      0 :=
  TraceLocalizationInput.intervalFubini_boundedMappingConeRotatedTriangle_second_comp_third source target

/-- Motive-root summary: interval-Fubini rotated third shifted cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_intervalFubini_boundedMappingConeRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.intervalFubini source target).boundedMappingConeRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.intervalFubini_boundedMappingConeRotatedTriangle_third_comp_shifted_first source target

/-- Motive-root summary: interval-Fubini inverse-rotated second cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_intervalFubini_boundedMappingConeInverseRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeInverseRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.intervalFubini source target).boundedMappingConeInverseRotatedTriangle.mor₃ =
      0 :=
  TraceLocalizationInput.intervalFubini_boundedMappingConeInverseRotatedTriangle_second_comp_third source target

/-- Motive-root summary: interval-Fubini inverse-rotated third shifted cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_intervalFubini_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeInverseRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.intervalFubini source target).boundedMappingConeInverseRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.intervalFubini_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first source target

/-- Motive-root summary: Tate-weight-drop rotated second cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_tateWeightDrop_boundedMappingConeRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.mor₃ =
      0 :=
  TraceLocalizationInput.tateWeightDrop_boundedMappingConeRotatedTriangle_second_comp_third source target

/-- Motive-root summary: Tate-weight-drop rotated third shifted cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_tateWeightDrop_boundedMappingConeRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.tateWeightDrop_boundedMappingConeRotatedTriangle_third_comp_shifted_first source target

/-- Motive-root summary: Tate-weight-drop inverse-rotated second cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_tateWeightDrop_boundedMappingConeInverseRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.mor₃ =
      0 :=
  TraceLocalizationInput.tateWeightDrop_boundedMappingConeInverseRotatedTriangle_second_comp_third source target

/-- Motive-root summary: Tate-weight-drop inverse-rotated third shifted cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_tateWeightDrop_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.tateWeightDrop_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first source target

end AnalyticMotives
end LFunctions
end Boundary
