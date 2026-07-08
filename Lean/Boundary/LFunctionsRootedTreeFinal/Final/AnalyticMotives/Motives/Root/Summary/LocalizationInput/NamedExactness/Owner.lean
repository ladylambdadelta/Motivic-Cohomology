import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.Named.Exactness.Owner

/-!
# Motive-root named analytic-generator cone exactness

This file exposes unrotated bounded cone exactness for the six concrete
analytic localization generators through the motive-root summary namespace.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Motive-root summary: descent-channel first consecutive cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_descentChannel_boundedMappingConeTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangle.mor₁ ≫
        (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangle.mor₂ =
      0 :=
  TraceLocalizationInput.descentChannel_boundedMappingConeTriangle_first_comp_second source target

/-- Motive-root summary: descent-channel second consecutive cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_descentChannel_boundedMappingConeTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangle.mor₂ ≫
        (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangle.mor₃ =
      0 :=
  TraceLocalizationInput.descentChannel_boundedMappingConeTriangle_second_comp_third source target

/-- Motive-root summary: descent-channel third shifted cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_descentChannel_boundedMappingConeTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangle.mor₃ ≫
        (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.descentChannel_boundedMappingConeTriangle_third_comp_shifted_first source target

/-- Motive-root summary: descent-refinement first consecutive cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_descentRefinement_boundedMappingConeTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangle.mor₁ ≫
        (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangle.mor₂ =
      0 :=
  TraceLocalizationInput.descentRefinement_boundedMappingConeTriangle_first_comp_second source target

/-- Motive-root summary: descent-refinement second consecutive cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_descentRefinement_boundedMappingConeTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangle.mor₂ ≫
        (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangle.mor₃ =
      0 :=
  TraceLocalizationInput.descentRefinement_boundedMappingConeTriangle_second_comp_third source target

/-- Motive-root summary: descent-refinement third shifted cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_descentRefinement_boundedMappingConeTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangle.mor₃ ≫
        (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.descentRefinement_boundedMappingConeTriangle_third_comp_shifted_first source target

/-- Motive-root summary: descent-schedule first consecutive cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_descentSchedule_boundedMappingConeTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangle.mor₁ ≫
        (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangle.mor₂ =
      0 :=
  TraceLocalizationInput.descentSchedule_boundedMappingConeTriangle_first_comp_second source target

/-- Motive-root summary: descent-schedule second consecutive cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_descentSchedule_boundedMappingConeTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangle.mor₂ ≫
        (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangle.mor₃ =
      0 :=
  TraceLocalizationInput.descentSchedule_boundedMappingConeTriangle_second_comp_third source target

/-- Motive-root summary: descent-schedule third shifted cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_descentSchedule_boundedMappingConeTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangle.mor₃ ≫
        (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.descentSchedule_boundedMappingConeTriangle_third_comp_shifted_first source target

/-- Motive-root summary: interval-Stokes first consecutive cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_intervalStokes_boundedMappingConeTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangle.mor₁ ≫
        (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangle.mor₂ =
      0 :=
  TraceLocalizationInput.intervalStokes_boundedMappingConeTriangle_first_comp_second source target

/-- Motive-root summary: interval-Stokes second consecutive cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_intervalStokes_boundedMappingConeTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangle.mor₂ ≫
        (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangle.mor₃ =
      0 :=
  TraceLocalizationInput.intervalStokes_boundedMappingConeTriangle_second_comp_third source target

/-- Motive-root summary: interval-Stokes third shifted cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_intervalStokes_boundedMappingConeTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangle.mor₃ ≫
        (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.intervalStokes_boundedMappingConeTriangle_third_comp_shifted_first source target

/-- Motive-root summary: interval-Fubini first consecutive cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_intervalFubini_boundedMappingConeTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangle.mor₁ ≫
        (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangle.mor₂ =
      0 :=
  TraceLocalizationInput.intervalFubini_boundedMappingConeTriangle_first_comp_second source target

/-- Motive-root summary: interval-Fubini second consecutive cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_intervalFubini_boundedMappingConeTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangle.mor₂ ≫
        (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangle.mor₃ =
      0 :=
  TraceLocalizationInput.intervalFubini_boundedMappingConeTriangle_second_comp_third source target

/-- Motive-root summary: interval-Fubini third shifted cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_intervalFubini_boundedMappingConeTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangle.mor₃ ≫
        (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.intervalFubini_boundedMappingConeTriangle_third_comp_shifted_first source target

/-- Motive-root summary: Tate-weight-drop first consecutive cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_tateWeightDrop_boundedMappingConeTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₁ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₂ =
      0 :=
  TraceLocalizationInput.tateWeightDrop_boundedMappingConeTriangle_first_comp_second source target

/-- Motive-root summary: Tate-weight-drop second consecutive cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_tateWeightDrop_boundedMappingConeTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₂ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₃ =
      0 :=
  TraceLocalizationInput.tateWeightDrop_boundedMappingConeTriangle_second_comp_third source target

/-- Motive-root summary: Tate-weight-drop third shifted cone composite vanishes. -/
theorem TraceAnalyticMotive.rootSummary_tateWeightDrop_boundedMappingConeTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₃ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.tateWeightDrop_boundedMappingConeTriangle_third_comp_shifted_first source target

end AnalyticMotives
end LFunctions
end Boundary
