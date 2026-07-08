import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Root.Summary.LocalizationInput.NamedExactness.Owner

/-!
# Top-root motive summary for named analytic-generator cone exactness

This file forwards unrotated named analytic-generator cone exactness to the
top-root motive summary namespace.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Top-root motive summary: descent-channel first cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootSummary_descentChannel_boundedMappingConeTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangle.mor₁ ≫
        (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangle.mor₂ =
      0 :=
  TraceAnalyticMotive.rootSummary_descentChannel_boundedMappingConeTriangle_first_comp_second source target

/-- Top-root motive summary: descent-channel second cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootSummary_descentChannel_boundedMappingConeTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangle.mor₂ ≫
        (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangle.mor₃ =
      0 :=
  TraceAnalyticMotive.rootSummary_descentChannel_boundedMappingConeTriangle_second_comp_third source target

/-- Top-root motive summary: descent-channel third shifted cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootSummary_descentChannel_boundedMappingConeTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangle.mor₃ ≫
        (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceAnalyticMotive.rootSummary_descentChannel_boundedMappingConeTriangle_third_comp_shifted_first source target

/-- Top-root motive summary: descent-refinement first cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootSummary_descentRefinement_boundedMappingConeTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangle.mor₁ ≫
        (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangle.mor₂ =
      0 :=
  TraceAnalyticMotive.rootSummary_descentRefinement_boundedMappingConeTriangle_first_comp_second source target

/-- Top-root motive summary: descent-refinement second cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootSummary_descentRefinement_boundedMappingConeTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangle.mor₂ ≫
        (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangle.mor₃ =
      0 :=
  TraceAnalyticMotive.rootSummary_descentRefinement_boundedMappingConeTriangle_second_comp_third source target

/-- Top-root motive summary: descent-refinement third shifted cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootSummary_descentRefinement_boundedMappingConeTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangle.mor₃ ≫
        (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceAnalyticMotive.rootSummary_descentRefinement_boundedMappingConeTriangle_third_comp_shifted_first source target

/-- Top-root motive summary: descent-schedule first cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootSummary_descentSchedule_boundedMappingConeTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangle.mor₁ ≫
        (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangle.mor₂ =
      0 :=
  TraceAnalyticMotive.rootSummary_descentSchedule_boundedMappingConeTriangle_first_comp_second source target

/-- Top-root motive summary: descent-schedule second cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootSummary_descentSchedule_boundedMappingConeTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangle.mor₂ ≫
        (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangle.mor₃ =
      0 :=
  TraceAnalyticMotive.rootSummary_descentSchedule_boundedMappingConeTriangle_second_comp_third source target

/-- Top-root motive summary: descent-schedule third shifted cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootSummary_descentSchedule_boundedMappingConeTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangle.mor₃ ≫
        (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceAnalyticMotive.rootSummary_descentSchedule_boundedMappingConeTriangle_third_comp_shifted_first source target

/-- Top-root motive summary: interval-Stokes first cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootSummary_intervalStokes_boundedMappingConeTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangle.mor₁ ≫
        (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangle.mor₂ =
      0 :=
  TraceAnalyticMotive.rootSummary_intervalStokes_boundedMappingConeTriangle_first_comp_second source target

/-- Top-root motive summary: interval-Stokes second cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootSummary_intervalStokes_boundedMappingConeTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangle.mor₂ ≫
        (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangle.mor₃ =
      0 :=
  TraceAnalyticMotive.rootSummary_intervalStokes_boundedMappingConeTriangle_second_comp_third source target

/-- Top-root motive summary: interval-Stokes third shifted cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootSummary_intervalStokes_boundedMappingConeTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangle.mor₃ ≫
        (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceAnalyticMotive.rootSummary_intervalStokes_boundedMappingConeTriangle_third_comp_shifted_first source target

/-- Top-root motive summary: interval-Fubini first cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootSummary_intervalFubini_boundedMappingConeTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangle.mor₁ ≫
        (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangle.mor₂ =
      0 :=
  TraceAnalyticMotive.rootSummary_intervalFubini_boundedMappingConeTriangle_first_comp_second source target

/-- Top-root motive summary: interval-Fubini second cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootSummary_intervalFubini_boundedMappingConeTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangle.mor₂ ≫
        (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangle.mor₃ =
      0 :=
  TraceAnalyticMotive.rootSummary_intervalFubini_boundedMappingConeTriangle_second_comp_third source target

/-- Top-root motive summary: interval-Fubini third shifted cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootSummary_intervalFubini_boundedMappingConeTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangle.mor₃ ≫
        (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceAnalyticMotive.rootSummary_intervalFubini_boundedMappingConeTriangle_third_comp_shifted_first source target

/-- Top-root motive summary: Tate-weight-drop first cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₁ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₂ =
      0 :=
  TraceAnalyticMotive.rootSummary_tateWeightDrop_boundedMappingConeTriangle_first_comp_second source target

/-- Top-root motive summary: Tate-weight-drop second cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₂ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₃ =
      0 :=
  TraceAnalyticMotive.rootSummary_tateWeightDrop_boundedMappingConeTriangle_second_comp_third source target

/-- Top-root motive summary: Tate-weight-drop third shifted cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₃ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceAnalyticMotive.rootSummary_tateWeightDrop_boundedMappingConeTriangle_third_comp_shifted_first source target

end AnalyticMotives
end LFunctions
end Boundary
