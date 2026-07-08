import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Root.Motives.Summary.LocalizationInput.NamedExactness.Owner

/-!
# Public named analytic-generator cone exactness facade

This file exposes unrotated named analytic-generator cone exactness at the
public root surface.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- Public root facade: descent-channel first cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_descentChannel_boundedMappingConeTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangle.mor₁ ≫
        (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangle.mor₂ =
      0 :=
  AnalyticMotivesRoot.rootSummary_descentChannel_boundedMappingConeTriangle_first_comp_second source target

/-- Public root facade: descent-channel second cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_descentChannel_boundedMappingConeTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangle.mor₂ ≫
        (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangle.mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_descentChannel_boundedMappingConeTriangle_second_comp_third source target

/-- Public root facade: descent-channel third shifted cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_descentChannel_boundedMappingConeTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangle.mor₃ ≫
        (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_descentChannel_boundedMappingConeTriangle_third_comp_shifted_first source target

/-- Public root facade: descent-refinement first cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_descentRefinement_boundedMappingConeTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangle.mor₁ ≫
        (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangle.mor₂ =
      0 :=
  AnalyticMotivesRoot.rootSummary_descentRefinement_boundedMappingConeTriangle_first_comp_second source target

/-- Public root facade: descent-refinement second cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_descentRefinement_boundedMappingConeTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangle.mor₂ ≫
        (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangle.mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_descentRefinement_boundedMappingConeTriangle_second_comp_third source target

/-- Public root facade: descent-refinement third shifted cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_descentRefinement_boundedMappingConeTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangle.mor₃ ≫
        (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_descentRefinement_boundedMappingConeTriangle_third_comp_shifted_first source target

/-- Public root facade: descent-schedule first cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_descentSchedule_boundedMappingConeTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangle.mor₁ ≫
        (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangle.mor₂ =
      0 :=
  AnalyticMotivesRoot.rootSummary_descentSchedule_boundedMappingConeTriangle_first_comp_second source target

/-- Public root facade: descent-schedule second cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_descentSchedule_boundedMappingConeTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangle.mor₂ ≫
        (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangle.mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_descentSchedule_boundedMappingConeTriangle_second_comp_third source target

/-- Public root facade: descent-schedule third shifted cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_descentSchedule_boundedMappingConeTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangle.mor₃ ≫
        (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_descentSchedule_boundedMappingConeTriangle_third_comp_shifted_first source target

/-- Public root facade: interval-Stokes first cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_intervalStokes_boundedMappingConeTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangle.mor₁ ≫
        (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangle.mor₂ =
      0 :=
  AnalyticMotivesRoot.rootSummary_intervalStokes_boundedMappingConeTriangle_first_comp_second source target

/-- Public root facade: interval-Stokes second cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_intervalStokes_boundedMappingConeTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangle.mor₂ ≫
        (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangle.mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_intervalStokes_boundedMappingConeTriangle_second_comp_third source target

/-- Public root facade: interval-Stokes third shifted cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_intervalStokes_boundedMappingConeTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangle.mor₃ ≫
        (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_intervalStokes_boundedMappingConeTriangle_third_comp_shifted_first source target

/-- Public root facade: interval-Fubini first cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_intervalFubini_boundedMappingConeTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangle.mor₁ ≫
        (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangle.mor₂ =
      0 :=
  AnalyticMotivesRoot.rootSummary_intervalFubini_boundedMappingConeTriangle_first_comp_second source target

/-- Public root facade: interval-Fubini second cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_intervalFubini_boundedMappingConeTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangle.mor₂ ≫
        (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangle.mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_intervalFubini_boundedMappingConeTriangle_second_comp_third source target

/-- Public root facade: interval-Fubini third shifted cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_intervalFubini_boundedMappingConeTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangle.mor₃ ≫
        (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_intervalFubini_boundedMappingConeTriangle_third_comp_shifted_first source target

/-- Public root facade: Tate-weight-drop first cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₁ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₂ =
      0 :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeTriangle_first_comp_second source target

/-- Public root facade: Tate-weight-drop second cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₂ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₃ =
      0 :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeTriangle_second_comp_third source target

/-- Public root facade: Tate-weight-drop third shifted cone composite vanishes. -/
theorem AnalyticMotivesRoot.rootFacade_tateWeightDrop_boundedMappingConeTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₃ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  AnalyticMotivesRoot.rootSummary_tateWeightDrop_boundedMappingConeTriangle_third_comp_shifted_first source target

end AnalyticMotives
end LFunctions
end Boundary
