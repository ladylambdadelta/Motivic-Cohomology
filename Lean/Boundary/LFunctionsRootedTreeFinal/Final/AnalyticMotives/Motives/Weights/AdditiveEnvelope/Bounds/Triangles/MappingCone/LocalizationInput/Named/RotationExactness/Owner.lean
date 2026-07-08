import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.Named.Exactness.Owner

/-!
# Rotated exactness for named analytic-generator cone triangles

This file completes the named rotated and inverse-rotated cone exactness
surface for the six concrete analytic localization generators.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The descent-channel rotated cone triangle has zero second consecutive composite. -/
theorem TraceLocalizationInput.descentChannel_boundedMappingConeRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.descentChannel source target).boundedMappingConeRotatedTriangle.mor₃ =
      0 :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_second_comp_third
    (TraceLocalizationInput.descentChannel source target)

/-- The descent-channel rotated cone triangle has zero third shifted consecutive composite. -/
theorem TraceLocalizationInput.descentChannel_boundedMappingConeRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.descentChannel source target).boundedMappingConeRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_third_comp_shifted_first
    (TraceLocalizationInput.descentChannel source target)

/-- The descent-channel inverse-rotated cone triangle has zero second consecutive composite. -/
theorem TraceLocalizationInput.descentChannel_boundedMappingConeInverseRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeInverseRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.descentChannel source target).boundedMappingConeInverseRotatedTriangle.mor₃ =
      0 :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_second_comp_third
    (TraceLocalizationInput.descentChannel source target)

/-- The descent-channel inverse-rotated cone triangle has zero third shifted consecutive composite. -/
theorem TraceLocalizationInput.descentChannel_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeInverseRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.descentChannel source target).boundedMappingConeInverseRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    (TraceLocalizationInput.descentChannel source target)

/-- The descent-refinement rotated cone triangle has zero second consecutive composite. -/
theorem TraceLocalizationInput.descentRefinement_boundedMappingConeRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.descentRefinement source target).boundedMappingConeRotatedTriangle.mor₃ =
      0 :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_second_comp_third
    (TraceLocalizationInput.descentRefinement source target)

/-- The descent-refinement rotated cone triangle has zero third shifted consecutive composite. -/
theorem TraceLocalizationInput.descentRefinement_boundedMappingConeRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.descentRefinement source target).boundedMappingConeRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_third_comp_shifted_first
    (TraceLocalizationInput.descentRefinement source target)

/-- The descent-refinement inverse-rotated cone triangle has zero second consecutive composite. -/
theorem TraceLocalizationInput.descentRefinement_boundedMappingConeInverseRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeInverseRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.descentRefinement source target).boundedMappingConeInverseRotatedTriangle.mor₃ =
      0 :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_second_comp_third
    (TraceLocalizationInput.descentRefinement source target)

/-- The descent-refinement inverse-rotated cone triangle has zero third shifted consecutive composite. -/
theorem TraceLocalizationInput.descentRefinement_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeInverseRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.descentRefinement source target).boundedMappingConeInverseRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    (TraceLocalizationInput.descentRefinement source target)

/-- The descent-schedule rotated cone triangle has zero second consecutive composite. -/
theorem TraceLocalizationInput.descentSchedule_boundedMappingConeRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.descentSchedule source target).boundedMappingConeRotatedTriangle.mor₃ =
      0 :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_second_comp_third
    (TraceLocalizationInput.descentSchedule source target)

/-- The descent-schedule rotated cone triangle has zero third shifted consecutive composite. -/
theorem TraceLocalizationInput.descentSchedule_boundedMappingConeRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.descentSchedule source target).boundedMappingConeRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_third_comp_shifted_first
    (TraceLocalizationInput.descentSchedule source target)

/-- The descent-schedule inverse-rotated cone triangle has zero second consecutive composite. -/
theorem TraceLocalizationInput.descentSchedule_boundedMappingConeInverseRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeInverseRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.descentSchedule source target).boundedMappingConeInverseRotatedTriangle.mor₃ =
      0 :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_second_comp_third
    (TraceLocalizationInput.descentSchedule source target)

/-- The descent-schedule inverse-rotated cone triangle has zero third shifted consecutive composite. -/
theorem TraceLocalizationInput.descentSchedule_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeInverseRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.descentSchedule source target).boundedMappingConeInverseRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    (TraceLocalizationInput.descentSchedule source target)

/-- The interval-Stokes rotated cone triangle has zero second consecutive composite. -/
theorem TraceLocalizationInput.intervalStokes_boundedMappingConeRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.intervalStokes source target).boundedMappingConeRotatedTriangle.mor₃ =
      0 :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_second_comp_third
    (TraceLocalizationInput.intervalStokes source target)

/-- The interval-Stokes rotated cone triangle has zero third shifted consecutive composite. -/
theorem TraceLocalizationInput.intervalStokes_boundedMappingConeRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.intervalStokes source target).boundedMappingConeRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_third_comp_shifted_first
    (TraceLocalizationInput.intervalStokes source target)

/-- The interval-Stokes inverse-rotated cone triangle has zero second consecutive composite. -/
theorem TraceLocalizationInput.intervalStokes_boundedMappingConeInverseRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeInverseRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.intervalStokes source target).boundedMappingConeInverseRotatedTriangle.mor₃ =
      0 :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_second_comp_third
    (TraceLocalizationInput.intervalStokes source target)

/-- The interval-Stokes inverse-rotated cone triangle has zero third shifted consecutive composite. -/
theorem TraceLocalizationInput.intervalStokes_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeInverseRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.intervalStokes source target).boundedMappingConeInverseRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    (TraceLocalizationInput.intervalStokes source target)

/-- The interval-Fubini rotated cone triangle has zero second consecutive composite. -/
theorem TraceLocalizationInput.intervalFubini_boundedMappingConeRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.intervalFubini source target).boundedMappingConeRotatedTriangle.mor₃ =
      0 :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_second_comp_third
    (TraceLocalizationInput.intervalFubini source target)

/-- The interval-Fubini rotated cone triangle has zero third shifted consecutive composite. -/
theorem TraceLocalizationInput.intervalFubini_boundedMappingConeRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.intervalFubini source target).boundedMappingConeRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_third_comp_shifted_first
    (TraceLocalizationInput.intervalFubini source target)

/-- The interval-Fubini inverse-rotated cone triangle has zero second consecutive composite. -/
theorem TraceLocalizationInput.intervalFubini_boundedMappingConeInverseRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeInverseRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.intervalFubini source target).boundedMappingConeInverseRotatedTriangle.mor₃ =
      0 :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_second_comp_third
    (TraceLocalizationInput.intervalFubini source target)

/-- The interval-Fubini inverse-rotated cone triangle has zero third shifted consecutive composite. -/
theorem TraceLocalizationInput.intervalFubini_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeInverseRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.intervalFubini source target).boundedMappingConeInverseRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    (TraceLocalizationInput.intervalFubini source target)

/-- The Tate-weight-drop rotated cone triangle has zero second consecutive composite. -/
theorem TraceLocalizationInput.tateWeightDrop_boundedMappingConeRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.mor₃ =
      0 :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_second_comp_third
    (TraceLocalizationInput.tateWeightDrop source target)

/-- The Tate-weight-drop rotated cone triangle has zero third shifted consecutive composite. -/
theorem TraceLocalizationInput.tateWeightDrop_boundedMappingConeRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_third_comp_shifted_first
    (TraceLocalizationInput.tateWeightDrop source target)

/-- The Tate-weight-drop inverse-rotated cone triangle has zero second consecutive composite. -/
theorem TraceLocalizationInput.tateWeightDrop_boundedMappingConeInverseRotatedTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.mor₂ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.mor₃ =
      0 :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_second_comp_third
    (TraceLocalizationInput.tateWeightDrop source target)

/-- The Tate-weight-drop inverse-rotated cone triangle has zero third shifted consecutive composite. -/
theorem TraceLocalizationInput.tateWeightDrop_boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.mor₃ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_third_comp_shifted_first
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
