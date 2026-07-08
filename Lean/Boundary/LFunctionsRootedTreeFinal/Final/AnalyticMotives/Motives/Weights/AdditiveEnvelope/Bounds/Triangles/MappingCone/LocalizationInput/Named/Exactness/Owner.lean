import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.Named.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.AnalyticMotives.Motives.Weights.AdditiveEnvelope.Bounds.Triangles.MappingCone.LocalizationInput.Rotation.Exactness.Owner

/-!
# Exactness of named analytic-generator cone triangles

This file specializes unrotated and rotated localization-input cone exactness
to the six concrete analytic generators.
-/

noncomputable section

namespace Boundary
namespace LFunctions
namespace AnalyticMotives

open CategoryTheory

/-- The descent-channel cone triangle has zero second consecutive composite. -/
theorem TraceLocalizationInput.descentChannel_boundedMappingConeTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangle.mor₂ ≫
        (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangle.mor₃ =
      0 :=
  TraceLocalizationInput.boundedMappingConeTriangle_second_comp_third
    (TraceLocalizationInput.descentChannel source target)

/-- The descent-channel cone triangle has zero third shifted consecutive composite. -/
theorem TraceLocalizationInput.descentChannel_boundedMappingConeTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangle.mor₃ ≫
        (TraceLocalizationInput.descentChannel source target).boundedMappingConeTriangle.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.boundedMappingConeTriangle_third_comp_shifted_first
    (TraceLocalizationInput.descentChannel source target)

/-- The descent-channel rotated cone triangle has zero first consecutive composite. -/
theorem TraceLocalizationInput.descentChannel_boundedMappingConeRotatedTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeRotatedTriangle.mor₁ ≫
        (TraceLocalizationInput.descentChannel source target).boundedMappingConeRotatedTriangle.mor₂ =
      0 :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_first_comp_second
    (TraceLocalizationInput.descentChannel source target)

/-- The descent-channel inverse-rotated cone triangle has zero first consecutive composite. -/
theorem TraceLocalizationInput.descentChannel_boundedMappingConeInverseRotatedTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentChannel source target).boundedMappingConeInverseRotatedTriangle.mor₁ ≫
        (TraceLocalizationInput.descentChannel source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      0 :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_first_comp_second
    (TraceLocalizationInput.descentChannel source target)

/-- The descent-refinement cone triangle has zero second consecutive composite. -/
theorem TraceLocalizationInput.descentRefinement_boundedMappingConeTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangle.mor₂ ≫
        (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangle.mor₃ =
      0 :=
  TraceLocalizationInput.boundedMappingConeTriangle_second_comp_third
    (TraceLocalizationInput.descentRefinement source target)

/-- The descent-refinement cone triangle has zero third shifted consecutive composite. -/
theorem TraceLocalizationInput.descentRefinement_boundedMappingConeTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangle.mor₃ ≫
        (TraceLocalizationInput.descentRefinement source target).boundedMappingConeTriangle.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.boundedMappingConeTriangle_third_comp_shifted_first
    (TraceLocalizationInput.descentRefinement source target)

/-- The descent-refinement rotated cone triangle has zero first consecutive composite. -/
theorem TraceLocalizationInput.descentRefinement_boundedMappingConeRotatedTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeRotatedTriangle.mor₁ ≫
        (TraceLocalizationInput.descentRefinement source target).boundedMappingConeRotatedTriangle.mor₂ =
      0 :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_first_comp_second
    (TraceLocalizationInput.descentRefinement source target)

/-- The descent-refinement inverse-rotated cone triangle has zero first consecutive composite. -/
theorem TraceLocalizationInput.descentRefinement_boundedMappingConeInverseRotatedTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentRefinement source target).boundedMappingConeInverseRotatedTriangle.mor₁ ≫
        (TraceLocalizationInput.descentRefinement source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      0 :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_first_comp_second
    (TraceLocalizationInput.descentRefinement source target)

/-- The descent-schedule cone triangle has zero second consecutive composite. -/
theorem TraceLocalizationInput.descentSchedule_boundedMappingConeTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangle.mor₂ ≫
        (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangle.mor₃ =
      0 :=
  TraceLocalizationInput.boundedMappingConeTriangle_second_comp_third
    (TraceLocalizationInput.descentSchedule source target)

/-- The descent-schedule cone triangle has zero third shifted consecutive composite. -/
theorem TraceLocalizationInput.descentSchedule_boundedMappingConeTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangle.mor₃ ≫
        (TraceLocalizationInput.descentSchedule source target).boundedMappingConeTriangle.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.boundedMappingConeTriangle_third_comp_shifted_first
    (TraceLocalizationInput.descentSchedule source target)

/-- The descent-schedule rotated cone triangle has zero first consecutive composite. -/
theorem TraceLocalizationInput.descentSchedule_boundedMappingConeRotatedTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeRotatedTriangle.mor₁ ≫
        (TraceLocalizationInput.descentSchedule source target).boundedMappingConeRotatedTriangle.mor₂ =
      0 :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_first_comp_second
    (TraceLocalizationInput.descentSchedule source target)

/-- The descent-schedule inverse-rotated cone triangle has zero first consecutive composite. -/
theorem TraceLocalizationInput.descentSchedule_boundedMappingConeInverseRotatedTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.descentSchedule source target).boundedMappingConeInverseRotatedTriangle.mor₁ ≫
        (TraceLocalizationInput.descentSchedule source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      0 :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_first_comp_second
    (TraceLocalizationInput.descentSchedule source target)

/-- The interval-Stokes cone triangle has zero second consecutive composite. -/
theorem TraceLocalizationInput.intervalStokes_boundedMappingConeTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangle.mor₂ ≫
        (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangle.mor₃ =
      0 :=
  TraceLocalizationInput.boundedMappingConeTriangle_second_comp_third
    (TraceLocalizationInput.intervalStokes source target)

/-- The interval-Stokes cone triangle has zero third shifted consecutive composite. -/
theorem TraceLocalizationInput.intervalStokes_boundedMappingConeTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangle.mor₃ ≫
        (TraceLocalizationInput.intervalStokes source target).boundedMappingConeTriangle.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.boundedMappingConeTriangle_third_comp_shifted_first
    (TraceLocalizationInput.intervalStokes source target)

/-- The interval-Stokes rotated cone triangle has zero first consecutive composite. -/
theorem TraceLocalizationInput.intervalStokes_boundedMappingConeRotatedTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeRotatedTriangle.mor₁ ≫
        (TraceLocalizationInput.intervalStokes source target).boundedMappingConeRotatedTriangle.mor₂ =
      0 :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_first_comp_second
    (TraceLocalizationInput.intervalStokes source target)

/-- The interval-Stokes inverse-rotated cone triangle has zero first consecutive composite. -/
theorem TraceLocalizationInput.intervalStokes_boundedMappingConeInverseRotatedTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalStokes source target).boundedMappingConeInverseRotatedTriangle.mor₁ ≫
        (TraceLocalizationInput.intervalStokes source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      0 :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_first_comp_second
    (TraceLocalizationInput.intervalStokes source target)

/-- The interval-Fubini cone triangle has zero second consecutive composite. -/
theorem TraceLocalizationInput.intervalFubini_boundedMappingConeTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangle.mor₂ ≫
        (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangle.mor₃ =
      0 :=
  TraceLocalizationInput.boundedMappingConeTriangle_second_comp_third
    (TraceLocalizationInput.intervalFubini source target)

/-- The interval-Fubini cone triangle has zero third shifted consecutive composite. -/
theorem TraceLocalizationInput.intervalFubini_boundedMappingConeTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangle.mor₃ ≫
        (TraceLocalizationInput.intervalFubini source target).boundedMappingConeTriangle.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.boundedMappingConeTriangle_third_comp_shifted_first
    (TraceLocalizationInput.intervalFubini source target)

/-- The interval-Fubini rotated cone triangle has zero first consecutive composite. -/
theorem TraceLocalizationInput.intervalFubini_boundedMappingConeRotatedTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeRotatedTriangle.mor₁ ≫
        (TraceLocalizationInput.intervalFubini source target).boundedMappingConeRotatedTriangle.mor₂ =
      0 :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_first_comp_second
    (TraceLocalizationInput.intervalFubini source target)

/-- The interval-Fubini inverse-rotated cone triangle has zero first consecutive composite. -/
theorem TraceLocalizationInput.intervalFubini_boundedMappingConeInverseRotatedTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.intervalFubini source target).boundedMappingConeInverseRotatedTriangle.mor₁ ≫
        (TraceLocalizationInput.intervalFubini source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      0 :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_first_comp_second
    (TraceLocalizationInput.intervalFubini source target)

/-- The Tate-weight-drop cone triangle has zero second consecutive composite. -/
theorem TraceLocalizationInput.tateWeightDrop_boundedMappingConeTriangle_second_comp_third
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₂ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₃ =
      0 :=
  TraceLocalizationInput.boundedMappingConeTriangle_second_comp_third
    (TraceLocalizationInput.tateWeightDrop source target)

/-- The Tate-weight-drop cone triangle has zero third shifted consecutive composite. -/
theorem TraceLocalizationInput.tateWeightDrop_boundedMappingConeTriangle_third_comp_shifted_first
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₃ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeTriangle.triangle.mor₁⟦(1 : ℤ)⟧' =
      0 :=
  TraceLocalizationInput.boundedMappingConeTriangle_third_comp_shifted_first
    (TraceLocalizationInput.tateWeightDrop source target)

/-- The Tate-weight-drop rotated cone triangle has zero first consecutive composite. -/
theorem TraceLocalizationInput.tateWeightDrop_boundedMappingConeRotatedTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.mor₁ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeRotatedTriangle.mor₂ =
      0 :=
  TraceLocalizationInput.boundedMappingConeRotatedTriangle_first_comp_second
    (TraceLocalizationInput.tateWeightDrop source target)

/-- The Tate-weight-drop inverse-rotated cone triangle has zero first consecutive composite. -/
theorem TraceLocalizationInput.tateWeightDrop_boundedMappingConeInverseRotatedTriangle_first_comp_second
    (source target : QTraceExpression) :
    (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.mor₁ ≫
        (TraceLocalizationInput.tateWeightDrop source target).boundedMappingConeInverseRotatedTriangle.mor₂ =
      0 :=
  TraceLocalizationInput.boundedMappingConeInverseRotatedTriangle_first_comp_second
    (TraceLocalizationInput.tateWeightDrop source target)

end AnalyticMotives
end LFunctions
end Boundary
