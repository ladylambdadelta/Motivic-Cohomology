import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CountableAvoidingScheduleCore

/-!
# Canonical analytic inputs for the Weil positivity owner

This file constructs the autocorrelation-specific countable-avoidance schedule
for the completed explicit-formula contour.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter

namespace ZetaAdmissibleFunction

/-- A supplied cofinal height function avoiding the autocorrelation horizontal
bad-height set gives the autocorrelation horizontal avoiding schedule. -/
def zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule_of_height
    (f : ZetaAdmissibleFunction)
    (height : ℝ → ℝ)
    (hcofinal : Tendsto height atTop atTop)
    (havoid : ∀ u : ℝ,
      height u ∉
        explicitFormulaContourHorizontalBadHeightSet
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)) :
    ExplicitFormulaHorizontalAvoidingHeightSchedule
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  explicitFormulaHorizontalAvoidingHeightSchedule_of_height
    (zetaCompletedExplicitFormula_autocorrelation_contourFamily f)
    height
    hcofinal
    havoid

/-- A supplied cofinal schedule avoiding the autocorrelation horizontal
bad-height set is already the autocorrelation horizontal avoiding schedule. -/
def zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule_of_schedule
    (f : ZetaAdmissibleFunction)
    (schedule :
      CountableAvoidingCofinalHeightSchedule
        (explicitFormulaContourHorizontalBadHeightSet
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))) :
    ExplicitFormulaHorizontalAvoidingHeightSchedule
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  schedule

/-- A supplied autocorrelation horizontal avoiding schedule has positive
top-and-bottom height separation from every finite singular-point list. -/
theorem zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule_singular_points_top_bottom_positive_separation_of_schedule
    (f : ZetaAdmissibleFunction)
    (schedule :
      ExplicitFormulaHorizontalAvoidingHeightSchedule
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (points : List ℂ)
    (hpoints :
      ∀ z : ℂ, z ∈ points → explicitFormulaContourSingularPoint z)
    (u : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ z : ℂ, z ∈ points →
        δ ≤ ‖schedule.height u - z.im‖ ∧
          δ ≤ ‖schedule.height u - (-z.im)‖ :=
  ExplicitFormulaHorizontalAvoidingHeightSchedule.singular_points_top_bottom_positive_separation
    schedule
    points
    hpoints
    u

/-- The autocorrelation contour family has a canonical horizontal avoiding schedule. -/
noncomputable def zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule
    (f : ZetaAdmissibleFunction) :
    ExplicitFormulaHorizontalAvoidingHeightSchedule
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f) :=
  CountableAvoidingCofinalHeightSchedule.of_countable_bad_set
    (explicitFormulaContourHorizontalBadHeightSet
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))
    (explicitFormulaContourHorizontalBadHeightSet_countable
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f))

/-- The canonical autocorrelation horizontal avoiding schedule has positive
top-and-bottom height separation from every finite singular-point list. -/
theorem zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule_singular_points_top_bottom_positive_separation
    (f : ZetaAdmissibleFunction)
    (points : List ℂ)
    (hpoints :
      ∀ z : ℂ, z ∈ points → explicitFormulaContourSingularPoint z)
    (u : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ z : ℂ, z ∈ points →
        δ ≤
            ‖(zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f).height u -
              z.im‖ ∧
          δ ≤
            ‖(zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f).height u -
              (-z.im)‖ :=
  zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule_singular_points_top_bottom_positive_separation_of_schedule
    f
    (zetaCompletedExplicitFormulaAutocorrelationHorizontalAvoidingSchedule f)
    points
    hpoints
    u

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
