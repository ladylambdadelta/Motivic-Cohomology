import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaVerticalChannels.OwnerParts.RightOnePoleOffPoleDecayEstimate

/-!
# One-pole tangent-boundary defect estimate

This file transports the direct right `s = 1` correction-face projection limit
to the tangent-boundary defect.  The analytic input itself is owned by
`RightOnePoleOffPoleDecayEstimate`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open LSeries ArithmeticFunction
open MeasureTheory
open scoped ArithmeticFunction
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The tangent-boundary defect has the same residue-free Cauchy projection
limit as the right one-pole face. -/
theorem zetaCompletedExplicitFormulaCorrectionOnePoleTangentBoundaryDefect_tendsto_projection
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) :
    Tendsto
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I)
      atTop
      (𝓝 (zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c)) := by
  have hright :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F (h.height_schedule.height u))
        atTop
        (𝓝 (zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c)) :=
    zetaCompletedExplicitFormulaCorrectionRightOnePoleOffPoleVerticalIntegral_tendsto_projection
      f F h
  have hhorizontal :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
            f F h u * Complex.I)
        atTop
        (𝓝 (0 * Complex.I)) :=
    (zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference_tendsto_zero
      f F h).mul tendsto_const_nhds
  have hhorizontal_zero :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
            f F h u * Complex.I)
        atTop
        (𝓝 0) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
              f F h u * Complex.I)
          atTop
          (𝓝 z))
      (zero_mul Complex.I)
      hhorizontal
  have hdiff :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
              f F h u * Complex.I)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c - 0)) :=
    hright.sub hhorizontal_zero
  have hdiff_projection :
      Tendsto
        (fun u : ℝ =>
          zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
              f F (h.height_schedule.height u) -
            zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
              f F h u * Complex.I)
        atTop
        (𝓝 (zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c)) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun u : ℝ =>
            zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
                f F (h.height_schedule.height u) -
              zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
                f F h u * Complex.I)
          atTop
          (𝓝 z))
      (sub_zero (zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c))
      hdiff
  have hpointwise :
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
            f F (h.height_schedule.height u) * Complex.I) =
      (fun u : ℝ =>
        zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
            f F (h.height_schedule.height u) -
          zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
            f F h u * Complex.I) := by
    funext u
    let R : ℂ :=
      zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral
        f F (h.height_schedule.height u)
    let L : ℂ :=
      zetaCompletedExplicitFormulaCorrectionLeftOnePoleVerticalIntegral
        f F (h.height_schedule.height u)
    let C : ℂ :=
      zetaCompletedExplicitFormulaCorrectionOnePoleTangentRectangleBoundaryIntegral
        f F (h.height_schedule.height u)
    let H : ℂ :=
      zetaCompletedExplicitFormulaCorrectionOnePoleScheduledHorizontalDifference
        f F h u
    have hR : R = L - C * Complex.I + H * Complex.I :=
      zetaCompletedExplicitFormulaCorrectionRightOnePoleVerticalIntegral_eq_left_sub_tangentBoundary_mul_I_add_horizontal_mul_I
        f F h u
    change L - C * Complex.I = R - H * Complex.I
    calc
      L - C * Complex.I = (L - C * Complex.I + H * Complex.I) - H * Complex.I := by
        exact (add_sub_cancel_right (L - C * Complex.I) (H * Complex.I)).symm
      _ = R - H * Complex.I := by
        exact congrArg (fun z : ℂ => z - H * Complex.I) hR.symm
  exact
    Eq.subst
      (motive := fun φ : ℝ → ℂ =>
        Tendsto φ atTop
          (𝓝 (zetaCompletedExplicitFormulaRightOnePoleCauchyProjectionValue f F.c)))
      hpointwise.symm
      hdiff_projection

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
