import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.Owner

/-!
# Scheduled inverse-quadratic tails

This file owns the neutral cofinal-height fact that an inverse-quadratic
scheduled rectangle-height envelope tends to zero.  It is shared by zero-pole
and one-pole horizontal estimates and has no pole-specific content.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- The scheduled inverse-quadratic tail weight tends to zero on any cofinal
height schedule. -/
theorem zetaCompletedExplicitFormulaCorrection_scheduledInverseQuadraticTailMajorant_tendsto_zero_ownerShared
    (F : ExplicitFormulaContourFamily)
    (hSchedule : ExplicitFormulaCofinalHeightSchedule F) (M : ℝ) :
    Tendsto
      (fun u : ℝ =>
        M * (1 + ‖(F.rectangle (hSchedule.height u)).T‖) ^ (-(2 : ℤ)))
      atTop
      (𝓝 0) := by
  have hheight_norm :
      Tendsto
        (fun u : ℝ => ‖(F.rectangle (hSchedule.height u)).T‖)
        atTop
        atTop :=
    tendsto_norm_atTop_atTop.comp hSchedule.cofinal
  have hheight_norm_plus_one :
      Tendsto
        (fun u : ℝ => 1 + ‖(F.rectangle (hSchedule.height u)).T‖)
        atTop
        atTop :=
    tendsto_atTop_add_const_left atTop (1 : ℝ) hheight_norm
  have hexponent_negative : (-(2 : ℤ)) < 0 :=
    Int.negSucc_lt_zero 1
  have hinverse_quadratic :
      Tendsto
        (fun u : ℝ =>
          (1 + ‖(F.rectangle (hSchedule.height u)).T‖) ^ (-(2 : ℤ)))
        atTop
        (𝓝 0) :=
    (tendsto_zpow_atTop_zero hexponent_negative).comp
      hheight_norm_plus_one
  have hscaled :
      Tendsto
        (fun u : ℝ =>
          M * (1 + ‖(F.rectangle (hSchedule.height u)).T‖) ^ (-(2 : ℤ)))
        atTop
        (𝓝 (M * 0)) :=
    hinverse_quadratic.const_mul M
  have hzero : M * 0 = 0 :=
    mul_zero M
  exact hzero ▸ hscaled

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
