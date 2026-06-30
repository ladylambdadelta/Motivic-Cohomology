import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.L3_TailAccountingAndCancellation
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetBranchWallMovingSpike

/-!
# Moving-spike branch-wall accounting

This file owns the BinetKernel-facing transport from the classical moving-spike
principal-tail estimate to the branch-wall cancellation package.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open Filter
open MeasureTheory

/-- Bounded-window principal-tail decay follows from the scalar decay of the
two-moving-log branch-wall window. -/
theorem Complex.binetSecondFormula_boundedWindow_decay_of_twoMovingLogWindow_decay
    (htwoMoving :
      ∃ Ctwo : ℝ,
        0 < Ctwo ∧
        ∀ w : ℂ,
          0 < w.re →
          2 ≤ ‖w‖ →
            2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                (2 *
                  (max
                    |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|
                    |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| +
                    Real.pi)) /
                  Real.exp ((2 : ℝ) * Real.pi * t) ≤
              (Ctwo / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w) :
    ∃ Cbounded : ℝ,
      0 < Cbounded ∧
      ∀ w : ℂ,
        0 < w.re →
        2 ≤ ‖w‖ →
          2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
              ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
            (Cbounded / ‖w‖) *
              Complex.binetSecondFormulaDecayingTailIntegral w := by
  match htwoMoving with
  | ⟨Ctwo, hCtwo_pos, htwoMoving_bound⟩ =>
      exact
        ⟨Ctwo, hCtwo_pos,
          fun w hw_re_pos hw_norm_two =>
            let P : ℝ → ℝ := fun t : ℝ =>
              ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖
            let G : ℝ → ℝ := fun t : ℝ =>
              (2 *
                (max
                  |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|
                  |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| +
                  Real.pi)) /
                Real.exp ((2 : ℝ) * Real.pi * t)
            let J : ℝ :=
              Complex.binetSecondFormulaDecayingTailIntegral w
            have hkernel_to_twoMoving :
                ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), P t ≤
                  ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), G t :=
              Complex.binetSecondFormula_principalTailKernel_integral_le_expWeighted_twoMovingLogWindow_boundedTailWindow_Ioc
                (w := w) hw_re_pos hw_norm_two
            have htwice :
                2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), P t ≤
                  2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), G t :=
              mul_le_mul_of_nonneg_left hkernel_to_twoMoving zero_le_two
            have htwoMoving_w :
                2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), G t ≤
                  (Ctwo / ‖w‖) * J :=
              htwoMoving_bound w hw_re_pos hw_norm_two
            le_trans htwice htwoMoving_w⟩

/-- Branch-wall tail absorption follows from the scalar decay of the
two-moving-log branch-wall window. -/
theorem Complex.binetSecondFormula_branchTail_wallCancellation_of_twoMovingLogWindow_decay
    (htwoMoving :
      ∃ Ctwo : ℝ,
        0 < Ctwo ∧
        ∀ w : ℂ,
          0 < w.re →
          2 ≤ ‖w‖ →
            2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                (2 *
                  (max
                    |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|
                    |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| +
                    Real.pi)) /
                  Real.exp ((2 : ℝ) * Real.pi * t) ≤
              (Ctwo / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w) :
    Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption := by
  exact
    Complex.binetSecondFormula_branchTail_wallCancellation_of_boundedWindow_decay
      (Complex.binetSecondFormula_boundedWindow_decay_of_twoMovingLogWindow_decay
        htwoMoving)

/-- Finite-height lower-vertical decay follows from the scalar decay of the
two-moving-log branch-wall window. -/
theorem Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_twoMovingLogWindow_decay
    (htwoMoving :
      ∃ Ctwo : ℝ,
        0 < Ctwo ∧
        ∀ w : ℂ,
          0 < w.re →
          2 ≤ ‖w‖ →
            2 * ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
                (2 *
                  (max
                    |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|
                    |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| +
                    Real.pi)) /
                  Real.exp ((2 : ℝ) * Real.pi * t) ≤
              (Ctwo / ‖w‖) *
                Complex.binetSecondFormulaDecayingTailIntegral w) :
    Complex.BinetSecondFormulaFiniteHeightLowerVerticalDifferenceDecay := by
  have htail :
      Complex.BinetSecondFormulaBranchWallContourCancellationTailAbsorption :=
    Complex.binetSecondFormula_branchTail_wallCancellation_of_twoMovingLogWindow_decay
      htwoMoving
  exact
    Complex.binetSecondFormula_finiteHeightLowerVerticalDifference_decay_of_wallCancellation
      htail

end

end LFunctions
end Boundary
