import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFarNegativeResidualArithmetic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.ShiftedReciprocalNegativeCubicBudget

/-!
# Refined-scale arithmetic for the far-negative tail

The two cubic coefficients are absorbed by one power of the deterministic
residual.  The curvature-square coefficient is instead bounded using the long
block relation `sqrt (1+‖t‖) < supportLength` together with the sharp
`supportLength ≤ (7/4) left` comparison.  This preserves the square-root scale
required by the final estimate.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.shift_sq_mul_shiftedFourthBudget_le
    (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) :
    A ^ 2 * Real.shiftedInverseFourthBudget A c ≤
      1 / (3 * c ^ 2) := by
  have hbudget := Real.shiftedInverseFourthBudget_eq_base hA hc
  have hbase : 0 < A + c := add_pos_of_nonneg_of_pos hA hc
  have hAle : A ≤ A + c := le_add_of_nonneg_right hc.le
  have hsquare := pow_le_pow_left₀ hA hAle 2
  have hcLeBase : c ≤ A + c := le_add_of_nonneg_left hA
  have hproduct : A ^ 2 * c ≤ (A + c) ^ 2 * (A + c) :=
    mul_le_mul hsquare hcLeBase hc.le (pow_nonneg hbase.le 2)
  have hscaleNonneg : 0 ≤ (3 : ℝ) * c :=
    mul_nonneg (Nat.cast_nonneg 3) hc.le
  have hscaled := mul_le_mul_of_nonneg_left hproduct hscaleNonneg
  have hleftScaled :
      ((3 : ℝ) * c) * (A ^ 2 * c) = A ^ 2 * (3 * c ^ 2) := by
    have hshuffle :
        ((3 : ℝ) * c) * (A ^ 2 * c) =
          (3 * A ^ 2) * (c * c) :=
      mul_mul_mul_comm 3 c (A ^ 2) c
    have hcommuteCoefficient :
        (3 : ℝ) * A ^ 2 * (c * c) = A ^ 2 * (3 * (c * c)) := by
      exact Eq.trans
        (congrArg (fun value : ℝ => value * (c * c))
          (mul_comm 3 (A ^ 2)))
        (mul_assoc (A ^ 2) 3 (c * c))
    exact Eq.trans hshuffle
      (Eq.trans hcommuteCoefficient
        (congrArg (fun value : ℝ => A ^ 2 * (3 * value))
          (pow_two c).symm))
  have hcube : (A + c) ^ 2 * (A + c) = (A + c) ^ 3 :=
    (pow_succ (A + c) 2).symm
  have hrightScaled :
      ((3 : ℝ) * c) * ((A + c) ^ 2 * (A + c)) =
        1 * (((3 : ℝ) * c) * (A + c) ^ 3) :=
    Eq.trans
      (congrArg (fun value : ℝ => ((3 : ℝ) * c) * value) hcube)
      (one_mul (((3 : ℝ) * c) * (A + c) ^ 3)).symm
  have hcross :
      A ^ 2 * (3 * c ^ 2) ≤
        1 * (((3 : ℝ) * c) * (A + c) ^ 3) :=
    Eq.mp
      (congrArg₂ (fun left right : ℝ => left ≤ right)
        hleftScaled hrightScaled)
      hscaled
  have hdenominatorLeft : 0 < ((3 : ℝ) * c) * (A + c) ^ 3 :=
    mul_pos
      (mul_pos (Nat.cast_pos.mpr (Nat.zero_lt_succ 2)) hc)
      (pow_pos hbase 3)
  have hdenominatorRight : 0 < (3 : ℝ) * c ^ 2 :=
    mul_pos (Nat.cast_pos.mpr (Nat.zero_lt_succ 2)) (pow_pos hc 2)
  have hcore :
      A ^ 2 / (((3 : ℝ) * c) * (A + c) ^ 3) ≤
        1 / (3 * c ^ 2) :=
    (div_le_div_iff₀ hdenominatorLeft hdenominatorRight).mpr hcross
  have hleftForm :
      A ^ 2 * Real.shiftedInverseFourthBudget A c =
        A ^ 2 / (((3 : ℝ) * c) * (A + c) ^ 3) := by
    exact Eq.trans (congrArg (fun value : ℝ => A ^ 2 * value) hbudget)
      (Eq.trans
        (congrArg (fun value : ℝ => A ^ 2 * value)
          (one_div (((3 : ℝ) * c) * (A + c) ^ 3)))
        (div_eq_mul_inv (A ^ 2)
          (((3 : ℝ) * c) * (A + c) ^ 3)).symm)
  exact Eq.mp
    (congrArg
      (fun left : ℝ => left ≤ 1 / (3 * c ^ 2)) hleftForm.symm)
    hcore

end
end LFunctions
end Boundary
