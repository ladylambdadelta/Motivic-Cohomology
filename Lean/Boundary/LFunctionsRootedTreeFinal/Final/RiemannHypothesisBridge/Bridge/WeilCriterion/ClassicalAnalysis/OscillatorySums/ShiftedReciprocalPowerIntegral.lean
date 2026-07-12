import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.ShiftedReciprocalPowerSeries
import Mathlib.Analysis.SpecialFunctions.Integrals

/-!
# Finite affine integrals for shifted reciprocal powers

Affine substitution converts the shifted reciprocal kernel into an ordinary
negative real power.  The standard `integral_rpow` formula then evaluates the
finite comparison integral exactly.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.one_div_rpow_eq_rpow_neg
    {x p : ℝ} (hx : 0 ≤ x) :
    1 / x ^ p = x ^ (-p) := by
  have hneg := Real.rpow_neg hx p
  exact Eq.trans (one_div _) (Eq.trans (congrArg Inv.inv rfl) hneg.symm)

theorem Real.shiftedReciprocalPowerKernel_succ_eq_affine_rpow
    (A c p x : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c) (hx : 0 ≤ x) :
    Real.shiftedReciprocalPowerKernel A c p (x + 1) =
      (c * x + (A + c)) ^ (-p) := by
  unfold Real.shiftedReciprocalPowerKernel
  have hinside :
      A + c * (x + 1) = c * x + (A + c) := by
    exact Eq.trans
      (congrArg (fun value : ℝ => A + value) (mul_add c x 1))
      (Eq.trans
        (congrArg (fun value : ℝ => A + (c * x + value)) (mul_one c))
        (Eq.trans (add_assoc A (c * x) c)
          (Eq.trans
            (congrArg (fun value : ℝ => value + c) (add_comm A (c * x)))
            (add_assoc (c * x) A c).symm)))
  have hnonneg : 0 ≤ c * x + (A + c) := by
    have hcx : 0 ≤ c * x := mul_nonneg hc.le hx
    have hAc : 0 ≤ A + c := add_nonneg hA hc.le
    exact add_nonneg hcx hAc
  exact Eq.trans
    (congrArg (fun value : ℝ => 1 / value ^ p) hinside)
    (Real.one_div_rpow_eq_rpow_neg hnonneg)

theorem Real.mul_integral_shiftedReciprocalPowerKernel_eq_rpow
    (A c p N : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c) (hN : 0 ≤ N) :
    c * (∫ x in (0 : ℝ)..N,
      Real.shiftedReciprocalPowerKernel A c p (x + 1)) =
      ∫ y in A + c..c * N + (A + c), y ^ (-p) := by
  have hpointwise := intervalIntegral.integral_congr
    (fun x hx =>
      Real.shiftedReciprocalPowerKernel_succ_eq_affine_rpow
        A c p x hA hc hx.1)
  have hsubstitution := intervalIntegral.mul_integral_comp_mul_add
    (a := (0 : ℝ)) (b := N) (c := c)
    (f := fun y : ℝ => y ^ (-p)) (A + c)
  have hleftEndpoint : c * 0 + (A + c) = A + c := by
    exact Eq.trans (congrArg (fun value : ℝ => value + (A + c)) (mul_zero c))
      (zero_add _)
  exact Eq.trans (congrArg (fun value : ℝ => c * value) hpointwise)
    (Eq.trans hsubstitution
      (congrArg₂
        (fun left right : ℝ => ∫ y in left..right, y ^ (-p))
        hleftEndpoint rfl))

theorem Real.integral_shiftedReciprocalPowerKernel_eq_rpow_endpoints
    (A c p N : ℝ)
    (hA : 0 ≤ A) (hc : 0 < c) (hN : 0 ≤ N)
    (hp : p ≠ 1) :
    c * (∫ x in (0 : ℝ)..N,
      Real.shiftedReciprocalPowerKernel A c p (x + 1)) =
      (((c * N + (A + c)) ^ (1 - p) - (A + c) ^ (1 - p)) /
        (1 - p)) := by
  have hsubstitution :=
    Real.mul_integral_shiftedReciprocalPowerKernel_eq_rpow
      A c p N hA hc hN
  have hleftPos : 0 < A + c := add_pos_of_nonneg_of_pos hA hc
  have hrightPos : 0 < c * N + (A + c) :=
    add_pos_of_nonneg_of_pos (mul_nonneg hc.le hN) hleftPos
  have hzeroNotMem : (0 : ℝ) ∉
      [[A + c, c * N + (A + c)]] := by
    have horder : A + c ≤ c * N + (A + c) :=
      le_add_of_nonneg_left (mul_nonneg hc.le hN)
    have hIcc := Set.uIcc_of_le horder
    intro hzero
    have hmem := hIcc.mp hzero
    exact (not_le_of_gt hleftPos) hmem.1
  have hexponent : -p ≠ -1 := by
    intro heq
    have hneg := neg_inj.mp heq
    exact hp hneg
  have hintegral := intervalIntegral.integral_rpow
    (a := A + c) (b := c * N + (A + c)) (r := -p)
    (Or.inr ⟨hexponent, hzeroNotMem⟩)
  have hplus : -p + 1 = 1 - p := by
    exact (sub_eq_add_neg 1 p).symm.trans (add_comm (-p) 1)
  have hnormalize := congrArg₂
    (fun numerator denominator : ℝ => numerator / denominator)
    (congrArg₂ (fun first second : ℝ => first - second)
      (congrArg (fun exponent : ℝ =>
        (c * N + (A + c)) ^ exponent) hplus)
      (congrArg (fun exponent : ℝ => (A + c) ^ exponent) hplus))
    hplus
  exact Eq.trans hsubstitution (Eq.trans hintegral hnormalize)

end
end LFunctions
end Boundary
