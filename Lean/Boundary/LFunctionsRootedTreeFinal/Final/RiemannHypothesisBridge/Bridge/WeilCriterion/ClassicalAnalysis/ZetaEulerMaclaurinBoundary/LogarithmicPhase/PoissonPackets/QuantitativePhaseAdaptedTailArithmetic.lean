import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedModeBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.SummableNormMajorant
import Mathlib.Data.Real.Pi.Bounds

/-!
# Reciprocal-power arithmetic for phase-adapted tails

Every positive integer mode has angular gap at least one.  Hence the cubic and
quartic reciprocal terms in the two-step packet majorant are dominated by its
inverse-square term, reducing tail summability to the canonical p-series.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.one_le_two_mul_pi :
    (1 : ℝ) ≤ 2 * Real.pi := by
  have hthree : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hpiLtTwoPi : Real.pi < 2 * Real.pi := by
    calc
      Real.pi < Real.pi + Real.pi :=
        lt_add_of_pos_right Real.pi Real.pi_pos
      _ = 2 * Real.pi := (two_mul Real.pi).symm
  have hthreeLtTwoPi : (3 : ℝ) < 2 * Real.pi :=
    lt_trans hthree hpiLtTwoPi
  have honeThree : (1 : ℝ) ≤ 3 := by
    exact Nat.one_le_ofNat
  exact le_trans honeThree hthreeLtTwoPi.le

theorem Complex.one_le_positiveModeGap
    (m : ℤ) (hm : 0 < m) :
    (1 : ℝ) ≤ Complex.logarithmicPhasePositiveModeGap m := by
  unfold Complex.logarithmicPhasePositiveModeGap
  have hmOne : (1 : ℤ) ≤ m := Int.add_one_le_iff.mpr hm
  have hmReal : (1 : ℝ) ≤ (m : ℝ) := by
    calc
      (1 : ℝ) = ((1 : ℤ) : ℝ) := Int.cast_one.symm
      _ ≤ (m : ℝ) := Int.cast_le.mpr hmOne
  have htwoPiNonneg : 0 ≤ 2 * Real.pi :=
    Complex.two_mul_pi_pos.le
  have hmul := mul_le_mul_of_nonneg_left hmReal htwoPiNonneg
  exact le_trans Complex.one_le_two_mul_pi
    (le_trans (le_of_eq (mul_one (2 * Real.pi)).symm) hmul)

theorem Real.inv_le_one_of_one_le
    {x : ℝ} (hx : 1 ≤ x) : x⁻¹ ≤ 1 := by
  have honeInv : (1 : ℝ)⁻¹ = 1 := inv_one
  have hinv : x⁻¹ ≤ (1 : ℝ)⁻¹ := inv_anti₀ zero_lt_one hx
  exact le_trans hinv (le_of_eq honeInv)

theorem Real.inv_nonneg_of_one_le
    {x : ℝ} (hx : 1 ≤ x) : 0 ≤ x⁻¹ := by
  exact (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hx)).le

theorem Real.inv_pow_three_le_inv_pow_two_of_one_le
    {x : ℝ} (hx : 1 ≤ x) :
    x⁻¹ ^ 3 ≤ x⁻¹ ^ 2 := by
  have hinvNonneg := Real.inv_nonneg_of_one_le hx
  have hinvLeOne := Real.inv_le_one_of_one_le hx
  have hsquareNonneg : 0 ≤ x⁻¹ ^ 2 := sq_nonneg x⁻¹
  have hmul := mul_le_mul_of_nonneg_left hinvLeOne hsquareNonneg
  calc
    x⁻¹ ^ 3 = x⁻¹ ^ 2 * x⁻¹ := pow_succ x⁻¹ 2
    _ ≤ x⁻¹ ^ 2 * 1 := hmul
    _ = x⁻¹ ^ 2 := mul_one _

theorem Real.inv_pow_four_le_inv_pow_two_of_one_le
    {x : ℝ} (hx : 1 ≤ x) :
    x⁻¹ ^ 4 ≤ x⁻¹ ^ 2 := by
  have hinvNonneg := Real.inv_nonneg_of_one_le hx
  have hinvLeOne := Real.inv_le_one_of_one_le hx
  have hsquareLeOne : x⁻¹ ^ 2 ≤ 1 := by
    have hmul := mul_le_mul hinvLeOne hinvLeOne hinvNonneg zero_le_one
    calc
      x⁻¹ ^ 2 = x⁻¹ * x⁻¹ := pow_two x⁻¹
      _ ≤ 1 * 1 := hmul
      _ = 1 := one_mul 1
  have hsquareNonneg : 0 ≤ x⁻¹ ^ 2 := sq_nonneg x⁻¹
  have hmul := mul_le_mul_of_nonneg_left hsquareLeOne hsquareNonneg
  calc
    x⁻¹ ^ 4 = x⁻¹ ^ 2 * x⁻¹ ^ 2 := pow_add x⁻¹ 2 2
    _ ≤ x⁻¹ ^ 2 * 1 := hmul
    _ = x⁻¹ ^ 2 := mul_one _

theorem Real.div_pow_three_le_div_pow_two_of_one_le
    {u x : ℝ} (hu : 0 ≤ u) (hx : 1 ≤ x) :
    u / x ^ 3 ≤ u / x ^ 2 := by
  have hinv := Real.inv_pow_three_le_inv_pow_two_of_one_le hx
  have hmul := mul_le_mul_of_nonneg_left hinv hu
  have hthree := Real.div_pow_eq_mul_inv_pow u x 3
  have htwo := Real.div_pow_eq_mul_inv_pow u x 2
  calc
    u / x ^ 3 = u * x⁻¹ ^ 3 := hthree
    _ ≤ u * x⁻¹ ^ 2 := hmul
    _ = u / x ^ 2 := htwo.symm

theorem Real.div_pow_four_le_div_pow_two_of_one_le
    {u x : ℝ} (hu : 0 ≤ u) (hx : 1 ≤ x) :
    u / x ^ 4 ≤ u / x ^ 2 := by
  have hinv := Real.inv_pow_four_le_inv_pow_two_of_one_le hx
  have hmul := mul_le_mul_of_nonneg_left hinv hu
  have hfour := Real.div_pow_eq_mul_inv_pow u x 4
  have htwo := Real.div_pow_eq_mul_inv_pow u x 2
  calc
    u / x ^ 4 = u * x⁻¹ ^ 4 := hfour
    _ ≤ u * x⁻¹ ^ 2 := hmul
    _ = u / x ^ 2 := htwo.symm

def Complex.logarithmicPhasePositiveModeInverseSquareCoefficient
    (t : ℝ) (a b : ℤ) : ℝ :=
  48 +
    6 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
      (Complex.logarithmicPhaseQuantitativeSupportLeft a) +
    Complex.logarithmicPhaseQuantitativeSupportLength a b *
      Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
        (Complex.logarithmicPhaseQuantitativeSupportLeft a) +
    3 * Complex.logarithmicPhaseQuantitativeSupportLength a b *
      (Complex.logarithmicPhaseAdaptedCurvatureUpper t
        (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2

def Complex.logarithmicPhasePositiveModeInverseSquareEnvelope
    (t : ℝ) (a b m : ℤ) : ℝ :=
  Complex.logarithmicPhasePositiveModeInverseSquareCoefficient t a b /
    (Complex.logarithmicPhasePositiveModeGap m) ^ 2

end
end LFunctions
end Boundary
