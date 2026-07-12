import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedModeBounds

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
  have htwoPositive : (0 : ℝ) < 2 := by exact OfNat.zero_lt 2
  have hsix : (6 : ℝ) < 2 * Real.pi := by
    have hmul := mul_lt_mul_of_pos_left hthree htwoPositive
    exact lt_of_eq_of_lt (show (6 : ℝ) = 2 * 3 from rfl) hmul
  exact le_trans (by exact OfNat.one_le_ofNat) hsix.le

theorem Complex.one_le_positiveModeGap
    (m : ℤ) (hm : 0 < m) :
    (1 : ℝ) ≤ Complex.logarithmicPhasePositiveModeGap m := by
  unfold Complex.logarithmicPhasePositiveModeGap
  have hmOne : (1 : ℤ) ≤ m := Int.add_one_le_iff.mpr hm
  have hmReal : (1 : ℝ) ≤ (m : ℝ) := Int.cast_le.mpr hmOne
  have htwoPiNonneg : 0 ≤ 2 * Real.pi :=
    Complex.two_mul_pi_pos.le
  have hmul := mul_le_mul_of_nonneg_left hmReal htwoPiNonneg
  exact le_trans Complex.one_le_two_mul_pi
    (le_trans (le_of_eq (mul_one (2 * Real.pi)).symm) hmul)

theorem Real.inv_le_one_of_one_le
    {x : ℝ} (hx : 1 ≤ x) : x⁻¹ ≤ 1 := by
  have hxPos : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have honeInv : (1 : ℝ)⁻¹ = 1 := inv_one
  have hinv := inv_anti₀ zero_lt_one hxPos hx
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
  have hthree : x⁻¹ ^ 3 = x⁻¹ ^ 2 * x⁻¹ :=
    pow_succ x⁻¹ 2
  have htwo : x⁻¹ ^ 2 = x⁻¹ ^ 2 * 1 :=
    (mul_one _).symm
  exact Eq.subst hthree.symm (Eq.subst htwo.symm hmul)

theorem Real.inv_pow_four_le_inv_pow_two_of_one_le
    {x : ℝ} (hx : 1 ≤ x) :
    x⁻¹ ^ 4 ≤ x⁻¹ ^ 2 := by
  have hinvNonneg := Real.inv_nonneg_of_one_le hx
  have hinvLeOne := Real.inv_le_one_of_one_le hx
  have hsquareLeOne : x⁻¹ ^ 2 ≤ 1 := by
    have hmul := mul_le_mul hinvLeOne hinvLeOne hinvNonneg zero_le_one
    exact Eq.trans (le_of_eq (pow_two x⁻¹))
      (le_trans hmul (le_of_eq (one_mul 1)))
  have hsquareNonneg : 0 ≤ x⁻¹ ^ 2 := sq_nonneg x⁻¹
  have hmul := mul_le_mul_of_nonneg_left hsquareLeOne hsquareNonneg
  have hfour : x⁻¹ ^ 4 = x⁻¹ ^ 2 * x⁻¹ ^ 2 :=
    (pow_add x⁻¹ 2 2).symm
  have htwo : x⁻¹ ^ 2 = x⁻¹ ^ 2 * 1 :=
    (mul_one _).symm
  exact Eq.subst hfour.symm (Eq.subst htwo.symm hmul)

theorem Real.div_pow_three_le_div_pow_two_of_one_le
    {u x : ℝ} (hu : 0 ≤ u) (hx : 1 ≤ x) :
    u / x ^ 3 ≤ u / x ^ 2 := by
  have hinv := Real.inv_pow_three_le_inv_pow_two_of_one_le hx
  have hmul := mul_le_mul_of_nonneg_left hinv hu
  have hthree := Real.div_pow_eq_mul_inv_pow u x 3
  have htwo := Real.div_pow_eq_mul_inv_pow u x 2
  exact Eq.subst hthree.symm (Eq.subst htwo.symm hmul)

theorem Real.div_pow_four_le_div_pow_two_of_one_le
    {u x : ℝ} (hu : 0 ≤ u) (hx : 1 ≤ x) :
    u / x ^ 4 ≤ u / x ^ 2 := by
  have hinv := Real.inv_pow_four_le_inv_pow_two_of_one_le hx
  have hmul := mul_le_mul_of_nonneg_left hinv hu
  have hfour := Real.div_pow_eq_mul_inv_pow u x 4
  have htwo := Real.div_pow_eq_mul_inv_pow u x 2
  exact Eq.subst hfour.symm (Eq.subst htwo.symm hmul)

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
