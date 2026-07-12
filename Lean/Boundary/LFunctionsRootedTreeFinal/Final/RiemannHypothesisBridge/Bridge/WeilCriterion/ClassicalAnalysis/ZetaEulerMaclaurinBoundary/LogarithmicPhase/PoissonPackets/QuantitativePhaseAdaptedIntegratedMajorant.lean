import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedGap
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeCutoffVariationBound

/-!
# Closed integrated majorant for phase-adapted packets

This owner performs the deterministic arithmetic between a uniform derivative
gap and the three cutoff masses.  It keeps every reciprocal transport visible,
so the later integer-tail summation receives a closed expression rather than
an analytic hypothesis.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped Interval

def Complex.logarithmicPhaseAdaptedCurvatureUpper
    (t left : ℝ) : ℝ :=
  ‖t‖ / left ^ 2

def Complex.logarithmicPhaseAdaptedThirdDerivativeUpper
    (t left : ℝ) : ℝ :=
  2 * ‖t‖ / left ^ 3

def Complex.logarithmicPhaseAdaptedClosedMajorant
    (t : ℝ) (a b : ℤ) (gap : ℝ) : ℝ :=
  48 / gap ^ 2 +
    6 * (Complex.logarithmicPhaseAdaptedCurvatureUpper t
      (Complex.logarithmicPhaseQuantitativeSupportLeft a)) / gap ^ 3 +
    Complex.logarithmicPhaseQuantitativeSupportLength a b *
      (Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
        (Complex.logarithmicPhaseQuantitativeSupportLeft a)) / gap ^ 3 +
    3 * Complex.logarithmicPhaseQuantitativeSupportLength a b *
      (Complex.logarithmicPhaseAdaptedCurvatureUpper t
        (Complex.logarithmicPhaseQuantitativeSupportLeft a)) ^ 2 / gap ^ 4

theorem Real.inv_nonneg_of_pos {x : ℝ} (hx : 0 < x) : 0 ≤ x⁻¹ :=
  (inv_pos.mpr hx).le

theorem Real.inv_le_inv_of_pos
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    y⁻¹ ≤ x⁻¹ := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  exact inv_anti₀ hx hy hxy

theorem Real.inv_pow_two_le_inv_pow_two
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    y⁻¹ ^ 2 ≤ x⁻¹ ^ 2 := by
  have hinv := Real.inv_le_inv_of_pos hx hxy
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hyInv : 0 ≤ y⁻¹ := Real.inv_nonneg_of_pos hy
  exact mul_self_le_mul_self hyInv hinv

theorem Real.inv_pow_three_le_inv_pow_three
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    y⁻¹ ^ 3 ≤ x⁻¹ ^ 3 := by
  have hinv := Real.inv_le_inv_of_pos hx hxy
  have hpowTwo := Real.inv_pow_two_le_inv_pow_two hx hxy
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hxInv : 0 ≤ x⁻¹ := Real.inv_nonneg_of_pos hx
  have hyInv : 0 ≤ y⁻¹ := Real.inv_nonneg_of_pos hy
  have hmul := mul_le_mul hpowTwo hinv hyInv hxInv
  exact Eq.subst (pow_succ y⁻¹ 2).symm
    (Eq.subst (pow_succ x⁻¹ 2).symm hmul)

theorem Real.inv_pow_four_le_inv_pow_four
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    y⁻¹ ^ 4 ≤ x⁻¹ ^ 4 := by
  have hpowTwo := Real.inv_pow_two_le_inv_pow_two hx hxy
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  have hxInvTwo : 0 ≤ x⁻¹ ^ 2 := sq_nonneg x⁻¹
  have hyInvTwo : 0 ≤ y⁻¹ ^ 2 := sq_nonneg y⁻¹
  have hmul := mul_le_mul hpowTwo hpowTwo hyInvTwo hxInvTwo
  have hyPower : y⁻¹ ^ 2 * y⁻¹ ^ 2 = y⁻¹ ^ 4 :=
    (pow_add y⁻¹ 2 2).symm
  have hxPower : x⁻¹ ^ 2 * x⁻¹ ^ 2 = x⁻¹ ^ 4 :=
    (pow_add x⁻¹ 2 2).symm
  exact Eq.subst hyPower (Eq.subst hxPower hmul)

theorem Real.div_pow_antitone_two
    {u x y : ℝ}
    (hu : 0 ≤ u) (hx : 0 < x) (hxy : x ≤ y) :
    u / y ^ 2 ≤ u / x ^ 2 := by
  have hinv := Real.inv_pow_two_le_inv_pow_two hx hxy
  have hmul := mul_le_mul_of_nonneg_left hinv hu
  have hyDiv := Real.div_pow_eq_mul_inv_pow u y 2
  have hxDiv := Real.div_pow_eq_mul_inv_pow u x 2
  exact Eq.subst hyDiv.symm (Eq.subst hxDiv.symm hmul)

theorem Real.div_pow_antitone_three
    {u x y : ℝ}
    (hu : 0 ≤ u) (hx : 0 < x) (hxy : x ≤ y) :
    u / y ^ 3 ≤ u / x ^ 3 := by
  have hinv := Real.inv_pow_three_le_inv_pow_three hx hxy
  have hmul := mul_le_mul_of_nonneg_left hinv hu
  have hyDiv := Real.div_pow_eq_mul_inv_pow u y 3
  have hxDiv := Real.div_pow_eq_mul_inv_pow u x 3
  exact Eq.subst hyDiv.symm (Eq.subst hxDiv.symm hmul)

theorem Real.div_pow_antitone_four
    {u x y : ℝ}
    (hu : 0 ≤ u) (hx : 0 < x) (hxy : x ≤ y) :
    u / y ^ 4 ≤ u / x ^ 4 := by
  have hinv := Real.inv_pow_four_le_inv_pow_four hx hxy
  have hmul := mul_le_mul_of_nonneg_left hinv hu
  have hyDiv := Real.div_pow_eq_mul_inv_pow u y 4
  have hxDiv := Real.div_pow_eq_mul_inv_pow u x 4
  exact Eq.subst hyDiv.symm (Eq.subst hxDiv.symm hmul)

theorem Complex.logarithmicPhaseAdaptedCurvatureUpper_nonneg
    (t left : ℝ) (hleft : 0 ≤ left) :
    0 ≤ Complex.logarithmicPhaseAdaptedCurvatureUpper t left := by
  unfold Complex.logarithmicPhaseAdaptedCurvatureUpper
  exact div_nonneg (norm_nonneg t) (pow_nonneg hleft 2)

theorem Complex.logarithmicPhaseAdaptedThirdDerivativeUpper_nonneg
    (t left : ℝ) (hleft : 0 ≤ left) :
    0 ≤ Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t left := by
  unfold Complex.logarithmicPhaseAdaptedThirdDerivativeUpper
  have hnumerator : 0 ≤ 2 * ‖t‖ :=
    mul_nonneg (by exact OfNat.zero_le 2) (norm_nonneg t)
  exact div_nonneg hnumerator (pow_nonneg hleft 3)

theorem Complex.logarithmicPhaseAdaptedCurvature_le_left
    (t left x : ℝ)
    (hleft : 0 < left) (hleftx : left ≤ x) :
    ‖t‖ / x ^ 2 ≤
      Complex.logarithmicPhaseAdaptedCurvatureUpper t left := by
  unfold Complex.logarithmicPhaseAdaptedCurvatureUpper
  exact Complex.div_square_le_div_leftSupport_square t hleft hleftx

theorem Complex.logarithmicPhaseAdaptedThirdDerivative_le_left
    (t left x : ℝ)
    (hleft : 0 < left) (hleftx : left ≤ x) :
    2 * ‖t‖ / x ^ 3 ≤
      Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t left := by
  unfold Complex.logarithmicPhaseAdaptedThirdDerivativeUpper
  have hx : 0 < x := lt_of_lt_of_le hleft hleftx
  have hcube : left ^ 3 ≤ x ^ 3 :=
    pow_le_pow_left₀ hleft.le hleftx 3
  have hleftCube : 0 < left ^ 3 := pow_pos hleft 3
  have hnumerator : 0 ≤ 2 * ‖t‖ :=
    mul_nonneg (by exact OfNat.zero_le 2) (norm_nonneg t)
  exact div_le_div_of_nonneg_left hnumerator hleftCube hcube

theorem Complex.logarithmicPhaseAdaptedClosedMajorant_nonneg
    (t : ℝ) (a b : ℤ) (gap : ℝ)
    (hab : a ≤ b)
    (hleft : 0 ≤ Complex.logarithmicPhaseQuantitativeSupportLeft a)
    (hgap : 0 ≤ gap) :
    0 ≤ Complex.logarithmicPhaseAdaptedClosedMajorant t a b gap := by
  unfold Complex.logarithmicPhaseAdaptedClosedMajorant
  have hgapTwo : 0 ≤ gap ^ 2 := pow_nonneg hgap 2
  have hgapThree : 0 ≤ gap ^ 3 := pow_nonneg hgap 3
  have hgapFour : 0 ≤ gap ^ 4 := pow_nonneg hgap 4
  have hlength := Complex.logarithmicPhaseQuantitativeSupportLength_nonneg a b hab
  have hcurvature :=
    Complex.logarithmicPhaseAdaptedCurvatureUpper_nonneg t _ hleft
  have hthird :=
    Complex.logarithmicPhaseAdaptedThirdDerivativeUpper_nonneg t _ hleft
  have hfirst : 0 ≤ (48 : ℝ) / gap ^ 2 :=
    div_nonneg (by exact OfNat.zero_le 48) hgapTwo
  have hsecond :
      0 ≤ 6 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
        (Complex.logarithmicPhaseQuantitativeSupportLeft a) / gap ^ 3 :=
    div_nonneg
      (mul_nonneg (by exact OfNat.zero_le 6) hcurvature) hgapThree
  have hthirdTerm :
      0 ≤ Complex.logarithmicPhaseQuantitativeSupportLength a b *
        Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a) / gap ^ 3 :=
    div_nonneg (mul_nonneg hlength hthird) hgapThree
  have hfourth :
      0 ≤ 3 * Complex.logarithmicPhaseQuantitativeSupportLength a b *
        Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2 / gap ^ 4 :=
    div_nonneg
      (mul_nonneg
        (mul_nonneg (by exact OfNat.zero_le 3) hlength)
        (pow_nonneg hcurvature 2)) hgapFour
  exact add_nonneg (add_nonneg (add_nonneg hfirst hsecond) hthirdTerm) hfourth

theorem Complex.logarithmicPhaseAdaptedClosedMajorant_gap_antitone
    (t : ℝ) (a b : ℤ) {gap₁ gap₂ : ℝ}
    (hab : a ≤ b)
    (hleft : 0 ≤ Complex.logarithmicPhaseQuantitativeSupportLeft a)
    (hgap₁ : 0 < gap₁) (hgaps : gap₁ ≤ gap₂) :
    Complex.logarithmicPhaseAdaptedClosedMajorant t a b gap₂ ≤
      Complex.logarithmicPhaseAdaptedClosedMajorant t a b gap₁ := by
  unfold Complex.logarithmicPhaseAdaptedClosedMajorant
  have hlength := Complex.logarithmicPhaseQuantitativeSupportLength_nonneg a b hab
  have hcurvature :=
    Complex.logarithmicPhaseAdaptedCurvatureUpper_nonneg t _ hleft
  have hthird :=
    Complex.logarithmicPhaseAdaptedThirdDerivativeUpper_nonneg t _ hleft
  have hfirst := Real.div_pow_antitone_two
    (u := (48 : ℝ)) (by exact OfNat.zero_le 48) hgap₁ hgaps
  have hsecondNumerator :
      0 ≤ 6 * Complex.logarithmicPhaseAdaptedCurvatureUpper t
        (Complex.logarithmicPhaseQuantitativeSupportLeft a) :=
    mul_nonneg (by exact OfNat.zero_le 6) hcurvature
  have hsecond := Real.div_pow_antitone_three
    hsecondNumerator hgap₁ hgaps
  have hthirdNumerator :
      0 ≤ Complex.logarithmicPhaseQuantitativeSupportLength a b *
        Complex.logarithmicPhaseAdaptedThirdDerivativeUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a) :=
    mul_nonneg hlength hthird
  have hthirdBound := Real.div_pow_antitone_three
    hthirdNumerator hgap₁ hgaps
  have hfourthNumerator :
      0 ≤ 3 * Complex.logarithmicPhaseQuantitativeSupportLength a b *
        Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2 :=
    mul_nonneg
      (mul_nonneg (by exact OfNat.zero_le 3) hlength)
      (pow_nonneg hcurvature 2)
  have hfourth := Real.div_pow_antitone_four
    hfourthNumerator hgap₁ hgaps
  exact add_le_add (add_le_add (add_le_add hfirst hsecond) hthirdBound) hfourth

def Complex.logarithmicPhasePositiveModeClosedMajorant
    (t : ℝ) (a b m : ℤ) : ℝ :=
  Complex.logarithmicPhaseAdaptedClosedMajorant t a b
    (Complex.logarithmicPhasePositiveModeGap m)

def Complex.logarithmicPhaseLeftInactiveClosedMajorant
    (t : ℝ) (a b m : ℤ) : ℝ :=
  Complex.logarithmicPhaseAdaptedClosedMajorant t a b
    (Complex.logarithmicPhaseLeftInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportLeft a))

def Complex.logarithmicPhaseRightInactiveClosedMajorant
    (t : ℝ) (a b m : ℤ) : ℝ :=
  Complex.logarithmicPhaseAdaptedClosedMajorant t a b
    (Complex.logarithmicPhaseRightInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportRight b))

end
end LFunctions
end Boundary
