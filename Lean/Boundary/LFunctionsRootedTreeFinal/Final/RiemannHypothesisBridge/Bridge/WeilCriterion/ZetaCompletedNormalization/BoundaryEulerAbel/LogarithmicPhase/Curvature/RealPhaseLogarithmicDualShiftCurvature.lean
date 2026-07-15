import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualDiscreteCollarCardinality

/-!
# Curvature of the dual shifted difference

This owner differentiates the exact shifted derivative.  For positive `x` and
positive shift `h`,

`(-‖t‖*h/(x*(x+h)))' = ‖t‖*h*(2*x+h)/(x^2*(x+h)^2)`.

The curvature is positive.  Explicit endpoint comparisons then provide the
uniform growth parameter used to convert derivative-value collars into spatial
collars.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.hasDerivAt_mul_self_add
    (h x : ℝ) :
    HasDerivAt (fun y : ℝ => y * (y + h)) (2 * x + h) x := by
  have hid : HasDerivAt (fun y : ℝ => y) 1 x := hasDerivAt_id x
  have hshift : HasDerivAt (fun y : ℝ => y + h) 1 x :=
    hid.add_const h
  have hproduct := hid.mul hshift
  have hnormalize : 1 * (x + h) + x * 1 = 2 * x + h := by
    exact Eq.trans
      (congrArg₂ (fun a b : ℝ => a + b)
        (one_mul (x + h)) (mul_one x))
      (Eq.trans
        (add_assoc x h x)
        (Eq.trans
          (congrArg (fun z : ℝ => x + z) (add_comm h x))
          (Eq.trans
            (add_assoc x x h).symm
            (congrArg (fun z : ℝ => z + h) (two_mul x).symm))))
  exact Eq.subst
    (motive := fun z : ℝ =>
      HasDerivAt (fun y : ℝ => y * (y + h)) z x)
    hnormalize.symm hproduct

theorem Real.hasDerivAt_inv_mul_self_add
    {h x : ℝ} (hx : x ≠ 0) (hxh : x + h ≠ 0) :
    HasDerivAt
      (fun y : ℝ => (y * (y + h))⁻¹)
      (-(2 * x + h) / (x * (x + h)) ^ 2) x := by
  have hbase := Real.hasDerivAt_mul_self_add h x
  have hdenom : x * (x + h) ≠ 0 := mul_ne_zero hx hxh
  exact hbase.inv hdenom

theorem Real.neg_mul_neg_div_eq_mul_div
    (T h numerator denominator : ℝ) :
    (-T * h) * (-numerator / denominator) =
      T * h * numerator / denominator := by
  calc
    (-T * h) * (-numerator / denominator) =
        ((-T * h) * (-numerator)) / denominator :=
      (mul_div_assoc (-T * h) (-numerator) denominator).symm
    _ = (T * h * numerator) / denominator := by
      exact congrArg (fun z : ℝ => z / denominator)
        (Eq.trans
          (mul_assoc (-T) h (-numerator)).symm
          (Eq.trans
            (congrArg (fun z : ℝ => z * (-numerator))
              (neg_mul T h))
            (Eq.trans
              (mul_neg (-(T * h)) numerator)
              (neg_neg ((T * h) * numerator)))))

theorem Real.mul_self_add_sq
    (x h : ℝ) :
    (x * (x + h)) ^ 2 = x ^ 2 * (x + h) ^ 2 := by
  exact mul_pow x (x + h) 2

theorem Complex.hasDerivAt_logarithmicPhaseDualShiftedDifferenceDerivative
    (t : ℝ) {h x : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    HasDerivAt
      (Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h)
      (Complex.logarithmicPhaseDualShiftedDifferenceSecondDerivative t h x) x := by
  have hxh : 0 < x + h := add_pos_of_pos_of_nonneg hx hh
  have hinverse := Real.hasDerivAt_inv_mul_self_add hx.ne' hxh.ne'
  have hscaled := hinverse.const_mul (-‖t‖ * h)
  have hsign := Real.neg_mul_neg_div_eq_mul_div
    ‖t‖ h (2 * x + h) ((x * (x + h)) ^ 2)
  have hsquare := Real.mul_self_add_sq x h
  have hnormalize :
      (-‖t‖ * h) * (-(2 * x + h) / (x * (x + h)) ^ 2) =
        Complex.logarithmicPhaseDualShiftedDifferenceSecondDerivative t h x := by
    unfold Complex.logarithmicPhaseDualShiftedDifferenceSecondDerivative
    exact Eq.trans hsign
      (congrArg
        (fun denominator : ℝ => ‖t‖ * h * (2 * x + h) / denominator)
        hsquare)
  unfold Complex.logarithmicPhaseDualShiftedDifferenceDerivative
  have hfunction :
      (fun y : ℝ => -‖t‖ * h / (y * (y + h))) =
        (fun y : ℝ => (-‖t‖ * h) * (y * (y + h))⁻¹) := by
    funext y
    exact div_eq_mul_inv (-‖t‖ * h) (y * (y + h))
  exact Eq.subst
    (motive := fun f : ℝ → ℝ =>
      HasDerivAt f
        (Complex.logarithmicPhaseDualShiftedDifferenceSecondDerivative t h x) x)
    hfunction.symm
    (Eq.subst
      (motive := fun z : ℝ =>
        HasDerivAt
          (fun y : ℝ => (-‖t‖ * h) * (y * (y + h))⁻¹) z x)
      hnormalize.symm hscaled)

theorem Complex.logarithmicPhaseDualShiftedDifferenceSecondDerivative_pos
    (t : ℝ) (ht : 1 ≤ ‖t‖) {h x : ℝ}
    (hh : 0 < h) (hx : 0 < x) :
    0 < Complex.logarithmicPhaseDualShiftedDifferenceSecondDerivative t h x := by
  unfold Complex.logarithmicPhaseDualShiftedDifferenceSecondDerivative
  have hnorm : 0 < ‖t‖ := lt_of_lt_of_le zero_lt_one ht
  have hfirst : 0 < ‖t‖ * h := mul_pos hnorm hh
  have hlinear : 0 < 2 * x + h :=
    add_pos (mul_pos zero_lt_two hx) hh
  have hnumerator : 0 < ‖t‖ * h * (2 * x + h) :=
    mul_pos hfirst hlinear
  have hxh : 0 < x + h := add_pos hx hh
  have hdenom : 0 < x ^ 2 * (x + h) ^ 2 :=
    mul_pos (sq_pos_of_pos hx) (sq_pos_of_pos hxh)
  exact div_pos hnumerator hdenom

theorem Complex.logarithmicPhaseDualShiftedDifferenceSecondDerivative_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) {h x : ℝ}
    (hh : 0 < h) (hx : 0 < x) :
    0 ≤ Complex.logarithmicPhaseDualShiftedDifferenceSecondDerivative t h x :=
  le_of_lt
    (Complex.logarithmicPhaseDualShiftedDifferenceSecondDerivative_pos
      t ht hh hx)

theorem Real.sq_mul_sq_mono
    {x y h : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) (hh : 0 ≤ h) :
    x ^ 2 * (x + h) ^ 2 ≤ y ^ 2 * (y + h) ^ 2 := by
  have hy : 0 ≤ y := le_trans hx hxy
  have hsum : x + h ≤ y + h := add_le_add_right hxy h
  have hxsum : 0 ≤ x + h := add_nonneg hx hh
  have hysum : 0 ≤ y + h := add_nonneg hy hh
  have hsquare := pow_le_pow_left₀ hx hxy 2
  have hsumSquare := pow_le_pow_left₀ hxsum hsum 2
  exact mul_le_mul hsquare hsumSquare
    (sq_nonneg (x + h)) (sq_nonneg y)

theorem Complex.logarithmicPhaseDualShiftedDifferenceSecondDerivative_lower_on_Icc
    (t : ℝ) {h L U x : ℝ}
    (hh : 0 < h) (hL : 0 < L) (hLU : L ≤ U)
    (hx : x ∈ Set.Icc L U) :
    ‖t‖ * h * (2 * L + h) /
        (U ^ 2 * (U + h) ^ 2) ≤
      Complex.logarithmicPhaseDualShiftedDifferenceSecondDerivative t h x := by
  unfold Complex.logarithmicPhaseDualShiftedDifferenceSecondDerivative
  have hxPos : 0 < x := lt_of_lt_of_le hL hx.1
  have hUPos : 0 < U := lt_of_lt_of_le hL hLU
  have hnumerator :
      ‖t‖ * h * (2 * L + h) ≤ ‖t‖ * h * (2 * x + h) := by
    have hlinear : 2 * L + h ≤ 2 * x + h :=
      add_le_add_right
        (mul_le_mul_of_nonneg_left hx.1 (le_of_lt zero_lt_two)) h
    exact mul_le_mul_of_nonneg_left hlinear
      (mul_nonneg (norm_nonneg t) (le_of_lt hh))
  have hdenom :
      x ^ 2 * (x + h) ^ 2 ≤ U ^ 2 * (U + h) ^ 2 :=
    Real.sq_mul_sq_mono (le_of_lt hxPos) hx.2 (le_of_lt hh)
  have hleftNumerator :
      0 ≤ ‖t‖ * h * (2 * L + h) := by
    exact mul_nonneg
      (mul_nonneg (norm_nonneg t) (le_of_lt hh))
      (add_nonneg
        (mul_nonneg (le_of_lt zero_lt_two) (le_of_lt hL))
        (le_of_lt hh))
  have hxDenom : 0 < x ^ 2 * (x + h) ^ 2 :=
    mul_pos (sq_pos_of_pos hxPos) (sq_pos_of_pos (add_pos hxPos hh))
  exact div_le_div hnumerator hdenom hleftNumerator (le_of_lt hxDenom)

theorem Complex.logarithmicPhaseDualShiftedDifferenceSecondDerivative_upper_on_Icc
    (t : ℝ) {h L U x : ℝ}
    (hh : 0 < h) (hL : 0 < L) (hLU : L ≤ U)
    (hx : x ∈ Set.Icc L U) :
    Complex.logarithmicPhaseDualShiftedDifferenceSecondDerivative t h x ≤
      ‖t‖ * h * (2 * U + h) /
        (L ^ 2 * (L + h) ^ 2) := by
  unfold Complex.logarithmicPhaseDualShiftedDifferenceSecondDerivative
  have hxPos : 0 < x := lt_of_lt_of_le hL hx.1
  have hnumerator :
      ‖t‖ * h * (2 * x + h) ≤ ‖t‖ * h * (2 * U + h) := by
    have hlinear : 2 * x + h ≤ 2 * U + h :=
      add_le_add_right
        (mul_le_mul_of_nonneg_left hx.2 (le_of_lt zero_lt_two)) h
    exact mul_le_mul_of_nonneg_left hlinear
      (mul_nonneg (norm_nonneg t) (le_of_lt hh))
  have hdenom :
      L ^ 2 * (L + h) ^ 2 ≤ x ^ 2 * (x + h) ^ 2 :=
    Real.sq_mul_sq_mono (le_of_lt hL) hx.1 (le_of_lt hh)
  have hleftNumerator : 0 ≤ ‖t‖ * h * (2 * x + h) :=
    mul_nonneg
      (mul_nonneg (norm_nonneg t) (le_of_lt hh))
      (add_nonneg
        (mul_nonneg (le_of_lt zero_lt_two) (le_of_lt hxPos))
        (le_of_lt hh))
  have hLDenom : 0 < L ^ 2 * (L + h) ^ 2 :=
    mul_pos (sq_pos_of_pos hL) (sq_pos_of_pos (add_pos hL hh))
  exact div_le_div hnumerator hdenom hleftNumerator (le_of_lt hLDenom)

end

end LFunctions
end Boundary
