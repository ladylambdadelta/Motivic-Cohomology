import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicDualBProcessAmplitude

/-!
# Weyl-shift geometry of the dual logarithmic phase

The dual stationary action differs from `‖t‖ log u` by a constant.  Its
positive shift difference therefore has the exact form

`D_h(x) = ‖t‖ * (log (x+h) - log x)`.

On the positive half-line,

`D_h'(x)  = -‖t‖*h/(x*(x+h))`,

`D_h''(x) = ‖t‖*h*(2*x+h)/(x^2*(x+h)^2)`.

Thus for a positive shift the first derivative is negative and strictly
increasing, while its absolute value is antitone.  This is the exact
first-derivative geometry needed for each off-diagonal Weyl correlation of the
dual phase.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseDualShiftedDifference
    (t h x : ℝ) : ℝ :=
  Complex.logarithmicPhaseDualStationaryActionClosed t (x + h) -
    Complex.logarithmicPhaseDualStationaryActionClosed t x

def Complex.logarithmicPhaseDualShiftedDifferenceClosed
    (t h x : ℝ) : ℝ :=
  ‖t‖ * (Real.log (x + h) - Real.log x)

def Complex.logarithmicPhaseDualShiftedDifferenceDerivative
    (t h x : ℝ) : ℝ :=
  -‖t‖ * h / (x * (x + h))

def Complex.logarithmicPhaseDualShiftedDifferenceSecondDerivative
    (t h x : ℝ) : ℝ :=
  ‖t‖ * h * (2 * x + h) /
    (x ^ 2 * (x + h) ^ 2)

theorem Complex.logarithmicPhaseDualShiftedDifference_eq_closed
    (t h x : ℝ) :
    Complex.logarithmicPhaseDualShiftedDifference t h x =
      Complex.logarithmicPhaseDualShiftedDifferenceClosed t h x := by
  unfold Complex.logarithmicPhaseDualShiftedDifference
  unfold Complex.logarithmicPhaseDualStationaryActionClosed
  unfold Complex.logarithmicPhaseDualShiftedDifferenceClosed
  have hconstant :
      (-‖t‖ * Real.log (‖t‖ / (2 * Real.pi)) + ‖t‖) -
        (-‖t‖ * Real.log (‖t‖ / (2 * Real.pi)) + ‖t‖) = 0 :=
    sub_self _
  calc
    (‖t‖ * Real.log (x + h) +
          (-‖t‖ * Real.log (‖t‖ / (2 * Real.pi)) + ‖t‖)) -
        (‖t‖ * Real.log x +
          (-‖t‖ * Real.log (‖t‖ / (2 * Real.pi)) + ‖t‖)) =
      (‖t‖ * Real.log (x + h) - ‖t‖ * Real.log x) + 0 := by
        exact Eq.trans
          (add_sub_add_comm
            (‖t‖ * Real.log (x + h))
            (-‖t‖ * Real.log (‖t‖ / (2 * Real.pi)) + ‖t‖)
            (‖t‖ * Real.log x)
            (-‖t‖ * Real.log (‖t‖ / (2 * Real.pi)) + ‖t‖))
          (congrArg
            (fun z : ℝ =>
              (‖t‖ * Real.log (x + h) - ‖t‖ * Real.log x) + z)
            hconstant)
    _ = ‖t‖ * Real.log (x + h) - ‖t‖ * Real.log x := add_zero _
    _ = ‖t‖ * (Real.log (x + h) - Real.log x) :=
      (mul_sub ‖t‖ (Real.log (x + h)) (Real.log x)).symm

theorem Real.inv_sub_inv_eq_neg_mul_div
    {x h : ℝ} (hx : x ≠ 0) (hxh : x + h ≠ 0) :
    (x + h)⁻¹ - x⁻¹ = -h / (x * (x + h)) := by
  have hdenom : x * (x + h) ≠ 0 := mul_ne_zero hx hxh
  exact (div_eq_iff hdenom).mpr
    (by
      calc
        ((x + h)⁻¹ - x⁻¹) * (x * (x + h)) =
            (x + h)⁻¹ * (x * (x + h)) -
              x⁻¹ * (x * (x + h)) := sub_mul _ _ _
        _ = x - (x + h) := by
          exact congrArg₂ (fun a b : ℝ => a - b)
            (Eq.trans
              (mul_assoc (x + h)⁻¹ x (x + h))
              (Eq.trans
                (congrArg (fun z : ℝ => z * (x + h))
                  (mul_comm (x + h)⁻¹ x))
                (Eq.trans
                  (mul_assoc x (x + h)⁻¹ (x + h)).symm
                  (Eq.trans
                    (congrArg (fun z : ℝ => x * z)
                      (inv_mul_cancel₀ hxh))
                    (mul_one x)))))
            (Eq.trans
              (mul_assoc x⁻¹ x (x + h)).symm
              (Eq.trans
                (congrArg (fun z : ℝ => z * (x + h))
                  (inv_mul_cancel₀ hx))
                (one_mul (x + h))))
        _ = -h := by
          exact Eq.trans (sub_add_eq_sub_sub_swap x x h)
            (Eq.trans
              (congrArg (fun z : ℝ => z - h) (sub_self x))
              (zero_sub h))
        _ = (-h / (x * (x + h))) * (x * (x + h)) := by
          exact (div_mul_cancel₀ (-h) hdenom).symm)

theorem Complex.hasDerivAt_logarithmicPhaseDualShiftedDifferenceClosed
    (t h : ℝ) {x : ℝ} (hx : 0 < x) (hh : 0 ≤ h) :
    HasDerivAt
      (Complex.logarithmicPhaseDualShiftedDifferenceClosed t h)
      (Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h x) x := by
  have hxh : 0 < x + h := add_pos_of_pos_of_nonneg hx hh
  have hlogShift :
      HasDerivAt (fun y : ℝ => Real.log (y + h)) (x + h)⁻¹ x := by
    have hinner : HasDerivAt (fun y : ℝ => y + h) 1 x :=
      hasDerivAt_id x |>.add_const h
    exact (Real.hasDerivAt_log hxh.ne').comp x hinner
  have hlog : HasDerivAt Real.log x⁻¹ x := Real.hasDerivAt_log hx.ne'
  have hdifference := hlogShift.sub hlog
  have hscaled := hdifference.const_mul ‖t‖
  have hinvDifference := Real.inv_sub_inv_eq_neg_mul_div hx.ne' hxh.ne'
  have hnormalize :
      ‖t‖ * ((x + h)⁻¹ - x⁻¹) =
        Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h x := by
    unfold Complex.logarithmicPhaseDualShiftedDifferenceDerivative
    exact Eq.trans
      (congrArg (fun z : ℝ => ‖t‖ * z) hinvDifference)
      (Eq.trans
        (mul_div_assoc ‖t‖ (-h) (x * (x + h))).symm
        (congrArg
          (fun z : ℝ => z / (x * (x + h)))
          (mul_neg ‖t‖ h)))
  unfold Complex.logarithmicPhaseDualShiftedDifferenceClosed
  exact Eq.subst
    (motive := fun z : ℝ =>
      HasDerivAt
        (fun y : ℝ => ‖t‖ * (Real.log (y + h) - Real.log y)) z x)
    hnormalize.symm hscaled

theorem Real.derivative_negativeProductQuotient_eq
    (T h x : ℝ) (hx : x ≠ 0) (hxh : x + h ≠ 0) :
    T * h * (2 * x + h) / (x ^ 2 * (x + h) ^ 2) =
      T * h * ((x + h) + x) / (x ^ 2 * (x + h) ^ 2) := by
  exact congrArg
    (fun z : ℝ => T * h * z / (x ^ 2 * (x + h) ^ 2))
    (Eq.trans
      (two_mul x)
      (Eq.trans
        (congrArg (fun z : ℝ => z + h) (add_comm x x))
        (Eq.trans
          (add_assoc x x h)
          (Eq.trans
            (congrArg (fun z : ℝ => x + z) (add_comm x h))
            (add_assoc (x + h) x 0).symm))))

theorem Complex.logarithmicPhaseDualShiftedDifferenceDerivative_neg
    (t : ℝ) (ht : 1 ≤ ‖t‖) {h x : ℝ}
    (hh : 0 < h) (hx : 0 < x) :
    Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h x < 0 := by
  unfold Complex.logarithmicPhaseDualShiftedDifferenceDerivative
  have hnorm : 0 < ‖t‖ := lt_of_lt_of_le zero_lt_one ht
  have hnumerator : -‖t‖ * h < 0 :=
    mul_neg_of_neg_of_pos (neg_neg_of_pos hnorm) hh
  have hxh : 0 < x + h := add_pos hx hh
  have hdenom : 0 < x * (x + h) := mul_pos hx hxh
  exact div_neg_of_neg_of_pos hnumerator hdenom

theorem Complex.logarithmicPhaseDualShiftedDifferenceDerivative_abs_eq
    (t : ℝ) {h x : ℝ} (hh : 0 ≤ h) (hx : 0 < x) :
    |Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h x| =
      ‖t‖ * h / (x * (x + h)) := by
  unfold Complex.logarithmicPhaseDualShiftedDifferenceDerivative
  have hnumerator : 0 ≤ ‖t‖ * h := mul_nonneg (norm_nonneg t) hh
  have hxh : 0 < x + h := add_pos_of_pos_of_nonneg hx hh
  have hdenom : 0 ≤ x * (x + h) := le_of_lt (mul_pos hx hxh)
  have hquotient : 0 ≤ ‖t‖ * h / (x * (x + h)) :=
    div_nonneg hnumerator hdenom
  exact Eq.trans
    (abs_neg (‖t‖ * h / (x * (x + h))))
    (abs_of_nonneg hquotient)

theorem Real.mul_add_mul_le_mul_add_mul
    {x y h : ℝ} (hxy : x ≤ y) (hh : 0 ≤ h)
    (hx : 0 ≤ x) :
    x * (x + h) ≤ y * (y + h) := by
  have hy : 0 ≤ y := le_trans hx hxy
  have hsum : x + h ≤ y + h := add_le_add_right hxy h
  exact mul_le_mul hxy hsum (add_nonneg hx hh) hy

theorem Complex.logarithmicPhaseDualShiftedDifferenceDerivative_abs_antitoneOn
    (t : ℝ) {h : ℝ} (hh : 0 ≤ h) :
    AntitoneOn
      (fun x : ℝ =>
        |Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h x|)
      (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hxDenom : 0 < x * (x + h) :=
    mul_pos hx (add_pos_of_pos_of_nonneg hx hh)
  have hdenom := Real.mul_add_mul_le_mul_add_mul hxy hh (le_of_lt hx)
  have hnumerator := mul_nonneg (norm_nonneg t) hh
  have hdivision := div_le_div_of_nonneg_left hnumerator hxDenom hdenom
  exact Eq.subst (motive := fun z : ℝ => z ≤ _)
    (Complex.logarithmicPhaseDualShiftedDifferenceDerivative_abs_eq
      t hh hy).symm
    (Eq.subst (motive := fun z : ℝ => _ ≤ z)
      (Complex.logarithmicPhaseDualShiftedDifferenceDerivative_abs_eq
        t hh hx).symm hdivision)

theorem Complex.logarithmicPhaseDualShiftedDifferenceDerivative_abs_lower_on_Icc
    (t : ℝ) {h L U x : ℝ}
    (hh : 0 < h) (hL : 0 < L) (hLU : L ≤ U)
    (hx : x ∈ Set.Icc L U) :
    ‖t‖ * h / (U * (U + h)) ≤
      |Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h x| := by
  have hU : 0 < U := lt_of_lt_of_le hL hLU
  have hformulaU :=
    Complex.logarithmicPhaseDualShiftedDifferenceDerivative_abs_eq
      t (le_of_lt hh) hU
  have hformulaX :=
    Complex.logarithmicPhaseDualShiftedDifferenceDerivative_abs_eq
      t (le_of_lt hh) (lt_of_lt_of_le hL hx.1)
  have hanti :=
    Complex.logarithmicPhaseDualShiftedDifferenceDerivative_abs_antitoneOn
      t (le_of_lt hh)
      (lt_of_lt_of_le hL hx.1) hU hx.2
  exact Eq.subst (motive := fun z : ℝ => z ≤ _)
    hformulaU.symm
    (Eq.subst (motive := fun z : ℝ => _ ≤ z)
      hformulaX.symm hanti)

theorem Complex.logarithmicPhaseDualShiftedDifferenceDerivative_abs_upper_on_Icc
    (t : ℝ) {h L U x : ℝ}
    (hh : 0 < h) (hL : 0 < L) (hLU : L ≤ U)
    (hx : x ∈ Set.Icc L U) :
    |Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h x| ≤
      ‖t‖ * h / (L * (L + h)) := by
  have hxPos : 0 < x := lt_of_lt_of_le hL hx.1
  have hformulaL :=
    Complex.logarithmicPhaseDualShiftedDifferenceDerivative_abs_eq
      t (le_of_lt hh) hL
  have hformulaX :=
    Complex.logarithmicPhaseDualShiftedDifferenceDerivative_abs_eq
      t (le_of_lt hh) hxPos
  have hanti :=
    Complex.logarithmicPhaseDualShiftedDifferenceDerivative_abs_antitoneOn
      t (le_of_lt hh) hL hxPos hx.1
  exact Eq.subst (motive := fun z : ℝ => z ≤ _)
    hformulaX.symm
    (Eq.subst (motive := fun z : ℝ => _ ≤ z)
      hformulaL.symm hanti)

theorem Complex.logarithmicPhaseDualShiftedDifferenceDerivative_strictMonoOn
    (t : ℝ) (ht : 1 ≤ ‖t‖) {h : ℝ} (hh : 0 < h) :
    StrictMonoOn
      (Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h)
      (Set.Ioi 0) := by
  intro x hx y hy hxy
  have habs :=
    Complex.logarithmicPhaseDualShiftedDifferenceDerivative_abs_antitoneOn
      t (le_of_lt hh) hx hy (le_of_lt hxy)
  have hxNeg :=
    Complex.logarithmicPhaseDualShiftedDifferenceDerivative_neg t ht hh hx
  have hyNeg :=
    Complex.logarithmicPhaseDualShiftedDifferenceDerivative_neg t ht hh hy
  have hstrictDenom : x * (x + h) < y * (y + h) := by
    have hsum : x + h < y + h := add_lt_add_right hxy h
    exact mul_lt_mul hxy hsum
      (add_pos hx hh) (le_of_lt hx)
  have hnumerator : 0 < ‖t‖ * h :=
    mul_pos (lt_of_lt_of_le zero_lt_one ht) hh
  have habsStrict :
      |Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h y| <
        |Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h x| := by
    have hxDenom := mul_pos hx (add_pos hx hh)
    have hdiv := div_lt_div_of_pos_left hnumerator hxDenom hstrictDenom
    exact Eq.subst (motive := fun z : ℝ => z < _)
      (Complex.logarithmicPhaseDualShiftedDifferenceDerivative_abs_eq
        t (le_of_lt hh) hy).symm
      (Eq.subst (motive := fun z : ℝ => _ < z)
        (Complex.logarithmicPhaseDualShiftedDifferenceDerivative_abs_eq
          t (le_of_lt hh) hx).symm hdiv)
  have hxAbs :
      |Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h x| =
        -Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h x :=
    abs_of_neg hxNeg
  have hyAbs :
      |Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h y| =
        -Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h y :=
    abs_of_neg hyNeg
  have hneg :
      -Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h y <
        -Complex.logarithmicPhaseDualShiftedDifferenceDerivative t h x :=
    Eq.subst (motive := fun z : ℝ => z < _)
      hyAbs habsStrict
  exact neg_lt_neg_iff.mp hneg

end

end LFunctions
end Boundary
