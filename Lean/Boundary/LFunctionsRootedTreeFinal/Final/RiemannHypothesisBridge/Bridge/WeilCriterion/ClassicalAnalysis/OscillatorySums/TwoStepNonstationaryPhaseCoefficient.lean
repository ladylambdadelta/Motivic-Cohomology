import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.TwoStepNonstationaryAmplitude

/-!
# Second derivative of the reciprocal phase coefficient

For `D=iφ'` and `c=D⁻¹`, this owner proves

`c'=-D'/D²`,
`c''=-D''/D²+2(D')²/D³`,

and supplies the norm estimates used by the two-step amplitude transform.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.realPhaseIntegrationCoefficientDerivative
    (φ' φ'' : ℝ → ℝ)
    (x : ℝ) : ℂ :=
  -(Complex.I * (φ'' x : ℂ)) /
    (Complex.realPhaseDerivativeDenominator φ' x) ^ 2

def Complex.realPhaseIntegrationCoefficientSecondDerivative
    (φ' φ'' φ''' : ℝ → ℝ)
    (x : ℝ) : ℂ :=
  -(Complex.I * (φ''' x : ℂ)) /
      (Complex.realPhaseDerivativeDenominator φ' x) ^ 2 +
    2 * (Complex.I * (φ'' x : ℂ)) ^ 2 /
      (Complex.realPhaseDerivativeDenominator φ' x) ^ 3

theorem Complex.hasDerivAt_realPhaseIntegrationCoefficient_named
    {φ' φ'' : ℝ → ℝ}
    {x : ℝ}
    (hφ' : HasDerivAt φ' (φ'' x) x)
    (hnonzero : Complex.realPhaseDerivativeDenominator φ' x ≠ 0) :
    HasDerivAt
      (Complex.realPhaseIntegrationCoefficient φ')
      (Complex.realPhaseIntegrationCoefficientDerivative φ' φ'' x)
      x := by
  unfold Complex.realPhaseIntegrationCoefficientDerivative
  exact Complex.hasDerivAt_realPhaseIntegrationCoefficient hφ' hnonzero

theorem Complex.hasDerivAt_realPhaseDerivativeDenominator
    {φ' φ'' : ℝ → ℝ}
    {x : ℝ}
    (hφ' : HasDerivAt φ' (φ'' x) x) :
    HasDerivAt
      (Complex.realPhaseDerivativeDenominator φ')
      (Complex.I * (φ'' x : ℂ)) x := by
  unfold Complex.realPhaseDerivativeDenominator
  exact hφ'.ofReal_comp.const_mul Complex.I

theorem Complex.hasDerivAt_realPhaseDerivativeDenominator_sq
    {φ' φ'' : ℝ → ℝ}
    {x : ℝ}
    (hφ' : HasDerivAt φ' (φ'' x) x) :
    HasDerivAt
      (fun y : ℝ =>
        (Complex.realPhaseDerivativeDenominator φ' y) ^ 2)
      (2 * Complex.realPhaseDerivativeDenominator φ' x *
        (Complex.I * (φ'' x : ℂ))) x := by
  exact (Complex.hasDerivAt_realPhaseDerivativeDenominator hφ').pow 2

theorem Complex.hasDerivAt_realPhaseIntegrationCoefficientDerivative
    {φ' φ'' φ''' : ℝ → ℝ}
    {x : ℝ}
    (hφ' : HasDerivAt φ' (φ'' x) x)
    (hφ'' : HasDerivAt φ'' (φ''' x) x)
    (hnonzero : Complex.realPhaseDerivativeDenominator φ' x ≠ 0) :
    HasDerivAt
      (Complex.realPhaseIntegrationCoefficientDerivative φ' φ'')
      (Complex.realPhaseIntegrationCoefficientSecondDerivative
        φ' φ'' φ''' x) x := by
  let D : ℂ := Complex.realPhaseDerivativeDenominator φ' x
  let D' : ℂ := Complex.I * (φ'' x : ℂ)
  let D'' : ℂ := Complex.I * (φ''' x : ℂ)
  have hnumerator :
      HasDerivAt (fun y : ℝ => -(Complex.I * (φ'' y : ℂ))) (-D'') x := by
    exact (hφ''.ofReal_comp.const_mul Complex.I).neg
  have hdenominator := Complex.hasDerivAt_realPhaseDerivativeDenominator_sq hφ'
  have hdenominatorNe : D ^ 2 ≠ 0 := pow_ne_zero 2 hnonzero
  have hquotient := hnumerator.div hdenominator hdenominatorNe
  unfold Complex.realPhaseIntegrationCoefficientDerivative
  unfold Complex.realPhaseIntegrationCoefficientSecondDerivative
  change HasDerivAt
    (fun y : ℝ =>
      -(Complex.I * (φ'' y : ℂ)) /
        (Complex.realPhaseDerivativeDenominator φ' y) ^ 2)
    (-D'' / D ^ 2 + 2 * D' ^ 2 / D ^ 3) x
  have hnormalize :
      ((-D'') * D ^ 2 - (-D') * (2 * D * D')) /
          (D ^ 2) ^ 2 =
        -D'' / D ^ 2 + 2 * D' ^ 2 / D ^ 3 := by
    have hD2Ne : D ^ 2 ≠ 0 := pow_ne_zero 2 hnonzero
    have hD3Ne : D ^ 3 ≠ 0 := pow_ne_zero 3 hnonzero
    have hD4Ne : (D ^ 2) ^ 2 ≠ 0 := pow_ne_zero 2 hD2Ne
    calc
      ((-D'') * D ^ 2 - (-D') * (2 * D * D')) /
          (D ^ 2) ^ 2 =
        ((-D'') * D ^ 2) / (D ^ 2) ^ 2 -
          ((-D') * (2 * D * D')) / (D ^ 2) ^ 2 :=
        div_sub_div_same _ _ _
      _ = -D'' / D ^ 2 - (-(2 * D' ^ 2 / D ^ 3)) := by
        exact congrArg₂ (fun first second : ℂ => first - second)
          (Eq.trans
            (mul_div_assoc (-D'') (D ^ 2) ((D ^ 2) ^ 2))
            (congrArg (fun value : ℂ => (-D'') * value)
              (div_pow_self (D ^ 2) 1 hD2Ne)))
          (by
            exact Eq.trans
              (congrArg (fun value : ℂ => value / (D ^ 2) ^ 2)
                ((mul_assoc (-D') (2 * D) D').trans
                  (congrArg (fun value : ℂ => value * D')
                    ((mul_assoc (-D') 2 D).trans
                      (congrArg (fun value : ℂ => value * D)
                        (mul_comm (-D') 2))))))
              rfl)
      _ = -D'' / D ^ 2 + 2 * D' ^ 2 / D ^ 3 :=
        (sub_neg_eq_add _ _)
  exact Eq.subst
    (motive := fun value : ℂ =>
      HasDerivAt
        (fun y : ℝ =>
          -(Complex.I * (φ'' y : ℂ)) /
            (Complex.realPhaseDerivativeDenominator φ' y) ^ 2)
        value x)
    hnormalize
    hquotient

theorem Complex.norm_realPhaseIntegrationCoefficientDerivative
    (φ' φ'' : ℝ → ℝ)
    (x : ℝ) :
    ‖Complex.realPhaseIntegrationCoefficientDerivative φ' φ'' x‖ =
      |φ'' x| / ‖φ' x‖ ^ 2 := by
  unfold Complex.realPhaseIntegrationCoefficientDerivative
  exact Eq.trans
    (Complex.norm_neg_I_mul_real_div_sq
      (φ'' x) (Complex.realPhaseDerivativeDenominator φ' x))
    (congrArg (fun denominator : ℝ => |φ'' x| / denominator ^ 2)
      (Complex.norm_realPhaseDerivativeDenominator φ' x))

theorem Complex.norm_realPhaseIntegrationCoefficientSecondDerivative_le
    (φ' φ'' φ''' : ℝ → ℝ)
    (x : ℝ) :
    ‖Complex.realPhaseIntegrationCoefficientSecondDerivative
        φ' φ'' φ''' x‖ ≤
      |φ''' x| / ‖φ' x‖ ^ 2 +
        2 * |φ'' x| ^ 2 / ‖φ' x‖ ^ 3 := by
  unfold Complex.realPhaseIntegrationCoefficientSecondDerivative
  have htriangle := norm_add_le
    (-(Complex.I * (φ''' x : ℂ)) /
      (Complex.realPhaseDerivativeDenominator φ' x) ^ 2)
    (2 * (Complex.I * (φ'' x : ℂ)) ^ 2 /
      (Complex.realPhaseDerivativeDenominator φ' x) ^ 3)
  have hfirst := Complex.norm_neg_I_mul_real_div_sq
    (φ''' x) (Complex.realPhaseDerivativeDenominator φ' x)
  have hsecond :
      ‖2 * (Complex.I * (φ'' x : ℂ)) ^ 2 /
          (Complex.realPhaseDerivativeDenominator φ' x) ^ 3‖ =
        2 * |φ'' x| ^ 2 / ‖φ' x‖ ^ 3 := by
    exact Eq.trans
      (norm_div _ _)
      (congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
        (Eq.trans (norm_mul 2 _)
          (congrArg₂ (fun first second : ℝ => first * second)
            (Real.norm_of_nonneg (Nat.cast_nonneg 2))
            (Eq.trans (norm_pow _ 2)
              (congrArg (fun value : ℝ => value ^ 2)
                ((norm_mul Complex.I (φ'' x : ℂ)).trans
                  ((congrArg₂ (fun first second : ℝ => first * second)
                    Complex.norm_I (Complex.norm_real (φ'' x))).trans
                    (one_mul _)))))))
        (Eq.trans (norm_pow _ 3)
          (congrArg (fun value : ℝ => value ^ 3)
            (Complex.norm_realPhaseDerivativeDenominator φ' x))))
  exact le_trans htriangle
    (le_of_eq
      (congrArg₂ (fun first second : ℝ => first + second)
        (Eq.trans hfirst
          (congrArg (fun denominator : ℝ =>
            |φ''' x| / denominator ^ 2)
            (Complex.norm_realPhaseDerivativeDenominator φ' x)))
        hsecond))

end
end LFunctions
end Boundary
