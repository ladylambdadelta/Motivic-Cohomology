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
  let denominator : ℝ → ℂ := Complex.realPhaseDerivativeDenominator φ'
  have hdenominator :=
    Complex.hasDerivAt_realPhaseDerivativeDenominator hφ'
  have hproduct := hdenominator.mul hdenominator
  have hfunction :
      (fun y : ℝ => denominator y ^ 2) =
        (fun y : ℝ => denominator y * denominator y) := by
    funext y
    exact pow_two (denominator y)
  have hderivative_eq :
      (Complex.I * (φ'' x : ℂ)) * denominator x +
          denominator x * (Complex.I * (φ'' x : ℂ)) =
        2 * denominator x * (Complex.I * (φ'' x : ℂ)) := by
    calc
      (Complex.I * (φ'' x : ℂ)) * denominator x +
          denominator x * (Complex.I * (φ'' x : ℂ)) =
          denominator x * (Complex.I * (φ'' x : ℂ)) +
            denominator x * (Complex.I * (φ'' x : ℂ)) :=
        congrArg
          (fun value : ℂ => value + denominator x * (Complex.I * (φ'' x : ℂ)))
          (mul_comm (Complex.I * (φ'' x : ℂ)) (denominator x))
      _ = 2 * (denominator x * (Complex.I * (φ'' x : ℂ))) :=
        (two_mul _).symm
      _ = 2 * denominator x * (Complex.I * (φ'' x : ℂ)) :=
        (mul_assoc _ _ _).symm
  have hproduct_function :
      HasDerivAt
        (fun y : ℝ => denominator y ^ 2)
        (2 * denominator x * (Complex.I * (φ'' x : ℂ))) x := by
    have hproduct_named :
        HasDerivAt
          (fun y : ℝ => denominator y * denominator y)
          (2 * denominator x * (Complex.I * (φ'' x : ℂ))) x := by
      change HasDerivAt
        (fun y : ℝ => denominator y * denominator y)
        (_ * denominator x + denominator x * _) x at hproduct
      exact hderivative_eq ▸ hproduct
    exact Eq.subst
      (motive := fun f : ℝ → ℂ =>
        HasDerivAt f (2 * denominator x * (Complex.I * (φ'' x : ℂ))) x)
      hfunction.symm hproduct_named
  exact hproduct_function

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
    have hinvpow : ((D ^ 2) ^ 2)⁻¹ = (D ^ 2)⁻¹ * (D ^ 2)⁻¹ := by
      exact (congrArg Inv.inv (pow_two (D ^ 2))).trans
        (mul_inv_rev (D ^ 2) (D ^ 2))
    have hdivpow : D ^ 2 / (D ^ 2) ^ 2 = (D ^ 2)⁻¹ := by
      calc
        D ^ 2 / (D ^ 2) ^ 2 = D ^ 2 * ((D ^ 2) ^ 2)⁻¹ :=
          div_eq_mul_inv _ _
        _ = D ^ 2 * ((D ^ 2)⁻¹ * (D ^ 2)⁻¹) :=
          congrArg (fun value : ℂ => D ^ 2 * value) hinvpow
        _ = (D ^ 2 * (D ^ 2)⁻¹) * (D ^ 2)⁻¹ :=
          (mul_assoc _ _ _).symm
        _ = 1 * (D ^ 2)⁻¹ :=
          congrArg (fun value : ℂ => value * (D ^ 2)⁻¹)
            (mul_inv_cancel₀ hD2Ne)
        _ = (D ^ 2)⁻¹ := one_mul _
    have hD4 : (D ^ 2) ^ 2 = D ^ 4 := by
      exact (pow_mul D 2 2).symm
    have hD4_over_D3 : D ^ 4 / D ^ 3 = D := by
      exact (div_eq_iff hD3Ne).2
        ((pow_succ D 3).trans (mul_comm (D ^ 3) D))
    have hnum : (-D') * (2 * D * D') = -(2 * D' ^ 2) * D := by
      have hinner : D' * (2 * D * D') = 2 * D' ^ 2 * D := by
        calc
          D' * (2 * D * D') = D' * (2 * (D * D')) :=
            congrArg (fun value : ℂ => D' * value) (mul_assoc 2 D D')
          _ = (D' * 2) * (D * D') :=
            (mul_assoc D' 2 (D * D')).symm
          _ = (2 * D') * (D * D') :=
            congrArg (fun value : ℂ => value * (D * D')) (mul_comm D' 2)
          _ = 2 * (D' * (D * D')) :=
            mul_assoc 2 D' (D * D')
          _ = 2 * ((D' * D) * D') :=
            congrArg (fun value : ℂ => 2 * value) (mul_assoc D' D D').symm
          _ = 2 * (D' * (D' * D)) :=
            congrArg (fun value : ℂ => 2 * value)
              ((mul_assoc D' D D').trans
                (congrArg (fun value : ℂ => D' * value) (mul_comm D D')))
          _ = 2 * ((D' * D') * D) :=
            congrArg (fun value : ℂ => 2 * value)
              (mul_assoc D' D' D).symm
          _ = 2 * (D' ^ 2 * D) :=
            congrArg (fun value : ℂ => 2 * (value * D)) (pow_two D').symm
          _ = 2 * D' ^ 2 * D :=
            (mul_assoc 2 (D' ^ 2) D).symm
      calc
        (-D') * (2 * D * D') = -(D' * (2 * D * D')) :=
          neg_mul D' (2 * D * D')
        _ = -(2 * D' ^ 2 * D) := congrArg Neg.neg hinner
        _ = -(2 * D' ^ 2) * D := by
          exact (neg_mul (2 * D' ^ 2) D).symm
    have hsecond_fraction :
        ((-D') * (2 * D * D')) / (D ^ 2) ^ 2 =
          -(2 * D' ^ 2 / D ^ 3) := by
      exact (div_eq_iff hD4Ne).2
        (calc
          (-D') * (2 * D * D') = -(2 * D' ^ 2) * D := hnum
          _ = -(2 * D' ^ 2 / D ^ 3) * D ^ 4 := by
            exact Eq.trans
              (neg_mul (2 * D' ^ 2) D)
              (Eq.trans
                (congrArg Neg.neg
                  (congrArg (fun value : ℂ => (2 * D' ^ 2) * value)
                    hD4_over_D3.symm))
                (Eq.trans
                  (congrArg Neg.neg
                    (mul_div_assoc (2 * D' ^ 2) (D ^ 4) (D ^ 3)).symm)
                  (Eq.trans
                    (congrArg Neg.neg
                      (div_mul_eq_mul_div (2 * D' ^ 2) (D ^ 3) (D ^ 4)).symm)
                    (neg_mul (2 * D' ^ 2 / D ^ 3) (D ^ 4)).symm)))
          _ = -(2 * D' ^ 2 / D ^ 3) * (D ^ 2) ^ 2 :=
            congrArg (fun value : ℂ => -(2 * D' ^ 2 / D ^ 3) * value) hD4.symm)
    calc
      ((-D'') * D ^ 2 - (-D') * (2 * D * D')) /
          (D ^ 2) ^ 2 =
        ((-D'') * D ^ 2) / (D ^ 2) ^ 2 -
          ((-D') * (2 * D * D')) / (D ^ 2) ^ 2 :=
        (div_sub_div_same _ _ _).symm
      _ = -D'' / D ^ 2 - (-(2 * D' ^ 2 / D ^ 3)) := by
        exact congrArg₂ (fun first second : ℂ => first - second)
          (Eq.trans
            (mul_div_assoc (-D'') (D ^ 2) ((D ^ 2) ^ 2))
            (congrArg (fun value : ℂ => (-D'') * value)
              hdivpow))
          hsecond_fraction
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
    have htwo_norm : ‖(2 : ℂ)‖ = (2 : ℝ) :=
      (Complex.norm_real 2).trans
        (Real.norm_of_nonneg (show (0 : ℝ) ≤ 2 from zero_le_two))
    exact Eq.trans
      (norm_div _ _)
      (congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
        (Eq.trans (norm_mul 2 _)
          (congrArg₂ (fun first second : ℝ => first * second)
            htwo_norm
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
