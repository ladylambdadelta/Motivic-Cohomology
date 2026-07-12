import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.TwoStepNonstationaryRawMajorant

/-!
# Arithmetic normalization of the two-step phase majorant

This owner rewrites all quotients as inverse powers, distributes the two raw
products, and combines repeated terms into the canonical coefficients
`1,3,1,3`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.div_pow_eq_mul_inv_pow
    (x g : ℝ) (n : ℕ) :
    x / g ^ n = x * g⁻¹ ^ n := by
  exact Eq.trans
    (div_eq_mul_inv x (g ^ n))
    (congrArg (fun value : ℝ => x * value) (inv_pow g n).symm)

theorem Real.div_eq_mul_inv_one
    (x g : ℝ) :
    x / g = x * g⁻¹ := by
  exact div_eq_mul_inv x g

theorem Complex.nonstationaryFirstDerivativeRawMajorant_eq_inversePowers
    (A A₁ A₂ v w g : ℝ) :
    Complex.nonstationaryFirstDerivativeRawMajorant A A₁ A₂ v w g =
      A₂ * g⁻¹ +
        2 * A₁ * (v * g⁻¹ ^ 2) +
        A * (w * g⁻¹ ^ 2 + 2 * v ^ 2 * g⁻¹ ^ 3) := by
  unfold Complex.nonstationaryFirstDerivativeRawMajorant
  have hv2 := Real.div_pow_eq_mul_inv_pow v g 2
  have hw2 := Real.div_pow_eq_mul_inv_pow w g 2
  have hvSq3 := Real.div_pow_eq_mul_inv_pow (2 * v ^ 2) g 3
  exact congrArg₂ (fun first second : ℝ => first + second)
    (congrArg₂ (fun first second : ℝ => first + second)
      rfl
      (congrArg (fun value : ℝ => 2 * A₁ * value)
        (Eq.trans hv2 (mul_assoc v (g⁻¹ ^ 2) 1))))
    (congrArg (fun value : ℝ => A * value)
      (congrArg₂ (fun first second : ℝ => first + second)
        hw2
        (Eq.trans hvSq3
          (mul_assoc 2 (v ^ 2) (g⁻¹ ^ 3)))))

def Complex.nonstationarySecondTransformExpandedMajorant
    (A A₁ A₂ v w g : ℝ) : ℝ :=
  A₂ * g⁻¹ ^ 2 +
    2 * A₁ * v * g⁻¹ ^ 3 +
    A * w * g⁻¹ ^ 3 +
    2 * A * v ^ 2 * g⁻¹ ^ 4 +
    A₁ * v * g⁻¹ ^ 3 +
    A * v ^ 2 * g⁻¹ ^ 4

theorem Complex.nonstationarySecondTransformRawMajorant_eq_expanded
    (A A₁ A₂ v w g : ℝ) :
    Complex.nonstationarySecondTransformRawMajorant A A₁ A₂ v w g =
      Complex.nonstationarySecondTransformExpandedMajorant A A₁ A₂ v w g := by
  unfold Complex.nonstationarySecondTransformRawMajorant
  unfold Complex.nonstationarySecondTransformExpandedMajorant
  have hfirst :=
    Complex.nonstationaryFirstDerivativeRawMajorant_eq_inversePowers
      A A₁ A₂ v w g
  have hv2 := Real.div_pow_eq_mul_inv_pow v g 2
  calc
    Complex.nonstationaryFirstDerivativeRawMajorant A A₁ A₂ v w g * g⁻¹ +
        (A₁ * g⁻¹ + A * (v / g ^ 2)) * (v / g ^ 2) =
      (A₂ * g⁻¹ + 2 * A₁ * (v * g⁻¹ ^ 2) +
          A * (w * g⁻¹ ^ 2 + 2 * v ^ 2 * g⁻¹ ^ 3)) * g⁻¹ +
        (A₁ * g⁻¹ + A * (v * g⁻¹ ^ 2)) *
          (v * g⁻¹ ^ 2) := by
      exact congrArg₂ (fun first second : ℝ => first + second)
        (congrArg (fun value : ℝ => value * g⁻¹) hfirst)
        (congrArg₂ (fun first second : ℝ => first * second)
          (congrArg (fun value : ℝ => A₁ * g⁻¹ + A * value) hv2)
          hv2)
    _ =
      (A₂ * g⁻¹) * g⁻¹ +
        (2 * A₁ * (v * g⁻¹ ^ 2)) * g⁻¹ +
        (A * (w * g⁻¹ ^ 2 + 2 * v ^ 2 * g⁻¹ ^ 3)) * g⁻¹ +
        (A₁ * g⁻¹) * (v * g⁻¹ ^ 2) +
        (A * (v * g⁻¹ ^ 2)) * (v * g⁻¹ ^ 2) := by
      exact Eq.trans
        (congrArg₂ (fun first second : ℝ => first + second)
          ((add_mul
            (A₂ * g⁻¹ + 2 * A₁ * (v * g⁻¹ ^ 2))
            (A * (w * g⁻¹ ^ 2 + 2 * v ^ 2 * g⁻¹ ^ 3)) g⁻¹).trans
            (congrArg (fun value : ℝ => value +
              (A * (w * g⁻¹ ^ 2 + 2 * v ^ 2 * g⁻¹ ^ 3)) * g⁻¹)
              (add_mul (A₂ * g⁻¹)
                (2 * A₁ * (v * g⁻¹ ^ 2)) g⁻¹)))
          (add_mul (A₁ * g⁻¹) (A * (v * g⁻¹ ^ 2))
            (v * g⁻¹ ^ 2)))
        (add_assoc
          (((A₂ * g⁻¹) * g⁻¹ +
            (2 * A₁ * (v * g⁻¹ ^ 2)) * g⁻¹) +
            (A * (w * g⁻¹ ^ 2 + 2 * v ^ 2 * g⁻¹ ^ 3)) * g⁻¹)
          ((A₁ * g⁻¹) * (v * g⁻¹ ^ 2))
          ((A * (v * g⁻¹ ^ 2)) * (v * g⁻¹ ^ 2))).symm
    _ = A₂ * g⁻¹ ^ 2 +
        2 * A₁ * v * g⁻¹ ^ 3 +
        A * w * g⁻¹ ^ 3 +
        2 * A * v ^ 2 * g⁻¹ ^ 4 +
        A₁ * v * g⁻¹ ^ 3 +
        A * v ^ 2 * g⁻¹ ^ 4 := by
      have hg2 : g⁻¹ * g⁻¹ = g⁻¹ ^ 2 := (pow_two g⁻¹).symm
      have hg3 : g⁻¹ ^ 2 * g⁻¹ = g⁻¹ ^ 3 := (pow_succ g⁻¹ 2).symm
      have hg4 : g⁻¹ ^ 3 * g⁻¹ = g⁻¹ ^ 4 := (pow_succ g⁻¹ 3).symm
      have hvSquare : v * v = v ^ 2 := (pow_two v).symm
      exact congrArg
        (fun powers : ℝ × ℝ × ℝ × ℝ =>
          A₂ * powers.1 +
            2 * A₁ * v * powers.2.1 +
            A * w * powers.2.1 +
            2 * A * v ^ 2 * powers.2.2.1 +
            A₁ * v * powers.2.1 +
            A * v ^ 2 * powers.2.2.1)
        (Prod.ext hg2 (Prod.ext hg3 (Prod.ext hg4 hvSquare)))

theorem Complex.nonstationarySecondTransformExpandedMajorant_eq_collected
    (A A₁ A₂ v w g : ℝ) :
    Complex.nonstationarySecondTransformExpandedMajorant A A₁ A₂ v w g =
      A₂ * g⁻¹ ^ 2 +
        3 * A₁ * v * g⁻¹ ^ 3 +
        A * w * g⁻¹ ^ 3 +
        3 * A * v ^ 2 * g⁻¹ ^ 4 := by
  unfold Complex.nonstationarySecondTransformExpandedMajorant
  let derivativeTerm := A₁ * v * g⁻¹ ^ 3
  let curvatureTerm := A * v ^ 2 * g⁻¹ ^ 4
  have hderivative :
      2 * A₁ * v * g⁻¹ ^ 3 + derivativeTerm =
        3 * A₁ * v * g⁻¹ ^ 3 := by
    change 2 * derivativeTerm + derivativeTerm = 3 * derivativeTerm
    exact (two_mul derivativeTerm).symm.trans
      ((add_mul 2 1 derivativeTerm).symm.trans
        (congrArg (fun coefficient : ℝ => coefficient * derivativeTerm)
          (show (2 : ℝ) + 1 = 3 from rfl)))
  have hcurvature :
      2 * A * v ^ 2 * g⁻¹ ^ 4 + curvatureTerm =
        3 * A * v ^ 2 * g⁻¹ ^ 4 := by
    change 2 * curvatureTerm + curvatureTerm = 3 * curvatureTerm
    exact (two_mul curvatureTerm).symm.trans
      ((add_mul 2 1 curvatureTerm).symm.trans
        (congrArg (fun coefficient : ℝ => coefficient * curvatureTerm)
          (show (2 : ℝ) + 1 = 3 from rfl)))
  exact
    (add_assoc
      (A₂ * g⁻¹ ^ 2 + 2 * A₁ * v * g⁻¹ ^ 3 + A * w * g⁻¹ ^ 3)
      (2 * A * v ^ 2 * g⁻¹ ^ 4)
      (derivativeTerm + curvatureTerm)).trans
      (congrArg (fun value : ℝ =>
        A₂ * g⁻¹ ^ 2 + value + A * w * g⁻¹ ^ 3 +
          3 * A * v ^ 2 * g⁻¹ ^ 4) hderivative)

theorem Complex.nonstationarySecondTransformRawMajorant_eq_canonical
    (A A₁ A₂ v w g : ℝ) :
    Complex.nonstationarySecondTransformRawMajorant A A₁ A₂ v w g =
      Complex.nonstationarySecondTransformMajorant A A₁ A₂ v w g := by
  have hexpanded :=
    Complex.nonstationarySecondTransformRawMajorant_eq_expanded
      A A₁ A₂ v w g
  have hcollected :=
    Complex.nonstationarySecondTransformExpandedMajorant_eq_collected
      A A₁ A₂ v w g
  unfold Complex.nonstationarySecondTransformMajorant
  have hdiv2 := Real.div_pow_eq_mul_inv_pow A₂ g 2
  have hdiv3a := Real.div_pow_eq_mul_inv_pow (3 * A₁ * v) g 3
  have hdiv3b := Real.div_pow_eq_mul_inv_pow (A * w) g 3
  have hdiv4 := Real.div_pow_eq_mul_inv_pow (3 * A * v ^ 2) g 4
  exact Eq.trans hexpanded
    (Eq.trans hcollected
      (congrArg₂ (fun first second : ℝ => first + second)
        (congrArg₂ (fun first second : ℝ => first + second)
          (congrArg₂ (fun first second : ℝ => first + second)
            hdiv2.symm hdiv3a.symm)
          hdiv3b.symm)
        hdiv4.symm))

theorem Complex.norm_nonstationarySecondTransform_le_canonicalMajorant
    (amplitude amplitudeDerivative amplitudeSecondDerivative : ℝ → ℂ)
    (φ' φ'' φ''' : ℝ → ℝ)
    (x : ℝ) :
    ‖Complex.nonstationarySecondTransformedAmplitude
        (Complex.nonstationaryFirstTransformedDerivativeExplicit
          amplitude amplitudeDerivative amplitudeSecondDerivative
          (Complex.realPhaseIntegrationCoefficient φ')
          (Complex.realPhaseIntegrationCoefficientDerivative φ' φ'')
          (Complex.realPhaseIntegrationCoefficientSecondDerivative
            φ' φ'' φ'''))
        amplitude amplitudeDerivative
        (Complex.realPhaseIntegrationCoefficient φ')
        (Complex.realPhaseIntegrationCoefficientDerivative φ' φ'') x‖ ≤
      Complex.nonstationarySecondTransformMajorant
        ‖amplitude x‖ ‖amplitudeDerivative x‖
        ‖amplitudeSecondDerivative x‖
        |φ'' x| |φ''' x| ‖φ' x‖ := by
  have hraw :=
    Complex.norm_nonstationarySecondTransform_le_rawMajorant
      amplitude amplitudeDerivative amplitudeSecondDerivative
      φ' φ'' φ''' x
  have harithmetic :=
    Complex.nonstationarySecondTransformRawMajorant_eq_canonical
      ‖amplitude x‖ ‖amplitudeDerivative x‖
      ‖amplitudeSecondDerivative x‖ |φ'' x| |φ''' x| ‖φ' x‖
  exact le_trans hraw (le_of_eq harithmetic)

end
end LFunctions
end Boundary
