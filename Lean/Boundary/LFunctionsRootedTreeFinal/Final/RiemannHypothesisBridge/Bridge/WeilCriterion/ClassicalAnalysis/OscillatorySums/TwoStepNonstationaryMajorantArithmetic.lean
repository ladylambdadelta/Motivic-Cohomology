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

theorem Real.two_mul_add_self_eq_three_mul
    (x : ℝ) :
    2 * x + x = 3 * x := by
  exact (congrArg (fun value : ℝ => 2 * x + value) (one_mul x).symm).trans
    ((add_mul 2 1 x).symm.trans
      (congrArg (fun coefficient : ℝ => coefficient * x)
        two_add_one_eq_three))

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
        hv2))
    (congrArg (fun value : ℝ => A * value)
      (congrArg₂ (fun first second : ℝ => first + second)
        hw2
        hvSq3))

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
      have hterm1 : (A₂ * g⁻¹) * g⁻¹ = A₂ * g⁻¹ ^ 2 :=
        (mul_assoc A₂ g⁻¹ g⁻¹).trans
          (congrArg (fun value : ℝ => A₂ * value) hg2)
      have hterm2 :
          (2 * A₁ * (v * g⁻¹ ^ 2)) * g⁻¹ =
            2 * A₁ * v * g⁻¹ ^ 3 := by
        exact (mul_assoc (2 * A₁) (v * g⁻¹ ^ 2) g⁻¹).trans
          ((congrArg (fun value : ℝ => (2 * A₁) * value)
            (mul_assoc v (g⁻¹ ^ 2) g⁻¹)).trans
            ((congrArg (fun value : ℝ => (2 * A₁) * (v * value)) hg3).trans
              (mul_assoc (2 * A₁) v (g⁻¹ ^ 3)).symm))
      have hterm3 :
          (A * (w * g⁻¹ ^ 2 + 2 * v ^ 2 * g⁻¹ ^ 3)) * g⁻¹ =
            A * w * g⁻¹ ^ 3 + 2 * A * v ^ 2 * g⁻¹ ^ 4 := by
        have hdistributed := add_mul
          (A * (w * g⁻¹ ^ 2)) (A * (2 * v ^ 2 * g⁻¹ ^ 3)) g⁻¹
        have houter := congrArg (fun value : ℝ => value * g⁻¹)
          (mul_add A (w * g⁻¹ ^ 2) (2 * v ^ 2 * g⁻¹ ^ 3))
        have hleft : (A * (w * g⁻¹ ^ 2)) * g⁻¹ = A * w * g⁻¹ ^ 3 := by
          exact (mul_assoc A (w * g⁻¹ ^ 2) g⁻¹).trans
            ((congrArg (fun value : ℝ => A * value)
              (mul_assoc w (g⁻¹ ^ 2) g⁻¹)).trans
              ((congrArg (fun value : ℝ => A * (w * value)) hg3).trans
                (mul_assoc A w (g⁻¹ ^ 3)).symm))
        have hright :
            (A * (2 * v ^ 2 * g⁻¹ ^ 3)) * g⁻¹ =
              2 * A * v ^ 2 * g⁻¹ ^ 4 := by
          have hcoefficient : A * (2 * v ^ 2) = 2 * A * v ^ 2 := by
            exact (mul_assoc A 2 (v ^ 2)).symm.trans
              (congrArg (fun value : ℝ => value * v ^ 2) (mul_comm A 2))
          exact (mul_assoc A (2 * v ^ 2 * g⁻¹ ^ 3) g⁻¹).trans
            ((congrArg (fun value : ℝ => A * value)
              (mul_assoc (2 * v ^ 2) (g⁻¹ ^ 3) g⁻¹)).trans
              ((congrArg (fun value : ℝ => A * ((2 * v ^ 2) * value)) hg4).trans
                ((mul_assoc A (2 * v ^ 2) (g⁻¹ ^ 4)).symm.trans
                  (congrArg (fun value : ℝ => value * g⁻¹ ^ 4) hcoefficient))))
        exact houter.trans
          (hdistributed.trans (congrArg₂ (fun p q : ℝ => p + q) hleft hright))
      have hterm4 :
          (A₁ * g⁻¹) * (v * g⁻¹ ^ 2) = A₁ * v * g⁻¹ ^ 3 := by
        exact (mul_assoc A₁ g⁻¹ (v * g⁻¹ ^ 2)).trans
          ((congrArg (fun value : ℝ => A₁ * value)
            ((mul_assoc g⁻¹ v (g⁻¹ ^ 2)).symm.trans
              ((congrArg (fun value : ℝ => value * g⁻¹ ^ 2) (mul_comm g⁻¹ v)).trans
                (mul_assoc v g⁻¹ (g⁻¹ ^ 2))))).trans
            ((mul_assoc A₁ v (g⁻¹ * g⁻¹ ^ 2)).symm.trans
              (congrArg (fun value : ℝ => A₁ * v * value)
                ((mul_comm g⁻¹ (g⁻¹ ^ 2)).trans hg3))))
      have hterm5 :
          (A * (v * g⁻¹ ^ 2)) * (v * g⁻¹ ^ 2) =
            A * v ^ 2 * g⁻¹ ^ 4 := by
        have hvv : v * v = v ^ 2 := (pow_two v).symm
        have hgg : g⁻¹ ^ 2 * g⁻¹ ^ 2 = g⁻¹ ^ 4 := by
          exact (congrArg (fun value : ℝ => g⁻¹ ^ 2 * value) (pow_two (g⁻¹))).trans
            ((mul_assoc (g⁻¹ ^ 2) g⁻¹ g⁻¹).symm.trans
              ((congrArg (fun value : ℝ => value * g⁻¹) hg3).trans
                (pow_succ g⁻¹ 3).symm))
        exact (mul_assoc A (v * g⁻¹ ^ 2) (v * g⁻¹ ^ 2)).trans
          ((congrArg (fun value : ℝ => A * value)
            ((mul_mul_mul_comm v (g⁻¹ ^ 2) v (g⁻¹ ^ 2)).trans
              (congrArg₂ (fun p q : ℝ => p * q) hvv hgg))).trans
            (mul_assoc A (v ^ 2) (g⁻¹ ^ 4)).symm)
      exact (congrArg
        (fun value : ℝ => value +
          (2 * A₁ * (v * g⁻¹ ^ 2)) * g⁻¹ +
          (A * (w * g⁻¹ ^ 2 + 2 * v ^ 2 * g⁻¹ ^ 3)) * g⁻¹ +
          (A₁ * g⁻¹) * (v * g⁻¹ ^ 2) +
          (A * (v * g⁻¹ ^ 2)) * (v * g⁻¹ ^ 2)) hterm1).trans
        ((congrArg
          (fun value : ℝ => A₂ * g⁻¹ ^ 2 + value +
            (A * (w * g⁻¹ ^ 2 + 2 * v ^ 2 * g⁻¹ ^ 3)) * g⁻¹ +
            (A₁ * g⁻¹) * (v * g⁻¹ ^ 2) +
            (A * (v * g⁻¹ ^ 2)) * (v * g⁻¹ ^ 2)) hterm2).trans
          ((congrArg
            (fun value : ℝ => A₂ * g⁻¹ ^ 2 + 2 * A₁ * v * g⁻¹ ^ 3 +
              value + (A₁ * g⁻¹) * (v * g⁻¹ ^ 2) +
              (A * (v * g⁻¹ ^ 2)) * (v * g⁻¹ ^ 2)) hterm3).trans
            ((congrArg
              (fun value : ℝ => A₂ * g⁻¹ ^ 2 + 2 * A₁ * v * g⁻¹ ^ 3 +
                (A * w * g⁻¹ ^ 3 + 2 * A * v ^ 2 * g⁻¹ ^ 4) + value +
                (A * (v * g⁻¹ ^ 2)) * (v * g⁻¹ ^ 2)) hterm4).trans
              ((congrArg
                (fun value : ℝ => A₂ * g⁻¹ ^ 2 + 2 * A₁ * v * g⁻¹ ^ 3 +
                  (A * w * g⁻¹ ^ 3 + 2 * A * v ^ 2 * g⁻¹ ^ 4) +
                  A₁ * v * g⁻¹ ^ 3 + value) hterm5).trans
                (congrArg
                  (fun value : ℝ => value + A₁ * v * g⁻¹ ^ 3 +
                    A * v ^ 2 * g⁻¹ ^ 4)
                  (add_assoc
                    (A₂ * g⁻¹ ^ 2 + 2 * A₁ * v * g⁻¹ ^ 3)
                    (A * w * g⁻¹ ^ 3)
                    (2 * A * v ^ 2 * g⁻¹ ^ 4)).symm)))))

theorem Complex.nonstationarySecondTransformExpandedMajorant_eq_collected
    (A A₁ A₂ v w g : ℝ) :
    Complex.nonstationarySecondTransformExpandedMajorant A A₁ A₂ v w g =
      A₂ * g⁻¹ ^ 2 +
        3 * A₁ * v * g⁻¹ ^ 3 +
        A * w * g⁻¹ ^ 3 +
        3 * A * v ^ 2 * g⁻¹ ^ 4 := by
  unfold Complex.nonstationarySecondTransformExpandedMajorant
  have hderivative :
      2 * A₁ * v * g⁻¹ ^ 3 + A₁ * v * g⁻¹ ^ 3 =
        3 * A₁ * v * g⁻¹ ^ 3 := by
    have htwo : 2 * (A₁ * v * g⁻¹ ^ 3) = 2 * A₁ * v * g⁻¹ ^ 3 :=
      (mul_assoc 2 (A₁ * v) (g⁻¹ ^ 3)).symm.trans
        (congrArg (fun value : ℝ => value * g⁻¹ ^ 3)
          (mul_assoc 2 A₁ v).symm)
    have hthree : 3 * (A₁ * v * g⁻¹ ^ 3) = 3 * A₁ * v * g⁻¹ ^ 3 :=
      (mul_assoc 3 (A₁ * v) (g⁻¹ ^ 3)).symm.trans
        (congrArg (fun value : ℝ => value * g⁻¹ ^ 3)
          (mul_assoc 3 A₁ v).symm)
    exact (congrArg (fun value : ℝ => value + A₁ * v * g⁻¹ ^ 3) htwo.symm).trans
      ((Real.two_mul_add_self_eq_three_mul (A₁ * v * g⁻¹ ^ 3)).trans hthree)
  have hcurvature :
      2 * A * v ^ 2 * g⁻¹ ^ 4 + A * v ^ 2 * g⁻¹ ^ 4 =
        3 * A * v ^ 2 * g⁻¹ ^ 4 := by
    have htwo : 2 * (A * v ^ 2 * g⁻¹ ^ 4) = 2 * A * v ^ 2 * g⁻¹ ^ 4 :=
      (mul_assoc 2 (A * v ^ 2) (g⁻¹ ^ 4)).symm.trans
        (congrArg (fun value : ℝ => value * g⁻¹ ^ 4)
          (mul_assoc 2 A (v ^ 2)).symm)
    have hthree : 3 * (A * v ^ 2 * g⁻¹ ^ 4) = 3 * A * v ^ 2 * g⁻¹ ^ 4 :=
      (mul_assoc 3 (A * v ^ 2) (g⁻¹ ^ 4)).symm.trans
        (congrArg (fun value : ℝ => value * g⁻¹ ^ 4)
          (mul_assoc 3 A (v ^ 2)).symm)
    exact (congrArg (fun value : ℝ => value + A * v ^ 2 * g⁻¹ ^ 4) htwo.symm).trans
      ((Real.two_mul_add_self_eq_three_mul (A * v ^ 2 * g⁻¹ ^ 4)).trans hthree)
  have hmoveDerivative :
      A₂ * g⁻¹ ^ 2 + 2 * A₁ * v * g⁻¹ ^ 3 + A * w * g⁻¹ ^ 3 +
          2 * A * v ^ 2 * g⁻¹ ^ 4 + A₁ * v * g⁻¹ ^ 3 + A * v ^ 2 * g⁻¹ ^ 4 =
        A₂ * g⁻¹ ^ 2 + (2 * A₁ * v * g⁻¹ ^ 3 + A₁ * v * g⁻¹ ^ 3) +
          A * w * g⁻¹ ^ 3 + (2 * A * v ^ 2 * g⁻¹ ^ 4 + A * v ^ 2 * g⁻¹ ^ 4) := by
    let p := A₂ * g⁻¹ ^ 2
    let q := 2 * A₁ * v * g⁻¹ ^ 3
    let r := A * w * g⁻¹ ^ 3
    let s := 2 * A * v ^ 2 * g⁻¹ ^ 4
    let u := A₁ * v * g⁻¹ ^ 3
    let z := A * v ^ 2 * g⁻¹ ^ 4
    change p + q + r + s + u + z = p + (q + u) + r + (s + z)
    calc
      p + q + r + s + u + z = ((p + q) + (r + s)) + (u + z) := by
        exact (congrArg (fun value : ℝ => value + u + z)
          (add_assoc (p + q) r s)).trans
          (add_assoc ((p + q) + (r + s)) u z)
      _ = ((p + q) + u) + ((r + s) + z) :=
        add_add_add_comm (p + q) (r + s) u z
      _ = p + (q + u) + (r + (s + z)) := by
        exact congrArg₂ (fun first second : ℝ => first + second)
          (add_assoc p q u) (add_assoc r s z)
      _ = p + (q + u) + r + (s + z) :=
        (add_assoc (p + (q + u)) r (s + z)).symm
  exact hmoveDerivative.trans
    ((congrArg₂ (fun p q : ℝ =>
        A₂ * g⁻¹ ^ 2 + p + A * w * g⁻¹ ^ 3 + q)
      hderivative hcurvature))

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
