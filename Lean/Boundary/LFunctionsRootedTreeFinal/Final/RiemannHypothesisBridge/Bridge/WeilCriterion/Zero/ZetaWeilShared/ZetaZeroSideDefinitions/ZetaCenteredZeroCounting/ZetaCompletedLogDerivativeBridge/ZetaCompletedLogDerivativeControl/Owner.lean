import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaAdmissibleFunction.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalizationBridge.Owner

/-!
# Boundary completed-log-derivative control

This file owns the strip-control package for the completed zeta negative
logarithmic derivative.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- Helper: Imaginary part of (1/2 + t*I) is t. -/
private lemma im_half_plus_t_i (t : ℝ) : ((1 / 2 : ℂ) + t * Complex.I).im = t := by
  have h1 : (1 / 2 : ℂ).im = 0 := by
    calc
      (1 / 2 : ℂ).im = (1 : ℂ).im / (2 : ℕ) := by
        exact Complex.div_natCast_im (1 : ℂ) 2
      _ = 0 / (2 : ℝ) := by
        exact congrArg (fun x : ℝ => x / (2 : ℝ)) Complex.one_im
      _ = 0 := by
        exact zero_div (2 : ℝ)
  have h2 : (t * Complex.I).im = t := by
    calc
      (t * Complex.I).im = (t : ℂ).re := by
        exact Complex.mul_I_im (t : ℂ)
      _ = t := by
        exact Complex.ofReal_re t
  calc ((1 / 2 : ℂ) + t * Complex.I).im
      = (1 / 2 : ℂ).im + (t * Complex.I).im := Complex.add_im _ _
    _ = 0 + t := by exact congr_arg₂ (· + ·) h1 h2
    _ = t := zero_add t

/-- The inverse-Gamma correction in the completed logarithmic derivative split. -/
noncomputable def inverseGammaCompletionLogDeriv (z : ℂ) : ℂ :=
  deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z / (Complex.Gammaℝ z)⁻¹

/-- The inverse-Gamma correction unfolds to the derivative quotient. -/
theorem inverseGammaCompletionLogDeriv_eq
    (z : ℂ) :
    inverseGammaCompletionLogDeriv z =
      deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z / (Complex.Gammaℝ z)⁻¹ :=
  rfl

/-- The logarithmic derivative of an inverse is the negative logarithmic
derivative of the original function, at a differentiability and nonvanishing
point. -/
theorem deriv_inv_div_inv_eq_neg_deriv_div
    {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℂ g z)
    (hz : g z ≠ 0) :
    deriv (fun w : ℂ => (g w)⁻¹) z / (g z)⁻¹ =
      -deriv g z / g z := by
  let a : ℂ := g z
  let d : ℂ := deriv g z
  have ha : a ≠ 0 := hz
  have hderiv :
      deriv (fun w : ℂ => (g w)⁻¹) z =
        -d / a ^ 2 := by
    exact deriv_inv'' hg hz
  have hcancel :
      (a ^ 2)⁻¹ * a = a⁻¹ := by
    have hpow : a ^ 2 = a * a :=
      pow_two a
    calc
      (a ^ 2)⁻¹ * a = (a * a)⁻¹ * a := by
        exact congrArg (fun x : ℂ => x⁻¹ * a) hpow
      _ = (a⁻¹ * a⁻¹) * a := by
        exact congrArg (fun x : ℂ => x * a) (mul_inv_rev a a)
      _ = a⁻¹ * (a⁻¹ * a) := by
        exact mul_assoc a⁻¹ a⁻¹ a
      _ = a⁻¹ * 1 := by
        exact congrArg (fun x : ℂ => a⁻¹ * x) (inv_mul_cancel₀ ha)
      _ = a⁻¹ :=
        mul_one a⁻¹
  have hquotient :
      (-d / a ^ 2) / a⁻¹ = -d / a := by
    calc
      (-d / a ^ 2) / a⁻¹ =
          (-d / a ^ 2) * (a⁻¹)⁻¹ := by
        exact div_eq_mul_inv (-d / a ^ 2) a⁻¹
      _ = (-d / a ^ 2) * a := by
        exact congrArg (fun x : ℂ => (-d / a ^ 2) * x) (inv_inv a)
      _ = (-d * (a ^ 2)⁻¹) * a := by
        exact congrArg (fun x : ℂ => x * a) (div_eq_mul_inv (-d) (a ^ 2))
      _ = -d * ((a ^ 2)⁻¹ * a) := by
        exact mul_assoc (-d) (a ^ 2)⁻¹ a
      _ = -d * a⁻¹ := by
        exact congrArg (fun x : ℂ => -d * x) hcancel
      _ = -d / a := by
        exact (div_eq_mul_inv (-d) a).symm
  calc
    deriv (fun w : ℂ => (g w)⁻¹) z / (g z)⁻¹ =
        (-d / a ^ 2) / a⁻¹ := by
      exact congrArg (fun x : ℂ => x / a⁻¹) hderiv
    _ = -d / a :=
      hquotient

/-- Deligne's `Gammaℝ` is complex-differentiable away from its nonpositive
even singular locus. -/
theorem Gammaℝ_differentiableAt_of_ne_zero_locus
    {z : ℂ}
    (hz : ∀ n : ℕ, z ≠ -(2 * (n : ℂ))) :
    DifferentiableAt ℂ Complex.Gammaℝ z := by
  have hpow :
      DifferentiableAt ℂ
        (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) z :=
    (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  have hgamma_arg :
      ∀ n : ℕ, z / 2 ≠ -(n : ℂ) := by
    intro n hzn
    have hmul :
        z / 2 * 2 = (-(n : ℂ)) * 2 :=
      congrArg (fun w : ℂ => w * 2) hzn
    have hz_eq_neg_two :
        z = -(2 * (n : ℂ)) := by
      calc
        z = z / 2 * 2 := by
          exact (div_mul_cancel₀ z (two_ne_zero : (2 : ℂ) ≠ 0)).symm
        _ = (-(n : ℂ)) * 2 :=
          hmul
        _ = -((n : ℂ) * 2) :=
          neg_mul (n : ℂ) 2
        _ = -(2 * (n : ℂ)) := by
          exact congrArg Neg.neg (mul_comm (n : ℂ) 2)
    exact hz n hz_eq_neg_two
  have hgamma :
      DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s / 2)) z :=
    (Complex.differentiableAt_Gamma (z / 2) hgamma_arg).comp
      z
      (differentiableAt_id.div_const (2 : ℂ))
  have hprod :
      DifferentiableAt ℂ
        (fun s : ℂ =>
          (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)) z :=
    hpow.mul hgamma
  have hfun :
      (fun s : ℂ =>
          (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)) =
        Complex.Gammaℝ := by
    funext s
    exact (Complex.Gammaℝ_def s).symm
  exact
    Eq.subst
      (motive := fun φ : ℂ → ℂ => DifferentiableAt ℂ φ z)
      hfun
      hprod

/-- Derivative of the elementary `π ^ (-s/2)` factor in Deligne's
`Gammaℝ`. -/
theorem Gammaℝ_piFactor_hasDerivAt
    (z : ℂ) :
    HasDerivAt
      (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2))
      ((Real.pi : ℂ) ^ (-z / 2) *
        Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)))
      z := by
  have hlinear :
      HasDerivAt (fun s : ℂ => -s / 2) (-(1 / 2 : ℂ)) z := by
    have hid : HasDerivAt (fun s : ℂ => s) 1 z :=
      hasDerivAt_id z
    have hneg : HasDerivAt (fun s : ℂ => -s) (-1) z :=
      hid.neg
    have hdiv : HasDerivAt (fun s : ℂ => -s / 2) ((-1 : ℂ) / 2) z :=
      hneg.div_const (2 : ℂ)
    have hderiv : ((-1 : ℂ) / 2) = -(1 / 2 : ℂ) := by
      exact (neg_div' (2 : ℂ) (1 : ℂ)).symm
    exact
      Eq.subst
        (motive := fun d : ℂ => HasDerivAt (fun s : ℂ => -s / 2) d z)
        hderiv
        hdiv
  exact
    hlinear.const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))

/-- Derivative of the half-argument ordinary Gamma factor in Deligne's
`Gammaℝ`. -/
theorem Gammaℝ_halfGammaFactor_hasDerivAt
    {z : ℂ}
    (hz : ∀ n : ℕ, z / 2 ≠ -(n : ℂ)) :
    HasDerivAt
      (fun s : ℂ => Complex.Gamma (s / 2))
      (deriv Complex.Gamma (z / 2) * (1 / 2 : ℂ))
      z := by
  have houter :
      HasDerivAt Complex.Gamma (deriv Complex.Gamma (z / 2)) (z / 2) :=
    (Complex.differentiableAt_Gamma (z / 2) hz).hasDerivAt
  have hinner :
      HasDerivAt (fun s : ℂ => s / 2) (1 / 2 : ℂ) z :=
    (hasDerivAt_id z).div_const (2 : ℂ)
  exact houter.comp z hinner

/-- Exact derivative formula for Deligne's `Gammaℝ` away from its
nonpositive-even singular locus. -/
theorem Gammaℝ_hasDerivAt_of_ne_zero_locus
    {z : ℂ}
    (hz : ∀ n : ℕ, z ≠ -(2 * (n : ℂ))) :
    HasDerivAt Complex.Gammaℝ
      (((Real.pi : ℂ) ^ (-z / 2) * Complex.log (Real.pi : ℂ) *
          (-(1 / 2 : ℂ))) *
          Complex.Gamma (z / 2) +
        (Real.pi : ℂ) ^ (-z / 2) *
          (deriv Complex.Gamma (z / 2) * (1 / 2 : ℂ)))
      z := by
  have hgamma_arg :
      ∀ n : ℕ, z / 2 ≠ -(n : ℂ) := by
    intro n hzn
    have hmul :
        z / 2 * 2 = (-(n : ℂ)) * 2 :=
      congrArg (fun w : ℂ => w * 2) hzn
    have hz_eq_neg_two :
        z = -(2 * (n : ℂ)) := by
      calc
        z = z / 2 * 2 := by
          exact (div_mul_cancel₀ z (two_ne_zero : (2 : ℂ) ≠ 0)).symm
        _ = (-(n : ℂ)) * 2 :=
          hmul
        _ = -((n : ℂ) * 2) :=
          neg_mul (n : ℂ) 2
        _ = -(2 * (n : ℂ)) := by
          exact congrArg Neg.neg (mul_comm (n : ℂ) 2)
    exact hz n hz_eq_neg_two
  have hpi :
      HasDerivAt
        (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2))
        ((Real.pi : ℂ) ^ (-z / 2) *
          Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)))
        z :=
    Gammaℝ_piFactor_hasDerivAt z
  have hgamma :
      HasDerivAt
        (fun s : ℂ => Complex.Gamma (s / 2))
        (deriv Complex.Gamma (z / 2) * (1 / 2 : ℂ))
        z :=
    Gammaℝ_halfGammaFactor_hasDerivAt hgamma_arg
  have hprod :
      HasDerivAt
        (fun s : ℂ =>
          (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2))
        (((Real.pi : ℂ) ^ (-z / 2) * Complex.log (Real.pi : ℂ) *
            (-(1 / 2 : ℂ))) *
            Complex.Gamma (z / 2) +
          (Real.pi : ℂ) ^ (-z / 2) *
            (deriv Complex.Gamma (z / 2) * (1 / 2 : ℂ)))
        z :=
    hpi.mul hgamma
  have hfun :
      (fun s : ℂ =>
          (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)) =
        Complex.Gammaℝ := by
    funext s
    exact (Complex.Gammaℝ_def s).symm
  exact
    Eq.subst
      (motive := fun φ : ℂ → ℂ =>
        HasDerivAt φ
          (((Real.pi : ℂ) ^ (-z / 2) * Complex.log (Real.pi : ℂ) *
              (-(1 / 2 : ℂ))) *
              Complex.Gamma (z / 2) +
            (Real.pi : ℂ) ^ (-z / 2) *
              (deriv Complex.Gamma (z / 2) * (1 / 2 : ℂ)))
          z)
      hfun
      hprod

/-- Quotient algebra for the logarithmic derivative of a product. -/
theorem mul_logDeriv_algebra
    {p p' g g' : ℂ}
    (hp : p ≠ 0)
    (hg : g ≠ 0) :
    (p' * g + p * g') / (p * g) = p' / p + g' / g := by
  have hpg : p * g ≠ 0 :=
    mul_ne_zero hp hg
  have hsplit :
      (p' * g + p * g') / (p * g) =
        (p' * g) / (p * g) + (p * g') / (p * g) := by
    exact add_div (p' * g) (p * g') (p * g)
  have hleft :
      (p' * g) / (p * g) = p' / p := by
    calc
      (p' * g) / (p * g) =
          (p' * g) * (p * g)⁻¹ := by
        exact div_eq_mul_inv (p' * g) (p * g)
      _ = (p' * g) * (g⁻¹ * p⁻¹) := by
        exact
          congrArg (fun x : ℂ => (p' * g) * x)
            (by
              calc
                (p * g)⁻¹ = g⁻¹ * p⁻¹ :=
                  mul_inv_rev p g
                _ = g⁻¹ * p⁻¹ :=
                  rfl)
      _ = p' * (g * (g⁻¹ * p⁻¹)) := by
        exact mul_assoc p' g (g⁻¹ * p⁻¹)
      _ = p' * ((g * g⁻¹) * p⁻¹) := by
        exact congrArg (fun x : ℂ => p' * x) (mul_assoc g g⁻¹ p⁻¹).symm
      _ = p' * (1 * p⁻¹) := by
        exact congrArg (fun x : ℂ => p' * (x * p⁻¹)) (mul_inv_cancel₀ hg)
      _ = p' * p⁻¹ := by
        exact congrArg (fun x : ℂ => p' * x) (one_mul p⁻¹)
      _ = p' / p := by
        exact (div_eq_mul_inv p' p).symm
  have hright :
      (p * g') / (p * g) = g' / g := by
    calc
      (p * g') / (p * g) =
          (p * g') * (p * g)⁻¹ := by
        exact div_eq_mul_inv (p * g') (p * g)
      _ = (p * g') * (g⁻¹ * p⁻¹) := by
        exact congrArg (fun x : ℂ => (p * g') * x) (mul_inv_rev p g)
      _ = p * (g' * (g⁻¹ * p⁻¹)) := by
        exact mul_assoc p g' (g⁻¹ * p⁻¹)
      _ = p * ((g' * g⁻¹) * p⁻¹) := by
        exact congrArg (fun x : ℂ => p * x) (mul_assoc g' g⁻¹ p⁻¹).symm
      _ = (p * (g' * g⁻¹)) * p⁻¹ := by
        exact (mul_assoc p (g' * g⁻¹) p⁻¹).symm
      _ = (g' * g⁻¹ * p) * p⁻¹ := by
        exact congrArg (fun x : ℂ => x * p⁻¹) (mul_comm p (g' * g⁻¹))
      _ = g' * g⁻¹ * (p * p⁻¹) := by
        exact mul_assoc (g' * g⁻¹) p p⁻¹
      _ = g' * g⁻¹ * 1 := by
        exact congrArg (fun x : ℂ => g' * g⁻¹ * x) (mul_inv_cancel₀ hp)
      _ = g' * g⁻¹ := by
        exact mul_one (g' * g⁻¹)
      _ = g' / g := by
        exact (div_eq_mul_inv g' g).symm
  calc
    (p' * g + p * g') / (p * g) =
        (p' * g) / (p * g) + (p * g') / (p * g) :=
      hsplit
    _ = p' / p + g' / g := by
      exact congrArg₂ HAdd.hAdd hleft hright

/-- The elementary `π ^ (-s/2)` factor has logarithmic derivative
`-log π / 2`. -/
theorem Gammaℝ_piFactor_logDeriv_eq
    (z : ℂ) :
    ((Real.pi : ℂ) ^ (-z / 2) *
        Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ))) /
      ((Real.pi : ℂ) ^ (-z / 2)) =
        Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)) := by
  let p : ℂ := (Real.pi : ℂ) ^ (-z / 2)
  let q : ℂ := Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ))
  have hp : p ≠ 0 := by
    intro hp_zero
    have hbase : (Real.pi : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hbase_zero : (Real.pi : ℂ) = 0 :=
      (Complex.cpow_eq_zero_iff (Real.pi : ℂ) (-z / 2)).mp hp_zero |>.1
    exact hbase hbase_zero
  calc
    ((Real.pi : ℂ) ^ (-z / 2) *
        Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ))) /
      ((Real.pi : ℂ) ^ (-z / 2)) =
        (p * q) / p := by
      exact congrArg
        (fun x : ℂ => x / ((Real.pi : ℂ) ^ (-z / 2)))
        (mul_assoc ((Real.pi : ℂ) ^ (-z / 2))
          (Complex.log (Real.pi : ℂ)) (-(1 / 2 : ℂ)))
    _ = (p * q) * p⁻¹ := by
      exact div_eq_mul_inv (p * q) p
    _ = q * p * p⁻¹ := by
      exact congrArg (fun x : ℂ => x * p⁻¹) (mul_comm p q)
    _ = q * (p * p⁻¹) := by
      exact mul_assoc q p p⁻¹
    _ = q * 1 := by
      exact congrArg (fun x : ℂ => q * x) (mul_inv_cancel₀ hp)
    _ = q :=
      mul_one q

/-- Exact logarithmic derivative decomposition for Deligne's `Gammaℝ`. -/
theorem Gammaℝ_logDeriv_eq_pi_add_halfGamma_logDeriv
    {z : ℂ}
    (hz : ∀ n : ℕ, z ≠ -(2 * (n : ℂ)))
    (hΓ : Complex.Gammaℝ z ≠ 0) :
    deriv Complex.Gammaℝ z / Complex.Gammaℝ z =
      Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)) +
        (deriv Complex.Gamma (z / 2) * (1 / 2 : ℂ)) /
          Complex.Gamma (z / 2) := by
  let p : ℂ := (Real.pi : ℂ) ^ (-z / 2)
  let p' : ℂ := p * Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ))
  let g : ℂ := Complex.Gamma (z / 2)
  let g' : ℂ := deriv Complex.Gamma (z / 2) * (1 / 2 : ℂ)
  have hp : p ≠ 0 := by
    intro hp_zero
    have hbase : (Real.pi : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have hbase_zero : (Real.pi : ℂ) = 0 :=
      (Complex.cpow_eq_zero_iff (Real.pi : ℂ) (-z / 2)).mp hp_zero |>.1
    exact hbase hbase_zero
  have hΓ_def :
      Complex.Gammaℝ z = p * g := by
    exact Complex.Gammaℝ_def z
  have hg : g ≠ 0 := by
    intro hg_zero
    have hprod_zero : p * g = 0 :=
      mul_eq_zero_of_right p hg_zero
    exact hΓ (hΓ_def.trans hprod_zero)
  have hderiv :
      deriv Complex.Gammaℝ z = p' * g + p * g' :=
    (Gammaℝ_hasDerivAt_of_ne_zero_locus hz).deriv
  have hquot :
      deriv Complex.Gammaℝ z / Complex.Gammaℝ z =
        (p' * g + p * g') / (p * g) := by
    calc
      deriv Complex.Gammaℝ z / Complex.Gammaℝ z =
          (p' * g + p * g') / Complex.Gammaℝ z := by
        exact congrArg (fun x : ℂ => x / Complex.Gammaℝ z) hderiv
      _ = (p' * g + p * g') / (p * g) := by
        exact congrArg (fun x : ℂ => (p' * g + p * g') / x) hΓ_def
  have hproduct :
      (p' * g + p * g') / (p * g) = p' / p + g' / g :=
    mul_logDeriv_algebra hp hg
  have hpi :
      p' / p = Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)) := by
    exact Gammaℝ_piFactor_logDeriv_eq z
  calc
    deriv Complex.Gammaℝ z / Complex.Gammaℝ z =
        (p' * g + p * g') / (p * g) :=
      hquot
    _ = p' / p + g' / g :=
      hproduct
    _ =
        Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)) +
          (deriv Complex.Gamma (z / 2) * (1 / 2 : ℂ)) /
            Complex.Gamma (z / 2) := by
      exact congrArg₂ HAdd.hAdd hpi rfl

/-- Conditional bridge from the inverse-`Gammaℝ` normalization used in the
completed-zeta split to the ordinary `Gammaℝ` logarithmic derivative. -/
theorem inverseGammaCompletionLogDeriv_eq_neg_Gammaℝ_logDeriv
    {z : ℂ}
    (hΓdiff : DifferentiableAt ℂ Complex.Gammaℝ z)
    (hΓ : Complex.Gammaℝ z ≠ 0) :
    inverseGammaCompletionLogDeriv z =
      -deriv Complex.Gammaℝ z / Complex.Gammaℝ z := by
  calc
    inverseGammaCompletionLogDeriv z =
        deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
          (Complex.Gammaℝ z)⁻¹ :=
      inverseGammaCompletionLogDeriv_eq z
    _ = -deriv Complex.Gammaℝ z / Complex.Gammaℝ z :=
      deriv_inv_div_inv_eq_neg_deriv_div hΓdiff hΓ

/-- The negative logarithmic derivative of the ordinary Riemann zeta factor. -/
noncomputable def riemannZetaNegLogDeriv (z : ℂ) : ℂ :=
  - deriv riemannZeta z / riemannZeta z

/-- The ordinary Riemann-zeta negative logarithmic derivative unfolds to the derivative
quotient. -/
theorem riemannZetaNegLogDeriv_eq
    (z : ℂ) :
    riemannZetaNegLogDeriv z =
      - deriv riemannZeta z / riemannZeta z :=
  rfl

/-- A zero-excised vertical strip carrier for the completed zeta logarithmic derivative.

This is geometric data only: it records the vertical strip and singular-locus exclusions.
Polynomial logarithmic-derivative bounds are owned by `CompletedZetaNegLogDerivControl`,
so scheduled carriers can be constructed from avoidance without circular analytic fields. -/
structure CompletedZetaZeroExcisedStrip (a b : ℝ) where
  carrier : Set ℂ
  in_strip : ∀ z : ℂ, z ∈ carrier → a ≤ z.re ∧ z.re ≤ b
  ne_zero : ∀ z : ℂ, z ∈ carrier → z ≠ 0
  ne_one : ∀ z : ℂ, z ∈ carrier → z ≠ 1
  zeta_ne_zero : ∀ z : ℂ, z ∈ carrier → completedRiemannZeta z ≠ 0
  gamma_ne_zero : ∀ z : ℂ, z ∈ carrier → Complex.Gammaℝ z ≠ 0

/-- A singleton carrier has a polynomial bound for any fixed complex-valued function. -/
theorem singleton_polynomial_bound
    (g : ℂ → ℂ) (z₀ : ℂ) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ ({z₀} : Set ℂ) →
        ‖g z‖ ≤ C * (1 + ‖z.im‖) ^ N := by
  let C : ℝ := ‖g z₀‖ + 1
  have hCpos : 0 < C :=
    add_pos_of_nonneg_of_pos (norm_nonneg (g z₀)) zero_lt_one
  refine ⟨C, hCpos, ?_⟩
  intro z hz
  have hzz₀ : z = z₀ :=
    Set.eq_of_mem_singleton hz
  have hnorm_eq : ‖g z‖ = ‖g z₀‖ :=
    congrArg (fun w : ℂ => ‖g w‖) hzz₀
  have hnorm_le_C_at_z₀ : ‖g z₀‖ ≤ C :=
    le_add_of_nonneg_right zero_le_one
  have hnorm_le_C : ‖g z‖ ≤ C :=
    Eq.subst
      (motive := fun y : ℝ => y ≤ C)
      hnorm_eq.symm
      hnorm_le_C_at_z₀
  have hbase : 1 ≤ 1 + ‖z.im‖ :=
    le_add_of_nonneg_right (norm_nonneg z.im)
  have hpow : 1 ≤ (1 + ‖z.im‖) ^ N :=
    one_le_pow₀ hbase
  have hCnonneg : 0 ≤ C :=
    le_of_lt hCpos
  exact hnorm_le_C.trans
    (le_mul_of_one_le_right hCnonneg hpow)

/-- The singleton zero-excised strip at a point satisfying the zero-excision predicates. -/
def CompletedZetaZeroExcisedStrip.singleton
    {a b : ℝ}
    (z₀ : ℂ)
    (hz₀_strip : a ≤ z₀.re ∧ z₀.re ≤ b)
    (hz₀_zero : z₀ ≠ 0)
    (hz₀_one : z₀ ≠ 1)
    (hz₀_zeta : completedRiemannZeta z₀ ≠ 0)
    (hz₀_gamma : Complex.Gammaℝ z₀ ≠ 0) :
    CompletedZetaZeroExcisedStrip a b :=
  { carrier := {z₀}
    in_strip :=
      fun _z hz =>
        Eq.subst
          (motive := fun w : ℂ => a ≤ w.re ∧ w.re ≤ b)
          (Set.eq_of_mem_singleton hz).symm
          hz₀_strip
    ne_zero :=
      fun _z hz =>
        Eq.subst
          (motive := fun w : ℂ => w ≠ 0)
          (Set.eq_of_mem_singleton hz).symm
          hz₀_zero
    ne_one :=
      fun _z hz =>
        Eq.subst
          (motive := fun w : ℂ => w ≠ 1)
          (Set.eq_of_mem_singleton hz).symm
          hz₀_one
    zeta_ne_zero :=
      fun _z hz =>
        Eq.subst
          (motive := fun w : ℂ => completedRiemannZeta w ≠ 0)
          (Set.eq_of_mem_singleton hz).symm
          hz₀_zeta
    gamma_ne_zero :=
      fun _z hz =>
        Eq.subst
          (motive := fun w : ℂ => Complex.Gammaℝ w ≠ 0)
          (Set.eq_of_mem_singleton hz).symm
          hz₀_gamma }

/-- The point of a singleton zero-excised strip belongs to its carrier. -/
theorem CompletedZetaZeroExcisedStrip.mem_singleton
    {a b : ℝ}
    (z₀ : ℂ)
    (hz₀_strip : a ≤ z₀.re ∧ z₀.re ≤ b)
    (hz₀_zero : z₀ ≠ 0)
    (hz₀_one : z₀ ≠ 1)
    (hz₀_zeta : completedRiemannZeta z₀ ≠ 0)
    (hz₀_gamma : Complex.Gammaℝ z₀ ≠ 0) :
    z₀ ∈
      (CompletedZetaZeroExcisedStrip.singleton
        z₀ hz₀_strip hz₀_zero hz₀_one hz₀_zeta hz₀_gamma).carrier :=
  Set.mem_singleton z₀

/-- The empty carrier is a zero-excised strip with vacuous polynomial bounds. -/
def CompletedZetaZeroExcisedStrip.empty
    (a b : ℝ) :
    CompletedZetaZeroExcisedStrip a b :=
  { carrier := ∅
    in_strip :=
      fun z hz =>
        False.elim (Set.not_mem_empty z hz)
    ne_zero :=
      fun z hz =>
        False.elim (Set.not_mem_empty z hz)
    ne_one :=
      fun z hz =>
        False.elim (Set.not_mem_empty z hz)
    zeta_ne_zero :=
      fun z hz =>
        False.elim (Set.not_mem_empty z hz)
    gamma_ne_zero :=
      fun z hz =>
        False.elim (Set.not_mem_empty z hz) }

/-- The union of two zero-excised strips over the same vertical strip is again a
zero-excised strip. -/
def CompletedZetaZeroExcisedStrip.union
    {a b : ℝ}
    (E₁ E₂ : CompletedZetaZeroExcisedStrip a b) :
    CompletedZetaZeroExcisedStrip a b :=
  { carrier := E₁.carrier ∪ E₂.carrier
    in_strip :=
      fun z hz =>
        match (Set.mem_union z E₁.carrier E₂.carrier).mp hz with
        | Or.inl hz₁ => E₁.in_strip z hz₁
        | Or.inr hz₂ => E₂.in_strip z hz₂
    ne_zero :=
      fun z hz =>
        match (Set.mem_union z E₁.carrier E₂.carrier).mp hz with
        | Or.inl hz₁ => E₁.ne_zero z hz₁
        | Or.inr hz₂ => E₂.ne_zero z hz₂
    ne_one :=
      fun z hz =>
        match (Set.mem_union z E₁.carrier E₂.carrier).mp hz with
        | Or.inl hz₁ => E₁.ne_one z hz₁
        | Or.inr hz₂ => E₂.ne_one z hz₂
    zeta_ne_zero :=
      fun z hz =>
        match (Set.mem_union z E₁.carrier E₂.carrier).mp hz with
        | Or.inl hz₁ => E₁.zeta_ne_zero z hz₁
        | Or.inr hz₂ => E₂.zeta_ne_zero z hz₂
    gamma_ne_zero :=
      fun z hz =>
        match (Set.mem_union z E₁.carrier E₂.carrier).mp hz with
        | Or.inl hz₁ => E₁.gamma_ne_zero z hz₁
        | Or.inr hz₂ => E₂.gamma_ne_zero z hz₂ }

/-- The left component of a zero-excised strip union is contained in the union carrier. -/
theorem CompletedZetaZeroExcisedStrip.mem_union_left
    {a b : ℝ}
    (E₁ E₂ : CompletedZetaZeroExcisedStrip a b)
    {z : ℂ} (hz : z ∈ E₁.carrier) :
    z ∈ (CompletedZetaZeroExcisedStrip.union E₁ E₂).carrier :=
  Set.mem_union_left E₂.carrier hz

/-- The right component of a zero-excised strip union is contained in the union carrier. -/
theorem CompletedZetaZeroExcisedStrip.mem_union_right
    {a b : ℝ}
    (E₁ E₂ : CompletedZetaZeroExcisedStrip a b)
    {z : ℂ} (hz : z ∈ E₂.carrier) :
    z ∈ (CompletedZetaZeroExcisedStrip.union E₁ E₂).carrier :=
  Set.mem_union_right E₁.carrier hz

/-- Pointwise compatibility between the completed zeta-side factor and the ordinary
Riemann-zeta logarithmic derivative. -/
theorem zetaSideNegLogDeriv_eq_riemannZetaNegLogDeriv
    {z : ℂ}
    (hz0 : z ≠ 0)
    (_hΛ : completedRiemannZeta z ≠ 0)
    (hΓ : Complex.Gammaℝ z ≠ 0) :
    zetaSideNegLogDeriv z = riemannZetaNegLogDeriv z := by
  have hderiv :
      deriv zetaSideFactor z = deriv riemannZeta z :=
    deriv_zetaSideFactor_eq_deriv_riemannZeta hz0 hΓ
  have hfactor :
      zetaSideFactor z = riemannZeta z :=
    zetaSideFactor_eq_riemannZeta hz0 hΓ
  unfold zetaSideNegLogDeriv
  calc
    - deriv zetaSideFactor z / zetaSideFactor z =
        - deriv riemannZeta z / zetaSideFactor z := by
      exact congrArg (fun x : ℂ => -x / zetaSideFactor z) hderiv
    _ = - deriv riemannZeta z / riemannZeta z := by
      exact congrArg (fun x : ℂ => - deriv riemannZeta z / x) hfactor
    _ = riemannZetaNegLogDeriv z := by
      exact (riemannZetaNegLogDeriv_eq z).symm

/-- On a zero-excised completed strip, the finite zeta-side logarithmic derivative is the
ordinary Riemann-zeta logarithmic derivative. -/
theorem zetaSideNegLogDeriv_eq_riemannZetaNegLogDeriv_of_mem_zeroExcisedStrip
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b)
    (z : ℂ) (hz : z ∈ E.carrier) :
    zetaSideNegLogDeriv z = riemannZetaNegLogDeriv z := by
  exact zetaSideNegLogDeriv_eq_riemannZetaNegLogDeriv
    (E.ne_zero z hz)
    (E.zeta_ne_zero z hz)
    (E.gamma_ne_zero z hz)

/-- The completed negative log-derivative is bounded by the zeta-side and archimedean
completion logarithmic derivative bounds on vertical strips. -/
theorem completedZetaNegLogDeriv_polynomialStripBound_of_zetaSide_and_gamma
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ)
    (hzeta :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          z ∈ E.carrier →
          ‖zetaSideNegLogDeriv z‖
            ≤ C * (1 + ‖z.im‖) ^ N)
    (hgamma :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          z ∈ E.carrier →
          ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z / (Complex.Gammaℝ z)⁻¹‖
            ≤ C * (1 + ‖z.im‖) ^ N) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ E.carrier →
        ‖completedZetaNegLogDeriv z‖
          ≤ C * (1 + ‖z.im‖) ^ N := by
  rcases hzeta with ⟨Czeta, hCzeta_pos, hCzeta_bound⟩
  rcases hgamma with ⟨Cgamma, hCgamma_pos, hCgamma_bound⟩
  refine ⟨Czeta + Cgamma, add_pos hCzeta_pos hCgamma_pos, ?_⟩
  intro z hz
  let correction :=
    inverseGammaCompletionLogDeriv z
  have hsplit :
      completedZetaNegLogDeriv z =
        zetaSideNegLogDeriv z + correction := by
    have hcorrection :
        correction =
          deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z / (Complex.Gammaℝ z)⁻¹ :=
      inverseGammaCompletionLogDeriv_eq z
    have hside :
        zetaSideNegLogDeriv z =
          completedZetaNegLogDeriv z - correction := by
      exact Eq.subst
        (motive := fun w : ℂ =>
          zetaSideNegLogDeriv z = completedZetaNegLogDeriv z - w)
        hcorrection.symm
        (zetaSideNegLogDeriv_eq_completed_sub_invGamma_correction
          (E.ne_zero z hz) (E.ne_one z hz)
          (E.zeta_ne_zero z hz) (E.gamma_ne_zero z hz))
    exact (eq_sub_iff_add_eq.mp hside).symm
  have hnorm_split :
      ‖completedZetaNegLogDeriv z‖ ≤
        ‖zetaSideNegLogDeriv z‖ + ‖correction‖ := by
    exact Eq.subst
      (motive := fun w : ℂ =>
        ‖w‖ ≤ ‖zetaSideNegLogDeriv z‖ + ‖correction‖)
      hsplit.symm
      (norm_add_le (zetaSideNegLogDeriv z) correction)
  have hbounds :
      ‖zetaSideNegLogDeriv z‖ + ‖correction‖ ≤
        Czeta * (1 + ‖z.im‖) ^ N +
          Cgamma * (1 + ‖z.im‖) ^ N := by
    have hcorrection :
        correction =
          deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z / (Complex.Gammaℝ z)⁻¹ :=
      inverseGammaCompletionLogDeriv_eq z
    have hgamma_bound_correction :
        ‖correction‖ ≤ Cgamma * (1 + ‖z.im‖) ^ N :=
      Eq.subst
        (motive := fun w : ℂ =>
          ‖w‖ ≤ Cgamma * (1 + ‖z.im‖) ^ N)
        hcorrection.symm
        (hCgamma_bound z hz)
    exact add_le_add (hCzeta_bound z hz) hgamma_bound_correction
  have hfactor :
      Czeta * (1 + ‖z.im‖) ^ N + Cgamma * (1 + ‖z.im‖) ^ N =
        (Czeta + Cgamma) * (1 + ‖z.im‖) ^ N := by
    exact (add_mul Czeta Cgamma ((1 + ‖z.im‖) ^ N)).symm
  exact hnorm_split.trans (hbounds.trans_eq hfactor)

/-- Strip control data for the completed zeta negative logarithmic derivative. -/
structure CompletedZetaNegLogDerivControl (f : ZetaAdmissibleFunction) where
  /-- Fixed-degree polynomial growth for the completed negative log derivative on a
  zero-excised strip.  This is the stable growth API used by rapid-decay products. -/
  zero_excised_polynomial_growth :
    ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b),
      ∃ K : ℕ,
        ∃ C : ℝ,
          0 < C ∧
          ∀ z : ℂ,
            z ∈ E.carrier →
            ‖completedZetaNegLogDeriv z‖
              ≤ C * (1 + ‖z.im‖) ^ K
  /-- Polynomial growth for the completed negative log derivative on a zero-excised strip. -/
  zero_excised_polynomial_strip_bound :
    ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ),
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
            z ∈ E.carrier →
            ‖completedZetaNegLogDeriv z‖
              ≤ C * (1 + ‖z.im‖) ^ N
  /-- A concrete polynomial-growth constant for each zero-excised strip and degree. -/
  zero_excised_polynomial_strip_bound_constant :
    ∀ (a b : ℝ), CompletedZetaZeroExcisedStrip a b → ℕ → ℝ
  /-- The concrete zero-excised strip-bound constant is positive. -/
  zero_excised_polynomial_strip_bound_constant_pos :
    ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ),
      0 < zero_excised_polynomial_strip_bound_constant a b E N
  /-- The concrete zero-excised strip-bound constant bounds the completed negative
  logarithmic derivative on the excised carrier. -/
  zero_excised_polynomial_strip_bound_constant_bound :
    ∀ (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ)
      (z : ℂ),
      z ∈ E.carrier →
      ‖completedZetaNegLogDeriv z‖ ≤
        zero_excised_polynomial_strip_bound_constant a b E N *
          (1 + ‖z.im‖) ^ N

/-- The strip-control package exposes fixed-degree zero-excised polynomial growth. -/
theorem CompletedZetaNegLogDerivControl.zeroExcisedPolynomialGrowth
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f)
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) :
    ∃ K : ℕ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          z ∈ E.carrier →
          ‖completedZetaNegLogDeriv z‖
            ≤ C * (1 + ‖z.im‖) ^ K := by
  exact h.zero_excised_polynomial_growth a b E

/-- The strip-control package exposes zero-excised polynomial pointwise growth. -/
theorem CompletedZetaNegLogDerivControl.zeroExcisedStripBound
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f)
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ E.carrier →
        ‖completedZetaNegLogDeriv z‖
          ≤ C * (1 + ‖z.im‖) ^ N := by
  exact h.zero_excised_polynomial_strip_bound a b E N

/-- The recorded zero-excised strip-bound constant. -/
def CompletedZetaNegLogDerivControl.zeroExcisedStripBoundConstant
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f)
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) : ℝ :=
  h.zero_excised_polynomial_strip_bound_constant a b E N

/-- The recorded zero-excised strip-bound constant is positive. -/
theorem CompletedZetaNegLogDerivControl.zeroExcisedStripBoundConstant_pos
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f)
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ) :
    0 < h.zeroExcisedStripBoundConstant a b E N :=
  h.zero_excised_polynomial_strip_bound_constant_pos a b E N

/-- The recorded zero-excised strip-bound constant bounds the completed negative
logarithmic derivative on the excised carrier. -/
theorem CompletedZetaNegLogDerivControl.zeroExcisedStripBoundConstant_bound
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f)
    (a b : ℝ) (E : CompletedZetaZeroExcisedStrip a b) (N : ℕ)
    (z : ℂ) (hz : z ∈ E.carrier) :
    ‖completedZetaNegLogDeriv z‖ ≤
      h.zeroExcisedStripBoundConstant a b E N * (1 + ‖z.im‖) ^ N :=
  h.zero_excised_polynomial_strip_bound_constant_bound a b E N z hz

/-- The completed negative log-derivative control is the owner-level strip package. -/
def CompletedZetaNegLogDerivControlPackage (f : ZetaAdmissibleFunction) : Type :=
  CompletedZetaNegLogDerivControl f

/-- The package is exactly the strip-control data. -/
def CompletedZetaNegLogDerivControlPackage_eq
    (f : ZetaAdmissibleFunction) :
    CompletedZetaNegLogDerivControlPackage f = CompletedZetaNegLogDerivControl f := by
  rfl

/-- A critical-line specialization of the zero-excised polynomial strip bound. -/
theorem CompletedZetaNegLogDerivControl.criticalLineBound_of_mem
    {f : ZetaAdmissibleFunction} (h : CompletedZetaNegLogDerivControl f)
    (E : CompletedZetaZeroExcisedStrip (1 / 2 : ℝ) (1 / 2 : ℝ)) (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ t : ℝ,
        ((1 / 2 : ℂ) + t * Complex.I) ∈ E.carrier →
        ‖completedZetaNegLogDeriv ((1 / 2 : ℂ) + t * Complex.I)‖
          ≤ C * (1 + ‖t‖) ^ N := by
  rcases h.zeroExcisedStripBound (1 / 2 : ℝ) (1 / 2 : ℝ) E N with
    ⟨C, hC, hbound⟩
  refine ⟨C, hC, ?_⟩
  intro t ht
  have him : ((1 / 2 : ℂ) + t * Complex.I).im = t :=
    im_half_plus_t_i t
  have hbound' :=
    hbound ((1 / 2 : ℂ) + t * Complex.I) ht
  have hRHS :
      C * (1 + ‖((1 / 2 : ℂ) + t * Complex.I).im‖) ^ N =
        C * (1 + ‖t‖) ^ N := by
    exact congrArg (fun u : ℝ => C * (1 + ‖u‖) ^ N) him
  exact hbound'.trans (le_of_eq hRHS)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
