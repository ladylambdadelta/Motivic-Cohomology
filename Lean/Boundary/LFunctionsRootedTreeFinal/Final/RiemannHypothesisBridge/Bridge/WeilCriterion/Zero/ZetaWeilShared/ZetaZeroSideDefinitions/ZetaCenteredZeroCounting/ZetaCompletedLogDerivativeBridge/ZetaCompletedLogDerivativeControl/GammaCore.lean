import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaAdmissibleFunction.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalizationBridge.Owner

/-!
# Gamma core for completed-log-derivative control

This file owns the elementary inverse-Gamma correction and Deligne-Gamma
derivative lemmas used by the completed log-derivative control owner.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

theorem one_div_two_im_eq_zero :
    (1 / 2 : ℂ).im = 0 :=
  let hdiv : (1 / 2 : ℂ).im = (1 : ℂ).im / (2 : ℕ) :=
    Complex.div_natCast_im (1 : ℂ) 2
  let hone : (1 : ℂ).im / (2 : ℕ) = 0 / (2 : ℝ) :=
    congrArg (fun x : ℝ => x / (2 : ℝ)) Complex.one_im
  let hzero : 0 / (2 : ℝ) = 0 :=
    zero_div (2 : ℝ)
  Eq.trans hdiv (Eq.trans hone hzero)

theorem ofReal_mul_I_im_eq_self
    (t : ℝ) :
    (t * Complex.I).im = t :=
  let hmul : (t * Complex.I).im = (t : ℂ).re :=
    Complex.mul_I_im (t : ℂ)
  let hre : (t : ℂ).re = t :=
    Complex.ofReal_re t
  Eq.trans hmul hre

theorem half_plus_t_i_im_step
    (t : ℝ) :
    ((1 / 2 : ℂ) + t * Complex.I).im = 0 + t :=
  let hadd :
      ((1 / 2 : ℂ) + t * Complex.I).im =
        (1 / 2 : ℂ).im + (t * Complex.I).im :=
    Complex.add_im (1 / 2 : ℂ) (t * Complex.I)
  let hcoords :
      (1 / 2 : ℂ).im + (t * Complex.I).im = 0 + t :=
    congrArg₂ HAdd.hAdd one_div_two_im_eq_zero
      (ofReal_mul_I_im_eq_self t)
  Eq.trans hadd hcoords

/-- Helper: imaginary part of `(1 / 2) + t * I` is `t`. -/
theorem im_half_plus_t_i (t : ℝ) : ((1 / 2 : ℂ) + t * Complex.I).im = t :=
  Eq.trans (half_plus_t_i_im_step t) (zero_add t)

/-- The inverse-Gamma correction in the completed logarithmic derivative split. -/
noncomputable def inverseGammaCompletionLogDeriv (z : ℂ) : ℂ :=
  deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z / (Complex.Gammaℝ z)⁻¹

/-- The inverse-Gamma correction unfolds to the derivative quotient. -/
theorem inverseGammaCompletionLogDeriv_eq
    (z : ℂ) :
    inverseGammaCompletionLogDeriv z =
      deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z / (Complex.Gammaℝ z)⁻¹ :=
  Eq.refl (inverseGammaCompletionLogDeriv z)

/-- Excluding the nonpositive-even `Gammaℝ` locus excludes the ordinary Gamma
locus after halving the argument. -/
theorem halfArgument_ne_negative_nat_of_ne_negative_even
    {z : ℂ}
    (hz : ∀ n : ℕ, z ≠ -(2 * (n : ℂ))) :
    ∀ n : ℕ, z / 2 ≠ -(n : ℂ) :=
  fun n hzn =>
    let hmul : z / 2 * 2 = (-(n : ℂ)) * 2 :=
      congrArg (fun w : ℂ => w * 2) hzn
    let hfirst : z = z / 2 * 2 :=
      (div_mul_cancel₀ z (two_ne_zero : (2 : ℂ) ≠ 0)).symm
    let hsecond : z = (-(n : ℂ)) * 2 :=
      Eq.trans hfirst hmul
    let hthird : (-(n : ℂ)) * 2 = -((n : ℂ) * 2) :=
      neg_mul (n : ℂ) 2
    let hfourth : -((n : ℂ) * 2) = -(2 * (n : ℂ)) :=
      congrArg Neg.neg (mul_comm (n : ℂ) 2)
    let hz_eq_neg_two : z = -(2 * (n : ℂ)) :=
      Eq.trans hsecond (Eq.trans hthird hfourth)
    hz n hz_eq_neg_two

/-- Deligne's `Gammaℝ` is definitionally the product of the `π` power and
the half-argument ordinary Gamma factor. -/
theorem Gammaℝ_eq_piFactor_mul_halfGamma_fun :
    (fun s : ℂ =>
        (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)) =
      Complex.Gammaℝ :=
  funext
    (fun s : ℂ =>
      (Complex.Gammaℝ_def s).symm)

theorem inv_square_mul_self_eq_inv
    {a : ℂ}
    (ha : a ≠ 0) :
    (a ^ 2)⁻¹ * a = a⁻¹ :=
  let hpow : a ^ 2 = a * a :=
    pow_two a
  let hstep₁ : (a ^ 2)⁻¹ * a = (a * a)⁻¹ * a :=
    congrArg (fun x : ℂ => x⁻¹ * a) hpow
  let hstep₂ : (a * a)⁻¹ * a = (a⁻¹ * a⁻¹) * a :=
    congrArg (fun x : ℂ => x * a) (mul_inv_rev a a)
  let hstep₃ : (a⁻¹ * a⁻¹) * a = a⁻¹ * (a⁻¹ * a) :=
    mul_assoc a⁻¹ a⁻¹ a
  let hstep₄ : a⁻¹ * (a⁻¹ * a) = a⁻¹ * 1 :=
    congrArg (fun x : ℂ => a⁻¹ * x) (inv_mul_cancel₀ ha)
  let hstep₅ : a⁻¹ * 1 = a⁻¹ :=
    mul_one a⁻¹
  Eq.trans hstep₁
    (Eq.trans hstep₂
      (Eq.trans hstep₃
        (Eq.trans hstep₄ hstep₅)))

theorem neg_div_square_div_inv_eq_neg_div
    {a d : ℂ}
    (ha : a ≠ 0) :
    (-d / a ^ 2) / a⁻¹ = -d / a :=
  let hcancel : (a ^ 2)⁻¹ * a = a⁻¹ :=
    inv_square_mul_self_eq_inv ha
  let hstep₁ : (-d / a ^ 2) / a⁻¹ =
      (-d / a ^ 2) * (a⁻¹)⁻¹ :=
    div_eq_mul_inv (-d / a ^ 2) a⁻¹
  let hstep₂ : (-d / a ^ 2) * (a⁻¹)⁻¹ =
      (-d / a ^ 2) * a :=
    congrArg (fun x : ℂ => (-d / a ^ 2) * x) (inv_inv a)
  let hstep₃ : (-d / a ^ 2) * a =
      (-d * (a ^ 2)⁻¹) * a :=
    congrArg (fun x : ℂ => x * a) (div_eq_mul_inv (-d) (a ^ 2))
  let hstep₄ : (-d * (a ^ 2)⁻¹) * a =
      -d * ((a ^ 2)⁻¹ * a) :=
    mul_assoc (-d) (a ^ 2)⁻¹ a
  let hstep₅ : -d * ((a ^ 2)⁻¹ * a) = -d * a⁻¹ :=
    congrArg (fun x : ℂ => -d * x) hcancel
  let hstep₆ : -d * a⁻¹ = -d / a :=
    (div_eq_mul_inv (-d) a).symm
  Eq.trans hstep₁
    (Eq.trans hstep₂
      (Eq.trans hstep₃
        (Eq.trans hstep₄
          (Eq.trans hstep₅ hstep₆))))

/-- The logarithmic derivative of an inverse is the negative logarithmic
derivative of the original function, at a differentiability and nonvanishing
point. -/
theorem deriv_inv_div_inv_eq_neg_deriv_div
    {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℂ g z)
    (hz : g z ≠ 0) :
    deriv (fun w : ℂ => (g w)⁻¹) z / (g z)⁻¹ =
      -deriv g z / g z :=
  let a : ℂ := g z
  let d : ℂ := deriv g z
  let ha : a ≠ 0 := hz
  let hderiv :
      deriv (fun w : ℂ => (g w)⁻¹) z =
        -d / a ^ 2 :=
    deriv_inv'' hg hz
  let hfirst :
      deriv (fun w : ℂ => (g w)⁻¹) z / (g z)⁻¹ =
        (-d / a ^ 2) / a⁻¹ :=
    congrArg (fun x : ℂ => x / a⁻¹) hderiv
  let hquotient :
      (-d / a ^ 2) / a⁻¹ = -d / a :=
    neg_div_square_div_inv_eq_neg_div ha
  Eq.trans hfirst hquotient

/-- Deligne's `Gammaℝ` is complex-differentiable away from its nonpositive
even singular locus. -/
theorem Gammaℝ_differentiableAt_of_ne_zero_locus
    {z : ℂ}
    (hz : ∀ n : ℕ, z ≠ -(2 * (n : ℂ))) :
    DifferentiableAt ℂ Complex.Gammaℝ z :=
  let hpow :
      DifferentiableAt ℂ
        (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2)) z :=
    (differentiableAt_id.neg.div_const (2 : ℂ)).const_cpow
      (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
  let hgamma_arg :
      ∀ n : ℕ, z / 2 ≠ -(n : ℂ) :=
    halfArgument_ne_negative_nat_of_ne_negative_even hz
  let hgamma :
      DifferentiableAt ℂ (fun s : ℂ => Complex.Gamma (s / 2)) z :=
    (Complex.differentiableAt_Gamma (z / 2) hgamma_arg).comp
      z
      (differentiableAt_id.div_const (2 : ℂ))
  let hprod :
      DifferentiableAt ℂ
        (fun s : ℂ =>
          (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)) z :=
    hpow.mul hgamma
  let hfun :
      (fun s : ℂ =>
          (Real.pi : ℂ) ^ (-s / 2) * Complex.Gamma (s / 2)) =
        Complex.Gammaℝ :=
    Gammaℝ_eq_piFactor_mul_halfGamma_fun
  Eq.subst
    (motive := fun phi : ℂ → ℂ => DifferentiableAt ℂ phi z)
    hfun
    hprod

theorem neg_id_div_two_hasDerivAt
    (z : ℂ) :
    HasDerivAt (fun s : ℂ => -s / 2) (-(1 / 2 : ℂ)) z :=
  let hid : HasDerivAt (fun s : ℂ => s) 1 z :=
    hasDerivAt_id z
  let hneg : HasDerivAt (fun s : ℂ => -s) (-1) z :=
    hid.neg
  let hdiv : HasDerivAt (fun s : ℂ => -s / 2) ((-1 : ℂ) / 2) z :=
    hneg.div_const (2 : ℂ)
  let hderiv : ((-1 : ℂ) / 2) = -(1 / 2 : ℂ) :=
    (neg_div' (2 : ℂ) (1 : ℂ)).symm
  Eq.subst
    (motive := fun d : ℂ => HasDerivAt (fun s : ℂ => -s / 2) d z)
    hderiv
    hdiv

/-- Derivative of the elementary `π ^ (-s/2)` factor in Deligne's `Gammaℝ`. -/
theorem Gammaℝ_piFactor_hasDerivAt
    (z : ℂ) :
    HasDerivAt
      (fun s : ℂ => (Real.pi : ℂ) ^ (-s / 2))
      ((Real.pi : ℂ) ^ (-z / 2) *
        Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)))
      z :=
  (neg_id_div_two_hasDerivAt z).const_cpow
    (Or.inl (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))

/-- Derivative of the half-argument ordinary Gamma factor in Deligne's `Gammaℝ`. -/
theorem Gammaℝ_halfGammaFactor_hasDerivAt
    {z : ℂ}
    (hz : ∀ n : ℕ, z / 2 ≠ -(n : ℂ)) :
    HasDerivAt
      (fun s : ℂ => Complex.Gamma (s / 2))
      (deriv Complex.Gamma (z / 2) * (1 / 2 : ℂ))
      z :=
  let houter :
      HasDerivAt Complex.Gamma (deriv Complex.Gamma (z / 2)) (z / 2) :=
    (Complex.differentiableAt_Gamma (z / 2) hz).hasDerivAt
  let hinner :
      HasDerivAt (fun s : ℂ => s / 2) (1 / 2 : ℂ) z :=
    (hasDerivAt_id z).div_const (2 : ℂ)
  houter.comp z hinner

theorem quotient_mul_right_cancel
    {p g p' : ℂ}
    (hg : g ≠ 0) :
    (p' * g) / (p * g) = p' / p :=
  let hdiv₁ :
      (p' * g) / (p * g) =
        (p' * g) * (p * g)⁻¹ :=
    div_eq_mul_inv (p' * g) (p * g)
  let hinv : (p * g)⁻¹ = g⁻¹ * p⁻¹ :=
    mul_inv_rev p g
  let hstep₁ :
      (p' * g) * (p * g)⁻¹ =
        (p' * g) * (g⁻¹ * p⁻¹) :=
    congrArg (fun x : ℂ => (p' * g) * x) hinv
  let hstep₂ :
      (p' * g) * (g⁻¹ * p⁻¹) =
        p' * (g * (g⁻¹ * p⁻¹)) :=
    mul_assoc p' g (g⁻¹ * p⁻¹)
  let hstep₃ :
      p' * (g * (g⁻¹ * p⁻¹)) =
        p' * ((g * g⁻¹) * p⁻¹) :=
    congrArg (fun x : ℂ => p' * x) (mul_assoc g g⁻¹ p⁻¹).symm
  let hstep₄ :
      p' * ((g * g⁻¹) * p⁻¹) =
        p' * (1 * p⁻¹) :=
    congrArg (fun x : ℂ => p' * (x * p⁻¹)) (mul_inv_cancel₀ hg)
  let hstep₅ :
      p' * (1 * p⁻¹) = p' * p⁻¹ :=
    congrArg (fun x : ℂ => p' * x) (one_mul p⁻¹)
  let hstep₆ : p' * p⁻¹ = p' / p :=
    (div_eq_mul_inv p' p).symm
  Eq.trans hdiv₁
    (Eq.trans hstep₁
      (Eq.trans hstep₂
        (Eq.trans hstep₃
          (Eq.trans hstep₄
            (Eq.trans hstep₅ hstep₆)))))

theorem quotient_mul_left_cancel
    {p g g' : ℂ}
    (hp : p ≠ 0) :
    (p * g') / (p * g) = g' / g :=
  let hdiv₁ :
      (p * g') / (p * g) =
        (p * g') * (p * g)⁻¹ :=
    div_eq_mul_inv (p * g') (p * g)
  let hinv : (p * g)⁻¹ = g⁻¹ * p⁻¹ :=
    mul_inv_rev p g
  let hstep₁ :
      (p * g') * (p * g)⁻¹ =
        (p * g') * (g⁻¹ * p⁻¹) :=
    congrArg (fun x : ℂ => (p * g') * x) hinv
  let hstep₂ :
      (p * g') * (g⁻¹ * p⁻¹) =
        p * (g' * (g⁻¹ * p⁻¹)) :=
    mul_assoc p g' (g⁻¹ * p⁻¹)
  let hstep₃ :
      p * (g' * (g⁻¹ * p⁻¹)) =
        p * ((g' * g⁻¹) * p⁻¹) :=
    congrArg (fun x : ℂ => p * x) (mul_assoc g' g⁻¹ p⁻¹).symm
  let hstep₄ :
      p * ((g' * g⁻¹) * p⁻¹) =
        (p * (g' * g⁻¹)) * p⁻¹ :=
    (mul_assoc p (g' * g⁻¹) p⁻¹).symm
  let hstep₅ :
      (p * (g' * g⁻¹)) * p⁻¹ =
        (g' * g⁻¹ * p) * p⁻¹ :=
    congrArg (fun x : ℂ => x * p⁻¹) (mul_comm p (g' * g⁻¹))
  let hstep₆ :
      (g' * g⁻¹ * p) * p⁻¹ =
        g' * g⁻¹ * (p * p⁻¹) :=
    mul_assoc (g' * g⁻¹) p p⁻¹
  let hstep₇ :
      g' * g⁻¹ * (p * p⁻¹) =
        g' * g⁻¹ * 1 :=
    congrArg (fun x : ℂ => g' * g⁻¹ * x) (mul_inv_cancel₀ hp)
  let hstep₈ :
      g' * g⁻¹ * 1 = g' * g⁻¹ :=
    mul_one (g' * g⁻¹)
  let hstep₉ :
      g' * g⁻¹ = g' / g :=
    (div_eq_mul_inv g' g).symm
  Eq.trans hdiv₁
    (Eq.trans hstep₁
      (Eq.trans hstep₂
        (Eq.trans hstep₃
          (Eq.trans hstep₄
            (Eq.trans hstep₅
              (Eq.trans hstep₆
                (Eq.trans hstep₇
                  (Eq.trans hstep₈ hstep₉))))))))

/-- Quotient algebra for the logarithmic derivative of a product. -/
theorem mul_logDeriv_algebra
    {p p' g g' : ℂ}
    (hp : p ≠ 0)
    (hg : g ≠ 0) :
    (p' * g + p * g') / (p * g) = p' / p + g' / g :=
  let hsplit :
      (p' * g + p * g') / (p * g) =
        (p' * g) / (p * g) + (p * g') / (p * g) :=
    add_div (p' * g) (p * g') (p * g)
  let hleft :
      (p' * g) / (p * g) = p' / p :=
    quotient_mul_right_cancel hg
  let hright :
      (p * g') / (p * g) = g' / g :=
    quotient_mul_left_cancel hp
  let hsum :
      (p' * g) / (p * g) + (p * g') / (p * g) =
        p' / p + g' / g :=
    congrArg₂ HAdd.hAdd hleft hright
  Eq.trans hsplit hsum

theorem cpow_ofReal_pi_ne_zero
    (z : ℂ) :
    (Real.pi : ℂ) ^ (-z / 2) ≠ 0 :=
  fun hp_zero =>
    let hbase : (Real.pi : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    let hbase_zero : (Real.pi : ℂ) = 0 :=
      (Complex.cpow_eq_zero_iff (Real.pi : ℂ) (-z / 2)).mp hp_zero |>.1
    hbase hbase_zero

theorem left_mul_div_self_eq_right
    {p q : ℂ}
    (hp : p ≠ 0) :
    (p * q) / p = q :=
  let hdiv : (p * q) / p = (p * q) * p⁻¹ :=
    div_eq_mul_inv (p * q) p
  let hcomm : (p * q) * p⁻¹ = (q * p) * p⁻¹ :=
    congrArg (fun x : ℂ => x * p⁻¹) (mul_comm p q)
  let hassoc : (q * p) * p⁻¹ = q * (p * p⁻¹) :=
    mul_assoc q p p⁻¹
  let hcancel : q * (p * p⁻¹) = q * 1 :=
    congrArg (fun x : ℂ => q * x) (mul_inv_cancel₀ hp)
  let hone : q * 1 = q :=
    mul_one q
  Eq.trans hdiv
    (Eq.trans hcomm
      (Eq.trans hassoc
        (Eq.trans hcancel hone)))

/-- The elementary `π ^ (-s/2)` factor has logarithmic derivative
`-log π / 2`. -/
theorem Gammaℝ_piFactor_logDeriv_eq
    (z : ℂ) :
    ((Real.pi : ℂ) ^ (-z / 2) *
        Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ))) /
      ((Real.pi : ℂ) ^ (-z / 2)) =
        Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ)) :=
  let p : ℂ := (Real.pi : ℂ) ^ (-z / 2)
  let q : ℂ := Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ))
  let hp : p ≠ 0 :=
    cpow_ofReal_pi_ne_zero z
  let hassoc :
      ((Real.pi : ℂ) ^ (-z / 2) *
          Complex.log (Real.pi : ℂ) * (-(1 / 2 : ℂ))) /
        ((Real.pi : ℂ) ^ (-z / 2)) =
          (p * q) / p :=
    congrArg
      (fun x : ℂ => x / ((Real.pi : ℂ) ^ (-z / 2)))
      (mul_assoc ((Real.pi : ℂ) ^ (-z / 2))
        (Complex.log (Real.pi : ℂ)) (-(1 / 2 : ℂ)))
  Eq.trans hassoc (left_mul_div_self_eq_right hp)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
