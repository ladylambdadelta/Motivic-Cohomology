import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.PoleClearedBoundarySetup.Owner

/-!
# Boundary logarithmic phase core estimates

This file owns the logarithmic phase function, its positive-real branch
normalization, and derivative/norm calculations.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

def boundaryLineOnePointRealParam_logarithmicPhaseFunction
    (t : ℝ)
    (x : ℝ) : ℂ :=
  Complex.exp ((-(t : ℂ) * Complex.I) * (Real.log x : ℂ))

/-- Owner API: positive real samples of the logarithmic phase are the complex
power samples used by the Dirichlet-polynomial primitive.

This is the branch-normalization calculation for the principal complex power on
the positive real axis. -/
theorem logarithmicPhaseFunction_positiveReal_cpow
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    boundaryLineOnePointRealParam_logarithmicPhaseFunction t x =
      (x : ℂ) ^ (-(t : ℂ) * Complex.I) := by
  let a : ℂ := -(t : ℂ) * Complex.I
  have hx_complex_ne : (x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hx.ne'
  have hlog : (Real.log x : ℂ) = Complex.log (x : ℂ) :=
    Complex.ofReal_log hx.le
  have harg_left :
      a * (Real.log x : ℂ) = (Real.log x : ℂ) * a :=
    mul_comm a (Real.log x : ℂ)
  have harg_right :
      (Real.log x : ℂ) * a = Complex.log (x : ℂ) * a :=
    congrArg (fun z : ℂ => z * a) hlog
  calc
    boundaryLineOnePointRealParam_logarithmicPhaseFunction t x =
        Complex.exp (a * (Real.log x : ℂ)) := by
          rfl
    _ = Complex.exp ((Real.log x : ℂ) * a) :=
          congrArg Complex.exp harg_left
    _ = Complex.exp (Complex.log (x : ℂ) * a) :=
          congrArg Complex.exp harg_right
    _ = (x : ℂ) ^ a :=
          (Complex.cpow_def_of_ne_zero hx_complex_ne a).symm

/-- Positive real samples of the logarithmic phase agree with the complex-power
notation used in the Dirichlet-polynomial partial sums. -/
theorem boundaryLineOnePointRealParam_logarithmicPhaseFunction_eq_cpow_of_pos
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    boundaryLineOnePointRealParam_logarithmicPhaseFunction t x =
      (x : ℂ) ^ (-(t : ℂ) * Complex.I) := by
  exact logarithmicPhaseFunction_positiveReal_cpow t hx

/-- Deep algebraic sink reordering the chain-rule derivative into the public
`a / x * f x` form. -/
theorem logarithmicPhaseFunction_positiveReal_derivative_reorder
    (t : ℝ)
    {x : ℝ}
    (_hx : 0 < x) :
    Complex.exp (((-(t : ℂ) * Complex.I) * (Real.log x : ℂ))) *
        (((-(t : ℂ) * Complex.I)) * ((x⁻¹ : ℝ) : ℂ)) =
      (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhaseFunction t x) := by
  let a : ℂ := -(t : ℂ) * Complex.I
  let E : ℂ := Complex.exp (a * (Real.log x : ℂ))
  have hinv : ((x⁻¹ : ℝ) : ℂ) = (x : ℂ)⁻¹ :=
    RCLike.ofReal_inv (K := ℂ) x
  have hreplace_inv :
      E * (a * ((x⁻¹ : ℝ) : ℂ)) = E * (a * (x : ℂ)⁻¹) :=
    congrArg (fun z : ℂ => E * (a * z)) hinv
  have hcomm :
      E * (a * (x : ℂ)⁻¹) = (a * (x : ℂ)⁻¹) * E :=
    mul_comm E (a * (x : ℂ)⁻¹)
  have hdiv : a / (x : ℂ) = a * (x : ℂ)⁻¹ :=
    div_eq_mul_inv a (x : ℂ)
  have hreplace_div :
      (a * (x : ℂ)⁻¹) * E = (a / (x : ℂ)) * E :=
    congrArg (fun z : ℂ => z * E) hdiv.symm
  calc
    E * (a * ((x⁻¹ : ℝ) : ℂ)) = E * (a * (x : ℂ)⁻¹) :=
      hreplace_inv
    _ = (a * (x : ℂ)⁻¹) * E :=
      hcomm
    _ = (a / (x : ℂ)) * E :=
      hreplace_div

/-- Owner API: derivative of the logarithmic phase on the positive real axis. -/
theorem logarithmicPhaseFunction_positiveReal_hasDerivAt
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt
      (boundaryLineOnePointRealParam_logarithmicPhaseFunction t)
      (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhaseFunction t x)
      x := by
  let a : ℂ := -(t : ℂ) * Complex.I
  have hlog_real : HasDerivAt Real.log x⁻¹ x :=
    Real.hasDerivAt_log hx.ne'
  have hlog_complex :
      HasDerivAt (fun y : ℝ => (Real.log y : ℂ)) ((x⁻¹ : ℝ) : ℂ) x :=
    hlog_real.ofReal_comp
  have hphase :
      HasDerivAt
        (fun y : ℝ => a * (Real.log y : ℂ))
        (a * ((x⁻¹ : ℝ) : ℂ))
        x :=
    hlog_complex.const_mul a
  have hexp :
      HasDerivAt
        (fun y : ℝ => Complex.exp (a * (Real.log y : ℂ)))
        (Complex.exp (a * (Real.log x : ℂ)) * (a * ((x⁻¹ : ℝ) : ℂ)))
        x :=
    hphase.cexp
  have hderiv_reorder :
      Complex.exp (a * (Real.log x : ℂ)) * (a * ((x⁻¹ : ℝ) : ℂ)) =
        (a / (x : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhaseFunction t x := by
    exact logarithmicPhaseFunction_positiveReal_derivative_reorder t hx
  exact hderiv_reorder ▸ hexp

/-- Real-part calculation for the purely imaginary logarithmic-phase exponent. -/
theorem logarithmicPhaseFunction_exponent_re_zero
    (t : ℝ)
    (x : ℝ) :
    (((-(t : ℂ) * Complex.I) * (Real.log x : ℂ)).re) = 0 := by
  let u : ℂ := -(t : ℂ) * Complex.I
  let v : ℂ := (Real.log x : ℂ)
  have hu_re : u.re = 0 := by
    have hneg_im : (-(t : ℂ)).im = 0 := by
      calc
        (-(t : ℂ)).im = -((t : ℂ).im) :=
          Complex.neg_im (t : ℂ)
        _ = -0 :=
          congrArg Neg.neg (Complex.ofReal_im t)
        _ = 0 :=
          neg_zero
    calc
      u.re = (-(t : ℂ) * Complex.I).re :=
        rfl
      _ = - (-(t : ℂ)).im :=
        Complex.mul_I_re (-(t : ℂ))
      _ = -0 :=
        congrArg Neg.neg hneg_im
      _ = 0 :=
        neg_zero
  have hv_im : v.im = 0 := by
    calc
      v.im = ((Real.log x : ℝ) : ℂ).im :=
        rfl
      _ = 0 :=
        Complex.ofReal_im (Real.log x)
  calc
    (((-(t : ℂ) * Complex.I) * (Real.log x : ℂ)).re) =
        u.re * v.re - u.im * v.im := by
      exact Complex.mul_re u v
    _ = 0 * v.re - u.im * v.im := by
      exact congrArg (fun y : ℝ => y * v.re - u.im * v.im) hu_re
    _ = 0 * v.re - u.im * 0 := by
      exact congrArg (fun y : ℝ => 0 * v.re - u.im * y) hv_im
    _ = 0 - u.im * 0 := by
      exact congrArg (fun y : ℝ => y - u.im * 0) (zero_mul v.re)
    _ = 0 - 0 := by
      exact congrArg (fun y : ℝ => 0 - y) (mul_zero u.im)
    _ = 0 :=
      sub_zero 0

/-- Unit norm of the positive-real logarithmic phase.

This is the elementary identity `‖exp (-it log x)‖ = 1`; it is peeled as the
phase-normalization sink used by the derivative norm algebra. -/
theorem boundaryLineOnePointRealParam_logarithmicPhaseFunction_norm
    (t : ℝ)
    (x : ℝ) :
    ‖boundaryLineOnePointRealParam_logarithmicPhaseFunction t x‖ = 1 := by
  let exponent : ℂ := (-(t : ℂ) * Complex.I) * (Real.log x : ℂ)
  have hnorm_abs :
      ‖Complex.exp exponent‖ = Complex.abs (Complex.exp exponent) :=
    Complex.norm_eq_abs (Complex.exp exponent)
  have habs_exp :
      Complex.abs (Complex.exp exponent) = Real.exp exponent.re :=
    Complex.abs_exp exponent
  have hexponent_re : exponent.re = 0 :=
    logarithmicPhaseFunction_exponent_re_zero t x
  have hexp_zero : Real.exp 0 = 1 :=
    Real.exp_zero
  calc
    ‖boundaryLineOnePointRealParam_logarithmicPhaseFunction t x‖ =
        ‖Complex.exp exponent‖ :=
      rfl
    _ = Complex.abs (Complex.exp exponent) :=
      hnorm_abs
    _ = Real.exp exponent.re :=
      habs_exp
    _ = Real.exp 0 :=
      congrArg Real.exp hexponent_re
    _ = 1 :=
      hexp_zero

/-- Numerator norm for the logarithmic-phase derivative. -/
theorem logarithmicPhaseFunction_derivative_numerator_norm
    (t : ℝ) :
    ‖(-(t : ℂ) * Complex.I)‖ = ‖t‖ := by
  have hmul :
      ‖(-(t : ℂ) * Complex.I)‖ = ‖-(t : ℂ)‖ * ‖Complex.I‖ :=
    norm_mul (-(t : ℂ)) Complex.I
  have hneg : ‖-(t : ℂ)‖ = ‖(t : ℂ)‖ :=
    norm_neg (t : ℂ)
  have hI : ‖Complex.I‖ = 1 :=
    RCLike.norm_I_of_ne_zero (K := ℂ) Complex.I_ne_zero
  have hreal : ‖(t : ℂ)‖ = ‖t‖ :=
    RCLike.norm_ofReal t
  calc
    ‖(-(t : ℂ) * Complex.I)‖ = ‖-(t : ℂ)‖ * ‖Complex.I‖ :=
      hmul
    _ = ‖(t : ℂ)‖ * ‖Complex.I‖ :=
      congrArg (fun y : ℝ => y * ‖Complex.I‖) hneg
    _ = ‖(t : ℂ)‖ * 1 :=
      congrArg (fun y : ℝ => ‖(t : ℂ)‖ * y) hI
    _ = ‖(t : ℂ)‖ :=
      mul_one ‖(t : ℂ)‖
    _ = ‖t‖ :=
      hreal

/-- Denominator norm for a positive real embedded in `ℂ`. -/
theorem logarithmicPhaseFunction_positiveReal_denominator_norm
    {x : ℝ}
    (hx : 0 < x) :
    ‖(x : ℂ)‖ = x := by
  have hreal : ‖(x : ℂ)‖ = ‖x‖ :=
    RCLike.norm_ofReal x
  have hx_norm : ‖x‖ = x :=
    Real.norm_of_nonneg hx.le
  exact hreal.trans hx_norm

/-- Division by a positive real denominator after taking complex norms. -/
theorem logarithmicPhaseFunction_positiveReal_norm_div_algebra
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    ‖(-(t : ℂ) * Complex.I)‖ / ‖(x : ℂ)‖ = ‖t‖ / x := by
  have hnum : ‖(-(t : ℂ) * Complex.I)‖ = ‖t‖ :=
    logarithmicPhaseFunction_derivative_numerator_norm t
  have hden : ‖(x : ℂ)‖ = x :=
    logarithmicPhaseFunction_positiveReal_denominator_norm hx
  calc
    ‖(-(t : ℂ) * Complex.I)‖ / ‖(x : ℂ)‖ =
        ‖t‖ / ‖(x : ℂ)‖ :=
      congrArg (fun y : ℝ => y / ‖(x : ℂ)‖) hnum
    _ = ‖t‖ / x :=
      congrArg (fun y : ℝ => ‖t‖ / y) hden

/-- Deep algebraic sink for the logarithmic-phase derivative norm on the
positive real axis. -/
theorem logarithmicPhaseFunction_positiveReal_derivative_norm_algebra
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    ‖(((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhaseFunction t x)‖ =
      ‖t‖ / x := by
  let numerator : ℂ := -(t : ℂ) * Complex.I
  let denominator : ℂ := (x : ℂ)
  let phase : ℂ := boundaryLineOnePointRealParam_logarithmicPhaseFunction t x
  have hphase_norm : ‖phase‖ = 1 :=
    boundaryLineOnePointRealParam_logarithmicPhaseFunction_norm t x
  have hproduct_norm :
      ‖(numerator / denominator) * phase‖ =
        ‖numerator / denominator‖ * ‖phase‖ :=
    norm_mul (numerator / denominator) phase
  have hquotient_norm :
      ‖numerator / denominator‖ = ‖numerator‖ / ‖denominator‖ :=
    norm_div numerator denominator
  have hquotient_norm_target :
      ‖numerator‖ / ‖denominator‖ = ‖t‖ / x :=
    logarithmicPhaseFunction_positiveReal_norm_div_algebra t hx
  calc
    ‖(((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhaseFunction t x)‖ =
        ‖(numerator / denominator) * phase‖ :=
      rfl
    _ = ‖numerator / denominator‖ * ‖phase‖ :=
      hproduct_norm
    _ = (‖numerator‖ / ‖denominator‖) * ‖phase‖ :=
      congrArg (fun y : ℝ => y * ‖phase‖) hquotient_norm
    _ = (‖numerator‖ / ‖denominator‖) * 1 :=
      congrArg (fun y : ℝ => (‖numerator‖ / ‖denominator‖) * y) hphase_norm
    _ = ‖numerator‖ / ‖denominator‖ :=
      mul_one (‖numerator‖ / ‖denominator‖)
    _ = ‖t‖ / x :=
      hquotient_norm_target

/-- The logarithmic phase has derivative `(-it / x) exp (-it log x)` on the
positive real line. -/
theorem boundaryLineOnePointRealParam_logarithmicPhaseFunction_hasDerivAt
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt
      (boundaryLineOnePointRealParam_logarithmicPhaseFunction t)
      (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhaseFunction t x)
      x := by
  exact logarithmicPhaseFunction_positiveReal_hasDerivAt t hx

/-- Owner API: the derivative magnitude of the logarithmic phase is `|t| / x`.

The proof combines the positive-real logarithmic branch normalization with
`‖exp (iθ)‖ = 1` and the reciprocal norm of a positive real. -/
theorem logarithmicPhaseFunction_positiveReal_derivative_norm_eq
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    ‖(((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhaseFunction t x)‖ =
      ‖t‖ / x := by
  exact logarithmicPhaseFunction_positiveReal_derivative_norm_algebra t hx

/-- The derivative magnitude of the logarithmic phase is exactly `|t| / x`. -/
theorem boundaryLineOnePointRealParam_logarithmicPhaseFunction_derivative_norm_eq
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    ‖(((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhaseFunction t x)‖ =
      ‖t‖ / x := by
  exact logarithmicPhaseFunction_positiveReal_derivative_norm_eq t hx

/-- The actual `deriv` of the logarithmic phase on the positive real axis. -/
theorem boundaryLineOnePointRealParam_logarithmicPhaseFunction_deriv_eq
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) x =
      (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhaseFunction t x) := by
  exact (boundaryLineOnePointRealParam_logarithmicPhaseFunction_hasDerivAt t hx).deriv

/-- The norm of the actual `deriv` of the logarithmic phase is `|t| / x`. -/
theorem boundaryLineOnePointRealParam_logarithmicPhaseFunction_deriv_norm_eq
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    ‖deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) x‖ =
      ‖t‖ / x := by
  have hderiv :
      deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) x =
        (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhaseFunction t x) :=
    boundaryLineOnePointRealParam_logarithmicPhaseFunction_deriv_eq t hx
  have hnorm :
      ‖(((-(t : ℂ) * Complex.I) / (x : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhaseFunction t x)‖ =
        ‖t‖ / x :=
    boundaryLineOnePointRealParam_logarithmicPhaseFunction_derivative_norm_eq t hx
  exact Eq.trans (congrArg norm hderiv) hnorm

/-- The complex reciprocal amplitude `x ↦ 1 / x` differentiated along the real
axis. -/
theorem complexReciprocalOfReal_hasDerivAt
    {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt
      (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ))
      (-(1 : ℂ) / (x : ℂ) ^ 2)
      x := by
  have hreal :
      HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x :=
    hasDerivAt_inv hx.ne'
  have hcomplex_real :
      HasDerivAt
        (fun y : ℝ => ((y⁻¹ : ℝ) : ℂ))
        (((-(x ^ 2)⁻¹ : ℝ) : ℂ))
        x :=
    hreal.ofReal_comp
  have hfunction_transport :
      (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) =ᶠ[𝓝 x]
        (fun y : ℝ => ((y⁻¹ : ℝ) : ℂ)) :=
    Filter.Eventually.of_forall
      (fun y : ℝ => (RCLike.ofReal_inv (K := ℂ) y).symm)
  have hderiv_value :
      (((-(x ^ 2)⁻¹ : ℝ) : ℂ)) = -(1 : ℂ) / (x : ℂ) ^ 2 := by
    have hcast_neg :
        (((-(x ^ 2)⁻¹ : ℝ) : ℂ)) =
          -((((x ^ 2)⁻¹ : ℝ) : ℂ)) :=
      RCLike.ofReal_neg (K := ℂ) ((x ^ 2)⁻¹)
    have hcast_inv :
        ((((x ^ 2)⁻¹ : ℝ) : ℂ)) =
          (((x ^ 2 : ℝ) : ℂ))⁻¹ :=
      RCLike.ofReal_inv (K := ℂ) (x ^ 2)
    have hcast_pow :
        (((x ^ 2 : ℝ) : ℂ)) = (x : ℂ) ^ 2 :=
      RCLike.ofReal_pow (K := ℂ) x 2
    have hneg_one_div :
        -(((x : ℂ) ^ 2)⁻¹) = -(1 : ℂ) / (x : ℂ) ^ 2 := by
      let z : ℂ := (x : ℂ) ^ 2
      have hone_mul : (1 : ℂ) * z⁻¹ = z⁻¹ :=
        one_mul z⁻¹
      have hneg_mul : (-(1 : ℂ)) * z⁻¹ = -((1 : ℂ) * z⁻¹) :=
        neg_mul (1 : ℂ) z⁻¹
      have hdiv : -(1 : ℂ) / z = (-(1 : ℂ)) * z⁻¹ :=
        div_eq_mul_inv (-(1 : ℂ)) z
      calc
        -(((x : ℂ) ^ 2)⁻¹) = -z⁻¹ :=
          rfl
        _ = -((1 : ℂ) * z⁻¹) :=
          congrArg Neg.neg hone_mul.symm
        _ = (-(1 : ℂ)) * z⁻¹ :=
          hneg_mul.symm
        _ = -(1 : ℂ) / z :=
          hdiv.symm
    calc
      (((-(x ^ 2)⁻¹ : ℝ) : ℂ)) =
          -((((x ^ 2)⁻¹ : ℝ) : ℂ)) :=
        hcast_neg
      _ = -((((x ^ 2 : ℝ) : ℂ))⁻¹) :=
        congrArg Neg.neg hcast_inv
      _ = -(((x : ℂ) ^ 2)⁻¹) :=
        congrArg (fun z : ℂ => -z⁻¹) hcast_pow
      _ = -(1 : ℂ) / (x : ℂ) ^ 2 :=
        hneg_one_div
  exact
    (hcomplex_real.congr_of_eventuallyEq hfunction_transport).congr_deriv
      hderiv_value

/-- The actual `deriv` of the reciprocal amplitude `x ↦ 1 / x` along the real
axis. -/
theorem complexReciprocalOfReal_deriv_eq
    {x : ℝ}
    (hx : 0 < x) :
    deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x =
      (-(1 : ℂ) / (x : ℂ) ^ 2) := by
  exact (complexReciprocalOfReal_hasDerivAt hx).deriv

/-- Norm of the reciprocal-amplitude derivative on the positive real axis. -/
theorem complexReciprocalOfReal_deriv_norm_eq
    {x : ℝ}
    (hx : 0 < x) :
    ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x‖ =
      (1 : ℝ) / x ^ 2 := by
  have hderiv :
      deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x =
        (-(1 : ℂ) / (x : ℂ) ^ 2) :=
    complexReciprocalOfReal_deriv_eq hx
  have hdiv :
      ‖(-(1 : ℂ) / (x : ℂ) ^ 2)‖ =
        ‖-(1 : ℂ)‖ / ‖(x : ℂ) ^ 2‖ :=
    norm_div (-(1 : ℂ)) ((x : ℂ) ^ 2)
  have hnum : ‖-(1 : ℂ)‖ = (1 : ℝ) := by
    calc
      ‖-(1 : ℂ)‖ = ‖(1 : ℂ)‖ :=
        norm_neg (1 : ℂ)
      _ = 1 :=
        norm_one
  have hxnorm : ‖(x : ℂ)‖ = x :=
    logarithmicPhaseFunction_positiveReal_denominator_norm hx
  have hden : ‖(x : ℂ) ^ 2‖ = x ^ 2 := by
    calc
      ‖(x : ℂ) ^ 2‖ = ‖(x : ℂ)‖ ^ 2 :=
        norm_pow (x : ℂ) 2
      _ = x ^ 2 :=
        congrArg (fun y : ℝ => y ^ 2) hxnorm
  calc
    ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x‖ =
        ‖-(1 : ℂ) / (x : ℂ) ^ 2‖ :=
      congrArg norm hderiv
    _ = ‖-(1 : ℂ)‖ / ‖(x : ℂ) ^ 2‖ :=
      hdiv
    _ = (1 : ℝ) / ‖(x : ℂ) ^ 2‖ :=
      congrArg (fun y : ℝ => y / ‖(x : ℂ) ^ 2‖) hnum
    _ = (1 : ℝ) / x ^ 2 :=
      congrArg (fun y : ℝ => (1 : ℝ) / y) hden

/-- Integer samples of the logarithmic phase have norm at most one. -/
theorem logarithmicPhase_nat_sample_norm_le_one
    (t : ℝ)
    (k : ℕ)
    [Decidable (-(t : ℂ) * Complex.I = 0)] :
    ‖(k : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ≤ 1 := by
  match (inferInstance : Decidable (k = 0)) with
  | isTrue hk =>
    let a : ℂ := -(t : ℂ) * Complex.I
    have hterm :
        (k : ℂ) ^ a = (0 : ℂ) ^ a := by
      have hnat_zero :
          (k : ℂ) ^ a = ((0 : ℕ) : ℂ) ^ a :=
        congrArg (fun n : ℕ => (n : ℂ) ^ a) hk
      have hzero_cast : ((0 : ℕ) : ℂ) = (0 : ℂ) :=
        Nat.cast_zero
      have hcast_zero : (((0 : ℕ) : ℂ) ^ a) = (0 : ℂ) ^ a :=
        congrArg (fun z : ℂ => z ^ a) hzero_cast
      exact hnat_zero.trans hcast_zero
    match (inferInstance : Decidable (a = 0)) with
    | isTrue ha =>
      have hzero_pow : (0 : ℂ) ^ a = 1 := by
        exact Eq.subst
          (motive := fun z : ℂ => (0 : ℂ) ^ z = 1)
          ha.symm
          (Complex.cpow_zero (0 : ℂ))
      have hnorm :
          ‖(k : ℂ) ^ a‖ = 1 := by
        calc
          ‖(k : ℂ) ^ a‖ = ‖(0 : ℂ) ^ a‖ :=
            congrArg norm hterm
          _ = ‖(1 : ℂ)‖ :=
            congrArg norm hzero_pow
          _ = 1 :=
            norm_one
      exact le_of_eq hnorm
    | isFalse ha =>
      have hzero_pow : (0 : ℂ) ^ a = 0 :=
        Complex.zero_cpow ha
      have hnorm :
          ‖(k : ℂ) ^ a‖ = 0 := by
        calc
          ‖(k : ℂ) ^ a‖ = ‖(0 : ℂ) ^ a‖ :=
            congrArg norm hterm
          _ = ‖(0 : ℂ)‖ :=
            congrArg norm hzero_pow
          _ = 0 :=
            norm_zero
      exact hnorm.le.trans zero_le_one
  | isFalse hk =>
    have hk_pos : 0 < k :=
      Nat.pos_of_ne_zero hk
    have hnorm :
        ‖(k : ℂ) ^ (-(t : ℂ) * Complex.I)‖ = (k : ℝ) ^ ((-(t : ℂ) * Complex.I).re) :=
      Complex.norm_natCast_cpow_of_pos hk_pos (-(t : ℂ) * Complex.I)
    have hre : (-(t : ℂ) * Complex.I).re = 0 := by
      have hneg_im : (-(t : ℂ)).im = 0 := by
        calc
          (-(t : ℂ)).im = -((t : ℂ).im) :=
            Complex.neg_im (t : ℂ)
          _ = -0 :=
            congrArg Neg.neg (Complex.ofReal_im t)
          _ = 0 :=
            neg_zero
      calc
        (-(t : ℂ) * Complex.I).re = - (-(t : ℂ)).im :=
          Complex.mul_I_re (-(t : ℂ))
        _ = -0 :=
          congrArg Neg.neg hneg_im
        _ = 0 :=
          neg_zero
    have hpow_zero : (k : ℝ) ^ ((-(t : ℂ) * Complex.I).re) = 1 := by
      exact Eq.subst
        (motive := fun x : ℝ => (k : ℝ) ^ x = 1)
        hre.symm
        (Real.rpow_zero (k : ℝ))
    exact le_of_eq (hnorm.trans hpow_zero)
end
end LFunctions
end Boundary
