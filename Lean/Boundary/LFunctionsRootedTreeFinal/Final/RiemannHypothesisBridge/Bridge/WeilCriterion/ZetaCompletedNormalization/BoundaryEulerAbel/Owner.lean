import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.PoleClearedBoundarySetup.Owner

/-!
# Boundary Euler-Abel estimates

This file is a mechanically split owner layer from the completed normalization
package.  It preserves the original declaration order and keeps downstream
imports routed through `ZetaCompletedNormalization.Owner`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

def boundaryLineOnePointRealParam_logarithmicPhasePartialSum
    (t : ℝ)
    (M : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc 0 M,
    (k : ℂ) ^ (-(t : ℂ) * Complex.I)

/-- Definitional expansion of the logarithmic-phase partial sum. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_eq
    (t : ℝ)
    (M : ℕ) :
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum t M =
      ∑ k ∈ Finset.Icc 0 M,
        (k : ℂ) ^ (-(t : ℂ) * Complex.I) := by
  rfl

/-- The continuous logarithmic phase whose integer samples are `n^{-it}` away
from the origin. -/
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
    (hx : 0 < x) :
    Complex.exp (((-(t : ℂ) * Complex.I) * (Real.log x : ℂ))) *
        (((-(t : ℂ) * Complex.I)) * (x⁻¹ : ℂ)) =
      (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhaseFunction t x) := by
  let a : ℂ := -(t : ℂ) * Complex.I
  let E : ℂ := Complex.exp (a * (Real.log x : ℂ))
  have hinv : (x⁻¹ : ℂ) = (x : ℂ)⁻¹ :=
    Complex.ofReal_inv x
  have hreplace_inv :
      E * (a * (x⁻¹ : ℂ)) = E * (a * (x : ℂ)⁻¹) :=
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
    E * (a * (x⁻¹ : ℂ)) = E * (a * (x : ℂ)⁻¹) :=
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
      HasDerivAt (fun y : ℝ => (Real.log y : ℂ)) (x⁻¹ : ℂ) x :=
    hlog_real.ofReal_comp
  have hphase :
      HasDerivAt
        (fun y : ℝ => a * (Real.log y : ℂ))
        (a * (x⁻¹ : ℂ))
        x :=
    hlog_complex.const_mul a
  have hexp :
      HasDerivAt
        (fun y : ℝ => Complex.exp (a * (Real.log y : ℂ)))
        (Complex.exp (a * (Real.log x : ℂ)) * (a * (x⁻¹ : ℂ)))
        x :=
    hphase.cexp
  have hderiv_reorder :
      Complex.exp (a * (Real.log x : ℂ)) * (a * (x⁻¹ : ℂ)) =
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
    norm_I
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
    norm_of_nonneg hx.le
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
      HasDerivAt (fun y : ℝ => (y : ℂ)) (1 : ℂ) x :=
    (hasDerivAt_id x).ofReal_comp
  have hne : (fun y : ℝ => (y : ℂ)) x ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hx.ne'
  exact hreal.inv hne

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
    (k : ℕ) :
    ‖(k : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ≤ 1 := by
  by_cases hk : k = 0
  · have hterm :
        (k : ℂ) ^ (-(t : ℂ) * Complex.I) =
          (0 : ℂ) ^ (-(t : ℂ) * Complex.I) := by
      exact congrArg (fun n : ℕ => (n : ℂ) ^ (-(t : ℂ) * Complex.I)) hk
    have hnorm_nonneg :
        0 ≤ ‖(k : ℂ) ^ (-(t : ℂ) * Complex.I)‖ :=
      norm_nonneg ((k : ℂ) ^ (-(t : ℂ) * Complex.I))
    exact le_trans hnorm_nonneg zero_le_one
  · have hk_pos : 0 < k :=
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

/-- Trivial cardinality bound for logarithmic-phase partial sums. -/
theorem logarithmicPhasePartialSum_norm_le_card
    (t : ℝ)
    (M : ℕ) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t M‖ ≤
      (M + 1 : ℝ) := by
  have hsum :
      ‖∑ k ∈ Finset.Icc 0 M, (k : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ≤
        ∑ k ∈ Finset.Icc 0 M, ‖(k : ℂ) ^ (-(t : ℂ) * Complex.I)‖ :=
    norm_sum_le (Finset.Icc 0 M)
      (fun k : ℕ => (k : ℂ) ^ (-(t : ℂ) * Complex.I))
  have hterms :
      (∑ k ∈ Finset.Icc 0 M, ‖(k : ℂ) ^ (-(t : ℂ) * Complex.I)‖) ≤
        ∑ k ∈ Finset.Icc 0 M, (1 : ℝ) := by
    exact Finset.sum_le_sum
      (fun k _hk => logarithmicPhase_nat_sample_norm_le_one t k)
  have hcard :
      (∑ k ∈ Finset.Icc 0 M, (1 : ℝ)) = (M + 1 : ℝ) := by
    calc
      (∑ k ∈ Finset.Icc 0 M, (1 : ℝ)) =
          ((Finset.Icc 0 M).card : ℝ) := by
        exact Finset.sum_const_nat (Finset.Icc 0 M) 1
      _ = (M + 1 : ℝ) := by
        exact congrArg (fun n : ℕ => (n : ℝ)) (Finset.card_Icc 0 M)
  exact le_trans hsum (le_trans hterms (le_of_eq hcard))

/-- Reciprocal endpoint times the trivial cardinality bound is at most two. -/
theorem logarithmicPhase_endpoint_trivial_bound
    (t : ℝ)
    {M : ℕ}
    (hM : 1 ≤ M) :
    ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          ⌊((M : ℕ) : ℝ)⌋₊‖ ≤ 2 := by
  have hfloor : ⌊((M : ℕ) : ℝ)⌋₊ = M :=
    Nat.floor_natCast M
  have hpartial :
      ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          ⌊((M : ℕ) : ℝ)⌋₊‖ ≤ (M + 1 : ℝ) := by
    exact Eq.subst
      (motive := fun R : ℕ =>
        ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t R‖ ≤
          (M + 1 : ℝ))
      hfloor.symm
      (logarithmicPhasePartialSum_norm_le_card t M)
  have hM_pos : 0 < M :=
    Nat.lt_of_succ_le hM
  have hM_real_pos : (0 : ℝ) < (M : ℝ) :=
    Nat.cast_pos.mpr hM_pos
  have hnorm_inv :
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ = (1 : ℝ) / (M : ℝ) := by
    have hnorm_real : ‖(((M : ℕ) : ℝ) : ℂ)‖ = (M : ℝ) := by
      exact Complex.norm_ofReal_of_nonneg (Nat.cast_nonneg M)
    calc
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ =
          (‖(((M : ℕ) : ℝ) : ℂ)‖)⁻¹ := by
        exact norm_inv ((((M : ℕ) : ℝ) : ℂ))
      _ = ((M : ℝ))⁻¹ := by
        exact congrArg Inv.inv hnorm_real
      _ = (1 : ℝ) / (M : ℝ) := by
        exact (one_div (M : ℝ)).symm
  have hmul_norm :
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊‖ ≤
        ((1 : ℝ) / (M : ℝ)) * (M + 1 : ℝ) := by
    have hnorm_mul :
        ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
              ⌊((M : ℕ) : ℝ)⌋₊‖ =
          ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ *
            ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
              ⌊((M : ℕ) : ℝ)⌋₊‖ :=
      norm_mul (((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))
        (boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          ⌊((M : ℕ) : ℝ)⌋₊)
    have hscaled :
        ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ *
            ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
              ⌊((M : ℕ) : ℝ)⌋₊‖ ≤
          ((1 : ℝ) / (M : ℝ)) * (M + 1 : ℝ) :=
      mul_le_mul
        (le_of_eq hnorm_inv)
        hpartial
        (Nat.cast_nonneg (M + 1))
        (norm_nonneg (((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)))
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ ((1 : ℝ) / (M : ℝ)) * (M + 1 : ℝ))
      hnorm_mul.symm
      hscaled
  have hratio_le_two :
      ((1 : ℝ) / (M : ℝ)) * (M + 1 : ℝ) ≤ 2 := by
    have hM_plus_le : (M + 1 : ℝ) ≤ 2 * (M : ℝ) := by
      have hone_le_M_real : (1 : ℝ) ≤ (M : ℝ) :=
        Nat.cast_le.mpr hM
      calc
        (M + 1 : ℝ) = (M : ℝ) + 1 := by
          exact Nat.cast_add M 1
        _ ≤ (M : ℝ) + (M : ℝ) :=
          add_le_add_left hone_le_M_real (M : ℝ)
        _ = 2 * (M : ℝ) := by
          exact (two_mul (M : ℝ)).symm
    have hdiv_le : (M + 1 : ℝ) / (M : ℝ) ≤ 2 :=
      (div_le_iff₀ hM_real_pos).mpr
        (Eq.subst
          (motive := fun x : ℝ => (M + 1 : ℝ) ≤ x)
          (mul_comm (2 : ℝ) (M : ℝ))
          hM_plus_le)
    have hmul_eq : ((1 : ℝ) / (M : ℝ)) * (M + 1 : ℝ) =
        (M + 1 : ℝ) / (M : ℝ) := by
      calc
        ((1 : ℝ) / (M : ℝ)) * (M + 1 : ℝ) =
            (M + 1 : ℝ) * ((1 : ℝ) / (M : ℝ)) := by
          exact mul_comm ((1 : ℝ) / (M : ℝ)) (M + 1 : ℝ)
        _ = (M + 1 : ℝ) / (M : ℝ) := by
          exact (mul_one_div (M + 1 : ℝ) (M : ℝ)).symm
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ 2)
      hmul_eq.symm
      hdiv_le
  exact le_trans hmul_norm hratio_le_two

/-- The logarithmic-phase derivative magnitude `|t| / u` is decreasing on the
positive real axis. -/
theorem logarithmicPhase_derivativeMagnitude_antitoneOn_positive
    (t : ℝ) :
    AntitoneOn (fun u : ℝ => ‖t‖ / u) (Set.Ioi 0) := by
  intro x hx y hy hxy
  have hreciprocal : (1 : ℝ) / y ≤ (1 : ℝ) / x :=
    one_div_le_one_div_of_le hy hxy
  have hnorm_nonneg : 0 ≤ ‖t‖ :=
    norm_nonneg t
  have hleft : ‖t‖ / y = ‖t‖ * ((1 : ℝ) / y) :=
    div_eq_mul_one_div ‖t‖ y
  have hright : ‖t‖ / x = ‖t‖ * ((1 : ℝ) / x) :=
    div_eq_mul_one_div ‖t‖ x
  exact Eq.subst
    (motive := fun target : ℝ => ‖t‖ / y ≤ target)
    hright.symm
    (Eq.subst
      (motive := fun source : ℝ => source ≤ ‖t‖ * ((1 : ℝ) / x))
      hleft.symm
      (mul_le_mul_of_nonneg_left hreciprocal hnorm_nonneg))

/-- Standard first-derivative test for the concrete logarithmic phase, after
the phase derivative and its monotonicity have been isolated. -/
theorem finiteFirstDerivativeTest_exp_sum_norm_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hphase_deriv :
      ∀ {u : ℝ}, 0 < u →
        deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) u =
          (((-(t : ℂ) * Complex.I) / (u : ℂ)) *
            boundaryLineOnePointRealParam_logarithmicPhaseFunction t u))
    (hphase_deriv_norm :
      ∀ {u : ℝ}, 0 < u →
        ‖deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) u‖ =
          ‖t‖ / u)
    (hphase_deriv_antitone :
      AntitoneOn (fun u : ℝ => ‖t‖ / u) (Set.Ioi 0))
    {x : ℝ}
    (hx : (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) := by
  sorry

/-- Monotone-phase first-derivative test for the concrete logarithmic phase. -/
theorem monotonePhase_firstDerivativeTest_partialSum_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hphase_deriv :
      ∀ {u : ℝ}, 0 < u →
        deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) u =
          (((-(t : ℂ) * Complex.I) / (u : ℂ)) *
            boundaryLineOnePointRealParam_logarithmicPhaseFunction t u))
    (hphase_deriv_norm :
      ∀ {u : ℝ}, 0 < u →
        ‖deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) u‖ =
          ‖t‖ / u)
    (hphase_deriv_antitone :
      AntitoneOn (fun u : ℝ => ‖t‖ / u) (Set.Ioi 0))
    {x : ℝ}
    (hx : (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) := by
  exact
    finiteFirstDerivativeTest_exp_sum_norm_le
      t ht hphase_deriv hphase_deriv_norm hphase_deriv_antitone hx

/-- Standard first-derivative test for the concrete logarithmic phase, after
the phase derivative and its monotonicity have been isolated. -/
theorem firstDerivativeTest_logarithmicPhase_partialSum_bound_of_monotone_phase
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hphase_deriv :
      ∀ {u : ℝ}, 0 < u →
        deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) u =
          (((-(t : ℂ) * Complex.I) / (u : ℂ)) *
            boundaryLineOnePointRealParam_logarithmicPhaseFunction t u))
    (hphase_deriv_norm :
      ∀ {u : ℝ}, 0 < u →
        ‖deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) u‖ =
          ‖t‖ / u)
    (hphase_deriv_antitone :
      AntitoneOn (fun u : ℝ => ‖t‖ / u) (Set.Ioi 0))
    {x : ℝ}
    (hx : (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) := by
  exact
    monotonePhase_firstDerivativeTest_partialSum_bound
      t ht hphase_deriv hphase_deriv_norm hphase_deriv_antitone hx

/-- Standard first-derivative test for the concrete logarithmic phase, after
the phase derivative and its monotonicity have been isolated. -/
theorem standardFirstDerivativeTest_logarithmicPhase_partialSum_bound_of_antitone
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hphase_deriv :
      ∀ {u : ℝ}, 0 < u →
        deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) u =
          (((-(t : ℂ) * Complex.I) / (u : ℂ)) *
            boundaryLineOnePointRealParam_logarithmicPhaseFunction t u))
    (hphase_deriv_norm :
      ∀ {u : ℝ}, 0 < u →
        ‖deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) u‖ =
          ‖t‖ / u)
    (hphase_deriv_antitone :
      AntitoneOn (fun u : ℝ => ‖t‖ / u) (Set.Ioi 0))
    {x : ℝ}
    (hx : (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) := by
  exact
    firstDerivativeTest_logarithmicPhase_partialSum_bound_of_monotone_phase
      t ht hphase_deriv hphase_deriv_norm hphase_deriv_antitone hx

/-- Standard first-derivative test for the concrete logarithmic phase.

This is the standard one-dimensional oscillatory-sum input for the concrete
phase `u ↦ exp (-i t log u)`: the phase derivative is exactly `-it/u`, its
magnitude is `|t|/u`, and the monotone first-derivative argument gives the
displayed partial-sum bound after the canonical cutoff; cf. Titchmarsh,
*The Theory of the Riemann Zeta-function*, §3.5. -/
theorem standardFirstDerivativeTest_logarithmicPhase_partialSum_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hphase_deriv :
      ∀ {u : ℝ}, 0 < u →
        deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) u =
          (((-(t : ℂ) * Complex.I) / (u : ℂ)) *
            boundaryLineOnePointRealParam_logarithmicPhaseFunction t u))
    (hphase_deriv_norm :
      ∀ {u : ℝ}, 0 < u →
        ‖deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) u‖ =
          ‖t‖ / u)
    {x : ℝ}
    (hx : (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) := by
  exact
    standardFirstDerivativeTest_logarithmicPhase_partialSum_bound_of_antitone
      t ht hphase_deriv hphase_deriv_norm
      (logarithmicPhase_derivativeMagnitude_antitoneOn_positive t) hx

/-- Concrete first-derivative/Euler-Maclaurin estimate for the logarithmic
phase. -/
theorem firstDerivativeEulerMaclaurin_logarithmicPhase_partialSum_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hphase_deriv :
      ∀ {u : ℝ}, 0 < u →
        deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) u =
          (((-(t : ℂ) * Complex.I) / (u : ℂ)) *
            boundaryLineOnePointRealParam_logarithmicPhaseFunction t u))
    (hphase_deriv_norm :
      ∀ {u : ℝ}, 0 < u →
        ‖deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) u‖ =
          ‖t‖ / u)
    {x : ℝ}
    (hx : (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) := by
  exact
    standardFirstDerivativeTest_logarithmicPhase_partialSum_bound
      t ht hphase_deriv hphase_deriv_norm hx

/-- Deep analytic owner estimate for logarithmic-phase partial sums.

This is the first-derivative/Euler-Maclaurin bound for
`u ↦ exp (-i t log u)` after the canonical cutoff; cf. Titchmarsh,
*The Theory of the Riemann Zeta-function*, §3.5. -/
theorem logarithmicPhasePartialSum_firstDerivative_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {x : ℝ}
    (hx : (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) := by
  exact
    firstDerivativeEulerMaclaurin_logarithmicPhase_partialSum_bound
      t ht
      (fun hu => boundaryLineOnePointRealParam_logarithmicPhaseFunction_deriv_eq t hu)
      (fun hu => boundaryLineOnePointRealParam_logarithmicPhaseFunction_deriv_norm_eq t hu)
      hx

/-- Standard first-derivative/Euler-Maclaurin estimate for the logarithmic
phase partial sums.

The proof is the classical monotone first-derivative argument for
`φ(x) = -t log x`, with the Euler-Maclaurin endpoint correction; cf.
Titchmarsh, *The Theory of the Riemann Zeta-function*, §3.5. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_norm_le_firstDerivative_core
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {x : ℝ}
    (hx : (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) := by
  exact logarithmicPhasePartialSum_firstDerivative_bound t ht hx

/-- First-derivative/Euler-Maclaurin owner estimate for the logarithmic phase
`u ↦ exp (-i t log u)`.

This is the analytic estimate which replaces any constant-ratio argument.  The
proof chain is the standard monotone first-derivative bound for
`φ(u) = -t log u`, plus the Euler-Maclaurin endpoint correction; cf.
Titchmarsh, *The Theory of the Riemann Zeta-function*, §3.5. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_norm_le_firstDerivative
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {x : ℝ}
    (hx : (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_norm_le_firstDerivative_core
      t ht hx

/-- Euler-Maclaurin / van-der-Corput bound for the logarithmic-phase oscillator.

This is the canonical replacement for the false constant-ratio geometric route:
the proof studies the phase `x ↦ -t log x` and obtains a partial-sum bound
with the necessary long-range `x / |t|` term.  The latter term is unavoidable:
the primitive of `u^{-it}` has size comparable to `x / |t|` for large `x`;
cf. Titchmarsh, *The Theory of the Riemann Zeta-function*, §3.5. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_norm_le_vdc
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {x : ℝ}
    (hx : (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_norm_le_firstDerivative
      t ht hx

/-- First conjunct of the finite Abel package: the endpoint partial sum at `M`
is exactly the first-derivative estimate at the real endpoint `M`. -/
theorem logarithmicPhase_firstDerivative_finiteAbel_rightPartial_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊((M : ℕ) : ℝ)⌋₊‖ ≤
      8 * ((((M : ℕ) : ℝ) / ‖t‖) + Real.sqrt (1 + ‖t‖)) *
        Real.log (2 + ((M : ℕ) : ℝ)) := by
  have hreal :
      ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) ≤ ((M : ℕ) : ℝ) :=
    Nat.cast_le.mpr hNM
  exact logarithmicPhasePartialSum_firstDerivative_bound t ht hreal

/-- Sharper endpoint estimate in the logarithmic-phase partial-summation
package.

This is not obtained by multiplying the coarse primitive bound by the reciprocal
endpoint weights.  It is the endpoint part of the oscillatory
Euler-Maclaurin/partial-summation argument, where cancellation at the cutoff and
right endpoint is retained. -/
theorem oscillatoryEulerMaclaurin_logarithmicPhase_endpoint_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊‖ +
        ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖) := by
  have hcutoff_one : 1 ≤ ⌊2 + ‖t‖⌋₊ :=
    Nat.succ_le_of_lt (boundaryLineOnePointRealParam_cutoff_pos t)
  have hM_one : 1 ≤ M :=
    le_trans hcutoff_one hNM
  have hright :
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊‖ ≤ 2 :=
    logarithmicPhase_endpoint_trivial_bound t hM_one
  have hleft :
      ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤ 2 :=
    logarithmicPhase_endpoint_trivial_bound t hcutoff_one
  have hsum_le_four :
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊‖ +
        ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤
        4 := by
    have htwo_add_two : (2 : ℝ) + 2 = 4 := by
      rfl
    exact (add_le_add hright hleft).trans_eq htwo_add_two
  have hlog_two : (1 : ℝ) ≤ Real.log (2 + ‖t‖) :=
    one_le_log_two_add_norm_of_one_le_norm ht
  have htwo_add_le_three_add : 2 + ‖t‖ ≤ 3 + ‖t‖ := by
    exact add_le_add_right (show (2 : ℝ) ≤ 3 by
      calc
        (2 : ℝ) ≤ 2 + 1 := le_add_of_nonneg_right zero_le_one
        _ = 3 := rfl) ‖t‖
  have hlog_mono :
      Real.log (2 + ‖t‖) ≤ Real.log (3 + ‖t‖) := by
    have hpos : 0 < 2 + ‖t‖ :=
      lt_of_lt_of_le zero_lt_one (one_le_two_add_norm t)
    exact Real.log_le_log hpos htwo_add_le_three_add
  have hlog_one : (1 : ℝ) ≤ Real.log (3 + ‖t‖) :=
    le_trans hlog_two hlog_mono
  have height_nonneg : 0 ≤ Real.log (3 + ‖t‖) :=
    le_trans zero_le_one hlog_one
  have hfour_le :
      (4 : ℝ) ≤ 2 + 8 * Real.log (3 + ‖t‖) := by
    have htwo_le_eight_log : (2 : ℝ) ≤ 8 * Real.log (3 + ‖t‖) := by
      have htwo_le_eight : (2 : ℝ) ≤ 8 := by
        calc
          (2 : ℝ) ≤ 2 + 6 := le_add_of_nonneg_right (show (0 : ℝ) ≤ 6 by
            calc
              (0 : ℝ) ≤ 1 := zero_le_one
              _ ≤ 6 := by
                calc
                  (1 : ℝ) ≤ 1 + 5 := le_add_of_nonneg_right (show (0 : ℝ) ≤ 5 by
                    calc
                      (0 : ℝ) ≤ 1 := zero_le_one
                      _ ≤ 5 := by
                        calc
                          (1 : ℝ) ≤ 1 + 4 := le_add_of_nonneg_right (show (0 : ℝ) ≤ 4 by
                            calc
                              (0 : ℝ) ≤ 1 := zero_le_one
                              _ ≤ 4 := by
                                calc
                                  (1 : ℝ) ≤ 1 + 3 := le_add_of_nonneg_right (show (0 : ℝ) ≤ 3 by
                                    calc
                                      (0 : ℝ) ≤ 1 := zero_le_one
                                      _ ≤ 3 := by
                                        calc
                                          (1 : ℝ) ≤ 1 + 2 := le_add_of_nonneg_right (le_of_lt two_pos)
                                          _ = 3 := rfl)
                                  _ = 4 := rfl)
                          _ = 5 := rfl)
                  _ = 6 := rfl)
          _ = 8 := rfl
      calc
        (2 : ℝ) ≤ 8 * 1 := by
          exact Eq.subst (motive := fun x : ℝ => 2 ≤ x) (mul_one (8 : ℝ)).symm htwo_le_eight
        _ ≤ 8 * Real.log (3 + ‖t‖) :=
          mul_le_mul_of_nonneg_left hlog_one
            (show (0 : ℝ) ≤ 8 by
              calc
                (0 : ℝ) ≤ 1 := zero_le_one
                _ ≤ 8 := le_trans zero_le_one htwo_le_eight)
    calc
      (4 : ℝ) = 2 + 2 := rfl
      _ ≤ 2 + 8 * Real.log (3 + ‖t‖) :=
        add_le_add_left htwo_le_eight_log 2
  exact le_trans hsum_le_four hfour_le

/-- Endpoint arithmetic after the logarithmic-phase first-derivative
Euler-Maclaurin estimate.

The two terms are the reciprocal endpoint contributions at the right endpoint
`M` and at the canonical cutoff `⌊2 + |t|⌋₊`.  The analytic input is only the
first-derivative primitive estimate; this theorem owns the subsequent
reciprocal-weight and cutoff arithmetic.  Cf. Apostol, *Introduction to
Analytic Number Theory*, partial summation, and Titchmarsh, Ch. 3. -/
theorem eulerMaclaurin_logarithmicPhase_finiteAbel_endpoint_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊‖ +
        ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖) := by
  exact oscillatoryEulerMaclaurin_logarithmicPhase_endpoint_bound t ht hNM

/-- The reciprocal derivative has the expected positive variation density on
the post-cutoff interval. -/
theorem reciprocalDerivative_norm_eq_on_positive_interval
    {a b x : ℝ}
    (ha : 0 < a)
    (hx : x ∈ Set.Icc a b) :
    ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x‖ =
      (1 : ℝ) / x ^ 2 := by
  have hx_pos : 0 < x :=
    lt_of_lt_of_le ha hx.1
  exact complexReciprocalOfReal_deriv_norm_eq hx_pos

/-- Concrete reciprocal variation bound on a finite post-cutoff interval.

This is the non-oscillatory real-variable input used by partial summation:
the total variation density of `u ↦ 1 / u` is `1/u^2` on the positive interval
starting at the canonical cutoff. -/
theorem concreteReciprocalVariation_density_bound_on_cutoff_interval
    (t : ℝ)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∀ x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
      ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x‖ =
        (1 : ℝ) / x ^ 2 := by
  intro x hx
  have hcutoff_pos : 0 < (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr (boundaryLineOnePointRealParam_cutoff_pos t)
  exact reciprocalDerivative_norm_eq_on_positive_interval hcutoff_pos hx

/-- Pointwise scalar majorization of the reciprocal-density integrand on the
post-cutoff interval. -/
theorem reciprocalDensityIntegral_pointwise_norm_le_scalar_majorant
    (t : ℝ)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hreciprocal_density :
      ∀ x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x‖ =
          (1 : ℝ) / x ^ 2) :
    ∀ x ∈ Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
      ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) := by
  intro x hx
  have hx_Icc :
      x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ) :=
    ⟨le_of_lt hx.1, hx.2⟩
  have hleft :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ x :=
    le_of_lt hx.1
  have hdensity :
      ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x‖ =
        (1 : ℝ) / x ^ 2 :=
    hreciprocal_density x hx_Icc
  have hpartial_x :
      ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) :=
    hpartial hleft
  have hnorm_mul :
      ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ =
        ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x‖ *
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ :=
    norm_mul
      (deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x)
      (boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊)
  have hdensity_nonneg :
      0 ≤ (1 : ℝ) / x ^ 2 := by
    exact Eq.subst
      (motive := fun u : ℝ => 0 ≤ u)
      hdensity
      (norm_nonneg (deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x))
  have hmul :
      ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x‖ *
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) :=
    Eq.subst
      (motive := fun u : ℝ =>
        u * ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
          ((1 : ℝ) / x ^ 2) *
            (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)))
      hdensity.symm
      (mul_le_mul_of_nonneg_left hpartial_x hdensity_nonneg)
  exact Eq.subst
    (motive := fun u : ℝ =>
      u ≤ ((1 : ℝ) / x ^ 2) *
        (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)))
    hnorm_mul.symm
    hmul

/-- Measure-theoretic norm domination for the reciprocal-density integral from
the pointwise scalar majorant. -/
theorem reciprocalDensityIntegral_norm_le_scalar_majorant_of_pointwise
    (t : ℝ)
    {M : ℕ}
    (hpointwise :
      ∀ x ∈ Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
          ((1 : ℝ) / x ^ 2) *
            (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) := by
  let s : Set ℝ :=
    Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ)
  let f : ℝ → ℂ := fun x =>
    deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
      boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊
  let g : ℝ → ℝ := fun x =>
    ((1 : ℝ) / x ^ 2) *
      (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
  have hg : Integrable g (volume.restrict s) := by
    fun_prop
  have hbound : ∀ᵐ x ∂volume.restrict s, ‖f x‖ ≤ g x :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun x hx => hpointwise x hx)
  exact norm_integral_le_of_norm_le hg hbound

/-- Bochner norm domination for the reciprocal-density logarithmic-phase
integral. -/
theorem reciprocalDensityIntegral_norm_le_scalar_majorant
    (t : ℝ)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hreciprocal_density :
      ∀ x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x‖ =
          (1 : ℝ) / x ^ 2) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) := by
  exact
    reciprocalDensityIntegral_norm_le_scalar_majorant_of_pointwise
      t
      (reciprocalDensityIntegral_pointwise_norm_le_scalar_majorant
        t hpartial hNM hreciprocal_density)

/-- The canonical Abel/Euler-Maclaurin cutoff is positive as a real endpoint. -/
theorem scalarReciprocalDensity_cutoff_real_pos
    (t : ℝ) :
    0 < (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) := by
  exact Nat.cast_pos.mpr (boundaryLineOnePointRealParam_cutoff_pos t)

/-- The canonical Abel/Euler-Maclaurin cutoff is at least two as a real
endpoint. -/
theorem scalarReciprocalDensity_two_le_cutoff_real
    (t : ℝ) :
    (2 : ℝ) ≤ (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) := by
  exact Nat.cast_le.mpr (boundaryLineOnePointRealParam_two_le_cutoff t)

/-- Points in the post-cutoff interval are positive. -/
theorem scalarReciprocalDensity_Ioc_point_pos
    (t : ℝ)
    {M : ℕ}
    {x : ℝ}
    (hx :
      x ∈ Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ)) :
    0 < x := by
  exact lt_trans (scalarReciprocalDensity_cutoff_real_pos t) hx.1

/-- Points in the closed post-cutoff interval are positive. -/
theorem scalarReciprocalDensity_Icc_point_pos
    (t : ℝ)
    {M : ℕ}
    {x : ℝ}
    (hx :
      x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ)) :
    0 < x := by
  exact lt_of_lt_of_le (scalarReciprocalDensity_cutoff_real_pos t) hx.1

/-- Positivity of the shifted logarithm on the scalar-calculus range. -/
theorem real_log_two_add_nonneg_of_two_le
    {x : ℝ}
    (hx : (2 : ℝ) ≤ x) :
    0 ≤ Real.log (2 + x) := by
  have hone_le_two : (1 : ℝ) ≤ 2 := by
    calc
      (1 : ℝ) ≤ 1 + 1 := le_add_of_nonneg_right zero_le_one
      _ = 2 := by
        rfl
  have htwo_le_two_add : (2 : ℝ) ≤ 2 + x :=
    le_trans hx (le_add_of_nonneg_left (show (0 : ℝ) ≤ 2 by
      calc
        (0 : ℝ) ≤ 1 := zero_le_one
        _ ≤ 2 := hone_le_two))
  exact Real.log_nonneg (le_trans hone_le_two htwo_le_two_add)

/-- On `2 ≤ x`, `log(2+x)/x` is bounded by the derivative density of
`(log(2+x))²`. -/
theorem real_log_two_add_div_self_le_log_sq_derivative_density
    {x : ℝ}
    (hx : (2 : ℝ) ≤ x) :
    Real.log (2 + x) / x ≤
      2 * Real.log (2 + x) / (2 + x) := by
  have hx_pos : 0 < x :=
    lt_of_lt_of_le zero_lt_two hx
  have hshift_pos : 0 < 2 + x :=
    add_pos_of_pos_of_nonneg zero_lt_two (le_trans (show (0 : ℝ) ≤ 2 by
      exact le_of_lt zero_lt_two) hx)
  have hlog_nonneg : 0 ≤ Real.log (2 + x) :=
    real_log_two_add_nonneg_of_two_le hx
  have hreciprocal :
      (1 : ℝ) / x ≤ 2 / (2 + x) := by
    have hmul :
        (2 + x) ≤ 2 * x := by
      calc
        2 + x ≤ x + x :=
          add_le_add_right hx x
        _ = 2 * x := by
          exact (two_mul x).symm
    exact (div_le_div_iff₀ hx_pos hshift_pos).mpr hmul
  have hscaled :
      Real.log (2 + x) * ((1 : ℝ) / x) ≤
        Real.log (2 + x) * (2 / (2 + x)) :=
    mul_le_mul_of_nonneg_left hreciprocal hlog_nonneg
  exact Eq.subst
    (motive := fun y : ℝ => y ≤ 2 * Real.log (2 + x) / (2 + x))
    (div_eq_mul_one_div (Real.log (2 + x)) x).symm
    (Eq.subst
      (motive := fun y : ℝ =>
        Real.log (2 + x) * (2 / (2 + x)) ≤ y)
      (by
        calc
          2 * Real.log (2 + x) / (2 + x) =
              (2 * Real.log (2 + x)) * ((1 : ℝ) / (2 + x)) := by
            exact div_eq_mul_one_div (2 * Real.log (2 + x)) (2 + x)
          _ = Real.log (2 + x) * (2 * ((1 : ℝ) / (2 + x))) := by
            ac_rfl
          _ = Real.log (2 + x) * (2 / (2 + x)) := by
            exact congrArg
              (fun y : ℝ => Real.log (2 + x) * y)
              (div_eq_mul_one_div 2 (2 + x)).symm)
      hscaled)

/-- Derivative of the square of the shifted logarithm. -/
theorem real_hasDerivAt_log_two_add_sq
    {x : ℝ}
    (hx : (0 : ℝ) < 2 + x) :
    HasDerivAt
      (fun y : ℝ => (Real.log (2 + y)) ^ 2)
      (2 * Real.log (2 + x) / (2 + x))
      x := by
  have hshift_ne : 2 + x ≠ 0 :=
    ne_of_gt hx
  have hshift :
      HasDerivAt (fun y : ℝ => 2 + y) 1 x :=
    (hasDerivAt_id x).const_add 2
  have hlog :
      HasDerivAt (fun y : ℝ => Real.log (2 + y)) ((2 + x)⁻¹) x :=
    (hasDerivAt_log hshift_ne).comp x hshift
  have hpow :
      HasDerivAt
        (fun y : ℝ => (Real.log (2 + y)) ^ 2)
        (((2 : ℝ) * (Real.log (2 + x)) ^ (2 - 1)) * ((2 + x)⁻¹))
        x :=
    (hasDerivAt_pow 2 (Real.log (2 + x))).comp x hlog
  have hcoeff :
      ((2 : ℝ) * (Real.log (2 + x)) ^ (2 - 1)) * ((2 + x)⁻¹) =
        2 * Real.log (2 + x) / (2 + x) := by
    calc
      ((2 : ℝ) * (Real.log (2 + x)) ^ (2 - 1)) * ((2 + x)⁻¹) =
          (2 * Real.log (2 + x)) * ((2 + x)⁻¹) := by
        rfl
      _ = 2 * Real.log (2 + x) / (2 + x) := by
        exact (div_eq_mul_inv (2 * Real.log (2 + x)) (2 + x)).symm
  exact hcoeff ▸ hpow

/-- Integral evaluation for the shifted-log square derivative density. -/
theorem real_intervalIntegral_log_sq_derivative_density_eq_sub
    {a b : ℝ}
    (ha : (2 : ℝ) ≤ a)
    (hab : a ≤ b) :
    ∫ x in a..b, 2 * Real.log (2 + x) / (2 + x) =
      (Real.log (2 + b)) ^ 2 - (Real.log (2 + a)) ^ 2 := by
  let F : ℝ → ℝ := fun x => (Real.log (2 + x)) ^ 2
  let G : ℝ → ℝ := fun x => 2 * Real.log (2 + x) / (2 + x)
  have hderiv :
      ∀ x ∈ Set.uIcc a b, HasDerivAt F (G x) x := by
    intro x hx
    have hmin_left : min a b = a :=
      min_eq_left hab
    have hax_min : min a b ≤ x :=
      (Set.mem_uIcc.mp hx).1
    have hax : a ≤ x :=
      Eq.subst
        (motive := fun y : ℝ => y ≤ x)
        hmin_left
        hax_min
    have htwo_le_x : (2 : ℝ) ≤ x :=
      le_trans ha hax
    have hpos : (0 : ℝ) < 2 + x :=
      add_pos_of_pos_of_nonneg zero_lt_two
        (le_trans (show (0 : ℝ) ≤ 2 by exact le_of_lt zero_lt_two) htwo_le_x)
    exact real_hasDerivAt_log_two_add_sq hpos
  have hint : IntervalIntegrable G volume a b := by
    fun_prop
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint

theorem real_integral_Ioc_log_sq_derivative_density_le_endpoint_sq
    {a b : ℝ}
    (ha : (2 : ℝ) ≤ a)
    (hab : a ≤ b) :
    ∫ x in Set.Ioc a b, 2 * Real.log (2 + x) / (2 + x) ≤
      (Real.log (2 + b)) ^ 2 := by
  have hset_interval :
      ∫ x in Set.Ioc a b, 2 * Real.log (2 + x) / (2 + x) =
        ∫ x in a..b, 2 * Real.log (2 + x) / (2 + x) :=
    (intervalIntegral.integral_of_le hab).symm
  have heval :
      ∫ x in a..b, 2 * Real.log (2 + x) / (2 + x) =
        (Real.log (2 + b)) ^ 2 - (Real.log (2 + a)) ^ 2 :=
    real_intervalIntegral_log_sq_derivative_density_eq_sub ha hab
  have hlower_nonneg : 0 ≤ (Real.log (2 + a)) ^ 2 :=
    sq_nonneg (Real.log (2 + a))
  have hsub :
      (Real.log (2 + b)) ^ 2 - (Real.log (2 + a)) ^ 2 ≤
        (Real.log (2 + b)) ^ 2 :=
    sub_le_self ((Real.log (2 + b)) ^ 2) hlower_nonneg
  exact Eq.subst
    (motive := fun y : ℝ => y ≤ (Real.log (2 + b)) ^ 2)
    hset_interval.symm
    (le_trans (le_of_eq heval) hsub)

/-- Fundamental-theorem comparison for the finite `log(2+x)/x` integral. -/
theorem real_integral_Ioc_log_two_add_div_self_le_log_endpoint_sq_of_pointwise
    {a b : ℝ}
    (ha : (2 : ℝ) ≤ a)
    (hab : a ≤ b)
    (hpointwise :
      ∀ x ∈ Set.Ioc a b,
        Real.log (2 + x) / x ≤
          2 * Real.log (2 + x) / (2 + x)) :
    ∫ x in Set.Ioc a b, Real.log (2 + x) / x ≤
      (Real.log (2 + b)) ^ 2 := by
  let f : ℝ → ℝ := fun x => Real.log (2 + x) / x
  let g : ℝ → ℝ := fun x => 2 * Real.log (2 + x) / (2 + x)
  have hf : Integrable f (volume.restrict (Set.Ioc a b)) := by
    fun_prop
  have hg : Integrable g (volume.restrict (Set.Ioc a b)) := by
    fun_prop
  have hle : f ≤ᵐ[volume.restrict (Set.Ioc a b)] g :=
    (ae_restrict_mem measurableSet_Ioc).mono hpointwise
  have hmono :
      ∫ x in Set.Ioc a b, Real.log (2 + x) / x ≤
        ∫ x in Set.Ioc a b, 2 * Real.log (2 + x) / (2 + x) :=
    integral_mono_ae hf hg hle
  exact le_trans hmono
    (real_integral_Ioc_log_sq_derivative_density_le_endpoint_sq ha hab)

/-- Canonical real-variable comparison for the finite `log(2+x)/x` integral.

On `2 ≤ a ≤ b`, the integrand is dominated by the derivative of
`(Real.log (2+x))^2`, since `1/x ≤ 2/(2+x)` and `Real.log (2+x) ≥ 0`.
This is the reusable scalar calculus theorem; the zeta cutoff theorem below is
only an endpoint instantiation. -/
theorem real_integral_Ioc_log_two_add_div_self_le_log_endpoint_sq
    {a b : ℝ}
    (ha : (2 : ℝ) ≤ a)
    (hab : a ≤ b) :
    ∫ x in Set.Ioc a b, Real.log (2 + x) / x ≤
      (Real.log (2 + b)) ^ 2 := by
  exact
    real_integral_Ioc_log_two_add_div_self_le_log_endpoint_sq_of_pointwise
      ha hab
      (fun x hx =>
        real_log_two_add_div_self_le_log_sq_derivative_density
          (le_trans ha (le_of_lt hx.1)))

/-- Nonnegativity of the reciprocal-density scalar integrand after `2`. -/
theorem real_log_two_add_div_sq_nonneg_of_two_le
    {x : ℝ}
    (hx : (2 : ℝ) ≤ x) :
    0 ≤ Real.log (2 + x) / x ^ 2 := by
  have hlog_nonneg : 0 ≤ Real.log (2 + x) :=
    real_log_two_add_nonneg_of_two_le hx
  have hx_pos : 0 < x :=
    lt_of_lt_of_le zero_lt_two hx
  have hx_sq_nonneg : 0 ≤ x ^ 2 :=
    sq_nonneg x
  exact div_nonneg hlog_nonneg hx_sq_nonneg

/-- Concrete finite integration-by-parts identity for
`u(x)=log(2+x)` and `v(x)=-1/x` on `[2,b]`. -/
theorem real_intervalIntegral_log_two_add_mul_inv_sq_eq_by_parts_core
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    let u : ℝ → ℝ := fun x => Real.log (2 + x)
    let v : ℝ → ℝ := fun x => -(1 / x)
    let u' : ℝ → ℝ := fun x => 1 / (2 + x)
    let v' : ℝ → ℝ := fun x => 1 / x ^ 2
    ∫ x in (2 : ℝ)..b, u x * v' x =
      u b * v b - u 2 * v 2 -
        ∫ x in (2 : ℝ)..b, u' x * v x := by
  let u : ℝ → ℝ := fun x => Real.log (2 + x)
  let v : ℝ → ℝ := fun x => -(1 / x)
  let u' : ℝ → ℝ := fun x => 1 / (2 + x)
  let v' : ℝ → ℝ := fun x => 1 / x ^ 2
  have hu :
      ∀ x ∈ [[(2 : ℝ), b]], HasDerivAt u (u' x) x := by
    intro x hx
    have hleft : (2 : ℝ) ≤ x :=
      (Set.mem_uIcc.mp hx).1
    have htwo_add_pos : 0 < 2 + x :=
      add_pos_of_pos_of_nonneg zero_lt_two
        (le_trans (le_of_lt zero_lt_two) hleft)
    have hbase : HasDerivAt (fun y : ℝ => 2 + y) 1 x :=
      (hasDerivAt_id x).const_add 2
    have hlog :
        HasDerivAt (fun y : ℝ => Real.log (2 + y)) ((2 + x)⁻¹) x :=
      Real.hasDerivAt_log htwo_add_pos.ne'.symm |>.comp x hbase
    have hnormal : (2 + x)⁻¹ = 1 / (2 + x) :=
      (one_div (2 + x)).symm
    exact Eq.subst
      (motive := fun D : ℝ => HasDerivAt u D x)
      hnormal
      hlog
  have hv :
      ∀ x ∈ [[(2 : ℝ), b]], HasDerivAt v (v' x) x := by
    intro x hx
    have hleft : (2 : ℝ) ≤ x :=
      (Set.mem_uIcc.mp hx).1
    have hx_ne : x ≠ 0 :=
      ne_of_gt (lt_of_lt_of_le zero_lt_two hleft)
    have hinv :
        HasDerivAt (fun y : ℝ => y⁻¹) (-(x ^ 2)⁻¹) x :=
      hasDerivAt_inv hx_ne
    have hneg :
        HasDerivAt (fun y : ℝ => -(y⁻¹)) (- (-(x ^ 2)⁻¹)) x :=
      hinv.neg
    have hfun :
        (fun y : ℝ => -(y⁻¹)) = v := by
      exact funext
        (fun y : ℝ =>
          congrArg Neg.neg (one_div y))
    have hnormal : - (-(x ^ 2)⁻¹) = 1 / x ^ 2 := by
      calc
        - (-(x ^ 2)⁻¹) = (x ^ 2)⁻¹ := neg_neg ((x ^ 2)⁻¹)
        _ = 1 / x ^ 2 := (one_div (x ^ 2)).symm
    exact Eq.subst
      (motive := fun D : ℝ => HasDerivAt v D x)
      hnormal
      (Eq.subst
        (motive := fun F : ℝ → ℝ => HasDerivAt F (- (-(x ^ 2)⁻¹)) x)
        hfun
        hneg)
  have hu_int : IntervalIntegrable u' volume (2 : ℝ) b := by
    fun_prop
  have hv_int : IntervalIntegrable v' volume (2 : ℝ) b := by
    fun_prop
  exact intervalIntegral.integral_mul_deriv_eq_deriv_mul
    hu hv hu_int hv_int

/-- Algebraic normalization of the finite by-parts RHS for
`u(x)=log(2+x)` and `v(x)=-1/x`. -/
theorem real_by_parts_log_two_add_endpoint_normalize
    {b : ℝ} :
    let u : ℝ → ℝ := fun x => Real.log (2 + x)
    let v : ℝ → ℝ := fun x => -(1 / x)
    u b * v b - u 2 * v 2 =
      (-Real.log (2 + b) / b) - (-Real.log 4 / 2) := by
  let u : ℝ → ℝ := fun x => Real.log (2 + x)
  let v : ℝ → ℝ := fun x => -(1 / x)
  have hvb : v b = -(1 / b) := rfl
  have hv2 : v 2 = -(1 / (2 : ℝ)) := rfl
  have hu2 : u 2 = Real.log 4 := by
    exact congrArg Real.log (show (2 : ℝ) + 2 = 4 by rfl)
  have hleft :
      u b * v b = -Real.log (2 + b) / b := by
    calc
      u b * v b = Real.log (2 + b) * (-(1 / b)) := rfl
      _ = -(Real.log (2 + b) * (1 / b)) :=
        (mul_neg (Real.log (2 + b)) (1 / b))
      _ = -(Real.log (2 + b) / b) := by
        exact congrArg Neg.neg
          (div_eq_mul_one_div (Real.log (2 + b)) b).symm
      _ = -Real.log (2 + b) / b :=
        (neg_div (Real.log (2 + b)) b).symm
  have hright :
      u 2 * v 2 = -Real.log 4 / 2 := by
    calc
      u 2 * v 2 = Real.log 4 * (-(1 / (2 : ℝ))) := by
        exact congrArg₂ (fun a c : ℝ => a * c) hu2 hv2
      _ = -(Real.log 4 * (1 / (2 : ℝ))) :=
        (mul_neg (Real.log 4) (1 / (2 : ℝ)))
      _ = -(Real.log 4 / 2) := by
        exact congrArg Neg.neg
          (div_eq_mul_one_div (Real.log 4) (2 : ℝ)).symm
      _ = -Real.log 4 / 2 :=
        (neg_div (Real.log 4) (2 : ℝ)).symm
  exact congrArg₂ (fun a c : ℝ => a - c) hleft hright

/-- Integral sign-change normalization for the finite by-parts remainder. -/
theorem real_intervalIntegral_log_two_add_by_parts_remainder_normalize
    {b : ℝ} :
    let u' : ℝ → ℝ := fun x => 1 / (2 + x)
    let v : ℝ → ℝ := fun x => -(1 / x)
    -(∫ x in (2 : ℝ)..b, u' x * v x) =
      ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) := by
  let u' : ℝ → ℝ := fun x => 1 / (2 + x)
  let v : ℝ → ℝ := fun x => -(1 / x)
  let r : ℝ → ℝ := fun x => (1 : ℝ) / (x * (2 + x))
  have hpoint : (fun x : ℝ => u' x * v x) = (fun x : ℝ => -r x) := by
    exact funext
      (fun x : ℝ =>
        calc
          u' x * v x = (1 / (2 + x)) * (-(1 / x)) := rfl
          _ = -((1 / (2 + x)) * (1 / x)) :=
            mul_neg (1 / (2 + x)) (1 / x)
          _ = -((1 : ℝ) / (x * (2 + x))) := by
            exact congrArg Neg.neg
              (one_div_mul_one_div_rev (a := (2 + x)) (b := x))
          _ = -r x := rfl)
  have hintegral :
      ∫ x in (2 : ℝ)..b, u' x * v x =
        ∫ x in (2 : ℝ)..b, -r x :=
    congrArg
      (fun f : ℝ → ℝ => ∫ x in (2 : ℝ)..b, f x)
      hpoint
  calc
    -(∫ x in (2 : ℝ)..b, u' x * v x) =
        -(∫ x in (2 : ℝ)..b, -r x) := by
      exact congrArg Neg.neg hintegral
    _ = - (-(∫ x in (2 : ℝ)..b, r x)) := by
      exact congrArg Neg.neg (intervalIntegral.integral_neg r)
    _ = ∫ x in (2 : ℝ)..b, r x :=
      neg_neg (∫ x in (2 : ℝ)..b, r x)

theorem real_intervalIntegral_log_two_add_mul_inv_sq_by_parts_rhs_normalize
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    let u : ℝ → ℝ := fun x => Real.log (2 + x)
    let v : ℝ → ℝ := fun x => -(1 / x)
    let u' : ℝ → ℝ := fun x => 1 / (2 + x)
    u b * v b - u 2 * v 2 -
        ∫ x in (2 : ℝ)..b, u' x * v x =
      ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
        ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) := by
  let u : ℝ → ℝ := fun x => Real.log (2 + x)
  let v : ℝ → ℝ := fun x => -(1 / x)
  let u' : ℝ → ℝ := fun x => 1 / (2 + x)
  have hendpoint :
      u b * v b - u 2 * v 2 =
        (-Real.log (2 + b) / b) - (-Real.log 4 / 2) :=
    real_by_parts_log_two_add_endpoint_normalize
  have hremainder :
      -(∫ x in (2 : ℝ)..b, u' x * v x) =
        ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) :=
    real_intervalIntegral_log_two_add_by_parts_remainder_normalize
  calc
    u b * v b - u 2 * v 2 -
        ∫ x in (2 : ℝ)..b, u' x * v x =
        (u b * v b - u 2 * v 2) +
          -(∫ x in (2 : ℝ)..b, u' x * v x) := by
      exact (sub_eq_add_neg
        (u b * v b - u 2 * v 2)
        (∫ x in (2 : ℝ)..b, u' x * v x))
    _ =
        ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
          -(∫ x in (2 : ℝ)..b, u' x * v x) := by
      exact congrArg
        (fun z : ℝ => z + -(∫ x in (2 : ℝ)..b, u' x * v x))
        hendpoint
    _ =
        ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
          ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) := by
      exact congrArg
        (fun z : ℝ => ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) + z)
        hremainder

theorem real_intervalIntegral_log_two_add_mul_inv_sq_eq_by_parts
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in (2 : ℝ)..b, Real.log (2 + x) * (1 / x ^ 2) =
      ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
        ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) := by
  let u : ℝ → ℝ := fun x => Real.log (2 + x)
  let v : ℝ → ℝ := fun x => -(1 / x)
  let u' : ℝ → ℝ := fun x => 1 / (2 + x)
  let v' : ℝ → ℝ := fun x => 1 / x ^ 2
  have hparts :
      ∫ x in (2 : ℝ)..b, u x * v' x =
        u b * v b - u 2 * v 2 -
          ∫ x in (2 : ℝ)..b, u' x * v x :=
    real_intervalIntegral_log_two_add_mul_inv_sq_eq_by_parts_core hb
  have hnormal :
      u b * v b - u 2 * v 2 -
          ∫ x in (2 : ℝ)..b, u' x * v x =
        ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
          ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) :=
    real_intervalIntegral_log_two_add_mul_inv_sq_by_parts_rhs_normalize hb
  exact Eq.trans hparts hnormal

/-- Algebraic normalization of the scalar reciprocal-density integrand. -/
theorem real_integral_Ioc_log_two_add_div_sq_eq_mul_inv_sq
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 =
      ∫ x in (2 : ℝ)..b, Real.log (2 + x) * (1 / x ^ 2) := by
  have hset :
      ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 =
        ∫ x in (2 : ℝ)..b, Real.log (2 + x) / x ^ 2 :=
    (intervalIntegral.integral_of_le hb).symm
  have hpoint :
      (fun x : ℝ => Real.log (2 + x) / x ^ 2) =
        (fun x : ℝ => Real.log (2 + x) * (1 / x ^ 2)) := by
    exact funext
      (fun x : ℝ =>
        div_eq_mul_one_div (Real.log (2 + x)) (x ^ 2))
  exact Eq.trans hset
    (congrArg
      (fun f : ℝ → ℝ => ∫ x in (2 : ℝ)..b, f x)
      hpoint)

/-- Interval/set normalization for the by-parts remainder term. -/
theorem real_intervalIntegral_one_div_mul_two_add_eq_Ioc
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) =
      ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) := by
  exact intervalIntegral.integral_of_le hb

/-- Partial-fraction identity for the finite scalar reciprocal-density
integrand. -/
theorem real_one_div_mul_two_add_eq_half_sub
    {x : ℝ}
    (hx : x ≠ 0)
    (hx_two : 2 + x ≠ 0) :
    (1 : ℝ) / (x * (2 + x)) =
      (1 / 2 : ℝ) * ((1 : ℝ) / x - (1 : ℝ) / (2 + x)) := by
  sorry

/-- Antiderivative evaluation for the reciprocal-density scalar integrand.

The antiderivative is `(log x - log (2 + x)) / 2`; the lower endpoint is
`2`, where the value is `(log 2 - log 4) / 2`. -/
theorem real_intervalIntegral_one_div_mul_two_add_eq_logs_interval_core
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) =
      ((Real.log b - Real.log (2 + b)) -
          (Real.log 2 - Real.log 4)) / 2 := by
  sorry

/-- Endpoint evaluation of the interval integral of the scalar reciprocal
density in interval-integral notation. -/
theorem real_intervalIntegral_one_div_mul_two_add_eq_logs_interval
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) =
      ((Real.log b - Real.log (2 + b)) -
          (Real.log 2 - Real.log 4)) / 2 := by
  exact real_intervalIntegral_one_div_mul_two_add_eq_logs_interval_core hb

/-- Integration-by-parts identity for the finite scalar tail
`∫ log(2+x)/x²`.

This is the exact finite identity behind the tail bound:
the antiderivative of the main part is `-log(2+x)/x`, and the remaining
positive term is `1/(x*(2+x))`. -/
theorem real_integral_Ioc_log_two_add_div_sq_eq_by_parts
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 =
      ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
        ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) := by
  have hmain :
      ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 =
        ∫ x in (2 : ℝ)..b, Real.log (2 + x) * (1 / x ^ 2) :=
    real_integral_Ioc_log_two_add_div_sq_eq_mul_inv_sq hb
  have hparts :
      ∫ x in (2 : ℝ)..b, Real.log (2 + x) * (1 / x ^ 2) =
        ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
          ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) :=
    real_intervalIntegral_log_two_add_mul_inv_sq_eq_by_parts hb
  have hremainder :
      ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) =
        ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) :=
    real_intervalIntegral_one_div_mul_two_add_eq_Ioc hb
  exact Eq.trans hmain
    (Eq.trans hparts
      (congrArg
        (fun R : ℝ =>
          ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) + R)
        hremainder))

/-- Elementary endpoint bound for the finite scalar tail after the
integration-by-parts identity. -/
theorem real_intervalIntegral_one_div_mul_two_add_eq_logs
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) =
      ((Real.log b - Real.log (2 + b)) -
          (Real.log 2 - Real.log 4)) / 2 := by
  have hset :
      ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) =
        ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) :=
    (intervalIntegral.integral_of_le hb).symm
  have heval :
      ∫ x in (2 : ℝ)..b, (1 : ℝ) / (x * (2 + x)) =
        ((Real.log b - Real.log (2 + b)) -
            (Real.log 2 - Real.log 4)) / 2 :=
    real_intervalIntegral_one_div_mul_two_add_eq_logs_interval hb
  exact Eq.trans hset heval

theorem real_intervalIntegral_one_div_mul_two_add_le_half_log_two
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) ≤
      Real.log 2 / 2 := by
  have heval :
      ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) =
        ((Real.log b - Real.log (2 + b)) -
            (Real.log 2 - Real.log 4)) / 2 :=
    real_intervalIntegral_one_div_mul_two_add_eq_logs hb
  have hb_pos : 0 < b :=
    lt_of_lt_of_le zero_lt_two hb
  have hb_le_two_add : b ≤ 2 + b :=
    le_add_of_nonneg_left (le_of_lt zero_lt_two)
  have hlog_le : Real.log b ≤ Real.log (2 + b) :=
    Real.log_le_log hb_pos hb_le_two_add
  have hdiff_nonpos : Real.log b - Real.log (2 + b) ≤ 0 :=
    sub_nonpos.mpr hlog_le
  have hlog_two_four :
      Real.log 2 - Real.log 4 = -(Real.log 2) := by
    have hfour : (4 : ℝ) = 2 * 2 := by
      exact (show (2 : ℝ) * 2 = 4 by rfl).symm
    have hlog4 : Real.log 4 = Real.log 2 + Real.log 2 := by
      calc
        Real.log 4 = Real.log (2 * 2) := congrArg Real.log hfour
        _ = Real.log 2 + Real.log 2 :=
          Real.log_mul (ne_of_gt zero_lt_two) (ne_of_gt zero_lt_two)
    calc
      Real.log 2 - Real.log 4 =
          Real.log 2 - (Real.log 2 + Real.log 2) := by
        exact congrArg (fun y : ℝ => Real.log 2 - y) hlog4
      _ = -(Real.log 2) := by
        exact sub_add_cancel (Real.log 2) (Real.log 2) ▸ rfl
  have hnum_le :
      (Real.log b - Real.log (2 + b)) -
          (Real.log 2 - Real.log 4) ≤ Real.log 2 := by
    have hrewrite :
        (Real.log b - Real.log (2 + b)) -
            (Real.log 2 - Real.log 4) =
          (Real.log b - Real.log (2 + b)) + Real.log 2 := by
      calc
        (Real.log b - Real.log (2 + b)) -
            (Real.log 2 - Real.log 4) =
          (Real.log b - Real.log (2 + b)) - (-(Real.log 2)) := by
          exact congrArg
            (fun y : ℝ => (Real.log b - Real.log (2 + b)) - y)
            hlog_two_four
        _ = (Real.log b - Real.log (2 + b)) + Real.log 2 :=
          sub_neg_eq_add (Real.log b - Real.log (2 + b)) (Real.log 2)
    exact Eq.subst
      (motive := fun y : ℝ => y ≤ Real.log 2)
      hrewrite.symm
      (calc
        (Real.log b - Real.log (2 + b)) + Real.log 2 ≤
            0 + Real.log 2 :=
          add_le_add_right hdiff_nonpos (Real.log 2)
        _ = Real.log 2 :=
          zero_add (Real.log 2))
  have hhalf_nonneg : (0 : ℝ) ≤ 2 :=
    le_of_lt zero_lt_two
  have hbound :
      ((Real.log b - Real.log (2 + b)) -
          (Real.log 2 - Real.log 4)) / 2 ≤ Real.log 2 / 2 :=
    div_le_div_of_nonneg_right hnum_le hhalf_nonneg
  exact Eq.subst
    (motive := fun y : ℝ => y ≤ Real.log 2 / 2)
    heval.symm
    hbound

/-- Endpoint contribution after integration by parts is bounded by `log 4 / 2`. -/
theorem real_log_two_add_by_parts_endpoint_le_log_four_half
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    (-Real.log (2 + b) / b) - (-Real.log 4 / 2) ≤
      Real.log 4 / 2 := by
  have hb_pos : 0 < b :=
    lt_of_lt_of_le zero_lt_two hb
  have hlog_nonneg : 0 ≤ Real.log (2 + b) :=
    real_log_two_add_nonneg_of_two_le hb
  have hdiv_nonneg : 0 ≤ Real.log (2 + b) / b :=
    div_nonneg hlog_nonneg (le_of_lt hb_pos)
  have hneg_nonpos : -Real.log (2 + b) / b ≤ 0 := by
    have hneg : -(Real.log (2 + b) / b) ≤ 0 :=
      neg_nonpos.mpr hdiv_nonneg
    exact Eq.subst
      (motive := fun y : ℝ => y ≤ 0)
      (neg_div (Real.log (2 + b)) b)
      hneg
  calc
    (-Real.log (2 + b) / b) - (-Real.log 4 / 2) =
        (-Real.log (2 + b) / b) + Real.log 4 / 2 := by
      exact sub_neg_eq_add (-Real.log (2 + b) / b) (Real.log 4 / 2)
    _ ≤ 0 + Real.log 4 / 2 :=
      add_le_add_right hneg_nonpos (Real.log 4 / 2)
    _ = Real.log 4 / 2 :=
      zero_add (Real.log 4 / 2)

/-- The sharp partial-fractions remainder and endpoint estimates fit under
the available `log 4` budget. -/
theorem real_log_four_half_add_log_two_half_le_log_four :
    Real.log 4 / 2 + Real.log 2 / 2 ≤ Real.log 4 := by
  have hlog_two_le_log_four : Real.log 2 ≤ Real.log 4 :=
    Real.log_le_log zero_lt_two
      (Eq.subst
        (motive := fun y : ℝ => (2 : ℝ) ≤ y)
        (show (2 : ℝ) + 2 = 4 by rfl)
        (le_add_of_nonneg_right (le_of_lt zero_lt_two)))
  have hhalf_nonneg : (0 : ℝ) ≤ 2 :=
    le_of_lt zero_lt_two
  have hhalf :
      Real.log 2 / 2 ≤ Real.log 4 / 2 :=
    div_le_div_of_nonneg_right hlog_two_le_log_four hhalf_nonneg
  have hsum :
      Real.log 4 / 2 + Real.log 2 / 2 ≤
        Real.log 4 / 2 + Real.log 4 / 2 :=
    add_le_add_left hhalf (Real.log 4 / 2)
  exact le_trans hsum (le_of_eq (add_halves (Real.log 4)))

theorem real_integral_Ioc_log_two_add_div_sq_by_parts_terms_le_log_four
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
        ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) ≤
      Real.log 4 := by
  have hendpoint :
      (-Real.log (2 + b) / b) - (-Real.log 4 / 2) ≤
        Real.log 4 / 2 :=
    real_log_two_add_by_parts_endpoint_le_log_four_half hb
  have hremainder :
      ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) ≤
        Real.log 2 / 2 :=
    real_intervalIntegral_one_div_mul_two_add_le_half_log_two hb
  have hsum :
      ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
          ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) ≤
        Real.log 4 / 2 + Real.log 2 / 2 :=
    add_le_add hendpoint hremainder
  exact le_trans hsum real_log_four_half_add_log_two_half_le_log_four

/-- Standard finite integration-by-parts tail estimate for
`log(2+x)/x²` from the canonical cutoff `2`.

The proof is the real-variable identity
`d(-log(2+x)/x) = log(2+x)/x² - 1/(x(2+x))`, followed by the elementary
endpoint estimate
`log 4 / 2 + ∫₂^∞ 1/(x(2+x)) ≤ log 4`. -/
theorem real_integral_Ioc_two_log_two_add_div_sq_tail_bound_by_parts
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 ≤
      Real.log 4 := by
  have hparts :
      ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 =
        ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
          ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) :=
    real_integral_Ioc_log_two_add_div_sq_eq_by_parts hb
  have hbound :
      ((-Real.log (2 + b) / b) - (-Real.log 4 / 2)) +
          ∫ x in Set.Ioc (2 : ℝ) b, (1 : ℝ) / (x * (2 + x)) ≤
        Real.log 4 :=
    real_integral_Ioc_log_two_add_div_sq_by_parts_terms_le_log_four hb
  exact Eq.subst
    (motive := fun y : ℝ => y ≤ Real.log 4)
    hparts.symm
    hbound

/-- Fixed improper-tail bound from the canonical cutoff `2`. -/
theorem real_integral_Ioc_two_log_two_add_div_sq_tail_bound
    {b : ℝ}
    (hb : (2 : ℝ) ≤ b) :
    ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 ≤
      Real.log 4 := by
  exact real_integral_Ioc_two_log_two_add_div_sq_tail_bound_by_parts hb

/-- Adjacent `Ioc` intervals split the finite reciprocal-density scalar
integral. -/
theorem real_integral_Ioc_log_two_add_div_sq_adjacent_split
    {a b : ℝ}
    (ha : (2 : ℝ) ≤ a)
    (hab : a ≤ b) :
    ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 =
      ∫ x in Set.Ioc (2 : ℝ) a, Real.log (2 + x) / x ^ 2 +
        ∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2 := by
  let f : ℝ → ℝ := fun x => Real.log (2 + x) / x ^ 2
  have htwo_b : (2 : ℝ) ≤ b :=
    le_trans ha hab
  have hleft :
      ∫ x in Set.Ioc (2 : ℝ) a, Real.log (2 + x) / x ^ 2 =
        ∫ x in (2 : ℝ)..a, f x :=
    (intervalIntegral.integral_of_le ha).symm
  have hright :
      ∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2 =
        ∫ x in a..b, f x :=
    (intervalIntegral.integral_of_le hab).symm
  have hall :
      ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 =
        ∫ x in (2 : ℝ)..b, f x :=
    (intervalIntegral.integral_of_le htwo_b).symm
  have hleft_interval : IntervalIntegrable f volume (2 : ℝ) a := by
    fun_prop
  have hright_interval : IntervalIntegrable f volume a b := by
    fun_prop
  have hadd :
      (∫ x in (2 : ℝ)..a, f x) + ∫ x in a..b, f x =
        ∫ x in (2 : ℝ)..b, f x :=
    intervalIntegral.integral_add_adjacent_intervals
      hleft_interval hright_interval
  exact Eq.trans hall
    (Eq.trans hadd.symm
      (congrArg₂ (fun u v : ℝ => u + v) hleft.symm hright.symm))

/-- Improper-tail comparison for `log(2+x)/x²` after the cutoff `2`.

This is the canonical real-analysis theorem behind the reciprocal-density
scalar estimate.  It is independent of zeta and is normally proved by
integration by parts:
`d(-log(2+x)/x) = log(2+x)/x² - 1/(x(2+x))`, followed by nonnegativity of the
remainder and endpoint evaluation at `x = 2`. -/
theorem real_integral_Ioc_log_two_add_div_sq_tail_bound_of_two_le
    {a b : ℝ}
    (ha : (2 : ℝ) ≤ a)
    (hab : a ≤ b) :
    ∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2 ≤
      Real.log 4 := by
  have htwo_le_b : (2 : ℝ) ≤ b :=
    le_trans ha hab
  have hnonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioc (2 : ℝ) a)]
        (fun x : ℝ => Real.log (2 + x) / x ^ 2) :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun x hx =>
        real_log_two_add_div_sq_nonneg_of_two_le (le_of_lt hx.1))
  have htail_split :
      ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 =
        ∫ x in Set.Ioc (2 : ℝ) a, Real.log (2 + x) / x ^ 2 +
          ∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2 := by
    exact real_integral_Ioc_log_two_add_div_sq_adjacent_split ha hab
  have hleft_nonneg :
      0 ≤ ∫ x in Set.Ioc (2 : ℝ) a, Real.log (2 + x) / x ^ 2 :=
    integral_nonneg_of_ae hnonneg
  have hle_tail :
      ∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2 ≤
        ∫ x in Set.Ioc (2 : ℝ) b, Real.log (2 + x) / x ^ 2 := by
    have hadd :
        ∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2 ≤
          ∫ x in Set.Ioc (2 : ℝ) a, Real.log (2 + x) / x ^ 2 +
            ∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2 :=
      le_add_of_nonneg_left hleft_nonneg
    exact Eq.subst
      (motive := fun y : ℝ =>
        ∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2 ≤ y)
      htail_split.symm
      hadd
  exact le_trans hle_tail
    (real_integral_Ioc_two_log_two_add_div_sq_tail_bound htwo_le_b)

theorem real_integral_Ioc_log_two_add_div_sq_tail_bound
    {a b : ℝ}
    (ha : (2 : ℝ) ≤ a)
    (hab : a ≤ b) :
    ∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2 ≤
      Real.log 4 := by
  exact
    real_integral_Ioc_log_two_add_div_sq_tail_bound_of_two_le
      ha hab

/-- Canonical real-variable comparison for the finite `log(2+x)/x²` integral.

On any interval beginning after `2`, the tail integral is bounded uniformly by
the full tail from `2` to infinity; that tail is below `Real.log 4`.  The
displayed height parameter is only used through `1 ≤ H`, hence
`Real.log 4 ≤ Real.log (3+H)`. -/
theorem real_integral_Ioc_log_two_add_div_sq_le_log_three_add_height
    {H a b : ℝ}
    (hH : (1 : ℝ) ≤ H)
    (ha : (2 : ℝ) ≤ a)
    (hab : a ≤ b) :
    ∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2 ≤
      Real.log (3 + H) := by
  have htail :
      ∫ x in Set.Ioc a b, Real.log (2 + x) / x ^ 2 ≤ Real.log 4 :=
    real_integral_Ioc_log_two_add_div_sq_tail_bound ha hab
  have hfour_le : (4 : ℝ) ≤ 3 + H := by
    calc
      (4 : ℝ) = 3 + 1 := by
        rfl
      _ ≤ 3 + H :=
        add_le_add_left hH 3
  have hlog_four_le : Real.log 4 ≤ Real.log (3 + H) := by
    have hfour_pos : (0 : ℝ) < 4 := by
      exact zero_lt_four
    exact Real.log_le_log hfour_pos hfour_le
  exact le_trans htail hlog_four_le

/-- Scalar calculus owner for the `log(2+x)/x` post-cutoff integral.

Proof route: on the post-cutoff interval, `2 ≤ x`, hence
`log(2+x)/x ≤ 2 * log(2+x)/(2+x)`, the derivative of
`(Real.log (2+x))^2`.  The fundamental theorem of calculus and endpoint
monotonicity then bound the finite interval by the right endpoint square. -/
theorem scalarReciprocalDensity_log_over_x_integral_bound_calculus
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        Real.log (2 + x) / x ≤
      (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2 := by
  have hN_two :
      (2 : ℝ) ≤ (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) :=
    scalarReciprocalDensity_two_le_cutoff_real t
  have hNM_real :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ ((M : ℕ) : ℝ) :=
    Nat.cast_le.mpr hNM
  exact
    real_integral_Ioc_log_two_add_div_self_le_log_endpoint_sq
      hN_two hNM_real

/-- Scalar calculus owner for the `log(2+x)/x²` post-cutoff integral.

Proof route: use `Real.log_div_self_rpow_antitoneOn` for the decreasing
positive tail profile after the cutoff, or equivalently integrate by parts:
`∫ log(2+x)/x²` is bounded by the cutoff endpoint contribution plus the
integrable `1/(x(2+x))` remainder.  Since the cutoff is at least `2+|t|`, the
result is dominated by `Real.log (3 + ‖t‖)`. -/
theorem scalarReciprocalDensity_log_over_x_sq_integral_bound_calculus
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        Real.log (2 + x) / x ^ 2 ≤
      Real.log (3 + ‖t‖) := by
  have hN_two :
      (2 : ℝ) ≤ (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) :=
    scalarReciprocalDensity_two_le_cutoff_real t
  have hNM_real :
      (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ ((M : ℕ) : ℝ) :=
    Nat.cast_le.mpr hNM
  exact
    real_integral_Ioc_log_two_add_div_sq_le_log_three_add_height
      ht hN_two hNM_real


/-- Finite-endpoint calculus bound for the `log(2+x)/x` contribution. -/
theorem scalarReciprocalDensity_log_over_x_integral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        Real.log (2 + x) / x ≤
      (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2 := by
  exact scalarReciprocalDensity_log_over_x_integral_bound_calculus t ht hNM

/-- Finite-endpoint calculus bound for the `log(2+x)/x^2` contribution. -/
theorem scalarReciprocalDensity_log_over_x_sq_integral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        Real.log (2 + x) / x ^ 2 ≤
      Real.log (3 + ‖t‖) := by
  exact scalarReciprocalDensity_log_over_x_sq_integral_bound_calculus t ht hNM

/-- Pointwise algebraic split of the coarse reciprocal-density majorant.

The factor `x / |t|` contributes the `log(2+x)/x` term, using `1 ≤ |t|`; the
remaining `sqrt(1+|t|)` term contributes `log(2+x)/x²`. -/
theorem scalarReciprocalDensityMajorant_pointwise_split
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {x : ℝ}
    (hx : 0 < x) :
    ((1 : ℝ) / x ^ 2) *
        (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) ≤
      8 * (Real.log (2 + x) / x) +
        8 * Real.sqrt (1 + ‖t‖) * (Real.log (2 + x) / x ^ 2) := by
  let L : ℝ := Real.log (2 + x)
  let S : ℝ := Real.sqrt (1 + ‖t‖)
  let T : ℝ := ‖t‖
  have hT_pos : 0 < T :=
    lt_of_lt_of_le zero_lt_one ht
  have hx_nonneg : 0 ≤ x :=
    le_of_lt hx
  have hx_sq_pos : 0 < x ^ 2 :=
    sq_pos_of_pos hx
  have hx_sq_nonneg : 0 ≤ x ^ 2 :=
    le_of_lt hx_sq_pos
  have hL_nonneg : 0 ≤ L := by
    have hone_le_two : (1 : ℝ) ≤ 2 := by
      calc
        (1 : ℝ) ≤ 1 + 1 := le_add_of_nonneg_right zero_le_one
        _ = 2 := by
          rfl
    have htwo_le_two_add : (2 : ℝ) ≤ 2 + x :=
      add_le_add_left hx_nonneg 2
    exact Real.log_nonneg (le_trans hone_le_two htwo_le_two_add)
  have hS_nonneg : 0 ≤ S :=
    Real.sqrt_nonneg (1 + ‖t‖)
  have height_nonneg : 0 ≤ (8 : ℝ) :=
    ofNat_nonneg 8
  have hweight_nonneg : 0 ≤ (1 : ℝ) / x ^ 2 := by
    exact div_nonneg zero_le_one hx_sq_nonneg
  have hfirst_ratio : x / T ≤ x := by
    have hmul_le : x ≤ x * T := by
      calc
        x = x * 1 := by
          exact (mul_one x).symm
        _ ≤ x * T :=
          mul_le_mul_of_nonneg_left ht hx_nonneg
    exact (div_le_iff₀ hT_pos).mpr hmul_le
  have hsum_le : (x / T) + S ≤ x + S :=
    add_le_add_right hfirst_ratio S
  have hmajor_le :
      8 * ((x / T) + S) * L ≤ 8 * (x + S) * L := by
    have hscaled :
        8 * ((x / T) + S) ≤ 8 * (x + S) :=
      mul_le_mul_of_nonneg_left hsum_le height_nonneg
    exact mul_le_mul_of_nonneg_right hscaled hL_nonneg
  have hweighted_major :
      ((1 : ℝ) / x ^ 2) * (8 * ((x / T) + S) * L) ≤
        ((1 : ℝ) / x ^ 2) * (8 * (x + S) * L) :=
    mul_le_mul_of_nonneg_left hmajor_le hweight_nonneg
  have hexpanded_bound :
      ((1 : ℝ) / x ^ 2) * (8 * (x + S) * L) =
        8 * (L / x) + 8 * S * (L / x ^ 2) := by
    calc
      ((1 : ℝ) / x ^ 2) * (8 * (x + S) * L) =
          ((1 : ℝ) / x ^ 2) * ((8 * x + 8 * S) * L) := by
        exact congrArg
          (fun y : ℝ => ((1 : ℝ) / x ^ 2) * (y * L))
          (mul_add 8 x S)
      _ = ((1 : ℝ) / x ^ 2) * (8 * x * L + 8 * S * L) := by
        exact congrArg
          (fun y : ℝ => ((1 : ℝ) / x ^ 2) * y)
          (add_mul (8 * x) (8 * S) L)
      _ =
          ((1 : ℝ) / x ^ 2) * (8 * x * L) +
            ((1 : ℝ) / x ^ 2) * (8 * S * L) := by
        exact mul_add ((1 : ℝ) / x ^ 2) (8 * x * L) (8 * S * L)
      _ = 8 * (L / x) +
            ((1 : ℝ) / x ^ 2) * (8 * S * L) := by
        have hx_ne : x ≠ 0 :=
          ne_of_gt hx
        have hx_sq_ne : x ^ 2 ≠ 0 :=
          pow_ne_zero 2 hx_ne
        have hfirst :
            ((1 : ℝ) / x ^ 2) * (8 * x * L) = 8 * (L / x) := by
          calc
            ((1 : ℝ) / x ^ 2) * (8 * x * L) =
                8 * L * (x / x ^ 2) := by
              ac_rfl
            _ = 8 * L * (1 / x) := by
              have hx_cancel : x / x ^ 2 = 1 / x := by
                calc
                  x / x ^ 2 = x / (x * x) := by
                    exact congrArg (fun y : ℝ => x / y) (sq x)
                  _ = 1 / x := by
                    exact div_mul_cancel_left₀ hx_ne x
              exact congrArg (fun y : ℝ => 8 * L * y) hx_cancel
            _ = 8 * (L / x) := by
              calc
                8 * L * (1 / x) = 8 * (L * (1 / x)) := by
                  exact mul_assoc 8 L (1 / x)
                _ = 8 * (L / x) := by
                  exact congrArg (fun y : ℝ => 8 * y) (div_eq_mul_one_div L x).symm
        exact congrArg
          (fun y : ℝ => y + ((1 : ℝ) / x ^ 2) * (8 * S * L))
          hfirst
      _ = 8 * (L / x) + 8 * S * (L / x ^ 2) := by
        have hsecond :
            ((1 : ℝ) / x ^ 2) * (8 * S * L) =
              8 * S * (L / x ^ 2) := by
          calc
            ((1 : ℝ) / x ^ 2) * (8 * S * L) =
                8 * S * (L * ((1 : ℝ) / x ^ 2)) := by
              ac_rfl
            _ = 8 * S * (L / x ^ 2) := by
              exact congrArg
                (fun y : ℝ => 8 * S * y)
                (div_eq_mul_one_div L (x ^ 2)).symm
        exact congrArg (fun y : ℝ => 8 * (L / x) + y) hsecond
  exact le_trans hweighted_major (le_of_eq hexpanded_bound)

/-- Integral transport of the pointwise scalar split over the post-cutoff
interval. -/
theorem scalarReciprocalDensityMajorant_integral_split_le_components
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) ≤
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        (8 * (Real.log (2 + x) / x) +
          8 * Real.sqrt (1 + ‖t‖) * (Real.log (2 + x) / x ^ 2)) := by
  let s : Set ℝ :=
    Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ)
  let f : ℝ → ℝ := fun x =>
    ((1 : ℝ) / x ^ 2) *
      (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
  let g : ℝ → ℝ := fun x =>
    8 * (Real.log (2 + x) / x) +
      8 * Real.sqrt (1 + ‖t‖) * (Real.log (2 + x) / x ^ 2)
  have hf : Integrable f (volume.restrict s) := by
    fun_prop
  have hg : Integrable g (volume.restrict s) := by
    fun_prop
  have hle : f ≤ᵐ[volume.restrict s] g :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun x hx =>
        scalarReciprocalDensityMajorant_pointwise_split
          t ht (scalarReciprocalDensity_Ioc_point_pos t hx))
  exact integral_mono_ae hf hg hle

/-- The component integral bounds imply the finite-endpoint bound for the
split scalar majorant. -/
theorem scalarReciprocalDensityMajorant_components_le_endpoint_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hlog_over_x :
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          Real.log (2 + x) / x ≤
        (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2)
    (hlog_over_x_sq :
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          Real.log (2 + x) / x ^ 2 ≤
        Real.log (3 + ‖t‖)) :
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        (8 * (Real.log (2 + x) / x) +
          8 * Real.sqrt (1 + ‖t‖) * (Real.log (2 + x) / x ^ 2)) ≤
      8 * (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2 +
        8 * Real.sqrt (1 + ‖t‖) * Real.log (3 + ‖t‖) := by
  let s : Set ℝ :=
    Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ)
  let f : ℝ → ℝ := fun x => Real.log (2 + x) / x
  let g : ℝ → ℝ := fun x => Real.log (2 + x) / x ^ 2
  let A : ℝ := (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2
  let B : ℝ := Real.log (3 + ‖t‖)
  let S : ℝ := Real.sqrt (1 + ‖t‖)
  have hf : Integrable (fun x => 8 * f x) (volume.restrict s) := by
    fun_prop
  have hg : Integrable (fun x => 8 * S * g x) (volume.restrict s) := by
    fun_prop
  have hsum_eq :
      (∫ x in s, (8 * f x + 8 * S * g x)) =
        (∫ x in s, 8 * f x) + ∫ x in s, 8 * S * g x :=
    integral_add hf hg
  have hf_scale :
      (∫ x in s, 8 * f x) = 8 * ∫ x in s, f x :=
    integral_mul_left 8 f
  have hg_scale :
      (∫ x in s, 8 * S * g x) = (8 * S) * ∫ x in s, g x :=
    integral_mul_left (8 * S) g
  have height_nonneg : 0 ≤ (8 : ℝ) := by
    exact ofNat_nonneg 8
  have hS_nonneg : 0 ≤ S :=
    Real.sqrt_nonneg (1 + ‖t‖)
  have hheightS_nonneg : 0 ≤ 8 * S :=
    mul_nonneg height_nonneg hS_nonneg
  have hfirst :
      (∫ x in s, 8 * f x) ≤ 8 * A := by
    exact Eq.subst
      (motive := fun y : ℝ => y ≤ 8 * A)
      hf_scale.symm
      (mul_le_mul_of_nonneg_left hlog_over_x height_nonneg)
  have hsecond :
      (∫ x in s, 8 * S * g x) ≤ (8 * S) * B := by
    exact Eq.subst
      (motive := fun y : ℝ => y ≤ (8 * S) * B)
      hg_scale.symm
      (mul_le_mul_of_nonneg_left hlog_over_x_sq hheightS_nonneg)
  have hsum_bound :
      (∫ x in s, 8 * f x) + ∫ x in s, 8 * S * g x ≤
        8 * A + (8 * S) * B :=
    add_le_add hfirst hsecond
  have htarget_eq :
      8 * A + (8 * S) * B =
        8 * (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2 +
          8 * Real.sqrt (1 + ‖t‖) * Real.log (3 + ‖t‖) := by
    rfl
  exact Eq.subst
    (motive := fun y : ℝ =>
      y ≤
        8 * (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2 +
          8 * Real.sqrt (1 + ‖t‖) * Real.log (3 + ‖t‖))
    hsum_eq.symm
    (le_trans hsum_bound (le_of_eq htarget_eq))

/-- Algebraic split of the coarse reciprocal-density scalar majorant into the
two real calculus integrals it requires. -/
theorem scalarReciprocalDensityMajorant_integral_split_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hlog_over_x :
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          Real.log (2 + x) / x ≤
        (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2)
    (hlog_over_x_sq :
      ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          Real.log (2 + x) / x ^ 2 ≤
        Real.log (3 + ‖t‖)) :
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) ≤
      8 * (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2 +
        8 * Real.sqrt (1 + ‖t‖) * Real.log (3 + ‖t‖) := by
  exact
    le_trans
      (scalarReciprocalDensityMajorant_integral_split_le_components t ht hNM)
      (scalarReciprocalDensityMajorant_components_le_endpoint_bound
        t ht hNM hlog_over_x hlog_over_x_sq)

/-- Finite-endpoint real calculus bound for the coarse reciprocal-density
majorant.

The coarse first-derivative partial-sum majorant contains an `x / |t|` term, so
integrating it against `x⁻²` produces logarithmic growth in the right endpoint.
This is the honest scalar comparison; the uniform Abel/Euler-Maclaurin integral
bound must use the oscillatory cancellation theorem below, not this coarse
majorant alone. -/
theorem scalarReciprocalDensityMajorant_finiteEndpoint_integral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) ≤
      8 * (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2 +
        8 * Real.sqrt (1 + ‖t‖) * Real.log (3 + ‖t‖) := by
  exact
    scalarReciprocalDensityMajorant_integral_split_bound
      t ht hNM
      (scalarReciprocalDensity_log_over_x_integral_bound t ht hNM)
      (scalarReciprocalDensity_log_over_x_sq_integral_bound t ht hNM)

/-- Finite real calculus estimate for the scalar reciprocal-density majorant.

This wrapper keeps the older local name while the owner theorem records the
finite-endpoint growth explicitly. -/
theorem reciprocalDensityIntegral_scalar_majorant_finite_endpoint_bound_calculus
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ((1 : ℝ) / x ^ 2) *
          (8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x)) ≤
      8 * (Real.log (2 + ((M : ℕ) : ℝ))) ^ 2 +
        8 * Real.sqrt (1 + ‖t‖) * Real.log (3 + ‖t‖) := by
  exact scalarReciprocalDensityMajorant_finiteEndpoint_integral_bound t ht hNM

/-- Oscillatory reciprocal-density integral estimate after the canonical cutoff.

This is not a consequence of integrating the coarse scalar majorant: that scalar
integral grows with the right endpoint.  The uniform bound is the
Euler-Maclaurin/first-derivative cancellation estimate for the concrete
reciprocal-amplitude term. -/
theorem partialSummation_reciprocalAmplitude_oscillatoryIntegral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hreciprocal_density :
      ∀ x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x‖ =
          (1 : ℝ) / x ^ 2) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      2 + 8 * Real.log (3 + ‖t‖) := by
  sorry

/-- Oscillatory reciprocal-density integral estimate after the canonical cutoff.

This is the concrete Abel/partial-summation estimate for the reciprocal
amplitude, consuming the already isolated partial-sum and reciprocal-density
inputs. -/
theorem oscillatoryReciprocalDensity_logarithmicPhase_integral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hreciprocal_density :
      ∀ x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x‖ =
          (1 : ℝ) / x ^ 2) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      2 + 8 * Real.log (3 + ‖t‖) := by
  exact
    partialSummation_reciprocalAmplitude_oscillatoryIntegral_bound
      t ht hpartial hNM hreciprocal_density

/-- Oscillatory reciprocal-density integral estimate after the canonical cutoff.

This local wrapper exposes the owner theorem under the reciprocal-density API. -/
theorem reciprocalDensityIntegral_oscillatory_le_log_cutoff
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hreciprocal_density :
      ∀ x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x‖ =
          (1 : ℝ) / x ^ 2) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      2 + 8 * Real.log (3 + ‖t‖) := by
  exact
    oscillatoryReciprocalDensity_logarithmicPhase_integral_bound
      t ht hpartial hNM hreciprocal_density

/-- Concrete reciprocal total-variation integral estimate after the
reciprocal derivative density has been identified. -/
theorem reciprocalDensityIntegral_logarithmicPhase_bound_of_partialSum_majorant
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hreciprocal_density :
      ∀ x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x‖ =
          (1 : ℝ) / x ^ 2) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖) := by
  exact
    reciprocalDensityIntegral_oscillatory_le_log_cutoff
      t ht hpartial hNM hreciprocal_density

/-- Concrete reciprocal total-variation integral estimate after the
reciprocal derivative density has been identified. -/
theorem concreteReciprocalVariation_logarithmicPhase_integral_bound_of_density
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hreciprocal_density :
      ∀ x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x‖ =
          (1 : ℝ) / x ^ 2) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖) := by
  exact
    reciprocalDensityIntegral_logarithmicPhase_bound_of_partialSum_majorant
      t ht hpartial hNM hreciprocal_density

/-- Concrete reciprocal total-variation integral estimate.

This is the real-variable Abel/Euler-Maclaurin variation step for the concrete
amplitude `u ↦ 1 / u`: after the cutoff `N = ⌊2 + |t|⌋₊`, the normalized
reciprocal derivative has total variation small enough that the first-derivative
partial-sum majorant gives the displayed logarithmic bound. -/
theorem concreteReciprocalVariation_logarithmicPhase_integral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    (hreciprocal_deriv :
      ∀ {u : ℝ}, 0 < u →
        deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) u =
          (-(1 : ℂ) / (u : ℂ) ^ 2))
    (hreciprocal_deriv_norm :
      ∀ {u : ℝ}, 0 < u →
        ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) u‖ =
          (1 : ℝ) / u ^ 2)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖) := by
  exact
    concreteReciprocalVariation_logarithmicPhase_integral_bound_of_density
      t ht hpartial hNM
      (concreteReciprocalVariation_density_bound_on_cutoff_interval t hNM)

/-- Concrete total-variation estimate for the reciprocal-amplitude term after
the logarithmic-phase first-derivative bound. -/
theorem oscillatoryEulerMaclaurin_logarithmicPhase_reciprocalVariation_bound_of_partialSums
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x))
    (hreciprocal_deriv :
      ∀ {u : ℝ}, 0 < u →
        deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) u =
          (-(1 : ℂ) / (u : ℂ) ^ 2))
    (hreciprocal_deriv_norm :
      ∀ {u : ℝ}, 0 < u →
        ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) u‖ =
          (1 : ℝ) / u ^ 2)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖) := by
  exact
    concreteReciprocalVariation_logarithmicPhase_integral_bound
      t ht hpartial hreciprocal_deriv hreciprocal_deriv_norm hNM

/-- Concrete reciprocal-variation integral estimate for the logarithmic phase.

This is the variation term in Abel/Euler-Maclaurin summation for the amplitude
`u ↦ 1 / u` and the concrete oscillator `u ↦ exp (-i t log u)`.  The
reciprocal derivative is normalized as `‖(1/u)'‖ = 1/u^2`; the remaining
analytic input is the same first-derivative cancellation used for the
logarithmic-phase partial sums. -/
theorem oscillatoryEulerMaclaurin_logarithmicPhase_reciprocalVariation_integral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hphase_deriv :
      ∀ {u : ℝ}, 0 < u →
        deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) u =
          (((-(t : ℂ) * Complex.I) / (u : ℂ)) *
            boundaryLineOnePointRealParam_logarithmicPhaseFunction t u))
    (hphase_deriv_norm :
      ∀ {u : ℝ}, 0 < u →
        ‖deriv (boundaryLineOnePointRealParam_logarithmicPhaseFunction t) u‖ =
          ‖t‖ / u)
    (hreciprocal_deriv :
      ∀ {u : ℝ}, 0 < u →
        deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) u =
          (-(1 : ℂ) / (u : ℂ) ^ 2))
    (hreciprocal_deriv_norm :
      ∀ {u : ℝ}, 0 < u →
        ‖deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) u‖ =
          (1 : ℝ) / u ^ 2)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖) := by
  have hpartial :
      ∀ {x : ℝ},
        (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x →
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
            8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) := by
    intro x hx
    exact
      firstDerivativeEulerMaclaurin_logarithmicPhase_partialSum_bound
        t ht hphase_deriv hphase_deriv_norm hx
  exact
    oscillatoryEulerMaclaurin_logarithmicPhase_reciprocalVariation_bound_of_partialSums
      t ht hpartial hreciprocal_deriv hreciprocal_deriv_norm hNM

/-- Sharper reciprocal-derivative integral estimate in the logarithmic-phase
partial-summation package.

This is the variation part of the oscillatory Euler-Maclaurin argument.  The
estimate keeps cancellation in the logarithmic phase before integrating against
the reciprocal derivative; it is not a consequence of the coarse primitive
majorant alone. -/
theorem oscillatoryEulerMaclaurin_logarithmicPhase_integral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖) := by
  exact
    oscillatoryEulerMaclaurin_logarithmicPhase_reciprocalVariation_integral_bound
      t ht
      (fun hu => boundaryLineOnePointRealParam_logarithmicPhaseFunction_deriv_eq t hu)
      (fun hu => boundaryLineOnePointRealParam_logarithmicPhaseFunction_deriv_norm_eq t hu)
      (fun hu => complexReciprocalOfReal_deriv_eq hu)
      (fun hu => complexReciprocalOfReal_deriv_norm_eq hu)
      hNM

/-- Integral arithmetic for the reciprocal-derivative term in the finite Abel
decomposition.

This is the variation side of partial summation for the weight `x ↦ 1 / x`.
After the first-derivative Euler-Maclaurin estimate bounds the logarithmic-phase
primitive, this theorem owns the monotone reciprocal-variation integral and the
normalization to the cutoff logarithm.  Cf. Edwards, *Riemann's Zeta Function*,
Euler-Maclaurin derivations. -/
theorem eulerMaclaurin_logarithmicPhase_finiteAbel_integral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖) := by
  exact oscillatoryEulerMaclaurin_logarithmicPhase_integral_bound t ht hNM

/-- Deep Euler-Maclaurin arithmetic owner for the finite Abel endpoint and
reciprocal-derivative integral terms.

This is the remaining bookkeeping attached to the first-derivative
Euler-Maclaurin estimate: the reciprocal endpoint weights and the integral of
the reciprocal derivative are both normalized to the same logarithmic cutoff
constant. -/
theorem logarithmicPhase_firstDerivative_finiteAbel_endpoint_integral_arithmetic
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊‖ +
        ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖)) ∧
    (‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖)) := by
  exact
    ⟨eulerMaclaurin_logarithmicPhase_finiteAbel_endpoint_bound t ht hNM,
      eulerMaclaurin_logarithmicPhase_finiteAbel_integral_bound t ht hNM⟩

/-- Exact endpoint arithmetic for the finite Abel package.  This is the
reciprocal-weight endpoint part after the first-derivative estimate has been
applied at `M` and at the canonical cutoff. -/
theorem logarithmicPhase_firstDerivative_finiteAbel_endpoint_arithmetic
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊‖ +
        ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖) := by
  exact
    (logarithmicPhase_firstDerivative_finiteAbel_endpoint_integral_arithmetic
      t ht hNM).1

/-- Exact reciprocal-derivative integral arithmetic for the finite Abel package.
The analytic input is the first-derivative partial-sum estimate; this lemma owns
the endpoint and logarithmic integral bookkeeping. -/
theorem logarithmicPhase_firstDerivative_finiteAbel_integral_arithmetic
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖) := by
  exact
    (logarithmicPhase_firstDerivative_finiteAbel_endpoint_integral_arithmetic
      t ht hNM).2

/-- Algebraic endpoint extraction from the logarithmic-phase first-derivative
partial-sum estimate.

This is not a separate analytic input: the two reciprocal endpoint weights are
controlled after the canonical cutoff by applying
`logarithmicPhasePartialSum_firstDerivative_bound` at `M` and at the cutoff. -/
theorem logarithmicPhase_firstDerivative_eulerMaclaurin_finiteAbel_package
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊((M : ℕ) : ℝ)⌋₊‖ ≤
        8 * ((((M : ℕ) : ℝ) / ‖t‖) + Real.sqrt (1 + ‖t‖)) *
          Real.log (2 + ((M : ℕ) : ℝ))) ∧
    (‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊‖ +
        ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖)) ∧
    (‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖)) := by
  exact
    ⟨logarithmicPhase_firstDerivative_finiteAbel_rightPartial_bound t ht hNM,
      logarithmicPhase_firstDerivative_finiteAbel_endpoint_arithmetic t ht hNM,
      logarithmicPhase_firstDerivative_finiteAbel_integral_arithmetic t ht hNM⟩

/-- Explicit finite Abel-tail constant for the logarithmic-phase oscillator
after the canonical cutoff.

The constant is intentionally not normalized to `1`: the owner estimate must
record the actual Abel endpoint and reciprocal-derivative contribution rather
than hiding it behind a false unit-bound surface. -/
def boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant
    (t : ℝ) : ℝ :=
  4 + 16 * Real.log (3 + ‖t‖)

/-- Owner API: endpoint contribution in the finite Abel decomposition after the
canonical cutoff. -/
theorem logarithmicPhase_finiteAbelEndpoint_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          ⌊((M : ℕ) : ℝ)⌋₊‖ +
      ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤
      2 + 8 * Real.log (3 + ‖t‖) := by
  exact (logarithmicPhase_firstDerivative_eulerMaclaurin_finiteAbel_package
    t ht hNM).2.1

/-- Endpoint contribution in the finite Abel decomposition after the canonical
cutoff.  This consumes the first-derivative logarithmic-phase primitive bound at
the two natural endpoints and the reciprocal endpoint weights. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelEndpoint_norm_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          ⌊((M : ℕ) : ℝ)⌋₊‖ +
      ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤
      2 + 8 * Real.log (3 + ‖t‖) := by
  exact logarithmicPhase_finiteAbelEndpoint_bound t ht hNM

/-- Owner API: reciprocal-derivative integral contribution in the finite Abel
decomposition after the canonical cutoff. -/
theorem logarithmicPhase_finiteAbelDerivativeIntegral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      2 + 8 * Real.log (3 + ‖t‖) := by
  exact
    (logarithmicPhase_firstDerivative_eulerMaclaurin_finiteAbel_package
      t ht hNM).2.2

/-- Reciprocal-derivative integral contribution in the finite Abel decomposition.
The integrand is the product of the derivative of `u ↦ 1/u` and the
first-derivative logarithmic-phase primitive bound. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelDerivativeIntegral_norm_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      2 + 8 * Real.log (3 + ‖t‖) := by
  exact logarithmicPhase_finiteAbelDerivativeIntegral_bound t ht hNM

/-- Finite Abel-tail estimate obtained from the exact Abel identity, endpoint
bounds, and reciprocal-derivative integral bound. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelTail_norm_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
        ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  let N : ℕ := ⌊2 + ‖t‖⌋₊
  let SM : ℂ :=
    ((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ) *
      boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
        ⌊((M : ℕ) : ℝ)⌋₊
  let SN : ℂ :=
    (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
      boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
        ⌊(((N : ℕ) : ℝ))⌋₊
  let J : ℂ :=
    ∫ x in Set.Ioc (((N : ℕ) : ℝ)) ((M : ℕ) : ℝ),
      deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊
  have hf_diff :
      ∀ x ∈ Set.Icc (((N : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        DifferentiableAt ℝ (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x := by
    intro x hx
    fun_prop
  have hf_int :
      IntegrableOn
        (deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)))
        (Set.Icc (((N : ℕ) : ℝ)) ((M : ℕ) : ℝ)) := by
    fun_prop
  have hidentity :
      (∑ k ∈ Finset.Ioc ⌊(((N : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
          ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))) =
        SM - SN - J := by
    exact
      abelSummation_boundaryLineOnePointRealParam_cutoff_finite_tail_endpoint_derivative_identity
        t hNM hf_diff hf_int
  have hendpoint :
      ‖SM‖ + ‖SN‖ ≤ 2 + 8 * Real.log (3 + ‖t‖) := by
    exact
      boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelEndpoint_norm_le
        t ht hNM
  have hintegral :
      ‖J‖ ≤ 2 + 8 * Real.log (3 + ‖t‖) := by
    exact
      boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelDerivativeIntegral_norm_le
        t ht hNM
  have htriangle :
      ‖SM - SN - J‖ ≤ ‖SM‖ + ‖SN‖ + ‖J‖ := by
    have hfirst : ‖SM - SN - J‖ ≤ ‖SM - SN‖ + ‖J‖ :=
      norm_sub_le (SM - SN) J
    have hsecond : ‖SM - SN‖ ≤ ‖SM‖ + ‖SN‖ :=
      norm_sub_le SM SN
    exact le_trans hfirst (add_le_add_right hsecond ‖J‖)
  have hpost_triangle :
      ‖SM‖ + ‖SN‖ + ‖J‖ ≤
        (2 + 8 * Real.log (3 + ‖t‖)) +
          (2 + 8 * Real.log (3 + ‖t‖)) := by
    exact add_le_add hendpoint hintegral
  have hconstant :
      (2 + 8 * Real.log (3 + ‖t‖)) +
          (2 + 8 * Real.log (3 + ‖t‖)) =
        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
    let L : ℝ := Real.log (3 + ‖t‖)
    have hadd :
        (2 + 8 * L) + (2 + 8 * L) =
          (2 + 2) + (8 * L + 8 * L) := by
      ac_rfl
    have htwo : (2 : ℝ) + 2 = 4 := by
      rfl
    have height_coeff : (8 : ℝ) + 8 = 16 := by
      rfl
    have height : (8 : ℝ) * L + 8 * L = 16 * L := by
      calc
        (8 : ℝ) * L + 8 * L = ((8 : ℝ) + 8) * L := by
          exact (add_mul (8 : ℝ) 8 L).symm
        _ = 16 * L := by
          exact congrArg (fun c : ℝ => c * L) height_coeff
    calc
      (2 + 8 * Real.log (3 + ‖t‖)) +
          (2 + 8 * Real.log (3 + ‖t‖)) =
          (2 + 8 * L) + (2 + 8 * L) := by
        rfl
      _ = (2 + 2) + (8 * L + 8 * L) :=
        hadd
      _ = 4 + (8 * L + 8 * L) := by
        exact congrArg (fun x : ℝ => x + (8 * L + 8 * L)) htwo
      _ = 4 + 16 * L := by
        exact congrArg (fun x : ℝ => 4 + x) height
      _ = boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
        rfl
  exact Eq.subst
    (motive := fun z : ℂ =>
      ‖z‖ ≤ boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t)
    hidentity.symm
    (le_trans htriangle (le_trans hpost_triangle (le_of_eq hconstant)))

/-- Concrete finite Abel-tail estimate obtained through Mathlib's Abel
summation theorem.

The finite summation-by-parts identity is supplied by
`sum_mul_eq_sub_sub_integral_mul`, via
`abelSummation_boundaryLineOnePointRealParam_cutoff_finite_tail_endpoint_derivative_identity`;
this theorem only exposes that canonical route under an explicit owner name. -/
theorem mathlibAbelSummation_boundaryLineOnePointRealParam_logarithmicPhase_finiteTail_norm_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
        ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  exact boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelTail_norm_le
    t ht hNM

/-- The completed Abel/Euler-Maclaurin tail package for the logarithmic-phase
oscillator after the canonical cutoff.

The pointwise primitive has an unavoidable `x / |t|` component, so the owner
bound carries the explicit cutoff constant
`boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t`.  The
classical proof combines Abel summation with cancellation in the endpoint and
reciprocal-derivative terms at `N = ⌊2 + |t|⌋₊`. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_abelTail_norm_le_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
        ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelTail_norm_le
      t ht hNM

/-- Abel summation in the precise finite form needed for the boundary-line tail:
coefficients are the logarithmic-phase oscillatory partial sums of `n^{-it}` and
the weight is `1/x`. -/
theorem abelSummation_boundaryLineOnePointRealParam_finite_tail_identity
    (t : ℝ)
    {a b : ℝ}
    (ha : 0 ≤ a)
    (hab : a ≤ b)
    (hf_diff :
      ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x)
    (hf_int :
      IntegrableOn
        (deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)))
        (Set.Icc a b)) :
    ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
        ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)) =
      ((b : ℂ)⁻¹ : ℂ) *
          (∑ k ∈ Finset.Icc 0 ⌊b⌋₊,
            (k : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        ((a : ℂ)⁻¹ : ℂ) *
          (∑ k ∈ Finset.Icc 0 ⌊a⌋₊,
            (k : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        ∫ x in Set.Ioc a b,
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            (∑ k ∈ Finset.Icc 0 ⌊x⌋₊,
              (k : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
  exact sum_mul_eq_sub_sub_integral_mul
    (fun k : ℕ => (k : ℂ) ^ (-(t : ℂ) * Complex.I))
    ha
    hab
    hf_diff
    hf_int

/-- Abel summation specialized to natural endpoints.  The floor terms are left
visible so the theorem is definitionally aligned with mathlib's statement. -/
theorem abelSummation_boundaryLineOnePointRealParam_finite_nat_tail_identity
    (t : ℝ)
    {N M : ℕ}
    (hNM : N ≤ M)
    (hf_diff :
      ∀ x ∈ Set.Icc ((N : ℕ) : ℝ) ((M : ℕ) : ℝ),
        DifferentiableAt ℝ (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x)
    (hf_int :
      IntegrableOn
        (deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)))
        (Set.Icc ((N : ℕ) : ℝ) ((M : ℕ) : ℝ))) :
    ∑ k ∈ Finset.Ioc ⌊((N : ℕ) : ℝ)⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
        ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)) =
      ((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ) *
          (∑ k ∈ Finset.Icc 0 ⌊((M : ℕ) : ℝ)⌋₊,
            (k : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        ((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ) *
          (∑ k ∈ Finset.Icc 0 ⌊((N : ℕ) : ℝ)⌋₊,
            (k : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        ∫ x in Set.Ioc ((N : ℕ) : ℝ) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            (∑ k ∈ Finset.Icc 0 ⌊x⌋₊,
              (k : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
  have ha : (0 : ℝ) ≤ ((N : ℕ) : ℝ) :=
    Nat.cast_nonneg N
  have hab : ((N : ℕ) : ℝ) ≤ ((M : ℕ) : ℝ) := by
    exact_mod_cast hNM
  exact abelSummation_boundaryLineOnePointRealParam_finite_tail_identity
    t ha hab hf_diff hf_int

/-- Abel summation with the canonical boundary-line cutoff as the left endpoint.
The floor terms are kept visible so this remains a direct transport of mathlib's
finite Abel identity. -/
theorem abelSummation_boundaryLineOnePointRealParam_cutoff_nat_tail_identity
    (t : ℝ)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hf_diff :
      ∀ x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        DifferentiableAt ℝ (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x)
    (hf_int :
      IntegrableOn
        (deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)))
        (Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ))) :
    ∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
        ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)) =
      ((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ) *
          (∑ k ∈ Finset.Icc 0 ⌊((M : ℕ) : ℝ)⌋₊,
            (k : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        (((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          (∑ k ∈ Finset.Icc 0 ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊,
            (k : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            (∑ k ∈ Finset.Icc 0 ⌊x⌋₊,
              (k : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
  exact abelSummation_boundaryLineOnePointRealParam_finite_nat_tail_identity
    t hNM hf_diff hf_int

/-- Exact finite Abel summation endpoint/deivative decomposition at the canonical
boundary-line cutoff, written in terms of the owner partial-sum primitive. -/
theorem abelSummation_boundaryLineOnePointRealParam_cutoff_finite_tail_endpoint_derivative_identity
    (t : ℝ)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hf_diff :
      ∀ x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        DifferentiableAt ℝ (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x)
    (hf_int :
      IntegrableOn
        (deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)))
        (Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ))) :
    ∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
        ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)) =
      ((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊ -
        (((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ -
        ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊ := by
  exact abelSummation_boundaryLineOnePointRealParam_cutoff_nat_tail_identity
    t hNM hf_diff hf_int

/-- The right endpoint in the finite Abel decomposition is controlled by the
reciprocal weight times the owner partial-sum bound. -/
theorem abelSummation_boundaryLineOnePointRealParam_right_endpoint_norm_le
    (t : ℝ)
    {M : ℕ}
    (K : ℝ)
    (hK_nonneg : 0 ≤ K)
    (hpartial :
      ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
        ⌊((M : ℕ) : ℝ)⌋₊‖ ≤ K) :
    ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          ⌊((M : ℕ) : ℝ)⌋₊‖ ≤
      (1 / (M : ℝ)) * K := by
  have hM_factor :
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ = 1 / (M : ℝ) := by
    calc
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ =
          ‖((((M : ℕ) : ℝ) : ℂ))‖⁻¹ := by
        exact norm_inv ((((M : ℕ) : ℝ) : ℂ))
      _ = ‖((M : ℝ))‖⁻¹ := by
        exact congrArg Inv.inv (Complex.norm_ofReal (M : ℝ))
      _ = (M : ℝ)⁻¹ := by
        have hM_nonneg : 0 ≤ (M : ℝ) :=
          Nat.cast_nonneg M
        exact congrArg Inv.inv (Real.norm_of_nonneg hM_nonneg)
      _ = 1 / (M : ℝ) := by
        exact (one_div (M : ℝ)).symm
  calc
    ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          ⌊((M : ℕ) : ℝ)⌋₊‖ =
        ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ *
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊‖ := by
          exact norm_mul (((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))
            (boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
              ⌊((M : ℕ) : ℝ)⌋₊)
    _ ≤ (1 / (M : ℝ)) * K := by
          exact mul_le_mul (le_of_eq hM_factor) hpartial hK_nonneg
            (norm_nonneg (((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)))

/-- The cutoff endpoint in the finite Abel decomposition is controlled by the
cutoff reciprocal weight times the owner partial-sum bound. -/
theorem abelSummation_boundaryLineOnePointRealParam_cutoff_endpoint_norm_le
    (t : ℝ)
    (K : ℝ)
    (hK_nonneg : 0 ≤ K)
    (hpartial :
      ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
        ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤ K) :
    ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤
      (1 / (⌊2 + ‖t‖⌋₊ : ℝ)) * K := by
  let N : ℕ := ⌊2 + ‖t‖⌋₊
  have hN_factor :
      ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ = 1 / (N : ℝ) := by
    calc
      ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ =
          ‖((((N : ℕ) : ℝ) : ℂ))‖⁻¹ := by
        exact norm_inv ((((N : ℕ) : ℝ) : ℂ))
      _ = ‖((N : ℝ))‖⁻¹ := by
        exact congrArg Inv.inv (Complex.norm_ofReal (N : ℝ))
      _ = (N : ℝ)⁻¹ := by
        have hN_nonneg : 0 ≤ (N : ℝ) :=
          Nat.cast_nonneg N
        exact congrArg Inv.inv (Real.norm_of_nonneg hN_nonneg)
      _ = 1 / (N : ℝ) := by
        exact (one_div (N : ℝ)).symm
  calc
    ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ =
        ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((N : ℕ) : ℝ))⌋₊‖ := by
          rfl
    _ = ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ *
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((N : ℕ) : ℝ))⌋₊‖ := by
          exact norm_mul (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))
            (boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
              ⌊(((N : ℕ) : ℝ))⌋₊)
    _ ≤ (1 / (N : ℝ)) * K := by
          exact mul_le_mul (le_of_eq hN_factor) hpartial hK_nonneg
            (norm_nonneg (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)))

/-- Finite Abel reduction for the post-cutoff boundary-line oscillatory tail.

This is the algebraic/order part of the Euler-Maclaurin tail route: once the
oscillatory primitives
`∑_{0 ≤ k ≤ floor x} k^{-it}` and the reciprocal-derivative integral have been
bounded, the finite weighted tail is bounded by the two endpoint terms and the
integral term. -/
theorem abelSummation_boundaryLineOnePointRealParam_cutoff_finite_tail_norm_le
    (t : ℝ)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hf_diff :
      ∀ x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        DifferentiableAt ℝ (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x)
    (hf_int :
      IntegrableOn
        (deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)))
        (Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ)))
    (K I : ℝ)
    (hK_nonneg : 0 ≤ K)
    (hpartial :
      ∀ x : ℝ,
        x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ) →
        ‖∑ k ∈ Finset.Icc 0 ⌊x⌋₊,
          (k : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ≤ K)
    (hintegral :
      ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            (∑ k ∈ Finset.Icc 0 ⌊x⌋₊,
              (k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤ I) :
    ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
        ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      (1 / (M : ℝ)) * K +
        (1 / (⌊2 + ‖t‖⌋₊ : ℝ)) * K + I := by
  let N : ℕ := ⌊2 + ‖t‖⌋₊
  let a : ℝ := ((N : ℕ) : ℝ)
  let b : ℝ := ((M : ℕ) : ℝ)
  let SM : ℂ :=
    ∑ k ∈ Finset.Icc 0 ⌊b⌋₊,
      (k : ℂ) ^ (-(t : ℂ) * Complex.I)
  let SN : ℂ :=
    ∑ k ∈ Finset.Icc 0 ⌊a⌋₊,
      (k : ℂ) ^ (-(t : ℂ) * Complex.I)
  let J : ℂ :=
    ∫ x in Set.Ioc a b,
      deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
        (∑ k ∈ Finset.Icc 0 ⌊x⌋₊,
          (k : ℂ) ^ (-(t : ℂ) * Complex.I))
  have hidentity :
      (∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
          ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))) =
        ((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ) * SM -
          (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN - J := by
    exact abelSummation_boundaryLineOnePointRealParam_cutoff_nat_tail_identity
      t hNM hf_diff hf_int
  have hM_mem :
      b ∈ Set.Icc a b := by
    exact ⟨by exact_mod_cast hNM, le_rfl⟩
  have hN_mem :
      a ∈ Set.Icc a b := by
    exact ⟨le_rfl, by exact_mod_cast hNM⟩
  have hSM_norm : ‖SM‖ ≤ K :=
    hpartial b hM_mem
  have hSN_norm : ‖SN‖ ≤ K :=
    hpartial a hN_mem
  have hM_factor :
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ = 1 / (M : ℝ) := by
    calc
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ =
          ‖((((M : ℕ) : ℝ) : ℂ))‖⁻¹ := by
        exact norm_inv ((((M : ℕ) : ℝ) : ℂ))
      _ = ‖((M : ℝ))‖⁻¹ := by
        exact congrArg Inv.inv (Complex.norm_ofReal (M : ℝ))
      _ = (M : ℝ)⁻¹ := by
        have hM_nonneg : 0 ≤ (M : ℝ) :=
          Nat.cast_nonneg M
        exact congrArg Inv.inv (Real.norm_of_nonneg hM_nonneg)
      _ = 1 / (M : ℝ) := by
        exact (one_div (M : ℝ)).symm
  have hN_factor :
      ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ = 1 / (N : ℝ) := by
    calc
      ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ =
          ‖((((N : ℕ) : ℝ) : ℂ))‖⁻¹ := by
        exact norm_inv ((((N : ℕ) : ℝ) : ℂ))
      _ = ‖((N : ℝ))‖⁻¹ := by
        exact congrArg Inv.inv (Complex.norm_ofReal (N : ℝ))
      _ = (N : ℝ)⁻¹ := by
        have hN_nonneg : 0 ≤ (N : ℝ) :=
          Nat.cast_nonneg N
        exact congrArg Inv.inv (Real.norm_of_nonneg hN_nonneg)
      _ = 1 / (N : ℝ) := by
        exact (one_div (N : ℝ)).symm
  have hM_term :
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM‖ ≤
        (1 / (M : ℝ)) * K := by
    calc
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM‖ =
          ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ * ‖SM‖ := by
        exact norm_mul (((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) SM
      _ ≤ (1 / (M : ℝ)) * K := by
        exact mul_le_mul (le_of_eq hM_factor) hSM_norm hK_nonneg
          (norm_nonneg (((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)))
  have hN_term :
      ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN‖ ≤
        (1 / (N : ℝ)) * K := by
    calc
      ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN‖ =
          ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ * ‖SN‖ := by
        exact norm_mul (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) SN
      _ ≤ (1 / (N : ℝ)) * K := by
        exact mul_le_mul (le_of_eq hN_factor) hSN_norm hK_nonneg
          (norm_nonneg (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)))
  have htriangle :
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM -
          (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN - J‖ ≤
        ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM‖ +
          ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN‖ + ‖J‖ := by
    have hfirst :
        ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM -
            (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN - J‖ ≤
          ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM -
            (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN‖ + ‖J‖ :=
      norm_sub_le
        (((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM -
          (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN)
        J
    have hsecond :
        ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM -
            (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN‖ ≤
          ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM‖ +
            ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN‖ :=
      norm_sub_le
        (((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM)
        (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN)
    exact le_trans hfirst (add_le_add_right hsecond ‖J‖)
  have hterms :
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM‖ +
          ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN‖ + ‖J‖ ≤
        (1 / (M : ℝ)) * K + (1 / (N : ℝ)) * K + I :=
    add_le_add (add_le_add hM_term hN_term) hintegral
  exact Eq.subst
    (motive := fun z : ℂ =>
      ‖z‖ ≤ (1 / (M : ℝ)) * K + (1 / (N : ℝ)) * K + I)
    hidentity.symm
    (le_trans htriangle hterms)

/-- Pointwise transport of the post-cutoff boundary-line Dirichlet tail to the
Abel-normalized oscillatory tail. -/
theorem boundaryLineOnePointRealParam_post_cutoff_dirichletTerm_eq_inv_mul_oscillation
    (t : ℝ)
    (n : ℕ) :
    (if ⌊2 + ‖t‖⌋₊ < n then
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)
      else
        0) =
      if ⌊2 + ‖t‖⌋₊ < n then
        ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))
      else
        0 := by
  by_cases hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n
  · have hn_pos : 0 < n :=
      lt_trans (boundaryLineOnePointRealParam_cutoff_pos t) hcutoff_lt_n
    have hleft :
        (if ⌊2 + ‖t‖⌋₊ < n then
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)
          else
            0) =
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t) :=
      if_pos hcutoff_lt_n
    have hterm :
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t) =
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
      boundaryLineOnePointRealParam_dirichletTerm_eq_inv_mul_oscillation_left
        t hn_pos
    have hright :
        (if ⌊2 + ‖t‖⌋₊ < n then
            ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))
          else
            0) =
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
      if_pos hcutoff_lt_n
    exact Eq.trans hleft (Eq.trans hterm hright.symm)
  · have hleft :
        (if ⌊2 + ‖t‖⌋₊ < n then
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)
          else
            0) =
          0 :=
      if_neg hcutoff_lt_n
    have hright :
        (if ⌊2 + ‖t‖⌋₊ < n then
            ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))
          else
            0) =
          0 :=
      if_neg hcutoff_lt_n
    exact Eq.trans hleft hright.symm

/-- The zeroth boundary-line Dirichlet monomial vanishes.  This is the only extra
index left after removing `Icc 1 N` from the natural-indexed Dirichlet series. -/
theorem boundaryLineOnePointRealParam_dirichletTerm_zero
    (t : ℝ) :
    (1 : ℂ) / ((0 : ℂ) ^ boundaryLineOnePointRealParam t) = 0 := by
  have hpoint_ne_zero : boundaryLineOnePointRealParam t ≠ 0 := by
    intro hpoint_zero
    have hre_zero :
        (boundaryLineOnePointRealParam t).re = (0 : ℂ).re :=
      congrArg Complex.re hpoint_zero
    have hre_one :
        (boundaryLineOnePointRealParam t).re = 1 :=
      boundaryLineOnePointRealParam_re t
    have hone_eq_zero : (1 : ℝ) = 0 :=
      Eq.trans hre_one.symm hre_zero
    exact one_ne_zero hone_eq_zero
  have hpow_zero :
      (0 : ℂ) ^ boundaryLineOnePointRealParam t = 0 := by
    exact (cpow_eq_zero_iff).mpr ⟨rfl, hpoint_ne_zero⟩
  calc
    (1 : ℂ) / ((0 : ℂ) ^ boundaryLineOnePointRealParam t) =
        (1 : ℂ) / 0 := by
          exact congrArg (fun z : ℂ => (1 : ℂ) / z) hpow_zero
    _ = 0 := by
          exact div_zero (1 : ℂ)

/-- The complement indicator obtained from removing `Icc 1 N` from the natural-indexed
Dirichlet series is exactly the post-cutoff tail indicator. -/
theorem boundaryLineOnePointRealParam_dirichlet_tail_indicator_eq_cutoff_if
    (t : ℝ)
    (N n : ℕ) :
    ({m : ℕ | m ∉ Finset.Icc 1 N}.indicator
        (fun m : ℕ =>
          (1 : ℂ) / ((m : ℂ) ^ boundaryLineOnePointRealParam t)) n) =
      if N < n then
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)
      else
        0 := by
  by_cases hN_lt_n : N < n
  · have hn_not_mem : n ∉ Finset.Icc 1 N := by
      intro hn_mem
      have hn_le_N : n ≤ N :=
        (Finset.mem_Icc.mp hn_mem).2
      exact (Nat.not_lt_of_ge hn_le_N) hN_lt_n
    have hn_mem_tail : n ∈ {m : ℕ | m ∉ Finset.Icc 1 N} :=
      hn_not_mem
    have hleft :
        ({m : ℕ | m ∉ Finset.Icc 1 N}.indicator
            (fun m : ℕ =>
              (1 : ℂ) / ((m : ℂ) ^ boundaryLineOnePointRealParam t)) n) =
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t) :=
      Set.indicator_of_mem hn_mem_tail
        (fun m : ℕ =>
          (1 : ℂ) / ((m : ℂ) ^ boundaryLineOnePointRealParam t))
    have hright :
        (if N < n then
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)
        else
          0) =
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t) :=
      if_pos hN_lt_n
    exact Eq.trans hleft hright.symm
  · by_cases hn_zero : n = 0
    · have hn_not_mem : n ∉ Finset.Icc 1 N := by
        intro hn_mem
        have hone_le_n : 1 ≤ n :=
          (Finset.mem_Icc.mp hn_mem).1
        have hone_le_zero : (1 : ℕ) ≤ 0 :=
          Eq.subst (motive := fun m : ℕ => 1 ≤ m) hn_zero hone_le_n
        exact (Nat.not_succ_le_zero 0) hone_le_zero
      have hn_mem_tail : n ∈ {m : ℕ | m ∉ Finset.Icc 1 N} :=
        hn_not_mem
      have hleft :
          ({m : ℕ | m ∉ Finset.Icc 1 N}.indicator
              (fun m : ℕ =>
                (1 : ℂ) / ((m : ℂ) ^ boundaryLineOnePointRealParam t)) n) =
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t) :=
        Set.indicator_of_mem hn_mem_tail
          (fun m : ℕ =>
            (1 : ℂ) / ((m : ℂ) ^ boundaryLineOnePointRealParam t))
      have hterm_zero :
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t) = 0 :=
        Eq.subst
          (motive := fun m : ℕ =>
            (1 : ℂ) / ((m : ℂ) ^ boundaryLineOnePointRealParam t) = 0)
          hn_zero.symm
          (boundaryLineOnePointRealParam_dirichletTerm_zero t)
      have hright :
          (if N < n then
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)
          else
            0) =
            0 :=
        if_neg hN_lt_n
      exact Eq.trans hleft (Eq.trans hterm_zero hright.symm)
    · have hn_pos : 0 < n :=
        Nat.pos_of_ne_zero hn_zero
      have hone_le_n : 1 ≤ n :=
        Nat.succ_le_of_lt hn_pos
      have hn_le_N : n ≤ N :=
        Nat.le_of_not_gt hN_lt_n
      have hn_mem_Icc : n ∈ Finset.Icc 1 N :=
        Finset.mem_Icc.mpr ⟨hone_le_n, hn_le_N⟩
      have hn_not_mem_tail : n ∉ {m : ℕ | m ∉ Finset.Icc 1 N} := by
        intro hn_mem_tail
        exact hn_mem_tail hn_mem_Icc
      have hleft :
          ({m : ℕ | m ∉ Finset.Icc 1 N}.indicator
              (fun m : ℕ =>
                (1 : ℂ) / ((m : ℂ) ^ boundaryLineOnePointRealParam t)) n) =
            0 :=
        Set.indicator_of_not_mem hn_not_mem_tail
          (fun m : ℕ =>
            (1 : ℂ) / ((m : ℂ) ^ boundaryLineOnePointRealParam t))
      have hright :
          (if N < n then
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)
          else
            0) =
            0 :=
        if_neg hN_lt_n
      exact Eq.trans hleft hright.symm

/-- Removing a finite Dirichlet truncation from a natural-indexed boundary-line
Dirichlet series gives the exact post-cutoff Dirichlet tail. -/
theorem boundaryLineOnePointRealParam_dirichlet_tail_after_cutoff_hasSum_zeta_remainder_of_dirichlet_series
    (t : ℝ)
    (N : ℕ)
    (hζ :
      HasSum
        (fun n : ℕ =>
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t))
        (riemannZeta (boundaryLineOnePointRealParam t))) :
    HasSum
        (fun n : ℕ =>
          if N < n then
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)
          else
            0)
        (riemannZeta (boundaryLineOnePointRealParam t) -
          ∑ n ∈ Finset.Icc 1 N,
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) := by
  have htail_compl :
      HasSum
        (fun x : {n : ℕ // n ∉ Finset.Icc 1 N} =>
          (1 : ℂ) / (((x : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t))
        (riemannZeta (boundaryLineOnePointRealParam t) -
          ∑ n ∈ Finset.Icc 1 N,
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) :=
    ((Finset.Icc 1 N).hasSum_iff_compl).mp hζ
  have htail_indicator :
      HasSum
        ({n : ℕ | n ∉ Finset.Icc 1 N}.indicator
          (fun n : ℕ =>
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)))
        (riemannZeta (boundaryLineOnePointRealParam t) -
          ∑ n ∈ Finset.Icc 1 N,
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) := by
    exact
      (hasSum_subtype_iff_indicator
        (s := {n : ℕ | n ∉ Finset.Icc 1 N})
        (f := fun n : ℕ =>
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t))).mp
        htail_compl
  exact htail_indicator.congr_fun
    (fun n : ℕ =>
      (boundaryLineOnePointRealParam_dirichlet_tail_indicator_eq_cutoff_if
        t N n).symm)

/-- The boundary point `1 + it` is away from the zeta pole when `|t| ≥ 1`. -/
theorem boundaryLineOnePointRealParam_ne_one_of_one_le_norm
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    boundaryLineOnePointRealParam t ≠ (1 : ℂ) := by
  intro hpoint
  have him_eq :
      t = 0 :=
    Eq.trans (boundaryLineOnePointRealParam_im t).symm
      (Eq.trans (congrArg Complex.im hpoint) rfl)
  have hnorm_eq :
      ‖t‖ = 0 :=
    norm_eq_zero.mpr him_eq
  have hone_le_zero :
      (1 : ℝ) ≤ 0 :=
    Eq.subst
      (motive := fun x : ℝ => (1 : ℝ) ≤ x)
      hnorm_eq
      ht
  exact not_lt_of_ge hone_le_zero zero_lt_one

/-- Analytic-continuation continuity of `ζ` at the boundary point `1 + it`, away
from the pole. -/
theorem boundaryLineOnePointRealParam_riemannZeta_continuousAt
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ContinuousAt riemannZeta (boundaryLineOnePointRealParam t) := by
  exact
    (differentiableAt_riemannZeta
      (boundaryLineOnePointRealParam_ne_one_of_one_le_norm t ht)).continuousAt

/-- The right-half-plane Abel family approaching the boundary point `1 + it`. -/
def boundaryLineOnePointRealParam_abscissaShift
    (σ t : ℝ) : ℂ :=
  (σ : ℂ) + (t : ℂ) * Complex.I

/-- Abel continuation of the half-plane Dirichlet identity to the boundary point
`1 + it`.

The ordinary boundary series `∑ n^{-1-it}` is not asserted to converge.  The
correct owner statement is the Abel-limit theorem: the half-plane sums
`∑ n^{-σ-it}` tend to the analytic-continuation value of `ζ` as
`σ ↓ 1`. -/
theorem boundaryLineOnePointRealParam_dirichlet_series_abel_tendsto_riemannZeta
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    Tendsto
      (fun σ : ℝ =>
        ∑' n : ℕ,
          (1 : ℂ) /
            ((n : ℂ) ^
              boundaryLineOnePointRealParam_abscissaShift σ t))
      (𝓝[>] (1 : ℝ))
      (𝓝 (riemannZeta (boundaryLineOnePointRealParam t))) := by
  have habscissa_path_continuousAt :
      ContinuousAt
        (fun σ : ℝ => boundaryLineOnePointRealParam_abscissaShift σ t)
        (1 : ℝ) := by
    unfold boundaryLineOnePointRealParam_abscissaShift
    exact
      Complex.continuous_ofReal.continuousAt.add
        continuousAt_const
  have habscissa_path_tendsto_raw :
      Tendsto
        (fun σ : ℝ => boundaryLineOnePointRealParam_abscissaShift σ t)
        (𝓝[>] (1 : ℝ))
        (𝓝 (boundaryLineOnePointRealParam_abscissaShift 1 t)) :=
    habscissa_path_continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have habscissa_path_endpoint :
      boundaryLineOnePointRealParam_abscissaShift 1 t =
        boundaryLineOnePointRealParam t := by
    exact Complex.ext rfl rfl
  have habscissa_path_tendsto_boundary :
      Tendsto
        (fun σ : ℝ => boundaryLineOnePointRealParam_abscissaShift σ t)
        (𝓝[>] (1 : ℝ))
        (𝓝 (boundaryLineOnePointRealParam t)) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun σ : ℝ => boundaryLineOnePointRealParam_abscissaShift σ t)
          (𝓝[>] (1 : ℝ))
          (𝓝 z))
      habscissa_path_endpoint
      habscissa_path_tendsto_raw
  have hzeta_path_tendsto :
      Tendsto
        (fun σ : ℝ =>
          riemannZeta (boundaryLineOnePointRealParam_abscissaShift σ t))
        (𝓝[>] (1 : ℝ))
        (𝓝 (riemannZeta (boundaryLineOnePointRealParam t))) :=
    (boundaryLineOnePointRealParam_riemannZeta_continuousAt t ht).tendsto.comp
      habscissa_path_tendsto_boundary
  have hdirichlet_eq_eventually :
      (fun σ : ℝ =>
        ∑' n : ℕ,
          (1 : ℂ) /
            ((n : ℂ) ^
              boundaryLineOnePointRealParam_abscissaShift σ t)) =ᶠ[𝓝[>] (1 : ℝ)]
        (fun σ : ℝ =>
          riemannZeta (boundaryLineOnePointRealParam_abscissaShift σ t)) := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ_re :
        (boundaryLineOnePointRealParam_abscissaShift σ t).re = σ := by
      rfl
    have hhalf_plane :
        1 < (boundaryLineOnePointRealParam_abscissaShift σ t).re :=
      Eq.subst
        (motive := fun x : ℝ => 1 < x)
        hσ_re.symm
        hσ
    exact (zeta_eq_tsum_one_div_nat_cpow hhalf_plane).symm
  exact Tendsto.congr' hdirichlet_eq_eventually hzeta_path_tendsto

/-- The Abel boundary value of the Dirichlet presentation is the analytic
continuation value of `ζ(1 + it)`. -/
theorem boundaryLineOnePointRealParam_dirichlet_series_abel_boundaryValue_eq_riemannZeta
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ∃ V : ℂ,
      Tendsto
        (fun σ : ℝ =>
          ∑' n : ℕ,
            (1 : ℂ) /
              ((n : ℂ) ^
                boundaryLineOnePointRealParam_abscissaShift σ t))
        (𝓝[>] (1 : ℝ))
        (𝓝 V) ∧
      V = riemannZeta (boundaryLineOnePointRealParam t) := by
  exact
    ⟨riemannZeta (boundaryLineOnePointRealParam t),
      boundaryLineOnePointRealParam_dirichlet_series_abel_tendsto_riemannZeta
        t ht,
      rfl⟩

/-- The Abel-damped finite cutoff prefix. -/
def abelBoundary_logarithmicPhase_dampedPrefix
    (t σ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
    (1 : ℂ) /
      ((n : ℂ) ^
        boundaryLineOnePointRealParam_abscissaShift σ t)

/-- The boundary finite cutoff prefix. -/
def abelBoundary_logarithmicPhase_boundaryPrefix
    (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
    ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))

/-- Termwise Abel-prefix continuity at the boundary point `σ = 1`.

For a fixed positive integer `n`, the half-plane term
`n^(-σ-it)` tends to its boundary logarithmic-phase value
`n⁻¹ n^(-it)`. -/
theorem abelBoundary_logarithmicPhase_dampedPrefix_term_tendsto
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n) :
    Tendsto
      (fun σ : ℝ =>
        (1 : ℂ) /
          ((n : ℂ) ^
            boundaryLineOnePointRealParam_abscissaShift σ t))
      (𝓝[>] (1 : ℝ))
      (𝓝 (((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)))) := by
  have hn_complex_ne : (n : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have habscissa_cont :
      ContinuousAt
        (fun σ : ℝ => boundaryLineOnePointRealParam_abscissaShift σ t)
        (1 : ℝ) := by
    unfold boundaryLineOnePointRealParam_abscissaShift
    exact
      Complex.continuous_ofReal.continuousAt.add
        continuousAt_const
  have habscissa_tendsto :
      Tendsto
        (fun σ : ℝ => boundaryLineOnePointRealParam_abscissaShift σ t)
        (𝓝[>] (1 : ℝ))
        (𝓝 (boundaryLineOnePointRealParam_abscissaShift 1 t)) :=
    habscissa_cont.tendsto.mono_left nhdsWithin_le_nhds
  have hterm_tendsto_raw :
      Tendsto
        (fun σ : ℝ =>
          (1 : ℂ) /
            ((n : ℂ) ^
              boundaryLineOnePointRealParam_abscissaShift σ t))
        (𝓝[>] (1 : ℝ))
        (𝓝
          ((1 : ℂ) /
            ((n : ℂ) ^
              boundaryLineOnePointRealParam_abscissaShift 1 t))) := by
    exact tendsto_const_nhds.div
      ((continuousAt_const_cpow hn_complex_ne).tendsto.comp
        habscissa_tendsto)
  have habscissa_endpoint :
      boundaryLineOnePointRealParam_abscissaShift 1 t =
        boundaryLineOnePointRealParam t :=
    Complex.ext rfl rfl
  have hboundary_term :
      (1 : ℂ) /
            ((n : ℂ) ^
              boundaryLineOnePointRealParam_abscissaShift 1 t) =
        ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
    exact Eq.trans
      (congrArg
        (fun z : ℂ => (1 : ℂ) / ((n : ℂ) ^ z))
        habscissa_endpoint)
      (boundaryLineOnePointRealParam_dirichletTerm_eq_inv_mul_oscillation_left
        t hn)
  exact Eq.subst
    (motive := fun z : ℂ =>
      Tendsto
        (fun σ : ℝ =>
          (1 : ℂ) /
            ((n : ℂ) ^
              boundaryLineOnePointRealParam_abscissaShift σ t))
        (𝓝[>] (1 : ℝ))
        (𝓝 z))
    hboundary_term
    hterm_tendsto_raw

/-- Finite-sum Abel-prefix continuity over a fixed cutoff interval. -/
theorem abelBoundary_logarithmicPhase_dampedPrefix_sum_tendsto
    (t : ℝ)
    (N : ℕ) :
    Tendsto
      (fun σ : ℝ =>
        ∑ n ∈ Finset.Icc 1 N,
          (1 : ℂ) /
            ((n : ℂ) ^
              boundaryLineOnePointRealParam_abscissaShift σ t))
      (𝓝[>] (1 : ℝ))
      (𝓝
        (∑ n ∈ Finset.Icc 1 N,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)))) := by
  refine Finset.Tendsto.sum ?_
  intro n hn_mem
  have hn_one_le : 1 ≤ n :=
    (Finset.mem_Icc.mp hn_mem).1
  have hn_pos : 0 < n :=
    Nat.lt_of_succ_le hn_one_le
  exact abelBoundary_logarithmicPhase_dampedPrefix_term_tendsto t hn_pos

/-- The Abel-damped prefix tends to the boundary prefix as `σ → 1+`.

This is finite-sum continuity plus the term identity at the boundary point. -/
theorem abelBoundary_logarithmicPhase_dampedPrefix_tendsto_boundaryPrefix
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    Tendsto
      (fun σ : ℝ => abelBoundary_logarithmicPhase_dampedPrefix t σ)
      (𝓝[>] (1 : ℝ))
      (𝓝 (abelBoundary_logarithmicPhase_boundaryPrefix t)) := by
  exact abelBoundary_logarithmicPhase_dampedPrefix_sum_tendsto
    t ⌊2 + ‖t‖⌋₊

/-- Abel-limit identity after subtracting the damped cutoff prefix.

This is pure limit algebra from the Abel convergence of the Dirichlet
presentation: subtracting the damped finite prefix from the Abel family
subtracts the boundary prefix in the limit. -/
theorem abelBoundary_dirichletSeries_dampedPrefix_subtracted_tendsto_zeta_remainder
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (habel :
      Tendsto
        (fun σ : ℝ =>
          ∑' n : ℕ,
            (1 : ℂ) /
              ((n : ℂ) ^
                boundaryLineOnePointRealParam_abscissaShift σ t))
        (𝓝[>] (1 : ℝ))
        (𝓝 (riemannZeta (boundaryLineOnePointRealParam t)))) :
    Tendsto
      (fun σ : ℝ =>
        (∑' n : ℕ,
          (1 : ℂ) /
            ((n : ℂ) ^
              boundaryLineOnePointRealParam_abscissaShift σ t)) -
          abelBoundary_logarithmicPhase_dampedPrefix t σ)
      (𝓝[>] (1 : ℝ))
      (𝓝
        (riemannZeta (boundaryLineOnePointRealParam t) -
          abelBoundary_logarithmicPhase_boundaryPrefix t)) := by
  exact habel.sub
    (abelBoundary_logarithmicPhase_dampedPrefix_tendsto_boundaryPrefix t ht)

/-- The Abel-damped post-cutoff logarithmic-phase tail.

This is a right-half-plane object: the ordinary boundary tail at `σ = 1` is
not asserted to converge. -/
def abelBoundary_logarithmicPhase_dampedTail
    (t σ : ℝ) : ℂ :=
  (∑' n : ℕ,
    (1 : ℂ) /
      ((n : ℂ) ^
        boundaryLineOnePointRealParam_abscissaShift σ t)) -
    abelBoundary_logarithmicPhase_dampedPrefix t σ

/-- Abel-tail normalization after removing the fixed cutoff prefix.

This theorem owns the index and term normalization between the Abel-regularized
Dirichlet remainder and the damped logarithmic-phase post-cutoff tail.  It is
the place where `Icc 1 N` prefix subtraction and the identity between
`n^{-(σ+it)}` and the damped reciprocal logarithmic oscillator are matched.  No
ordinary boundary `HasSum` or undamped tail convergence is asserted here. -/
theorem abelBoundary_logarithmicPhase_dampedTail_index_normalization
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hprefix :
      Tendsto
        (fun σ : ℝ =>
          (∑' n : ℕ,
            (1 : ℂ) /
              ((n : ℂ) ^
                boundaryLineOnePointRealParam_abscissaShift σ t)) -
            abelBoundary_logarithmicPhase_dampedPrefix t σ)
        (𝓝[>] (1 : ℝ))
        (𝓝
          (riemannZeta (boundaryLineOnePointRealParam t) -
            abelBoundary_logarithmicPhase_boundaryPrefix t))) :
    Tendsto
      (fun σ : ℝ => abelBoundary_logarithmicPhase_dampedTail t σ)
      (𝓝[>] (1 : ℝ))
      (𝓝
        (riemannZeta (boundaryLineOnePointRealParam t) -
          ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
            ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)))) := by
  exact hprefix

/-- Owner convergence theorem for Abel-damped tails after the canonical cutoff.

This is the exact limiting statement behind the Abel boundary transport: the
post-cutoff Abel-damped tail converges to the analytic-continuation zeta value
with the finite cutoff truncation removed.  The proof is the fixed-prefix Abel
limit, the identity between Dirichlet terms and damped reciprocal logarithmic
oscillators in the half-plane, and the Abel limit
`boundaryLineOnePointRealParam_dirichlet_series_abel_tendsto_riemannZeta`.
It deliberately does not assert ordinary boundary `HasSum`. -/
theorem abelBoundary_logarithmicPhase_dampedTail_tendsto_zeta_remainder
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (habel :
      Tendsto
        (fun σ : ℝ =>
          ∑' n : ℕ,
            (1 : ℂ) /
              ((n : ℂ) ^
                boundaryLineOnePointRealParam_abscissaShift σ t))
        (𝓝[>] (1 : ℝ))
        (𝓝 (riemannZeta (boundaryLineOnePointRealParam t)))) :
    Tendsto
      (fun σ : ℝ => abelBoundary_logarithmicPhase_dampedTail t σ)
      (𝓝[>] (1 : ℝ))
      (𝓝
        (riemannZeta (boundaryLineOnePointRealParam t) -
          ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
            ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)))) := by
  have hprefix :
      Tendsto
        (fun σ : ℝ =>
          (∑' n : ℕ,
            (1 : ℂ) /
              ((n : ℂ) ^
                boundaryLineOnePointRealParam_abscissaShift σ t)) -
            abelBoundary_logarithmicPhase_dampedPrefix t σ)
        (𝓝[>] (1 : ℝ))
        (𝓝
          (riemannZeta (boundaryLineOnePointRealParam t) -
            abelBoundary_logarithmicPhase_boundaryPrefix t)) :=
    abelBoundary_dirichletSeries_dampedPrefix_subtracted_tendsto_zeta_remainder
      t ht habel
  exact
    abelBoundary_logarithmicPhase_dampedTail_index_normalization
      t ht hprefix

/-- A complex limit of an eventually norm-bounded family is norm-bounded by the
same constant.

This is the reusable pure-topology closure step for Abel transport: the closed
ball `{z | ‖z‖ ≤ C}` contains the eventual tail, hence contains the limit. -/
theorem complex_norm_le_of_eventually_norm_le_of_tendsto
    {ι : Type*}
    {l : Filter ι}
    [NeBot l]
    {u : ι → ℂ}
    {z : ℂ}
    {C : ℝ}
    (hu : Tendsto u l (𝓝 z))
    (hbound : ∀ᶠ i in l, ‖u i‖ ≤ C) :
    ‖z‖ ≤ C := by
  have hclosed : IsClosed {w : ℂ | ‖w‖ ≤ C} :=
    isClosed_le continuous_norm continuous_const
  exact hclosed.mem_of_tendsto hu hbound

/-- Norm transport from a uniformly bounded Abel-damped tail family to its Abel
boundary limit.

This is the topological endpoint of the Abel argument: once the damped tails are
eventually uniformly bounded as `σ → 1+` and converge to the analytic boundary
remainder, the same bound holds for the remainder. -/
theorem abelBoundary_logarithmicPhase_dampedTail_uniform_bound_transport
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hdamped_bound :
      ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
        ‖abelBoundary_logarithmicPhase_dampedTail t σ‖ ≤
          boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t)
    (hdamped :
      Tendsto
        (fun σ : ℝ => abelBoundary_logarithmicPhase_dampedTail t σ)
        (𝓝[>] (1 : ℝ))
        (𝓝
          (riemannZeta (boundaryLineOnePointRealParam t) -
            ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
              ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))))) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  let limit : ℂ :=
    riemannZeta (boundaryLineOnePointRealParam t) -
      ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
        ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))
  have htail_tendsto :
      Tendsto
        (fun σ : ℝ => abelBoundary_logarithmicPhase_dampedTail t σ)
        (𝓝[>] (1 : ℝ))
        (𝓝 limit) :=
    hdamped
  exact
    complex_norm_le_of_eventually_norm_le_of_tendsto
      htail_tendsto
      hdamped_bound

/-- In a left-neighborhood of `1`, the Abel parameter is eventually nonnegative. -/
theorem abel_left_neighborhood_eventually_nonnegative :
    ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 0 ≤ r := by
  have hpositive_nhds : ∀ᶠ r : ℝ in 𝓝 (1 : ℝ), 0 < r :=
    isOpen_Ioi.mem_nhds zero_lt_one
  exact
    (eventually_nhdsWithin_of_eventually_nhds hpositive_nhds).mono
      (fun r hr => le_of_lt hr)

/-- Algebraic step in the shifted finite Abel transform. -/
theorem abel_positive_weighted_tail_step_algebra
    (p q A B x : ℂ) :
    p * A + B + p * x =
      q * (A + x) + (B + (p - q) * (A + x)) := by
  have hcombine :
      q * (A + x) + (p - q) * (A + x) =
        p * (A + x) := by
    calc
      q * (A + x) + (p - q) * (A + x)
          = (q + (p - q)) * (A + x) :=
            (add_mul q (p - q) (A + x)).symm
      _ = p * (A + x) := by
        exact congrArg (fun z : ℂ => z * (A + x)) (add_sub_cancel_left q p)
  have hright :
      q * (A + x) + (B + (p - q) * (A + x)) =
        B + (q * (A + x) + (p - q) * (A + x)) := by
    calc
      q * (A + x) + (B + (p - q) * (A + x))
          = (q * (A + x) + B) + (p - q) * (A + x) :=
            (add_assoc (q * (A + x)) B ((p - q) * (A + x))).symm
      _ = (B + q * (A + x)) + (p - q) * (A + x) := by
        exact congrArg (fun z : ℂ => z + (p - q) * (A + x))
          (add_comm (q * (A + x)) B)
      _ = B + (q * (A + x) + (p - q) * (A + x)) :=
        add_assoc B (q * (A + x)) ((p - q) * (A + x))
  have hleft :
      p * A + B + p * x =
        B + (p * A + p * x) := by
    calc
      p * A + B + p * x
          = (B + p * A) + p * x := by
            exact congrArg (fun z : ℂ => z + p * x)
              (add_comm (p * A) B)
      _ = B + (p * A + p * x) :=
        add_assoc B (p * A) (p * x)
  calc
    p * A + B + p * x
        = B + (p * A + p * x) := hleft
    _ = B + p * (A + x) := by
      exact congrArg (fun z : ℂ => B + z) (mul_add p A x).symm
    _ = B + (q * (A + x) + (p - q) * (A + x)) := by
      exact congrArg (fun z : ℂ => B + z) hcombine.symm
    _ = q * (A + x) + (B + (p - q) * (A + x)) :=
      hright.symm

/-- Finite Abel summation identity for positive real weights on a natural tail.

The weighted finite tail is a convex positive combination of the finite partial
tail sums, plus the terminal weighted partial sum.  This is the finite
summation-by-parts identity underlying the abstract Abel theorem. -/
theorem abel_positive_weighted_tail_finite_summation_by_parts
    {u : ℕ → ℂ}
    {w : ℕ → ℝ}
    {N M : ℕ}
    (hNM : N ≤ M) :
    (∑ k ∈ Finset.Ioc N M, ((w k : ℝ) : ℂ) * u k) =
      ((w (M + 1) : ℝ) : ℂ) *
          (∑ k ∈ Finset.Ioc N M, u k) +
        ∑ k ∈ Finset.Ioc N M,
          (((w k - w (k + 1) : ℝ) : ℂ) *
            (∑ j ∈ Finset.Ioc N k, u j)) := by
  refine Nat.le_induction ?base ?step M hNM
  · have hinterval : Finset.Ioc N N = ∅ :=
      Finset.Ioc_self N
    have hleft :
        (∑ k ∈ Finset.Ioc N N, ((w k : ℝ) : ℂ) * u k) = 0 := by
      exact Eq.trans
        (congrArg
          (fun s : Finset ℕ => ∑ k ∈ s, ((w k : ℝ) : ℂ) * u k)
          hinterval)
        (Finset.sum_empty (fun k : ℕ => ((w k : ℝ) : ℂ) * u k))
    have hpartial :
        (∑ k ∈ Finset.Ioc N N, u k) = 0 := by
      exact Eq.trans
        (congrArg (fun s : Finset ℕ => ∑ k ∈ s, u k) hinterval)
        (Finset.sum_empty u)
    have hvariation :
        (∑ k ∈ Finset.Ioc N N,
          (((w k - w (k + 1) : ℝ) : ℂ) *
            (∑ j ∈ Finset.Ioc N k, u j))) = 0 := by
      exact Eq.trans
        (congrArg
          (fun s : Finset ℕ =>
            ∑ k ∈ s,
              (((w k - w (k + 1) : ℝ) : ℂ) *
                (∑ j ∈ Finset.Ioc N k, u j)))
          hinterval)
        (Finset.sum_empty
          (fun k : ℕ =>
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))))
    have hright :
        ((w (N + 1) : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc N N, u k) +
          ∑ k ∈ Finset.Ioc N N,
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j)) = 0 := by
      calc
        ((w (N + 1) : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc N N, u k) +
          ∑ k ∈ Finset.Ioc N N,
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))
            =
          ((w (N + 1) : ℝ) : ℂ) * 0 + 0 := by
            exact congrArg₂ (fun x y : ℂ => x + y)
              (congrArg (fun z : ℂ => ((w (N + 1) : ℝ) : ℂ) * z) hpartial)
              hvariation
        _ = 0 + 0 := by
          exact congrArg (fun z : ℂ => z + 0)
            (mul_zero ((w (N + 1) : ℝ) : ℂ))
        _ = 0 := zero_add 0
    exact hleft.trans hright.symm
  · intro M hNM ih
    have hleft_step :
        (∑ k ∈ Finset.Ioc N (M + 1), ((w k : ℝ) : ℂ) * u k) =
          (∑ k ∈ Finset.Ioc N M, ((w k : ℝ) : ℂ) * u k) +
            ((w (M + 1) : ℝ) : ℂ) * u (M + 1) := by
      exact Finset.sum_Ioc_succ_top hNM
    have hpartial_step :
        (∑ k ∈ Finset.Ioc N (M + 1), u k) =
          (∑ k ∈ Finset.Ioc N M, u k) + u (M + 1) := by
      exact Finset.sum_Ioc_succ_top hNM
    have hvariation_step :
        (∑ k ∈ Finset.Ioc N (M + 1),
          (((w k - w (k + 1) : ℝ) : ℂ) *
            (∑ j ∈ Finset.Ioc N k, u j))) =
          (∑ k ∈ Finset.Ioc N M,
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))) +
            (((w (M + 1) - w ((M + 1) + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N (M + 1), u j)) := by
      exact Finset.sum_Ioc_succ_top hNM
    have hdiff_cast :
        ((w (M + 1) - w ((M + 1) + 1) : ℝ) : ℂ) =
          ((w (M + 1) : ℝ) : ℂ) -
            ((w ((M + 1) + 1) : ℝ) : ℂ) :=
      Complex.ofReal_sub (w (M + 1)) (w ((M + 1) + 1))
    let A : ℂ := ∑ k ∈ Finset.Ioc N M, u k
    let B : ℂ :=
      ∑ k ∈ Finset.Ioc N M,
        (((w k - w (k + 1) : ℝ) : ℂ) *
          (∑ j ∈ Finset.Ioc N k, u j))
    let p : ℂ := ((w (M + 1) : ℝ) : ℂ)
    let q : ℂ := ((w ((M + 1) + 1) : ℝ) : ℂ)
    let x : ℂ := u (M + 1)
    have htarget_algebra :
        p * A + B + p * x =
          q * (A + x) + (B + (p - q) * (A + x)) :=
      abel_positive_weighted_tail_step_algebra p q A B x
    calc
      (∑ k ∈ Finset.Ioc N (M + 1), ((w k : ℝ) : ℂ) * u k)
          =
        (∑ k ∈ Finset.Ioc N M, ((w k : ℝ) : ℂ) * u k) +
          ((w (M + 1) : ℝ) : ℂ) * u (M + 1) := hleft_step
      _ =
        (((w (M + 1) : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc N M, u k) +
          ∑ k ∈ Finset.Ioc N M,
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))) +
          ((w (M + 1) : ℝ) : ℂ) * u (M + 1) := by
        exact congrArg
          (fun z : ℂ => z + ((w (M + 1) : ℝ) : ℂ) * u (M + 1))
          ih
      _ =
        ((w ((M + 1) + 1) : ℝ) : ℂ) *
            ((∑ k ∈ Finset.Ioc N M, u k) + u (M + 1)) +
          ((∑ k ∈ Finset.Ioc N M,
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))) +
            ((((w (M + 1) : ℝ) : ℂ) -
              ((w ((M + 1) + 1) : ℝ) : ℂ)) *
              ((∑ k ∈ Finset.Ioc N M, u k) + u (M + 1)))) := by
        exact htarget_algebra
      _ =
        ((w ((M + 1) + 1) : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc N (M + 1), u k) +
          ((∑ k ∈ Finset.Ioc N M,
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))) +
            (((w (M + 1) - w ((M + 1) + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N (M + 1), u j))) := by
        exact congrArg₂ (fun x y : ℂ => x + y)
          (congrArg
            (fun z : ℂ => ((w ((M + 1) + 1) : ℝ) : ℂ) * z)
            hpartial_step.symm)
          (congrArg₂ (fun x y : ℂ => x + y)
            rfl
            (congrArg₂ (fun x y : ℂ => x * y) hdiff_cast.symm hpartial_step.symm))
      _ =
        ((w ((M + 1) + 1) : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc N (M + 1), u k) +
          ∑ k ∈ Finset.Ioc N (M + 1),
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j)) := by
        exact congrArg
          (fun z : ℂ =>
            ((w ((M + 1) + 1) : ℝ) : ℂ) *
              (∑ k ∈ Finset.Ioc N (M + 1), u k) + z)
          hvariation_step.symm

/-- Bounded tail partial sums force the bounding constant to be nonnegative. -/
theorem abel_positive_weighted_tail_bound_constant_nonneg
    {u : ℕ → ℂ}
    {N : ℕ}
    {C : ℝ}
    (hpartial :
      ∀ K : ℕ,
        N ≤ K →
        ‖∑ k ∈ Finset.Ioc N K, u k‖ ≤ C) :
    0 ≤ C := by
  have hinterval : Finset.Ioc N N = ∅ :=
    Finset.Ioc_self N
  have hsum :
      (∑ k ∈ Finset.Ioc N N, u k) = 0 := by
    exact Eq.trans
      (congrArg (fun s : Finset ℕ => ∑ k ∈ s, u k) hinterval)
      (Finset.sum_empty u)
  have hnorm :
      ‖∑ k ∈ Finset.Ioc N N, u k‖ = 0 := by
    exact congrArg norm hsum
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ C)
      hnorm.symm
      (hpartial N le_rfl)

/-- Nonnegative adjacent weight difference from antitonicity. -/
theorem abel_positive_weighted_tail_weight_difference_nonneg
    {w : ℕ → ℝ}
    {N k : ℕ}
    (hw_antitone : ∀ a b : ℕ, N < a → a ≤ b → w b ≤ w a)
    (hk : N < k) :
    0 ≤ w k - w (k + 1) := by
  have hnext : w (k + 1) ≤ w k :=
    hw_antitone k (k + 1) hk (Nat.le_succ k)
  exact sub_nonneg.mpr hnext

/-- Finite positive-weight Abel bound from bounded finite partial tail sums. -/
theorem abel_positive_weighted_tail_finite_norm_le_of_bounded_partial_sums
    {u : ℕ → ℂ}
    {w : ℕ → ℝ}
    {N M : ℕ}
    {C : ℝ}
    (hNM : N ≤ M)
    (hpartial :
      ∀ K : ℕ,
        N ≤ K →
        ‖∑ k ∈ Finset.Ioc N K, u k‖ ≤ C)
    (hw_nonneg : ∀ k : ℕ, N < k → 0 ≤ w k)
    (hw_antitone : ∀ k l : ℕ, N < k → k ≤ l → w l ≤ w k)
    (hw_variation :
      w (M + 1) + ∑ k ∈ Finset.Ioc N M, (w k - w (k + 1)) ≤ 1) :
    ‖∑ k ∈ Finset.Ioc N M, ((w k : ℝ) : ℂ) * u k‖ ≤ C := by
  have hC_nonneg : 0 ≤ C :=
    abel_positive_weighted_tail_bound_constant_nonneg hpartial
  have hidentity :
      (∑ k ∈ Finset.Ioc N M, ((w k : ℝ) : ℂ) * u k) =
        ((w (M + 1) : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc N M, u k) +
          ∑ k ∈ Finset.Ioc N M,
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j)) :=
    abel_positive_weighted_tail_finite_summation_by_parts hNM
  have hterminal_nonneg : 0 ≤ w (M + 1) := by
    exact hw_nonneg (M + 1) (Nat.lt_succ_of_le hNM)
  have hterminal_norm :
      ‖((w (M + 1) : ℝ) : ℂ) *
          (∑ k ∈ Finset.Ioc N M, u k)‖ ≤
        w (M + 1) * C := by
    have hmul :
        ‖((w (M + 1) : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc N M, u k)‖ =
          ‖((w (M + 1) : ℝ) : ℂ)‖ *
            ‖∑ k ∈ Finset.Ioc N M, u k‖ :=
      norm_mul ((w (M + 1) : ℝ) : ℂ)
        (∑ k ∈ Finset.Ioc N M, u k)
    have hreal_norm :
        ‖((w (M + 1) : ℝ) : ℂ)‖ = w (M + 1) := by
      have hcomplex_real : ‖((w (M + 1) : ℝ) : ℂ)‖ = ‖w (M + 1)‖ :=
        RCLike.norm_ofReal (w (M + 1))
      have hreal_abs : ‖w (M + 1)‖ = w (M + 1) :=
        Real.norm_of_nonneg hterminal_nonneg
      exact hcomplex_real.trans hreal_abs
    have hmul_bound :
        ‖((w (M + 1) : ℝ) : ℂ)‖ *
            ‖∑ k ∈ Finset.Ioc N M, u k‖ ≤
          w (M + 1) * C := by
      exact mul_le_mul
        (le_of_eq hreal_norm)
        (hpartial M hNM)
        hC_nonneg
        (norm_nonneg ((w (M + 1) : ℝ) : ℂ))
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ w (M + 1) * C)
      hmul.symm
      hmul_bound
  have hsum_norm :
      ‖∑ k ∈ Finset.Ioc N M,
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))‖ ≤
        (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) * C := by
    have hterm :
        ∀ k ∈ Finset.Ioc N M,
          ‖(((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))‖ ≤
            (w k - w (k + 1)) * C := by
      intro k hk_mem
      have hk_tail : N < k :=
        (Finset.mem_Ioc.mp hk_mem).1
      have hk_le_M : k ≤ M :=
        (Finset.mem_Ioc.mp hk_mem).2
      have hdiff_nonneg : 0 ≤ w k - w (k + 1) :=
        abel_positive_weighted_tail_weight_difference_nonneg
          hw_antitone hk_tail
      have hmul :
          ‖(((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))‖ =
            ‖((w k - w (k + 1) : ℝ) : ℂ)‖ *
              ‖∑ j ∈ Finset.Ioc N k, u j‖ :=
        norm_mul ((w k - w (k + 1) : ℝ) : ℂ)
          (∑ j ∈ Finset.Ioc N k, u j)
      have hreal_norm :
          ‖((w k - w (k + 1) : ℝ) : ℂ)‖ =
            w k - w (k + 1) := by
        have hcomplex_real :
            ‖((w k - w (k + 1) : ℝ) : ℂ)‖ =
              ‖w k - w (k + 1)‖ :=
          RCLike.norm_ofReal (w k - w (k + 1))
        have hreal_abs : ‖w k - w (k + 1)‖ = w k - w (k + 1) :=
          Real.norm_of_nonneg hdiff_nonneg
        exact hcomplex_real.trans hreal_abs
      have hbound :
          ‖((w k - w (k + 1) : ℝ) : ℂ)‖ *
              ‖∑ j ∈ Finset.Ioc N k, u j‖ ≤
            (w k - w (k + 1)) * C := by
        exact mul_le_mul
          (le_of_eq hreal_norm)
          (hpartial k (Nat.le_of_lt hk_tail))
          hC_nonneg
          (norm_nonneg ((w k - w (k + 1) : ℝ) : ℂ))
      exact Eq.subst
        (motive := fun x : ℝ => x ≤ (w k - w (k + 1)) * C)
        hmul.symm
        hbound
    have hsum_le :
        ‖∑ k ∈ Finset.Ioc N M,
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))‖ ≤
          ∑ k ∈ Finset.Ioc N M,
            ‖(((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))‖ :=
      norm_sum_le
        (Finset.Ioc N M)
        (fun k : ℕ =>
          (((w k - w (k + 1) : ℝ) : ℂ) *
            (∑ j ∈ Finset.Ioc N k, u j)))
    have hsum_bound :
        (∑ k ∈ Finset.Ioc N M,
            ‖(((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))‖) ≤
          ∑ k ∈ Finset.Ioc N M, (w k - w (k + 1)) * C :=
      Finset.sum_le_sum hterm
    have hfactor :
        (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1)) * C) =
          (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) * C := by
      exact (Finset.sum_mul (Finset.Ioc N M)
        (fun k : ℕ => w k - w (k + 1)) C).symm
    exact le_trans hsum_le (hsum_bound.trans_eq hfactor)
  have htriangle :
      ‖((w (M + 1) : ℝ) : ℂ) *
            (∑ k ∈ Finset.Ioc N M, u k) +
          ∑ k ∈ Finset.Ioc N M,
            (((w k - w (k + 1) : ℝ) : ℂ) *
              (∑ j ∈ Finset.Ioc N k, u j))‖ ≤
        w (M + 1) * C +
          (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) * C :=
    (norm_add_le
      (((w (M + 1) : ℝ) : ℂ) *
        (∑ k ∈ Finset.Ioc N M, u k))
      (∑ k ∈ Finset.Ioc N M,
        (((w k - w (k + 1) : ℝ) : ℂ) *
          (∑ j ∈ Finset.Ioc N k, u j)))).trans
      (add_le_add hterminal_norm hsum_norm)
  have hvariation_mul :
      w (M + 1) * C +
          (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) * C ≤
        C := by
    have hfactor :
        w (M + 1) * C +
            (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) * C =
          (w (M + 1) +
            ∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) * C := by
      exact (add_mul (w (M + 1))
        (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) C).symm
    have hscaled :
        (w (M + 1) +
            ∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) * C ≤
          1 * C :=
      mul_le_mul_of_nonneg_right hw_variation hC_nonneg
    have hone_mul : (1 : ℝ) * C = C :=
      one_mul C
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ C)
      hfactor.symm
      (hscaled.trans_eq hone_mul)
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ C)
    hidentity.symm
    (le_trans htriangle hvariation_mul)

/-- Sequential finite partial-sum bounds pass to an existing infinite sum.

This is the topological closure step separated from Abel summation itself.  It
does not assert conditional Dirichlet convergence as a `tsum`; that input must
be supplied by a genuine `HasSum`/summability theorem for the concrete weighted
tail. -/
theorem complex_norm_le_of_hasSum_and_range_partial_bounds
    {f : ℕ → ℂ}
    {S : ℂ}
    {C : ℝ}
    (hf : HasSum f S)
    (hbound : ∀ n : ℕ, ‖∑ k ∈ Finset.range n, f k‖ ≤ C) :
    ‖S‖ ≤ C := by
  exact
    le_of_tendsto
      hf.tendsto_sum_nat.norm
      (Eventually.of_forall hbound)

/-- Existing `HasSum` plus sequential partial-sum bounds gives the corresponding
`tsum` norm bound. -/
theorem complex_norm_tsum_le_of_hasSum_and_range_partial_bounds
    {f : ℕ → ℂ}
    {S : ℂ}
    {C : ℝ}
    (hf : HasSum f S)
    (hbound : ∀ n : ℕ, ‖∑ k ∈ Finset.range n, f k‖ ≤ C) :
    ‖∑' k : ℕ, f k‖ ≤ C := by
  have hS_bound : ‖S‖ ≤ C :=
    complex_norm_le_of_hasSum_and_range_partial_bounds hf hbound
  have hS_eq_tsum : S = ∑' k : ℕ, f k :=
    hf.tsum_eq
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ C)
    hS_eq_tsum
    hS_bound

/-- The abstract Abel theorem reduced to finite summation by parts and the
standard `tsum` limit passage. -/
theorem abel_positive_weighted_tail_norm_le_of_bounded_partial_sums_from_finite
    {u : ℕ → ℂ}
    {w : ℕ → ℝ}
    {N : ℕ}
    {C : ℝ}
    (hpartial :
      ∀ M : ℕ,
        N ≤ M →
        ‖∑ k ∈ Finset.Ioc N M, u k‖ ≤ C)
    (hw_nonneg : ∀ k : ℕ, N < k → 0 ≤ w k)
    (hw_antitone : ∀ k l : ℕ, N < k → k ≤ l → w l ≤ w k)
    (hw_variation : ∀ M : ℕ, N ≤ M → w (M + 1) +
        ∑ k ∈ Finset.Ioc N M, (w k - w (k + 1)) ≤ 1)
    (hw_tendsto : Tendsto (fun M : ℕ => w M) atTop (𝓝 0))
    (hhas :
      HasSum
        (fun k : ℕ => if N < k then ((w k : ℝ) : ℂ) * u k else 0)
        (∑' k : ℕ, if N < k then ((w k : ℝ) : ℂ) * u k else 0))
    (hrange_bound :
      ∀ n : ℕ,
        ‖∑ k ∈ Finset.range n,
          if N < k then ((w k : ℝ) : ℂ) * u k else 0‖ ≤ C) :
    ‖∑' k : ℕ, if N < k then ((w k : ℝ) : ℂ) * u k else 0‖ ≤ C := by
  exact
    complex_norm_tsum_le_of_hasSum_and_range_partial_bounds
      hhas
      hrange_bound

/-- Abstract Abel transform bound from bounded finite tail sums.

This is the positive-weight summation-by-parts core: for a tail sequence whose
finite partial sums from `N` onward are bounded by `C`, a positive decreasing
weight family of total variation at most `1` gives a weighted tail bounded by
the same `C`.  This is the convex-combination form of Abel's theorem for
bounded partial sums. -/
theorem abel_positive_weighted_tail_norm_le_of_bounded_partial_sums
    {u : ℕ → ℂ}
    {w : ℕ → ℝ}
    {N : ℕ}
    {C : ℝ}
    (hpartial :
      ∀ M : ℕ,
        N ≤ M →
        ‖∑ k ∈ Finset.Ioc N M, u k‖ ≤ C) :
    (hw_nonneg : ∀ k : ℕ, N < k → 0 ≤ w k)
    (hw_antitone : ∀ k l : ℕ, N < k → k ≤ l → w l ≤ w k)
    (hw_variation : ∀ M : ℕ, N ≤ M → w (M + 1) +
        ∑ k ∈ Finset.Ioc N M, (w k - w (k + 1)) ≤ 1)
    (hw_tendsto : Tendsto (fun M : ℕ => w M) atTop (𝓝 0))
    (hhas :
      HasSum
        (fun k : ℕ => if N < k then ((w k : ℝ) : ℂ) * u k else 0)
        (∑' k : ℕ, if N < k then ((w k : ℝ) : ℂ) * u k else 0))
    (hrange_bound :
      ∀ n : ℕ,
        ‖∑ k ∈ Finset.range n,
          if N < k then ((w k : ℝ) : ℂ) * u k else 0‖ ≤ C) :
    ‖∑' k : ℕ, if N < k then ((w k : ℝ) : ℂ) * u k else 0‖ ≤ C := by
  exact
    abel_positive_weighted_tail_norm_le_of_bounded_partial_sums_from_finite
      hpartial hw_nonneg hw_antitone hw_variation hw_tendsto hhas
      hrange_bound

/-- Complement of `Icc 1 N` as a post-cutoff indicator for functions whose
zeroth term vanishes. -/
theorem nat_not_Icc_one_indicator_eq_cutoff_if_of_zero
    {E : Type*}
    [Zero E]
    (f : ℕ → E)
    (N n : ℕ)
    (hf_zero : f 0 = 0) :
    ({m : ℕ | m ∉ Finset.Icc 1 N}.indicator f n) =
      if N < n then f n else 0 := by
  by_cases hN_lt_n : N < n
  · have hn_not_mem : n ∉ Finset.Icc 1 N := by
      intro hn_mem
      have hn_le_N : n ≤ N :=
        (Finset.mem_Icc.mp hn_mem).2
      exact (Nat.not_lt_of_ge hn_le_N) hN_lt_n
    have hn_mem_tail : n ∈ {m : ℕ | m ∉ Finset.Icc 1 N} :=
      hn_not_mem
    have hleft :
        ({m : ℕ | m ∉ Finset.Icc 1 N}.indicator f n) = f n :=
      Set.indicator_of_mem hn_mem_tail f
    have hright :
        (if N < n then f n else 0) = f n :=
      if_pos hN_lt_n
    exact Eq.trans hleft hright.symm
  · by_cases hn_zero : n = 0
    · have hn_not_mem : n ∉ Finset.Icc 1 N := by
        intro hn_mem
        have hone_le_n : 1 ≤ n :=
          (Finset.mem_Icc.mp hn_mem).1
        have hone_le_zero : (1 : ℕ) ≤ 0 :=
          Eq.subst (motive := fun m : ℕ => 1 ≤ m) hn_zero hone_le_n
        exact (Nat.not_succ_le_zero 0) hone_le_zero
      have hn_mem_tail : n ∈ {m : ℕ | m ∉ Finset.Icc 1 N} :=
        hn_not_mem
      have hleft :
          ({m : ℕ | m ∉ Finset.Icc 1 N}.indicator f n) = f n :=
        Set.indicator_of_mem hn_mem_tail f
      have hf_n_zero : f n = 0 :=
        Eq.subst (motive := fun m : ℕ => f m = 0) hn_zero.symm hf_zero
      have hright :
          (if N < n then f n else 0) = 0 :=
        if_neg hN_lt_n
      exact Eq.trans hleft (Eq.trans hf_n_zero hright.symm)
    · have hn_pos : 0 < n :=
        Nat.pos_of_ne_zero hn_zero
      have hone_le_n : 1 ≤ n :=
        Nat.succ_le_of_lt hn_pos
      have hn_le_N : n ≤ N :=
        Nat.le_of_not_gt hN_lt_n
      have hn_mem_Icc : n ∈ Finset.Icc 1 N :=
        Finset.mem_Icc.mpr ⟨hone_le_n, hn_le_N⟩
      have hn_not_mem_tail : n ∉ {m : ℕ | m ∉ Finset.Icc 1 N} := by
        intro hn_mem_tail
        exact hn_mem_tail hn_mem_Icc
      have hleft :
          ({m : ℕ | m ∉ Finset.Icc 1 N}.indicator f n) = 0 :=
        Set.indicator_of_not_mem hn_not_mem_tail f
      have hright :
          (if N < n then f n else 0) = 0 :=
        if_neg hN_lt_n
      exact Eq.trans hleft hright.symm

/-- Removing the damped finite prefix from the half-plane Dirichlet series gives
the damped post-cutoff tail as an indicator `tsum`. -/
theorem abelBoundary_logarithmicPhase_dampedTail_eq_indicator_tsum
    (t σ : ℝ)
    (hσ : 1 < σ) :
    abelBoundary_logarithmicPhase_dampedTail t σ =
      ∑' k : ℕ,
        if ⌊2 + ‖t‖⌋₊ < k then
          (1 : ℂ) /
            ((k : ℂ) ^
              boundaryLineOnePointRealParam_abscissaShift σ t)
        else
          0 := by
  let N : ℕ := ⌊2 + ‖t‖⌋₊
  let f : ℕ → ℂ := fun n : ℕ =>
    (1 : ℂ) /
      ((n : ℂ) ^
        boundaryLineOnePointRealParam_abscissaShift σ t)
  have hσ_re :
      (boundaryLineOnePointRealParam_abscissaShift σ t).re = σ := by
    rfl
  have hhalf_plane :
      1 < (boundaryLineOnePointRealParam_abscissaShift σ t).re :=
    Eq.subst
      (motive := fun x : ℝ => 1 < x)
      hσ_re.symm
      hσ
  have hf_summable : Summable f :=
    (Complex.summable_one_div_nat_cpow
      (p := boundaryLineOnePointRealParam_abscissaShift σ t)).mpr
      hhalf_plane
  have hf_has :
      HasSum f (∑' n : ℕ, f n) :=
    hf_summable.hasSum
  have htail_compl :
      HasSum
        (fun x : {n : ℕ // n ∉ Finset.Icc 1 N} => f x)
        ((∑' n : ℕ, f n) - ∑ n ∈ Finset.Icc 1 N, f n) :=
    ((Finset.Icc 1 N).hasSum_iff_compl).mp hf_has
  have htail_indicator :
      HasSum
        ({n : ℕ | n ∉ Finset.Icc 1 N}.indicator f)
        ((∑' n : ℕ, f n) - ∑ n ∈ Finset.Icc 1 N, f n) := by
    exact
      (hasSum_subtype_iff_indicator
        (s := {n : ℕ | n ∉ Finset.Icc 1 N})
        (f := f)).mp
        htail_compl
  have hf_zero : f 0 = 0 := by
    have hpoint_ne_zero :
        boundaryLineOnePointRealParam_abscissaShift σ t ≠ 0 := by
      intro hpoint_zero
      have hre_zero :
          (boundaryLineOnePointRealParam_abscissaShift σ t).re = (0 : ℂ).re :=
        congrArg Complex.re hpoint_zero
      have hσ_zero : σ = 0 :=
        Eq.trans hσ_re.symm hre_zero
      have hone_lt_zero : (1 : ℝ) < 0 :=
        Eq.subst (motive := fun x : ℝ => 1 < x) hσ_zero hσ
      exact not_lt_of_ge zero_le_one hone_lt_zero
    have hpow_zero :
        (0 : ℂ) ^ boundaryLineOnePointRealParam_abscissaShift σ t = 0 := by
      exact (cpow_eq_zero_iff).mpr ⟨rfl, hpoint_ne_zero⟩
    calc
      f 0 = (1 : ℂ) /
          ((0 : ℂ) ^ boundaryLineOnePointRealParam_abscissaShift σ t) := by
        rfl
      _ = (1 : ℂ) / 0 := by
        exact congrArg (fun z : ℂ => (1 : ℂ) / z) hpow_zero
      _ = 0 := by
        exact div_zero (1 : ℂ)
  have hindicator :
      ({n : ℕ | n ∉ Finset.Icc 1 N}.indicator f) =
        (fun k : ℕ => if N < k then f k else 0) :=
    funext
      (fun n : ℕ =>
        nat_not_Icc_one_indicator_eq_cutoff_if_of_zero f N n hf_zero)
  have htail_if :
      HasSum
        (fun k : ℕ => if N < k then f k else 0)
        ((∑' n : ℕ, f n) - ∑ n ∈ Finset.Icc 1 N, f n) :=
    Eq.subst
      (motive := fun g : ℕ → ℂ =>
        HasSum g ((∑' n : ℕ, f n) - ∑ n ∈ Finset.Icc 1 N, f n))
      hindicator
      htail_indicator
  exact htail_if.tsum_eq.symm

/-- The Dirichlet damping weight for a fixed abscissa. -/
def abelBoundary_logarithmicPhase_dirichletWeight
    (σ : ℝ)
    (k : ℕ) : ℝ :=
  ((k : ℝ) ^ (1 - σ : ℝ))

/-- Exponent normal form for the Abel-damped logarithmic-phase factorization. -/
theorem abelBoundary_logarithmicPhase_damped_exponent_eq
    (t σ : ℝ) :
    ((1 - σ : ℝ) : ℂ) + (-1 : ℂ) + (-(t : ℂ) * Complex.I) =
      -boundaryLineOnePointRealParam_abscissaShift σ t := by
  unfold boundaryLineOnePointRealParam_abscissaShift
  exact Complex.ext rfl rfl

/-- Positive-natural complex-power normalization for the Abel-damped boundary
term.

This is the exact `cpow` algebra sink: split the exponent
`σ + it` into the reciprocal boundary factor and the real Dirichlet damping
weight `k^(1-σ)`. -/
theorem abelBoundary_logarithmicPhase_positiveNat_cpow_damped_factorization
    (t σ : ℝ)
    {k : ℕ}
    (hk : 0 < k) :
    (1 : ℂ) /
        ((k : ℂ) ^
          boundaryLineOnePointRealParam_abscissaShift σ t) =
      ((abelBoundary_logarithmicPhase_dirichletWeight σ k : ℝ) : ℂ) *
        (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))) := by
  let x : ℂ := (k : ℂ)
  have hx_ne : x ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt hk)
  have hk_nonneg : (0 : ℝ) ≤ (k : ℝ) :=
    Nat.cast_nonneg k
  have hweight :
      ((abelBoundary_logarithmicPhase_dirichletWeight σ k : ℝ) : ℂ) =
        x ^ (((1 - σ : ℝ) : ℂ)) := by
    exact Complex.ofReal_cpow hk_nonneg (1 - σ)
  have hinv :
      ((k : ℂ)⁻¹ : ℂ) = x ^ (-1 : ℂ) := by
    exact (Complex.cpow_neg_one x).symm
  have hproduct_one :
      ((abelBoundary_logarithmicPhase_dirichletWeight σ k : ℝ) : ℂ) *
          (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))) =
        x ^ (((1 - σ : ℝ) : ℂ)) *
          (x ^ (-1 : ℂ) * x ^ (-(t : ℂ) * Complex.I)) := by
    exact congrArg₂ (fun a b : ℂ => a * b) hweight
      (congrArg₂ (fun a b : ℂ => a * b) hinv rfl)
  have hproduct_two :
      x ^ (((1 - σ : ℝ) : ℂ)) *
          (x ^ (-1 : ℂ) * x ^ (-(t : ℂ) * Complex.I)) =
        x ^ ((((1 - σ : ℝ) : ℂ) + (-1 : ℂ)) +
          (-(t : ℂ) * Complex.I)) := by
    have hleft :
        x ^ (((1 - σ : ℝ) : ℂ)) * x ^ (-1 : ℂ) =
          x ^ (((1 - σ : ℝ) : ℂ) + (-1 : ℂ)) :=
      (Complex.cpow_add (((1 - σ : ℝ) : ℂ)) (-1 : ℂ) hx_ne).symm
    have hright :
        x ^ ((((1 - σ : ℝ) : ℂ) + (-1 : ℂ)) +
            (-(t : ℂ) * Complex.I)) =
          x ^ (((1 - σ : ℝ) : ℂ) + (-1 : ℂ)) *
            x ^ (-(t : ℂ) * Complex.I) :=
      Complex.cpow_add
        (((1 - σ : ℝ) : ℂ) + (-1 : ℂ))
        (-(t : ℂ) * Complex.I)
        hx_ne
    calc
      x ^ (((1 - σ : ℝ) : ℂ)) *
          (x ^ (-1 : ℂ) * x ^ (-(t : ℂ) * Complex.I)) =
          (x ^ (((1 - σ : ℝ) : ℂ)) * x ^ (-1 : ℂ)) *
            x ^ (-(t : ℂ) * Complex.I) := by
        exact (mul_assoc
          (x ^ (((1 - σ : ℝ) : ℂ)))
          (x ^ (-1 : ℂ))
          (x ^ (-(t : ℂ) * Complex.I))).symm
      _ = x ^ (((1 - σ : ℝ) : ℂ) + (-1 : ℂ)) *
            x ^ (-(t : ℂ) * Complex.I) := by
        exact congrArg
          (fun y : ℂ => y * x ^ (-(t : ℂ) * Complex.I))
          hleft
      _ = x ^ ((((1 - σ : ℝ) : ℂ) + (-1 : ℂ)) +
            (-(t : ℂ) * Complex.I)) := by
        exact hright.symm
  have hproduct_three :
      x ^ ((((1 - σ : ℝ) : ℂ) + (-1 : ℂ)) +
          (-(t : ℂ) * Complex.I)) =
        x ^ (-boundaryLineOnePointRealParam_abscissaShift σ t) := by
    exact congrArg (fun z : ℂ => x ^ z)
      (abelBoundary_logarithmicPhase_damped_exponent_eq t σ)
  have hleft :
      (1 : ℂ) /
          ((k : ℂ) ^
            boundaryLineOnePointRealParam_abscissaShift σ t) =
        x ^ (-boundaryLineOnePointRealParam_abscissaShift σ t) := by
    calc
      (1 : ℂ) /
          ((k : ℂ) ^
            boundaryLineOnePointRealParam_abscissaShift σ t) =
          ((x ^ boundaryLineOnePointRealParam_abscissaShift σ t)⁻¹) := by
        exact one_div (x ^ boundaryLineOnePointRealParam_abscissaShift σ t)
      _ = x ^ (-boundaryLineOnePointRealParam_abscissaShift σ t) := by
        exact (Complex.cpow_neg x
          (boundaryLineOnePointRealParam_abscissaShift σ t)).symm
  exact Eq.trans hleft
    (Eq.trans hproduct_three.symm
      (Eq.trans hproduct_two.symm hproduct_one.symm))

/-- A right-half-plane post-cutoff term is the Dirichlet damping weight times the boundary
oscillatory term. -/
theorem abelBoundary_logarithmicPhase_dampedTail_term_eq_weighted_boundaryTerm
    (t σ : ℝ)
    {k : ℕ}
    (hk : 0 < k) :
    (1 : ℂ) /
        ((k : ℂ) ^
          boundaryLineOnePointRealParam_abscissaShift σ t) =
      ((abelBoundary_logarithmicPhase_dirichletWeight σ k : ℝ) : ℂ) *
        (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))) := by
  exact
    abelBoundary_logarithmicPhase_positiveNat_cpow_damped_factorization
      t σ hk

/-- The damped tail indicator `tsum` is the abstract Abel weighted tail. -/
theorem abelBoundary_logarithmicPhase_dampedTail_indicator_tsum_eq_abstract_weighted_tail
    (t σ : ℝ)
    (hσ : 1 < σ) :
    (∑' k : ℕ,
        if ⌊2 + ‖t‖⌋₊ < k then
          (1 : ℂ) /
            ((k : ℂ) ^
              boundaryLineOnePointRealParam_abscissaShift σ t)
        else
          0) =
      ∑' k : ℕ,
        if ⌊2 + ‖t‖⌋₊ < k then
          ((abelBoundary_logarithmicPhase_dirichletWeight σ k : ℝ) : ℂ) *
            (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)))
        else
          0 := by
  exact tsum_congr
    (fun k => by
      by_cases hk : ⌊2 + ‖t‖⌋₊ < k
      · have hkpos : 0 < k :=
          lt_trans (boundaryLineOnePointRealParam_cutoff_pos t) hk
        exact Eq.trans
          (if_pos hk)
          (Eq.trans
            (abelBoundary_logarithmicPhase_dampedTail_term_eq_weighted_boundaryTerm
              t σ hkpos)
            (if_pos hk).symm)
      · exact Eq.trans (if_neg hk) (if_neg hk).symm)

/-- Identification of the logarithmic-phase damped tail with the abstract Abel
weighted tail.

For `σ > 1`, the damping weight is `k^(1 - σ)`, not a geometric weight. -/
theorem abelBoundary_logarithmicPhase_dampedTail_eq_abstract_weighted_tail
    (t σ : ℝ)
    (hσ : 1 < σ) :
    abelBoundary_logarithmicPhase_dampedTail t σ =
      ∑' k : ℕ,
        if ⌊2 + ‖t‖⌋₊ < k then
          ((abelBoundary_logarithmicPhase_dirichletWeight σ k : ℝ) : ℂ) *
            (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)))
        else
          0 := by
  exact Eq.trans
    (abelBoundary_logarithmicPhase_dampedTail_eq_indicator_tsum t σ hσ)
    (abelBoundary_logarithmicPhase_dampedTail_indicator_tsum_eq_abstract_weighted_tail
      t σ hσ)

/-- Dirichlet weights after the cutoff are nonnegative. -/
theorem abelBoundary_logarithmicPhase_dirichletWeight_nonneg
    (σ : ℝ)
    {k : ℕ}
    (hk : 0 < k) :
    0 ≤ abelBoundary_logarithmicPhase_dirichletWeight σ k := by
  exact Real.rpow_nonneg (Nat.cast_nonneg k) (1 - σ)

/-- Dirichlet weights are decreasing on the post-cutoff tail for `σ > 1`. -/
theorem abelBoundary_logarithmicPhase_dirichletWeight_antitone
    (σ : ℝ)
    (hσ : 1 < σ) :
    ∀ k l : ℕ,
      0 < k →
      k ≤ l →
      abelBoundary_logarithmicPhase_dirichletWeight σ l ≤
        abelBoundary_logarithmicPhase_dirichletWeight σ k := by
  intro k l hk hkl
  have hk_real_pos : (0 : ℝ) < (k : ℝ) := by
    exact Nat.cast_pos.mpr hk
  have hkl_real : (k : ℝ) ≤ (l : ℝ) := by
    exact Nat.cast_le.mpr hkl
  have hexponent_nonpos : 1 - σ ≤ 0 :=
    sub_nonpos.mpr (le_of_lt hσ)
  exact
    Real.rpow_le_rpow_of_nonpos
      hk_real_pos
      hkl_real
      hexponent_nonpos

/-- The first Dirichlet weight on any natural tail is at most one. -/
theorem abelBoundary_logarithmicPhase_dirichletWeight_succ_le_one
    (σ : ℝ)
    (hσ : 1 < σ)
    (N : ℕ) :
    abelBoundary_logarithmicPhase_dirichletWeight σ (N + 1) ≤ 1 := by
  have hone_le_base : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
    exact Nat.cast_le.mpr (Nat.succ_le_succ (Nat.zero_le N))
  have hexponent_nonpos : 1 - σ ≤ 0 :=
    sub_nonpos.mpr (le_of_lt hσ)
  exact
    Real.rpow_le_one_of_one_le_of_nonpos
      hone_le_base
      hexponent_nonpos

/-- The additive cancellation used in adjacent-difference telescoping. -/
theorem real_adjacent_difference_telescope_step
    (a b c : ℝ) :
    a + (b + (c - a)) = c + b := by
  calc
    a + (b + (c - a)) = a + ((c - a) + b) := by
      exact congrArg (fun x : ℝ => a + x) (add_comm b (c - a))
    _ = (a + (c - a)) + b := by
      exact (add_assoc a (c - a) b).symm
    _ = c + b := by
      exact congrArg (fun x : ℝ => x + b) (add_sub_cancel_left a c)

/-- Finite variation of any adjacent-difference tail telescopes on `Ioc`. -/
theorem finset_Ioc_adjacent_difference_telescope
    (w : ℕ → ℝ)
    (N M : ℕ)
    (hNM : N ≤ M) :
    w (M + 1) + ∑ k ∈ Finset.Ioc N M, (w k - w (k + 1)) =
      w (N + 1) := by
  refine Nat.le_induction ?_ ?_ M hNM
  · have hinterval : Finset.Ioc N N = ∅ :=
      Finset.Ioc_self N
    have hsum :
        (∑ k ∈ Finset.Ioc N N, (w k - w (k + 1))) = 0 := by
      exact Eq.trans
        (congrArg
          (fun s : Finset ℕ => ∑ k ∈ s, (w k - w (k + 1)))
          hinterval)
        (Finset.sum_empty (fun k : ℕ => w k - w (k + 1)))
    calc
      w (N + 1) + ∑ k ∈ Finset.Ioc N N, (w k - w (k + 1)) =
          w (N + 1) + 0 := by
        exact congrArg (fun x : ℝ => w (N + 1) + x) hsum
      _ = w (N + 1) := by
        exact add_zero (w (N + 1))
  · intro M hNM hM
    have hsum_succ :
        (∑ k ∈ Finset.Ioc N (M + 1), (w k - w (k + 1))) =
          (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) +
            (w (M + 1) - w ((M + 1) + 1)) := by
      exact Finset.sum_Ioc_succ_top hNM
        (fun k : ℕ => w k - w (k + 1))
    calc
      w ((M + 1) + 1) +
          ∑ k ∈ Finset.Ioc N (M + 1), (w k - w (k + 1)) =
          w ((M + 1) + 1) +
            ((∑ k ∈ Finset.Ioc N M, (w k - w (k + 1))) +
              (w (M + 1) - w ((M + 1) + 1))) := by
        exact congrArg (fun x : ℝ => w ((M + 1) + 1) + x) hsum_succ
      _ = w (M + 1) +
            ∑ k ∈ Finset.Ioc N M, (w k - w (k + 1)) := by
        exact real_adjacent_difference_telescope_step
          (w ((M + 1) + 1))
          (∑ k ∈ Finset.Ioc N M, (w k - w (k + 1)))
          (w (M + 1))
      _ = w (N + 1) := hM

/-- The finite variation of Dirichlet weights on a post-cutoff tail is at most
the first weight, hence at most `1`. -/
theorem abelBoundary_logarithmicPhase_dirichletWeight_variation_le_one
    (σ : ℝ)
    (hσ : 1 < σ)
    (N : ℕ) :
    ∀ M : ℕ,
      N ≤ M →
      abelBoundary_logarithmicPhase_dirichletWeight σ (M + 1) +
          ∑ k ∈ Finset.Ioc N M,
            (abelBoundary_logarithmicPhase_dirichletWeight σ k -
              abelBoundary_logarithmicPhase_dirichletWeight σ (k + 1)) ≤
        1 := by
  intro M hNM
  have htelescopes :
      abelBoundary_logarithmicPhase_dirichletWeight σ (M + 1) +
          ∑ k ∈ Finset.Ioc N M,
            (abelBoundary_logarithmicPhase_dirichletWeight σ k -
              abelBoundary_logarithmicPhase_dirichletWeight σ (k + 1)) =
        abelBoundary_logarithmicPhase_dirichletWeight σ (N + 1) :=
    finset_Ioc_adjacent_difference_telescope
      (abelBoundary_logarithmicPhase_dirichletWeight σ)
      N M hNM
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ 1)
      htelescopes.symm
      (abelBoundary_logarithmicPhase_dirichletWeight_succ_le_one σ hσ N)

/-- Dirichlet weights tend to zero for `σ > 1`. -/
theorem abelBoundary_logarithmicPhase_dirichletWeight_tendsto_zero
    (σ : ℝ)
    (hσ : 1 < σ) :
    Tendsto
      (fun k : ℕ => abelBoundary_logarithmicPhase_dirichletWeight σ k)
      atTop
      (𝓝 0) := by
  have hexponent_pos : 0 < σ - 1 :=
    sub_pos.mpr hσ
  have hraw :
      Tendsto
        (fun x : ℝ => x ^ (-(σ - 1)))
        atTop
        (𝓝 0) :=
    tendsto_rpow_neg_atTop hexponent_pos
  have hnat :
      Tendsto
        (fun k : ℕ => ((k : ℝ) ^ (-(σ - 1))))
        atTop
        (𝓝 0) :=
    hraw.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  exact hnat.congr'
    (Eventually.of_forall
      (fun k : ℕ =>
        congrArg (fun exponent : ℝ => ((k : ℝ) ^ exponent))
          (neg_sub σ 1)))

/-- The concrete Abel-damped logarithmic-phase tail is an honest `HasSum`.

This is the summability input missing from the generic Abel API: for `σ > 1`
the damped tail is absolutely summable, so its `tsum` is represented by a
genuine `HasSum`. -/
theorem abelBoundary_logarithmicPhase_abstract_weighted_tail_hasSum
    (t σ : ℝ)
    (hσ : 1 < σ) :
    HasSum
      (fun k : ℕ =>
        if ⌊2 + ‖t‖⌋₊ < k then
          ((abelBoundary_logarithmicPhase_dirichletWeight σ k : ℝ) : ℂ) *
            (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)))
        else
          0)
      (∑' k : ℕ,
        if ⌊2 + ‖t‖⌋₊ < k then
          ((abelBoundary_logarithmicPhase_dirichletWeight σ k : ℝ) : ℂ) *
            (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)))
        else
          0) := by
  let p : ℂ := boundaryLineOnePointRealParam_abscissaShift σ t
  let f : ℕ → ℂ := fun k : ℕ => (1 : ℂ) / ((k : ℂ) ^ p)
  let g : ℕ → ℂ := fun k : ℕ =>
    if ⌊2 + ‖t‖⌋₊ < k then f k else 0
  let h : ℕ → ℂ := fun k : ℕ =>
    if ⌊2 + ‖t‖⌋₊ < k then
      ((abelBoundary_logarithmicPhase_dirichletWeight σ k : ℝ) : ℂ) *
        (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)))
    else
      0
  have hp_re : p.re = σ := by
    rfl
  have hp_half_plane : 1 < p.re :=
    Eq.subst
      (motive := fun x : ℝ => 1 < x)
      hp_re.symm
      hσ
  have hf_summable : Summable f :=
    (Complex.summable_one_div_nat_cpow (p := p)).mpr hp_half_plane
  have hg_summable : Summable g :=
    Summable.indicator hf_summable {k : ℕ | ⌊2 + ‖t‖⌋₊ < k}
  have h_eq_g : h = g := by
    exact funext
      (fun k : ℕ => by
        by_cases hk : ⌊2 + ‖t‖⌋₊ < k
        · have hk_pos : 0 < k :=
            lt_trans (boundaryLineOnePointRealParam_cutoff_pos t) hk
          have hfactor :
              f k =
                ((abelBoundary_logarithmicPhase_dirichletWeight σ k : ℝ) : ℂ) *
                  (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))) :=
            abelBoundary_logarithmicPhase_positiveNat_cpow_damped_factorization
              t σ hk_pos
          have hh :
              h k =
                ((abelBoundary_logarithmicPhase_dirichletWeight σ k : ℝ) : ℂ) *
                  (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))) :=
            if_pos hk
          have hg :
              g k = f k :=
            if_pos hk
          exact Eq.trans hh (Eq.trans hfactor.symm hg.symm)
        · have hh : h k = 0 :=
            if_neg hk
          have hg : g k = 0 :=
            if_neg hk
          exact Eq.trans hh hg.symm)
  have hh_summable : Summable h :=
    Summable.congr hg_summable
      (fun k : ℕ => (congrFun h_eq_g k).symm)
  have htarget_eq : h =
      (fun k : ℕ =>
        if ⌊2 + ‖t‖⌋₊ < k then
          ((abelBoundary_logarithmicPhase_dirichletWeight σ k : ℝ) : ℂ) *
            (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)))
        else
          0) :=
    rfl
  exact Eq.subst
    (motive := fun q : ℕ → ℂ => HasSum q (∑' k : ℕ, q k))
    htarget_eq
    hh_summable.hasSum

/-- Filtering a finite range by a strict post-cutoff condition gives the
corresponding `Ioc` interval with terminal index `n - 1`. -/
theorem finset_range_filter_strict_cutoff_eq_Ioc_pred
    (N n : ℕ)
    (hn : 0 < n) :
    (Finset.range n).filter (fun k : ℕ => N < k) =
      Finset.Ioc N (n - 1) := by
  ext k
  constructor
  · intro hk
    have hk_range : k ∈ Finset.range n :=
      (Finset.mem_filter.mp hk).1
    have hN_lt_k : N < k :=
      (Finset.mem_filter.mp hk).2
    have hk_lt_n : k < n :=
      Finset.mem_range.mp hk_range
    have hk_le_pred : k ≤ n - 1 :=
      (Nat.lt_iff_le_pred hn).mp hk_lt_n
    exact Finset.mem_Ioc.mpr ⟨hN_lt_k, hk_le_pred⟩
  · intro hk
    have hN_lt_k : N < k :=
      (Finset.mem_Ioc.mp hk).1
    have hk_le_pred : k ≤ n - 1 :=
      (Finset.mem_Ioc.mp hk).2
    have hk_lt_n : k < n :=
      (Nat.lt_iff_le_pred hn).mpr hk_le_pred
    have hk_range : k ∈ Finset.range n :=
      Finset.mem_range.mpr hk_lt_n
    exact Finset.mem_filter.mpr ⟨hk_range, hN_lt_k⟩

/-- Concrete range partial sums of the Abel-damped logarithmic-phase tail are
bounded by the finite Abel estimate.

This is the range-index bridge needed to feed the topological `HasSum` limit
passage. The proof is finite index bookkeeping: a range partial sum of the
post-cutoff indicator tail is either empty or an `Ioc` finite tail, and the
finite Abel estimate applies to that terminal index. -/
theorem abelBoundary_logarithmicPhase_abstract_weighted_tail_range_bound_of_finiteAbel
    (t σ C : ℝ)
    (hσ : 1 < σ)
    (hfinite :
      ∀ M : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ M →
        ‖∑ k ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
            ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤ C) :
    ∀ n : ℕ,
      ‖∑ k ∈ Finset.range n,
        if ⌊2 + ‖t‖⌋₊ < k then
          ((abelBoundary_logarithmicPhase_dirichletWeight σ k : ℝ) : ℂ) *
            (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)))
        else
          0‖ ≤ C := by
  let N : ℕ := ⌊2 + ‖t‖⌋₊
  let u : ℕ → ℂ := fun k : ℕ =>
    ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))
  let w : ℕ → ℝ := abelBoundary_logarithmicPhase_dirichletWeight σ
  have hC_nonneg : 0 ≤ C :=
    abel_positive_weighted_tail_bound_constant_nonneg
      (u := u) (N := N) hfinite
  intro n
  by_cases hn_zero : n = 0
  · have hrange_empty : Finset.range n = ∅ := by
      exact Eq.subst
        (motive := fun m : ℕ => Finset.range m = ∅)
        hn_zero.symm
        Finset.range_zero
    have hsum_zero :
        (∑ k ∈ Finset.range n,
          if N < k then ((w k : ℝ) : ℂ) * u k else 0) = 0 := by
      exact Eq.trans
        (congrArg
          (fun s : Finset ℕ =>
            ∑ k ∈ s, if N < k then ((w k : ℝ) : ℂ) * u k else 0)
          hrange_empty)
        (Finset.sum_empty
          (fun k : ℕ => if N < k then ((w k : ℝ) : ℂ) * u k else 0))
    have hnorm_zero :
        ‖∑ k ∈ Finset.range n,
          if N < k then ((w k : ℝ) : ℂ) * u k else 0‖ = 0 :=
      congrArg norm hsum_zero
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ C)
      hnorm_zero.symm
      hC_nonneg
  · have hn_pos : 0 < n :=
      Nat.pos_of_ne_zero hn_zero
    have hsum_filter :
        (∑ k ∈ Finset.range n,
          if N < k then ((w k : ℝ) : ℂ) * u k else 0) =
          ∑ k ∈ (Finset.range n).filter (fun k : ℕ => N < k),
            ((w k : ℝ) : ℂ) * u k := by
      exact (Finset.sum_filter (s := Finset.range n)
        (p := fun k : ℕ => N < k)
        (f := fun k : ℕ => ((w k : ℝ) : ℂ) * u k)).symm
    have hfilter_eq :
        (Finset.range n).filter (fun k : ℕ => N < k) =
          Finset.Ioc N (n - 1) :=
      finset_range_filter_strict_cutoff_eq_Ioc_pred N n hn_pos
    have hsum_ioc :
        (∑ k ∈ Finset.range n,
          if N < k then ((w k : ℝ) : ℂ) * u k else 0) =
          ∑ k ∈ Finset.Ioc N (n - 1), ((w k : ℝ) : ℂ) * u k :=
      Eq.trans hsum_filter
        (congrArg
          (fun s : Finset ℕ => ∑ k ∈ s, ((w k : ℝ) : ℂ) * u k)
          hfilter_eq)
    by_cases hN_le_pred : N ≤ n - 1
    · have hfinite_bound :
          ‖∑ k ∈ Finset.Ioc N (n - 1), ((w k : ℝ) : ℂ) * u k‖ ≤ C :=
        abel_positive_weighted_tail_finite_norm_le_of_bounded_partial_sums
          (u := u) (w := w) (N := N) (M := n - 1) (C := C)
          hN_le_pred
          hfinite
          (fun k hk =>
            abelBoundary_logarithmicPhase_dirichletWeight_nonneg σ
              (lt_of_le_of_lt (Nat.zero_le N) hk))
          (fun k l hk hkl =>
            abelBoundary_logarithmicPhase_dirichletWeight_antitone σ hσ k l
              (lt_of_le_of_lt (Nat.zero_le N) hk) hkl)
          (abelBoundary_logarithmicPhase_dirichletWeight_variation_le_one σ hσ
            N (n - 1) hN_le_pred)
      exact Eq.subst
        (motive := fun z : ℂ => ‖z‖ ≤ C)
        hsum_ioc.symm
        hfinite_bound
    · have hpred_le_N : n - 1 ≤ N :=
        Nat.le_of_lt (Nat.lt_of_not_ge hN_le_pred)
      have hioc_empty : Finset.Ioc N (n - 1) = ∅ :=
        Finset.Ioc_eq_empty_of_le hpred_le_N
      have hsum_ioc_zero :
          (∑ k ∈ Finset.Ioc N (n - 1), ((w k : ℝ) : ℂ) * u k) = 0 := by
        exact Eq.trans
          (congrArg
            (fun s : Finset ℕ => ∑ k ∈ s, ((w k : ℝ) : ℂ) * u k)
            hioc_empty)
          (Finset.sum_empty (fun k : ℕ => ((w k : ℝ) : ℂ) * u k))
      have hsum_zero :
          (∑ k ∈ Finset.range n,
            if N < k then ((w k : ℝ) : ℂ) * u k else 0) = 0 :=
        Eq.trans hsum_ioc hsum_ioc_zero
      have hnorm_zero :
          ‖∑ k ∈ Finset.range n,
            if N < k then ((w k : ℝ) : ℂ) * u k else 0‖ = 0 :=
        congrArg norm hsum_zero
      exact Eq.subst
        (motive := fun x : ℝ => x ≤ C)
        hnorm_zero.symm
        hC_nonneg

/-- Transport the abstract Abel weighted-tail bound to the logarithmic-phase
damped tail as `σ → 1+`. -/
theorem abelBoundary_logarithmicPhase_dampedTail_bound_of_abstract_abel
    (t : ℝ)
    (C : ℝ)
    (hfinite :
      ∀ M : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ M →
        ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
            ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤ C) :
    ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      ‖abelBoundary_logarithmicPhase_dampedTail t σ‖ ≤ C := by
  have hpartial :
      ∀ M : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ M →
        ‖∑ k ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
            ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤ C := by
    intro M hM
    have hleft :
        ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ = ⌊2 + ‖t‖⌋₊ :=
      Nat.floor_natCast ⌊2 + ‖t‖⌋₊
    have hright :
        ⌊((M : ℕ) : ℝ)⌋₊ = M :=
      Nat.floor_natCast M
    have hsource :
        ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
            ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤ C :=
      hfinite M hM
    have hleft_transport :
        ‖∑ k ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
            ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤ C :=
      Eq.subst
        (motive := fun N : ℕ =>
          ‖∑ k ∈ Finset.Ioc N ⌊((M : ℕ) : ℝ)⌋₊,
              ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤ C)
        hleft
        hsource
    exact
      Eq.subst
        (motive := fun R : ℕ =>
          ‖∑ k ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ R,
              ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤ C)
        hright
        hleft_transport
  have habstract :
      ∀ σ : ℝ,
        1 < σ →
        ‖∑' k : ℕ,
          if ⌊2 + ‖t‖⌋₊ < k then
            ((abelBoundary_logarithmicPhase_dirichletWeight σ k : ℝ) : ℂ) *
              (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)))
          else
            0‖ ≤ C := by
    intro σ hσ
    exact
      abel_positive_weighted_tail_norm_le_of_bounded_partial_sums
      (u := fun k : ℕ =>
        ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)))
      (w := abelBoundary_logarithmicPhase_dirichletWeight σ)
      (N := ⌊2 + ‖t‖⌋₊)
      (C := C)
      hpartial
      (fun k hk =>
        abelBoundary_logarithmicPhase_dirichletWeight_nonneg σ
          (lt_of_le_of_lt (Nat.zero_le ⌊2 + ‖t‖⌋₊) hk))
      (fun k l hk hkl =>
        abelBoundary_logarithmicPhase_dirichletWeight_antitone σ hσ k l
          (lt_of_le_of_lt (Nat.zero_le ⌊2 + ‖t‖⌋₊) hk) hkl)
      (abelBoundary_logarithmicPhase_dirichletWeight_variation_le_one σ hσ
        ⌊2 + ‖t‖⌋₊)
      (abelBoundary_logarithmicPhase_dirichletWeight_tendsto_zero σ hσ)
      (abelBoundary_logarithmicPhase_abstract_weighted_tail_hasSum t σ hσ)
      (abelBoundary_logarithmicPhase_abstract_weighted_tail_range_bound_of_finiteAbel
        t σ C hσ hpartial)
  filter_upwards [self_mem_nhdsWithin] with σ hσ
  have htail_eq :
      abelBoundary_logarithmicPhase_dampedTail t σ =
        ∑' k : ℕ,
          if ⌊2 + ‖t‖⌋₊ < k then
            ((abelBoundary_logarithmicPhase_dirichletWeight σ k : ℝ) : ℂ) *
              (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)))
          else
            0 :=
    abelBoundary_logarithmicPhase_dampedTail_eq_abstract_weighted_tail
      t σ hσ
  exact Eq.subst
    (motive := fun z : ℂ => ‖z‖ ≤ C)
    htail_eq.symm
    (habstract σ hσ)

/-- Abel damping theorem for a tail with bounded finite partial sums.

If every finite tail partial sum after the cutoff is bounded by `C`, then the
Abel-damped tail is eventually bounded by `C` as the damping parameter tends to
the boundary from the right.  This is the positive-weight Abel summation
principle: the damped tail is obtained as the limit of convex weighted averages
of the bounded finite partial sums. -/
theorem abel_damped_tail_norm_le_of_bounded_finite_tail_sums
    (t : ℝ)
    (C : ℝ)
    (hfinite :
      ∀ M : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ M →
        ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
            ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤ C) :
    ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      ‖abelBoundary_logarithmicPhase_dampedTail t σ‖ ≤ C := by
  exact abelBoundary_logarithmicPhase_dampedTail_bound_of_abstract_abel
    t C hfinite

/-- Abel damping comparison for the logarithmic-phase post-cutoff tail.

This is the honest bridge from uniformly bounded finite post-cutoff Abel sums to
an eventual bound for the Abel-damped post-cutoff tail as `σ → 1+`.  Its proof
is Abel's theorem for bounded partial sums applied to the cutoff tail, not
ordinary convergence of the undamped boundary series. -/
theorem abelBoundary_logarithmicPhase_dampedTail_bound_of_finiteAbel
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hfinite :
      ∀ M : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ M →
        ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
            ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
          boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t) :
    ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      ‖abelBoundary_logarithmicPhase_dampedTail t σ‖ ≤
        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  exact
    abel_damped_tail_norm_le_of_bounded_finite_tail_sums
      t
      (boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t)
      hfinite

/-- Deep Abel-limit transport for the canonical post-cutoff logarithmic-phase
tail.

This is the limiting passage from the uniformly bounded finite Abel tails after
`N = ⌊2 + |t|⌋₊` to the analytic-continuation boundary value supplied by
`boundaryLineOnePointRealParam_dirichlet_series_abel_tendsto_riemannZeta`.  It
does not assert ordinary convergence of the boundary Dirichlet series. -/
theorem abelBoundary_logarithmicPhase_oscillatory_tail_after_cutoff_bound_of_finiteAbel
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hfinite :
      ∀ M : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ M →
        ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
            ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
          boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t)
    (habel :
      Tendsto
        (fun σ : ℝ =>
          ∑' n : ℕ,
            (1 : ℂ) /
              ((n : ℂ) ^
                boundaryLineOnePointRealParam_abscissaShift σ t))
        (𝓝[>] (1 : ℝ))
        (𝓝 (riemannZeta (boundaryLineOnePointRealParam t)))) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  have htails :
      Tendsto
        (fun σ : ℝ => abelBoundary_logarithmicPhase_dampedTail t σ)
        (𝓝[>] (1 : ℝ))
        (𝓝
          (riemannZeta (boundaryLineOnePointRealParam t) -
            ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
              ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)))) :=
    abelBoundary_logarithmicPhase_dampedTail_tendsto_zeta_remainder
      t ht habel
  have hdamped_bound :
      ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
        ‖abelBoundary_logarithmicPhase_dampedTail t σ‖ ≤
          boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t :=
    abelBoundary_logarithmicPhase_dampedTail_bound_of_finiteAbel
      t ht hfinite
  exact
    abelBoundary_logarithmicPhase_dampedTail_uniform_bound_transport
      t ht hdamped_bound htails

/-- Owner Abel-boundary API for the canonical post-cutoff oscillatory tail.

This is the boundary-value passage from finite Abel tails to the analytic
continuation value of `ζ(1 + it)`, after the endpoint and derivative-integral
Abel estimates have been isolated. The proof chain is Abel summation for finite
tails, the logarithmic-phase first-derivative estimate, Abel limiting from the
right half-plane, and the Dirichlet-continuation boundary identity; cf.
Titchmarsh, *The Theory of the Riemann Zeta-function*, §3.5. -/
theorem abelBoundary_logarithmicPhase_oscillatory_tail_after_cutoff_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  have hfinite :
      ∀ M : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ M →
        ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
            ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
          boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
    intro M hNM
    exact
      boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelTail_norm_le
        t ht hNM
  have habel :
      Tendsto
        (fun σ : ℝ =>
          ∑' n : ℕ,
            (1 : ℂ) /
              ((n : ℂ) ^
                boundaryLineOnePointRealParam_abscissaShift σ t))
        (𝓝[>] (1 : ℝ))
        (𝓝 (riemannZeta (boundaryLineOnePointRealParam t))) :=
    boundaryLineOnePointRealParam_dirichlet_series_abel_tendsto_riemannZeta
      t ht
  exact
    abelBoundary_logarithmicPhase_oscillatory_tail_after_cutoff_bound_of_finiteAbel
      t ht hfinite habel

/-- Explicit Abel/Euler-Maclaurin estimate for the exact post-cutoff oscillatory
boundary-line zeta remainder.

Intended proof chain:
apply `abelSummation_boundaryLineOnePointRealParam_cutoff_nat_tail_identity` to
finite tails, bound the oscillatory partial sums
`∑_{0 ≤ n ≤ M} n^{-it}` on the range `1 ≤ |t|` by the logarithmic-phase
Euler/van-der-Corput estimate, use
`positive_nat_reciprocal_antitone` for the decreasing Abel weight, identify the
Abel boundary value with the analytic continuation of `ζ`, and combine the endpoint
and integral estimates at `N = ⌊2 + |t|⌋₊`; cf. Titchmarsh, *The Theory of the
Riemann Zeta-function*, §3.5. -/
theorem abelEulerMaclaurin_boundaryLineOnePointRealParam_oscillatory_tail_after_cutoff_norm_le_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  exact abelBoundary_logarithmicPhase_oscillatory_tail_after_cutoff_bound t ht

/-- Exact post-cutoff oscillatory tail after the cutoff `N = ⌊2 + |t|⌋₊`.

The proof is now only the conjunction of the peeled Dirichlet-continuation
identity and the explicit Abel/Euler-Maclaurin endpoint/integral estimate. -/
theorem eulerMaclaurin_boundaryLineOnePointRealParam_oscillatory_tail_after_cutoff_hasSum_norm_le_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  exact
    (abelEulerMaclaurin_boundaryLineOnePointRealParam_oscillatory_tail_after_cutoff_norm_le_explicit
      t ht)

/-- Transport a boundary-line tail norm estimate from the Abel-normalized oscillatory
finite truncation back to the original Dirichlet monomials. -/
theorem boundaryLineOnePointRealParam_tail_norm_le_explicit_of_oscillatory_tail_norm_le_explicit
    (t : ℝ)
    (hosc :
      ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
      ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  have hfinite :
      (∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) =
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
    boundaryLineOnePointRealParam_finite_truncation_eq_inv_mul_oscillation_sum
      t ⌊2 + ‖t‖⌋₊
  have htail_transport :
      riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t) =
      riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
    congrArg
      (fun S : ℂ => riemannZeta (boundaryLineOnePointRealParam t) - S)
      hfinite
  exact Eq.subst
    (motive := fun z : ℂ =>
      ‖z‖ ≤ boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t)
    htail_transport.symm
    hosc

/-- Classical Euler-Maclaurin tail estimate after truncation at
`N = ⌊2 + |t|⌋₊`.

This is now only the mechanical transport from the oscillatory Abel-tail form
`n⁻¹ n⁻ⁱᵗ` back to the original boundary-line Dirichlet monomials. -/
theorem eulerMaclaurin_boundaryLineOnePointRealParam_classical_tail_estimate
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
      ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  have htail :
      ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t :=
    eulerMaclaurin_boundaryLineOnePointRealParam_oscillatory_tail_after_cutoff_hasSum_norm_le_explicit
      t ht
  exact boundaryLineOnePointRealParam_tail_norm_le_explicit_of_oscillatory_tail_norm_le_explicit
    t htail

/-- The exact Abel/Euler-Maclaurin tail estimate after truncation at
`N = ⌊2 + |t|⌋₊`. -/
theorem eulerMaclaurin_riemannZeta_one_add_it_tail_after_cutoff_norm_le_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
      ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  exact eulerMaclaurin_boundaryLineOnePointRealParam_classical_tail_estimate t ht

/-- Public Abel/Euler-Maclaurin zeta-tail root.  The proof is now only name
transport from the canonical Euler-Maclaurin tail estimate at the exact cutoff. -/
theorem abelEulerMaclaurin_riemannZeta_one_add_it_tail_norm_le_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
      ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  exact eulerMaclaurin_riemannZeta_one_add_it_tail_after_cutoff_norm_le_explicit t ht

/-- Triangle-inequality split of `ζ(1+it)` into its Abel/Euler-Maclaurin tail
and finite Dirichlet truncation. -/
theorem boundaryLineOnePointRealParam_zeta_norm_le_tail_plus_truncation
    (t : ℝ) :
    ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
      ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ +
      ‖∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ := by
  let S : ℂ :=
    ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
      (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)
  have hsplit :
      riemannZeta (boundaryLineOnePointRealParam t) =
        (riemannZeta (boundaryLineOnePointRealParam t) - S) + S := by
    exact (sub_add_cancel (riemannZeta (boundaryLineOnePointRealParam t)) S).symm
  exact Eq.subst
    (motive := fun w : ℂ =>
      ‖w‖ ≤ ‖riemannZeta (boundaryLineOnePointRealParam t) - S‖ + ‖S‖)
    hsplit.symm
    (norm_add_le (riemannZeta (boundaryLineOnePointRealParam t) - S) S)

/-- The analytic tail estimate and finite harmonic majorant give the intermediate
explicit-tail boundary estimate. -/
theorem abelEulerMaclaurin_riemannZeta_one_add_it_vertical_explicit_tail_add_log_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
        (1 + Real.log (2 + ‖t‖)) := by
  have hsplit :
      ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
        ‖riemannZeta (boundaryLineOnePointRealParam t) -
          ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ +
        ‖∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ :=
    boundaryLineOnePointRealParam_zeta_norm_le_tail_plus_truncation t
  have htail :
      ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t :=
    abelEulerMaclaurin_riemannZeta_one_add_it_tail_norm_le_explicit t ht
  have hfinite :
      ‖∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
        1 + Real.log (2 + ‖t‖) :=
    boundaryLineOnePointRealParam_finite_dirichlet_truncation_norm_le_one_add_log t
  have htail_plus_finite :
      ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ +
        ‖∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
          (1 + Real.log (2 + ‖t‖)) :=
    add_le_add htail hfinite
  exact le_trans hsplit htail_plus_finite

/-- On the large vertical range, the intermediate `2 + log` bound is absorbed by
`3 * log`. -/
theorem two_add_log_two_add_norm_le_three_mul_log_two_add_norm_of_one_le_norm
    {t : ℝ}
    (ht : 1 ≤ ‖t‖) :
    2 + Real.log (2 + ‖t‖) ≤
      3 * Real.log (2 + ‖t‖) := by
  let L : ℝ := Real.log (2 + ‖t‖)
  have hlog_one : (1 : ℝ) ≤ L :=
    one_le_log_two_add_norm_of_one_le_norm ht
  have htwo_le_twoL : (2 : ℝ) ≤ 2 * L := by
    calc
      (2 : ℝ) = 2 * 1 := by
        exact (mul_one 2).symm
      _ ≤ 2 * L :=
        mul_le_mul_of_nonneg_left hlog_one zero_le_two
  calc
    2 + Real.log (2 + ‖t‖) = 2 + L := rfl
    _ ≤ 2 * L + L :=
      add_le_add_right htwo_le_twoL L
    _ = (2 + 1) * L := by
      exact (add_mul 2 1 L).symm
    _ = 3 * L := rfl
    _ = 3 * Real.log (2 + ‖t‖) := rfl

/-- The enlarged logarithmic argument `3 + |t|` is absorbed by twice the
canonical boundary-line logarithm. -/
theorem log_three_add_norm_le_two_mul_log_two_add_norm
    (t : ℝ) :
    Real.log (3 + ‖t‖) ≤
      2 * Real.log (2 + ‖t‖) := by
  let x : ℝ := ‖t‖
  have hx_nonneg : 0 ≤ x :=
    norm_nonneg t
  have hleft_pos : 0 < 3 + x := by
    have hthree_pos : (0 : ℝ) < 3 :=
      three_pos
    exact lt_of_lt_of_le hthree_pos (le_add_of_nonneg_right hx_nonneg)
  have hright_pos : 0 < 2 * (2 + x) := by
    have htwo_pos : (0 : ℝ) < 2 :=
      zero_lt_two
    have harg_pos : 0 < 2 + x :=
      lt_of_lt_of_le zero_lt_two (le_add_of_nonneg_right hx_nonneg)
    exact mul_pos htwo_pos harg_pos
  have harg_ne : (2 : ℝ) + x ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_two (le_add_of_nonneg_right hx_nonneg))
  have htwo_ne : (2 : ℝ) ≠ 0 :=
    ne_of_gt zero_lt_two
  have harg_ge_two : (2 : ℝ) ≤ 2 + x :=
    le_add_of_nonneg_right hx_nonneg
  have hthree_le :
      3 + x ≤ 2 * (2 + x) := by
    have hx_le_two_x : x ≤ 2 * x := by
      calc
        x = 1 * x := by
          exact (one_mul x).symm
        _ ≤ 2 * x :=
          mul_le_mul_of_nonneg_right one_le_two hx_nonneg
    calc
      3 + x ≤ 4 + 2 * x :=
        add_le_add (by exact three_le_four) hx_le_two_x
      _ = 2 * (2 + x) := by
        exact (left_distrib 2 2 x).symm
  have hlog_le :
      Real.log (3 + x) ≤ Real.log (2 * (2 + x)) :=
    Real.log_le_log hleft_pos hthree_le
  have hlog_mul :
      Real.log (2 * (2 + x)) =
        Real.log 2 + Real.log (2 + x) :=
    Real.log_mul htwo_ne harg_ne
  have hlog_two_le :
      Real.log 2 ≤ Real.log (2 + x) :=
    Real.log_le_log zero_lt_two harg_ge_two
  have hsum_le :
      Real.log 2 + Real.log (2 + x) ≤
        Real.log (2 + x) + Real.log (2 + x) :=
    add_le_add_right hlog_two_le (Real.log (2 + x))
  calc
    Real.log (3 + ‖t‖) = Real.log (3 + x) := rfl
    _ ≤ Real.log (2 * (2 + x)) :=
      hlog_le
    _ = Real.log 2 + Real.log (2 + x) :=
      hlog_mul
    _ ≤ Real.log (2 + x) + Real.log (2 + x) :=
      hsum_le
    _ = 2 * Real.log (2 + x) := by
      exact (two_mul (Real.log (2 + x))).symm
    _ = 2 * Real.log (2 + ‖t‖) := rfl

/-- The explicit Abel-tail constant plus finite-truncation logarithmic term is
absorbed by an absolute multiple of the canonical logarithm. -/
theorem boundaryLineOnePointRealParam_explicit_tail_plus_log_le_constant_log
    {t : ℝ}
    (ht : 1 ≤ ‖t‖) :
    boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
        (1 + Real.log (2 + ‖t‖)) ≤
      38 * Real.log (2 + ‖t‖) := by
  let L : ℝ := Real.log (2 + ‖t‖)
  have hL_one : (1 : ℝ) ≤ L :=
    one_le_log_two_add_norm_of_one_le_norm ht
  have hL_nonneg : 0 ≤ L :=
    le_trans zero_le_one hL_one
  have hfour_le : (4 : ℝ) ≤ 4 * L := by
    calc
      (4 : ℝ) = 4 * 1 := by
        exact (mul_one 4).symm
      _ ≤ 4 * L :=
        mul_le_mul_of_nonneg_left hL_one (by exact zero_le_four)
  have hone_le : (1 : ℝ) ≤ L :=
    hL_one
  have hlog_three :
      Real.log (3 + ‖t‖) ≤ 2 * L := by
    exact log_three_add_norm_le_two_mul_log_two_add_norm t
  have hsixteen_log :
      16 * Real.log (3 + ‖t‖) ≤ 32 * L := by
    calc
      16 * Real.log (3 + ‖t‖) ≤ 16 * (2 * L) :=
        mul_le_mul_of_nonneg_left hlog_three
          (show (0 : ℝ) ≤ 16 from Nat.cast_nonneg 16)
      _ = (16 * 2) * L := by
        exact (mul_assoc 16 2 L).symm
      _ = 32 * L := rfl
  have htail :
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t ≤
        36 * L := by
    calc
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t =
          4 + 16 * Real.log (3 + ‖t‖) := rfl
      _ ≤ 4 * L + 32 * L :=
        add_le_add hfour_le hsixteen_log
      _ = (4 + 32) * L := by
        exact (add_mul 4 32 L).symm
      _ = 36 * L := rfl
  have hfinite :
      1 + Real.log (2 + ‖t‖) ≤ 2 * L := by
    calc
      1 + Real.log (2 + ‖t‖) = 1 + L := rfl
      _ ≤ L + L :=
        add_le_add_right hone_le L
      _ = 2 * L := by
        exact (two_mul L).symm
  calc
    boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
        (1 + Real.log (2 + ‖t‖)) ≤
      36 * L + 2 * L :=
        add_le_add htail hfinite
    _ = (36 + 2) * L := by
      exact (add_mul 36 2 L).symm
    _ = 38 * L := rfl
    _ = 38 * Real.log (2 + ‖t‖) := rfl

/-- The finite truncation plus the Abel/Euler-Maclaurin tail gives the logarithmic
boundary estimate with the explicit Abel-tail constant still visible. -/
theorem abelEulerMaclaurin_riemannZeta_one_add_it_vertical_log_growth_bound_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
        (1 + Real.log (2 + ‖t‖)) := by
  exact
    abelEulerMaclaurin_riemannZeta_one_add_it_vertical_explicit_tail_add_log_bound
      t ht

/-- The exact analytic Abel/Euler-Maclaurin tail estimate on `ζ(1 + it)`.

Intended proof chain:
Dirichlet truncation at `N = ⌊2 + |t|⌋₊`, Abel summation for the oscillatory tail
`∑ n^{-1-it}`, Euler-Maclaurin control of the endpoint remainder, the harmonic
majorant for the finite part, and the standard logarithmic normalization; cf.
Titchmarsh, *The Theory of the Riemann Zeta-function*, §3.5. -/
theorem abelEulerMaclaurin_riemannZeta_one_add_it_vertical_log_growth_bound_analytic :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
          A * Real.log (2 + ‖t‖) := by
  refine ⟨38, ?_, ?_⟩
  · exact Nat.cast_pos.mpr (by decide : (0 : ℕ) < 38)
  · intro t ht
    have hexplicit :
        ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
          boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
            (1 + Real.log (2 + ‖t‖)) :=
      abelEulerMaclaurin_riemannZeta_one_add_it_vertical_log_growth_bound_explicit
        t ht
    have habsorb :
        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
            (1 + Real.log (2 + ‖t‖)) ≤
          38 * Real.log (2 + ‖t‖) :=
      boundaryLineOnePointRealParam_explicit_tail_plus_log_le_constant_log ht
    exact le_trans hexplicit habsorb

/-- Euler-Maclaurin/Abel-truncation boundary estimate for the Riemann zeta function on
`1 + it`.

This is the canonical classical number-theoretic input: truncate the Dirichlet
series at height comparable to `|t|`, control the tail by Euler-Maclaurin or Abel
summation, and obtain the standard logarithmic bound; cf. Titchmarsh, §3.5. -/
theorem abelEulerMaclaurin_riemannZeta_one_add_it_vertical_log_growth_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
          A * Real.log (2 + ‖t‖) := by
  exact abelEulerMaclaurin_riemannZeta_one_add_it_vertical_log_growth_bound_analytic

/-- The historical owner-root spelling for the boundary-line logarithmic zeta estimate.

The proof is only name transport from the canonical Abel/Euler-Maclaurin theorem on
`ζ(1 + it)`. -/
theorem eulerMaclaurin_riemannZeta_boundaryLineOnePointRealParam_vertical_log_growth_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
          A * Real.log (2 + ‖t‖) := by
  exact abelEulerMaclaurin_riemannZeta_one_add_it_vertical_log_growth_bound

/-- Classical real-parameter logarithmic vertical growth of raw zeta on `1 + it`.

This is the smallest analytic number-theory input: truncate the Dirichlet series at
height comparable to `|t|`, control the tail by Abel summation or Euler-Maclaurin,
and obtain the standard `O(log (2 + |t|))` boundary-line bound; cf. Titchmarsh,
The Theory of the Riemann Zeta-function, §3.5. -/
theorem classicalZeta_riemannZeta_boundaryLineOnePointRealParam_vertical_log_growth_bound_from_EulerMaclaurin_truncation :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
          A * Real.log (2 + ‖t‖) := by
  exact
    eulerMaclaurin_riemannZeta_boundaryLineOnePointRealParam_vertical_log_growth_bound

/-- Classical real-parameter logarithmic vertical growth of zeta on the line `1 + it`.

This is only the definitional transport from the raw boundary-line zeta value to the
local real-parameter name. -/
theorem classicalZeta_boundaryLineOneZetaRealParam_vertical_log_growth_bound_from_EulerMaclaurin_truncation :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖boundaryLineOneZetaRealParam t‖ ≤ A * Real.log (2 + ‖t‖) := by
  rcases
    classicalZeta_riemannZeta_boundaryLineOnePointRealParam_vertical_log_growth_bound_from_EulerMaclaurin_truncation
    with ⟨A, hA_pos, hbound⟩
  refine ⟨A, hA_pos, ?_⟩
  intro t ht
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ A * Real.log (2 + ‖t‖))
    (show ‖riemannZeta (boundaryLineOnePointRealParam t)‖ =
        ‖boundaryLineOneZetaRealParam t‖ from rfl)
    (hbound t ht)

/-- A logarithmic zeta estimate on `re = 1` gives the log-linear estimate for the
pole-cleared product `(s - 1)ζ(s)`. -/
theorem boundaryLine_one_zeta_log_growth_bound_to_poleCleared_log_linear_growth_bound
    (hzeta :
      ∃ A : ℝ,
        0 < A ∧
        ∀ w : ℂ,
          w.re = 1 →
          1 ≤ ‖w.im‖ →
          ‖riemannZeta w‖ ≤ A * Real.log (2 + ‖w.im‖)) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
  rcases hzeta with ⟨A, hA_pos, hzeta_bound⟩
  refine ⟨A, hA_pos, ?_⟩
  intro w hw_re hw_im
  have hpole_norm :
      ‖w - 1‖ ≤ 1 + ‖w.im‖ :=
    boundaryLine_one_sub_one_norm_le_vertical_height hw_re
  have hzeta_norm :
      ‖riemannZeta w‖ ≤ A * Real.log (2 + ‖w.im‖) :=
    hzeta_bound w hw_re hw_im
  have hzeta_rhs_nonneg :
      0 ≤ A * Real.log (2 + ‖w.im‖) :=
    le_trans (norm_nonneg (riemannZeta w)) hzeta_norm
  have hheight_nonneg : 0 ≤ 1 + ‖w.im‖ :=
    le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg w.im))
  have hmul :
      ‖w - 1‖ * ‖riemannZeta w‖ ≤
        (1 + ‖w.im‖) * (A * Real.log (2 + ‖w.im‖)) :=
    mul_le_mul hpole_norm hzeta_norm hzeta_rhs_nonneg hheight_nonneg
  have htarget_eq :
      (1 + ‖w.im‖) * (A * Real.log (2 + ‖w.im‖)) =
        A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
    calc
      (1 + ‖w.im‖) * (A * Real.log (2 + ‖w.im‖)) =
          ((1 + ‖w.im‖) * A) * Real.log (2 + ‖w.im‖) := by
        exact mul_assoc (1 + ‖w.im‖) A (Real.log (2 + ‖w.im‖))
      _ =
          (A * (1 + ‖w.im‖)) * Real.log (2 + ‖w.im‖) := by
        exact congrArg
          (fun x : ℝ => x * Real.log (2 + ‖w.im‖))
          (mul_comm (1 + ‖w.im‖) A)
      _ =
          A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
        exact rfl
  have hnorm_eq :
      ‖(w - 1) * riemannZeta w‖ = ‖w - 1‖ * ‖riemannZeta w‖ :=
    norm_mul (w - 1) (riemannZeta w)
  exact Eq.subst
    (motive := fun x : ℝ =>
      ‖(w - 1) * riemannZeta w‖ ≤ x)
    htarget_eq
    (Eq.subst
      (motive := fun x : ℝ => x ≤
        (1 + ‖w.im‖) * (A * Real.log (2 + ‖w.im‖)))
      hnorm_eq.symm
      hmul)

/-- Classical logarithmic vertical growth of zeta on the boundary line `re = 1`, proved
by Euler-Maclaurin/Abel truncation.

This is the exact analytic number-theory input: truncate the Dirichlet series at
height comparable to `|t|`, control the tail by Abel summation or Euler-Maclaurin,
and obtain the standard `O(log (2 + |t|))` boundary-line bound. -/
theorem classicalZeta_boundaryLine_one_vertical_log_growth_bound_from_EulerMaclaurin_truncation :
    ∃ A : ℝ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖riemannZeta w‖ ≤ A * Real.log (2 + ‖w.im‖) := by
  rcases
    classicalZeta_boundaryLineOneZetaRealParam_vertical_log_growth_bound_from_EulerMaclaurin_truncation
    with ⟨A, hA_pos, hbound⟩
  refine ⟨A, hA_pos, ?_⟩
  intro w hw_re hw_im
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ A * Real.log (2 + ‖w.im‖))
    (norm_riemannZeta_boundaryLine_one_eq_norm_realParam hw_re).symm
    (hbound w.im hw_im)

/-- Classical logarithmic vertical growth of zeta on the boundary line `re = 1`, in the
standard partial-summation/truncation form. -/
theorem classicalZeta_boundaryLine_one_vertical_log_growth_bound_from_truncation :
    ∃ A : ℝ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖riemannZeta w‖ ≤ A * Real.log (2 + ‖w.im‖) := by
  exact
    classicalZeta_boundaryLine_one_vertical_log_growth_bound_from_EulerMaclaurin_truncation

/-- Classical log-linear vertical growth of the pole-cleared zeta factor on the boundary
line `re = 1`, obtained from the raw boundary-line zeta estimate and the elementary
pole-clearing factor. -/
theorem classicalZeta_poleCleared_boundaryLine_one_vertical_log_linear_growth_bound_from_truncation :
    ∃ A : ℝ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
  exact boundaryLine_one_zeta_log_growth_bound_to_poleCleared_log_linear_growth_bound
    classicalZeta_boundaryLine_one_vertical_log_growth_bound_from_truncation

/-- The logarithmic boundary-line zeta estimate gives the log-linear estimate for the
pole-cleared product `(s - 1)ζ(s)`. -/
theorem classicalZeta_poleCleared_boundaryLine_one_vertical_log_linear_growth_bound_of_zeta_log
    (hzeta :
      ∃ A : ℝ,
        0 < A ∧
        ∀ w : ℂ,
          w.re = 1 →
          1 ≤ ‖w.im‖ →
          ‖riemannZeta w‖ ≤ A * Real.log (2 + ‖w.im‖)) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
  exact boundaryLine_one_zeta_log_growth_bound_to_poleCleared_log_linear_growth_bound hzeta

/-- Classical log-linear vertical growth of the pole-cleared zeta factor on the boundary
line `re = 1`.  This is the standard boundary-line zeta estimate in the form needed before
coarsening to a finite polynomial envelope. -/
theorem classicalZeta_poleCleared_boundaryLine_one_vertical_log_linear_growth_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
  exact classicalZeta_poleCleared_boundaryLine_one_vertical_log_linear_growth_bound_from_truncation

/-- A log-linear vertical-height boundary estimate gives the coarser polynomial envelope
used by the normalization chain. -/
theorem boundaryLine_one_log_linear_growth_bound_to_polynomial_growth_bound
    {f : ℂ → ℂ}
    (hlog :
      ∃ A : ℝ,
        0 < A ∧
        ∀ w : ℂ,
          w.re = 1 →
          1 ≤ ‖w.im‖ →
          ‖f w‖ ≤ A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖)) :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖f w‖ ≤ A * (1 + ‖w.im‖) ^ m := by
  rcases hlog with ⟨A, hA_pos, hbound⟩
  refine ⟨2 * A, 2, ?_, ?_⟩
  · exact mul_pos two_pos hA_pos
  intro w hw_re hw_im
  let H : ℝ := 1 + ‖w.im‖
  have hH_nonneg : 0 ≤ H :=
    le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg w.im))
  have hH_ge_one : (1 : ℝ) ≤ H :=
    le_add_of_nonneg_right (norm_nonneg w.im)
  have hlog_arg_pos : 0 < 2 + ‖w.im‖ := by
    exact add_pos_of_pos_of_nonneg (by norm_num : (0 : ℝ) < 2) (norm_nonneg w.im)
  have hlog_le_arg :
      Real.log (2 + ‖w.im‖) ≤ 2 + ‖w.im‖ :=
    Real.log_le_self hlog_arg_pos.le
  have harg_eq : 2 + ‖w.im‖ = H + 1 := by
    change 2 + ‖w.im‖ = (1 + ‖w.im‖) + 1
    ring
  have harg_le_twoH : 2 + ‖w.im‖ ≤ 2 * H := by
    rw [harg_eq]
    nlinarith
  have hlog_le_twoH :
      Real.log (2 + ‖w.im‖) ≤ 2 * H :=
    le_trans hlog_le_arg harg_le_twoH
  have hleft_nonneg : 0 ≤ A * H :=
    mul_nonneg (le_of_lt hA_pos) hH_nonneg
  have hmul_log_le :
      A * H * Real.log (2 + ‖w.im‖) ≤ A * H * (2 * H) :=
    mul_le_mul_of_nonneg_left hlog_le_twoH hleft_nonneg
  have htarget_eq :
      A * H * (2 * H) = (2 * A) * H ^ (2 : ℕ) := by
    ring
  exact le_trans (hbound w hw_re hw_im)
    (Eq.subst
      (motive := fun x : ℝ =>
        A * H * Real.log (2 + ‖w.im‖) ≤ x)
      htarget_eq
      hmul_log_le)

/-- Standard polynomial vertical growth of the pole-cleared zeta factor on the boundary
line `re = 1`.

This is the classical boundary-line estimate for the removable meromorphic factor
`(s - 1)ζ(s)`, stated before conversion to the coarser finite-order envelope. -/
theorem riemannZeta_poleCleared_boundaryLine_one_vertical_polynomial_growth_bound_standard :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * (1 + ‖w.im‖) ^ m := by
  exact boundaryLine_one_log_linear_growth_bound_to_polynomial_growth_bound
    classicalZeta_poleCleared_boundaryLine_one_vertical_log_linear_growth_bound

/-- Standard finite-order vertical growth of the pole-cleared zeta factor on the boundary
line `re = 1`, converted from the polynomial boundary-line estimate.

This is the zeta-side finite-order theorem that must come from boundary-line estimates
for the pole-cleared meromorphic zeta function, not from the false far-right `re = 2`
Dirichlet-series route. -/
theorem riemannZeta_poleCleared_boundaryLine_one_vertical_growth_bound_standard :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w.im‖) ^ m) := by
  exact boundaryLine_one_polynomial_growth_bound_to_exponential_growth_bound
    riemannZeta_poleCleared_boundaryLine_one_vertical_polynomial_growth_bound_standard

/-- The standard vertical-height finite-order estimate for `(s - 1)ζ(s)` on `re = 1`
implies the complex-height envelope consumed by the strip-normalization chain. -/
theorem riemannZeta_poleCleared_boundaryLine_one_growth_bound_of_vertical_growth
    (hvertical :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ w : ℂ,
          w.re = 1 →
          1 ≤ ‖w.im‖ →
          ‖(w - 1) * riemannZeta w‖ ≤
            A * Real.exp (B * (1 + ‖w.im‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  rcases hvertical with ⟨A, B, m, hA, hB, hbound⟩
  refine ⟨A, B, m, hA, hB, ?_⟩
  intro w hw_re hw_im
  exact le_trans (hbound w hw_re hw_im)
    (finiteOrder_vertical_envelope_le_complex_envelope
      (le_of_lt hA)
      (le_of_lt hB))

/-- Standard finite-order vertical growth of the pole-cleared zeta factor on the boundary
line `re = 1`, in the complex-height envelope used downstream. -/
theorem riemannZeta_poleCleared_boundaryLine_one_growth_bound_standard :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  exact riemannZeta_poleCleared_boundaryLine_one_growth_bound_of_vertical_growth
    riemannZeta_poleCleared_boundaryLine_one_vertical_growth_bound_standard

/-- The removable pole-cleared boundary-line estimate implies the raw
`(s - 1)ζ(s)` boundary-line estimate on the vertical tail.

The vertical-tail hypothesis excludes the removable point `1`, so the raw product and
`poleClearedRiemannZeta` agree there. -/
theorem riemannZeta_boundaryLine_one_raw_growth_bound_of_poleCleared_growth_bound
    (hpole :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ w : ℂ,
          w.re = 1 →
          1 ≤ ‖w.im‖ →
          ‖poleClearedRiemannZeta w‖ ≤
            A * Real.exp (B * (1 + ‖w‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  rcases hpole with ⟨A, B, m, hA, hB, hpole_bound⟩
  refine ⟨A, B, m, hA, hB, ?_⟩
  intro w hw_re hw_im
  have hw_ne_one : w ≠ 1 := by
    intro hw
    have him_zero : w.im = 0 := by
      calc
        w.im = (1 : ℂ).im := by
          exact congrArg Complex.im hw
        _ = 0 := by
          exact Complex.one_im
    have him_norm_zero : ‖w.im‖ = 0 := by
      calc
        ‖w.im‖ = ‖(0 : ℝ)‖ := by
          exact congrArg norm him_zero
        _ = 0 := by
          exact norm_zero
    have hone_le_zero : (1 : ℝ) ≤ 0 :=
      Eq.subst
        (motive := fun x : ℝ => (1 : ℝ) ≤ x)
        him_norm_zero
        hw_im
    exact not_lt_of_ge hone_le_zero zero_lt_one
  have hpole_eq :
      poleClearedRiemannZeta w = (w - 1) * riemannZeta w :=
    poleClearedRiemannZeta_eq_of_ne_one hw_ne_one
  exact Eq.subst
    (motive := fun x : ℂ =>
      ‖x‖ ≤ A * Real.exp (B * (1 + ‖w‖) ^ m))
    hpole_eq
    (hpole_bound w hw_re hw_im)

/-- Pole-cleared zeta has finite-order vertical growth on the boundary line `re = 1`.

This is the smallest zeta-side analytic primitive needed on the reflected left boundary:
reflection sends `re z = 0` to `re (1 - z) = 1`, not to the `re = 2`
Dirichlet-series boundary. -/

end
end LFunctions
end Boundary
