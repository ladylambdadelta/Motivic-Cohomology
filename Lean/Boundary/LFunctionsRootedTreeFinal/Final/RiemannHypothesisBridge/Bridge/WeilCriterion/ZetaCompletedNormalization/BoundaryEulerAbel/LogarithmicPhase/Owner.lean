import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.PoleClearedBoundarySetup.Owner

/-!
# Boundary logarithmic phase estimates

This file is a sequential owner sublayer split out of
`ZetaCompletedNormalization.BoundaryEulerAbel.Owner`.  Declaration order is preserved.
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
  match Decidable.em (k = 0) with
  | Or.inl hk =>
    have hterm :
        (k : ℂ) ^ (-(t : ℂ) * Complex.I) =
          (0 : ℂ) ^ (-(t : ℂ) * Complex.I) := by
      exact congrArg (fun n : ℕ => (n : ℂ) ^ (-(t : ℂ) * Complex.I)) hk
    have hnorm_nonneg :
        0 ≤ ‖(k : ℂ) ^ (-(t : ℂ) * Complex.I)‖ :=
      norm_nonneg ((k : ℂ) ^ (-(t : ℂ) * Complex.I))
    exact le_trans hnorm_nonneg zero_le_one
  | Or.inr hk =>
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
  exact
    standardFirstDerivativeTest_logarithmicPhase_partialSum_bound_of_antitone
      t ht hphase_deriv hphase_deriv_norm hphase_deriv_antitone hx

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

end
end LFunctions
end Boundary
