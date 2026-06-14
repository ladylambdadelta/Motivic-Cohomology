import LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.BoundaryLine
import Mathlib.Analysis.Complex.Angle

/-!
# Logarithmic phase estimates

This file owns the oscillatory phase `n^{-it}` input used by the
Euler-Maclaurin boundary argument.  The phase is logarithmic, not a
constant-ratio geometric progression.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Logarithmic-phase partial sums for the boundary-line oscillator `n^{-it}`. -/
def Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum
    (t : ℝ)
    (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    ((n : ℂ) ^ (-(t : ℂ) * Complex.I))

/-- Definitional expansion of the logarithmic-phase partial sum. -/
theorem Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum_eq
    (t : ℝ)
    (N : ℕ) :
    Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum t N =
      ∑ n ∈ Finset.Icc 1 N,
        ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
  rfl

/-- The continuous logarithmic phase whose positive integer samples are
`n^{-it}`. -/
def Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction
    (t : ℝ)
    (x : ℝ) : ℂ :=
  Complex.exp ((-(t : ℂ) * Complex.I) * (Real.log x : ℂ))

/-- The real scalar phase behind the boundary-line oscillator. -/
def Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
    (t : ℝ)
    (x : ℝ) : ℝ :=
  -t * Real.log x

/-- The complex logarithmic phase is the exponential of the real scalar phase. -/
theorem Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_eq_realPhase
    (t : ℝ)
    (x : ℝ) :
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t x =
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t x : ℂ)) := by
  have hphase :
      (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t x : ℂ)) =
        (-(t : ℂ) * Complex.I) * (Real.log x : ℂ) := by
    calc
      Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t x : ℂ) =
          Complex.I * ((-t * Real.log x : ℝ) : ℂ) := by
        rfl
      _ = Complex.I * ((-t : ℝ) : ℂ) * (Real.log x : ℂ) := by
        exact congrArg (fun z : ℂ => Complex.I * z)
          (map_mul (Complex.ofRealHom) (-t) (Real.log x))
      _ = ((-t : ℝ) : ℂ) * Complex.I * (Real.log x : ℂ) := by
        exact congrArg (fun z : ℂ => z * (Real.log x : ℂ))
          (mul_comm Complex.I ((-t : ℝ) : ℂ))
      _ = (-(t : ℂ) * Complex.I) * (Real.log x : ℂ) := by
        exact congrArg (fun z : ℂ => (z * Complex.I) * (Real.log x : ℂ))
          (Complex.ofReal_neg t)
  exact congrArg Complex.exp hphase

/-- Positive real samples of the logarithmic phase agree with the complex-power
notation used in the Dirichlet-polynomial partial sums. -/
theorem Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_eq_cpow_of_pos
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t x =
      (x : ℂ) ^ (-(t : ℂ) * Complex.I) := by
  let a : ℂ := -(t : ℂ) * Complex.I
  have hx_complex_ne : (x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hx.ne'
  have hlog : (Real.log x : ℂ) = Complex.log (x : ℂ) :=
    Complex.ofReal_log hx.le
  have hcomm :
      a * (Real.log x : ℂ) = (Real.log x : ℂ) * a :=
    mul_comm a (Real.log x : ℂ)
  have hreplace :
      (Real.log x : ℂ) * a = Complex.log (x : ℂ) * a :=
    congrArg (fun z : ℂ => z * a) hlog
  calc
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t x =
        Complex.exp (a * (Real.log x : ℂ)) := by
      rfl
    _ = Complex.exp ((Real.log x : ℂ) * a) :=
      congrArg Complex.exp hcomm
    _ = Complex.exp (Complex.log (x : ℂ) * a) :=
      congrArg Complex.exp hreplace
    _ = (x : ℂ) ^ a :=
      (Complex.cpow_def_of_ne_zero hx_complex_ne a).symm

/-- Algebraic reordering of the chain-rule derivative into the public
`(-it / x) * phase x` form. -/
theorem Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_derivative_reorder
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    Complex.exp (((-(t : ℂ) * Complex.I) * (Real.log x : ℂ))) *
        (((-(t : ℂ) * Complex.I)) * (x⁻¹ : ℂ)) =
      (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t x) := by
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

/-- Derivative of the positive-real logarithmic phase. -/
theorem Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_hasDerivAt
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t)
      (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t x)
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
          Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t x :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_derivative_reorder
      t hx
  exact hderiv_reorder ▸ hexp

/-- The actual derivative of the positive-real logarithmic phase. -/
theorem Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_deriv_eq
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t) x =
      (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t x) := by
  exact
    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_hasDerivAt
      t hx).deriv

/-- Real-part calculation for the purely imaginary logarithmic-phase exponent. -/
theorem Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_exponent_re_zero
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

/-- Unit norm of the positive-real logarithmic phase. -/
theorem Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_norm
    (t : ℝ)
    (x : ℝ) :
    ‖Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t x‖ = 1 := by
  let exponent : ℂ := (-(t : ℂ) * Complex.I) * (Real.log x : ℂ)
  have hnorm_abs :
      ‖Complex.exp exponent‖ = Complex.abs (Complex.exp exponent) :=
    Complex.norm_eq_abs (Complex.exp exponent)
  have habs_exp :
      Complex.abs (Complex.exp exponent) = Real.exp exponent.re :=
    Complex.abs_exp exponent
  have hexponent_re : exponent.re = 0 :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_exponent_re_zero
      t x
  calc
    ‖Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t x‖ =
        ‖Complex.exp exponent‖ :=
      rfl
    _ = Complex.abs (Complex.exp exponent) :=
      hnorm_abs
    _ = Real.exp exponent.re :=
      habs_exp
    _ = Real.exp 0 :=
      congrArg Real.exp hexponent_re
    _ = 1 :=
      Real.exp_zero

/-- Numerator norm in the logarithmic-phase derivative. -/
theorem Complex.boundaryLineOnePointRealParam_logarithmicPhase_derivative_numerator_norm
    (t : ℝ) :
    ‖(-(t : ℂ) * Complex.I)‖ = ‖t‖ := by
  calc
    ‖(-(t : ℂ) * Complex.I)‖ = ‖-(t : ℂ)‖ * ‖Complex.I‖ :=
      norm_mul (-(t : ℂ)) Complex.I
    _ = ‖(t : ℂ)‖ * ‖Complex.I‖ := by
      exact congrArg (fun y : ℝ => y * ‖Complex.I‖) (norm_neg (t : ℂ))
    _ = ‖(t : ℂ)‖ * 1 := by
      exact congrArg (fun y : ℝ => ‖(t : ℂ)‖ * y) norm_I
    _ = ‖(t : ℂ)‖ :=
      mul_one ‖(t : ℂ)‖
    _ = ‖t‖ :=
      RCLike.norm_ofReal t

/-- Denominator norm for a positive real embedded in `ℂ`. -/
theorem Complex.boundaryLineOnePointRealParam_positiveReal_denominator_norm
    {x : ℝ}
    (hx : 0 < x) :
    ‖(x : ℂ)‖ = x := by
  have hreal : ‖(x : ℂ)‖ = ‖x‖ :=
    RCLike.norm_ofReal x
  have hx_norm : ‖x‖ = x :=
    norm_of_nonneg hx.le
  exact hreal.trans hx_norm

/-- The derivative magnitude of the logarithmic phase is exactly `|t| / x`. -/
theorem Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_deriv_norm_eq
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t) x‖ =
      ‖t‖ / x := by
  have hderiv :
      deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t) x =
        (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
          Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t x) :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_deriv_eq t hx
  have hphase_norm :
      ‖Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t x‖ = 1 :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_norm t x
  have hnum : ‖(-(t : ℂ) * Complex.I)‖ = ‖t‖ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhase_derivative_numerator_norm t
  have hden : ‖(x : ℂ)‖ = x :=
    Complex.boundaryLineOnePointRealParam_positiveReal_denominator_norm hx
  calc
    ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t) x‖ =
        ‖(((-(t : ℂ) * Complex.I) / (x : ℂ)) *
          Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t x)‖ := by
      exact congrArg norm hderiv
    _ =
        ‖((-(t : ℂ) * Complex.I) / (x : ℂ))‖ *
          ‖Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t x‖ :=
      norm_mul
        (((-(t : ℂ) * Complex.I) / (x : ℂ)))
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t x)
    _ = ‖((-(t : ℂ) * Complex.I) / (x : ℂ))‖ * 1 := by
      exact congrArg
        (fun y : ℝ => ‖((-(t : ℂ) * Complex.I) / (x : ℂ))‖ * y)
        hphase_norm
    _ = ‖((-(t : ℂ) * Complex.I) / (x : ℂ))‖ :=
      mul_one ‖((-(t : ℂ) * Complex.I) / (x : ℂ))‖
    _ = ‖(-(t : ℂ) * Complex.I)‖ / ‖(x : ℂ)‖ :=
      norm_div (-(t : ℂ) * Complex.I) (x : ℂ)
    _ = ‖t‖ / ‖(x : ℂ)‖ := by
      exact congrArg (fun y : ℝ => y / ‖(x : ℂ)‖) hnum
    _ = ‖t‖ / x := by
      exact congrArg (fun y : ℝ => ‖t‖ / y) hden

/-- Derivative of the real scalar logarithmic phase. -/
theorem Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_hasDerivAt
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (-t / x)
      x := by
  have hlog : HasDerivAt Real.log x⁻¹ x :=
    Real.hasDerivAt_log hx.ne'
  have hmul :
      HasDerivAt
        (fun y : ℝ => -t * Real.log y)
        ((-t) * x⁻¹)
        x :=
    hlog.const_mul (-t)
  have hderiv : (-t) * x⁻¹ = -t / x :=
    (div_eq_mul_inv (-t) x).symm
  exact Eq.subst
    (motive := fun d : ℝ =>
      HasDerivAt
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        d
        x)
    hderiv
    hmul

/-- Derivative formula for the real scalar logarithmic phase. -/
theorem Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_deriv_eq
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x =
      -t / x := by
  exact
    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_hasDerivAt
      t hx).deriv

/-- Absolute derivative of the real scalar phase is `|t| / x`. -/
theorem Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_deriv_norm_eq
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x‖ =
      ‖t‖ / x := by
  have hderiv :
      deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x =
        -t / x :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_deriv_eq t hx
  have hx_norm : ‖x‖ = x :=
    norm_of_nonneg hx.le
  calc
    ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x‖ =
        ‖-t / x‖ := by
      exact congrArg norm hderiv
    _ = ‖-t‖ / ‖x‖ :=
      norm_div (-t) x
    _ = ‖t‖ / ‖x‖ := by
      exact congrArg (fun y : ℝ => y / ‖x‖) (norm_neg t)
    _ = ‖t‖ / x := by
      exact congrArg (fun y : ℝ => ‖t‖ / y) hx_norm

/-- The logarithmic-phase derivative magnitude `|t| / x` is decreasing on the
positive real axis. -/
theorem Complex.logarithmicPhase_derivativeMagnitude_antitoneOn_positive
    (t : ℝ) :
    AntitoneOn (fun x : ℝ => ‖t‖ / x) (Set.Ioi 0) := by
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

/-- Lower derivative-magnitude bound on a positive block. -/
theorem Complex.logarithmicPhase_derivativeMagnitude_block_lower_bound
    (t : ℝ)
    {a b x : ℝ}
    (ha : 0 < a)
    (hxb : x ∈ Set.Icc a b) :
    ‖t‖ / b ≤ ‖t‖ / x := by
  have hx_pos : 0 < x :=
    lt_of_lt_of_le ha hxb.1
  exact
    Complex.logarithmicPhase_derivativeMagnitude_antitoneOn_positive t
      hx_pos
      (lt_of_lt_of_le ha hxb.2)
      hxb.2

/-- Integer samples of the continuous logarithmic phase are the terms
`n^{-it}`. -/
theorem Complex.logarithmicPhase_integer_sample_eq
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n) :
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t n =
      (n : ℂ) ^ (-(t : ℂ) * Complex.I) := by
  exact
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_eq_cpow_of_pos
      t (by exact_mod_cast hn)

/-- The derivative of the logarithmic phase has the expected lower bound on a
positive integer block. -/
theorem Complex.logarithmicPhase_deriv_norm_block_lower_bound
    (t : ℝ)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    {x : ℝ}
    (hx : x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) :
    ((‖t‖ : ℝ) / ((b + 1 : ℕ) : ℝ)) ≤
      ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t) x‖ := by
  have ha_pos_nat : 0 < a :=
    Nat.lt_of_succ_le ha
  have hb_pos_nat : 0 < b + 1 :=
    Nat.succ_pos b
  have ha_pos_real : 0 < (a : ℝ) := by
    exact_mod_cast ha_pos_nat
  have hx_pos : 0 < x :=
    lt_of_lt_of_le ha_pos_real hx.1
  have hderiv_norm :
      ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t) x‖ =
        ‖t‖ / x :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_deriv_norm_eq
      t hx_pos
  have hblock :
      ‖t‖ / ((b + 1 : ℕ) : ℝ) ≤ ‖t‖ / x :=
    Complex.logarithmicPhase_derivativeMagnitude_block_lower_bound
      t
      (by exact_mod_cast hb_pos_nat)
      hx
  exact Eq.subst
    (motive := fun target : ℝ => ‖t‖ / ((b + 1 : ℕ) : ℝ) ≤ target)
    hderiv_norm.symm
    hblock

/-- The logarithmic-phase derivative magnitude is monotone on every positive
integer block. -/
theorem Complex.logarithmicPhase_deriv_norm_antitoneOn_integer_block
    (t : ℝ)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    AntitoneOn
      (fun x : ℝ =>
        ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t) x‖)
      (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) := by
  intro x hx y hy hxy
  have ha_pos_nat : 0 < a :=
    Nat.lt_of_succ_le ha
  have ha_pos_real : 0 < (a : ℝ) := by
    exact_mod_cast ha_pos_nat
  have hx_pos : 0 < x :=
    lt_of_lt_of_le ha_pos_real hx.1
  have hy_pos : 0 < y :=
    lt_of_lt_of_le ha_pos_real hy.1
  have hx_deriv :
      ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t) x‖ =
        ‖t‖ / x :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_deriv_norm_eq
      t hx_pos
  have hy_deriv :
      ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t) y‖ =
        ‖t‖ / y :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_deriv_norm_eq
      t hy_pos
  have hphase :
      ‖t‖ / y ≤ ‖t‖ / x :=
    Complex.logarithmicPhase_derivativeMagnitude_antitoneOn_positive t
      hx_pos hy_pos hxy
  exact Eq.subst
    (motive := fun target : ℝ =>
      ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t) y‖ ≤
        target)
    hx_deriv.symm
    (Eq.subst
      (motive := fun source : ℝ => source ≤ ‖t‖ / x)
      hy_deriv.symm
      hphase)

/-- The real scalar logarithmic-phase derivative has the same lower bound on
positive integer blocks. -/
theorem Complex.logarithmicPhaseRealPhase_deriv_norm_block_lower_bound
    (t : ℝ)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    {x : ℝ}
    (hx : x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) :
    ((‖t‖ : ℝ) / ((b + 1 : ℕ) : ℝ)) ≤
      ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x‖ := by
  have ha_pos_nat : 0 < a :=
    Nat.lt_of_succ_le ha
  have hb_pos_nat : 0 < b + 1 :=
    Nat.succ_pos b
  have ha_pos_real : 0 < (a : ℝ) := by
    exact_mod_cast ha_pos_nat
  have hx_pos : 0 < x :=
    lt_of_lt_of_le ha_pos_real hx.1
  have hderiv_norm :
      ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x‖ =
        ‖t‖ / x :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_deriv_norm_eq
      t hx_pos
  have hblock :
      ‖t‖ / ((b + 1 : ℕ) : ℝ) ≤ ‖t‖ / x :=
    Complex.logarithmicPhase_derivativeMagnitude_block_lower_bound
      t
      (by exact_mod_cast hb_pos_nat)
      hx
  exact Eq.subst
    (motive := fun target : ℝ => ‖t‖ / ((b + 1 : ℕ) : ℝ) ≤ target)
    hderiv_norm.symm
    hblock

/-- The absolute real scalar-phase derivative is monotone on every positive
integer block. -/
theorem Complex.logarithmicPhaseRealPhase_deriv_norm_antitoneOn_integer_block
    (t : ℝ)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    AntitoneOn
      (fun x : ℝ =>
        ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x‖)
      (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) := by
  intro x hx y hy hxy
  have ha_pos_nat : 0 < a :=
    Nat.lt_of_succ_le ha
  have ha_pos_real : 0 < (a : ℝ) := by
    exact_mod_cast ha_pos_nat
  have hx_pos : 0 < x :=
    lt_of_lt_of_le ha_pos_real hx.1
  have hy_pos : 0 < y :=
    lt_of_lt_of_le ha_pos_real hy.1
  have hx_deriv :
      ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x‖ =
        ‖t‖ / x :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_deriv_norm_eq
      t hx_pos
  have hy_deriv :
      ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y‖ =
        ‖t‖ / y :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase_deriv_norm_eq
      t hy_pos
  have hphase :
      ‖t‖ / y ≤ ‖t‖ / x :=
    Complex.logarithmicPhase_derivativeMagnitude_antitoneOn_positive t
      hx_pos hy_pos hxy
  exact Eq.subst
    (motive := fun target : ℝ =>
      ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) y‖ ≤
        target)
    hx_deriv.symm
    (Eq.subst
      (motive := fun source : ℝ => source ≤ ‖t‖ / x)
      hy_deriv.symm
      hphase)

/-- The real exponential attached to a scalar phase has unit norm. -/
theorem Complex.realPhase_exp_I_norm
    (φ : ℝ → ℝ)
    (x : ℝ) :
    ‖Complex.exp (Complex.I * (φ x : ℂ))‖ = 1 := by
  have hexp_re : (Complex.I * (φ x : ℂ)).re = 0 := by
    calc
      (Complex.I * (φ x : ℂ)).re = -((φ x : ℂ).im) :=
        Complex.I_mul_re (φ x : ℂ)
      _ = -0 := by
        exact congrArg Neg.neg (Complex.ofReal_im (φ x))
      _ = 0 :=
        neg_zero
  calc
    ‖Complex.exp (Complex.I * (φ x : ℂ))‖ =
        Complex.abs (Complex.exp (Complex.I * (φ x : ℂ))) :=
      Complex.norm_eq_abs (Complex.exp (Complex.I * (φ x : ℂ)))
    _ = Real.exp (Complex.I * (φ x : ℂ)).re :=
      Complex.abs_exp (Complex.I * (φ x : ℂ))
    _ = Real.exp 0 :=
      congrArg Real.exp hexp_re
    _ = 1 :=
      Real.exp_zero

/-- Finite exponential sums are trivially bounded by the length of their
indexing interval.  This is the nonoscillatory endpoint of the first derivative
argument. -/
theorem Complex.realPhase_integer_block_bound_by_card
    (φ : ℝ → ℝ)
    {a b : ℕ} :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        ((Finset.Icc a b).card : ℝ) := by
  calc
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        ∑ n ∈ Finset.Icc a b,
          ‖Complex.exp (Complex.I * (φ n : ℂ))‖ :=
      norm_sum_le (Finset.Icc a b)
        (fun n => Complex.exp (Complex.I * (φ n : ℂ)))
    _ = ∑ n ∈ Finset.Icc a b, (1 : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro n hn
      exact Complex.realPhase_exp_I_norm φ n
    _ = ((Finset.Icc a b).card : ℝ) :=
      Finset.sum_const_one

/-- Phase increment between adjacent integer samples. -/
def Complex.realPhase_integerIncrement
    (φ : ℝ → ℝ)
    (n : ℕ) : ℝ :=
  φ (n + 1 : ℕ) - φ n

/-- Separation of all adjacent phase increments from integral multiples of
`2π`.  This is the missing frequency-separation hypothesis in the honest
Kusmin-Landau estimate for `exp(i φ(n))`. -/
def Complex.realPhase_integerIncrementSeparatedOn
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (λ : ℝ) : Prop :=
  ∀ n : ℕ,
    n ∈ Finset.Ico a b →
      ∀ k : ℤ,
        λ ≤
          ‖Complex.realPhase_integerIncrement φ n -
            (2 * Real.pi * (k : ℝ))‖

/-- Monotonicity of the adjacent integer phase increments on a block.

This is the discrete finite-difference hypothesis needed in the honest
Kusmin-Landau summation-by-parts primitive.  Separation from `2πℤ` alone is not
enough: adjacent increments can alternate between two separated frequencies and
keep the sampled phases aligned over long blocks. -/
def Complex.realPhase_integerIncrementMonotoneOn
    (φ : ℝ → ℝ)
    (a b : ℕ) : Prop :=
  MonotoneOn
    (fun n : ℕ => Complex.realPhase_integerIncrement φ n)
    (Finset.Ico a b : Set ℕ) ∨
  AntitoneOn
    (fun n : ℕ => Complex.realPhase_integerIncrement φ n)
    (Finset.Ico a b : Set ℕ)

/-- Endpoint control for a one-point exponential block. -/
theorem Complex.realPhase_singleton_integer_block_bound
    (φ : ℝ → ℝ)
    (a : ℕ)
    {λ : ℝ}
    (hλ_pos : 0 < λ) :
    ‖∑ n ∈ Finset.Icc a a,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        8 * (λ⁻¹ + 1) := by
  have hblock :
      ‖∑ n ∈ Finset.Icc a a,
        Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
          ((Finset.Icc a a).card : ℝ) :=
    Complex.realPhase_integer_block_bound_by_card φ
  have hcard : ((Finset.Icc a a).card : ℝ) = 1 := by
    have hIcc : Finset.Icc a a = ({a} : Finset ℕ) :=
      Finset.Icc_self a
    have hcard_nat : (Finset.Icc a a).card = 1 := by
      calc
        (Finset.Icc a a).card = ({a} : Finset ℕ).card :=
          congrArg Finset.card hIcc
        _ = 1 :=
          Finset.card_singleton a
    exact congrArg Nat.cast hcard_nat
  have hλ_inv_nonneg : 0 ≤ λ⁻¹ :=
    inv_nonneg.mpr hλ_pos.le
  have hone_le_eight : (1 : ℝ) ≤ 8 * 1 := by
    norm_num
  have hone_le_target : (1 : ℝ) ≤ 8 * (λ⁻¹ + 1) := by
    have hone_le_sum : (1 : ℝ) ≤ λ⁻¹ + 1 :=
      le_add_of_nonneg_left hλ_inv_nonneg
    exact le_trans hone_le_eight
      (mul_le_mul_of_nonneg_left hone_le_sum (by norm_num : (0 : ℝ) ≤ 8))
  exact le_trans hblock
    (Eq.subst
      (motive := fun c : ℝ => c ≤ 8 * (λ⁻¹ + 1))
      hcard.symm
      hone_le_target)

/-- Reciprocal norm control from a positive denominator lower bound. -/
theorem Complex.realPhase_inv_norm_le_of_denominator_lower_bound
    {z : ℂ}
    {λ : ℝ}
    (hλ_pos : 0 < λ)
    (hden : λ ≤ 2 * ‖z‖) :
    ‖z⁻¹‖ ≤ 2 * λ⁻¹ := by
  have hhalf_pos : 0 < λ / 2 := by
    exact div_pos hλ_pos (by norm_num : (0 : ℝ) < 2)
  have hnorm_lower : λ / 2 ≤ ‖z‖ := by
    have hden' : λ ≤ ‖z‖ * 2 := by
      exact Eq.subst (motive := fun r : ℝ => λ ≤ r) (mul_comm 2 ‖z‖) hden
    exact (div_le_iff₀' (by norm_num : (0 : ℝ) < 2)).mpr hden'
  have hinv_mono : ‖z‖⁻¹ ≤ (λ / 2)⁻¹ :=
    inv_anti₀ hhalf_pos hnorm_lower
  have hhalf_inv : (λ / 2)⁻¹ = 2 * λ⁻¹ := by
    have hλ_ne : λ ≠ 0 :=
      ne_of_gt hλ_pos
    field_simp [hλ_ne]
  calc
    ‖z⁻¹‖ = ‖z‖⁻¹ :=
      norm_inv z
    _ ≤ (λ / 2)⁻¹ :=
      hinv_mono
    _ = 2 * λ⁻¹ :=
      hhalf_inv

/-- The `(-π, π]` representative is obtained by subtracting an integral
multiple of `2π`. -/
theorem Complex.realPhase_twoPi_toIocMod_integerDistance
    (θ : ℝ) :
    ∃ k : ℤ,
      θ - (2 * Real.pi * (k : ℝ)) =
        toIocMod Real.two_pi_pos (-Real.pi) θ := by
  let k : ℤ := toIocDiv Real.two_pi_pos (-Real.pi) θ
  refine ⟨k, ?_⟩
  have howner :
      θ - k • ((2 * Real.pi) : ℝ) =
        toIocMod Real.two_pi_pos (-Real.pi) θ :=
    self_sub_toIocDiv_zsmul Real.two_pi_pos (-Real.pi) θ
  have hzsmul :
      k • ((2 * Real.pi) : ℝ) = 2 * Real.pi * (k : ℝ) := by
    calc
      k • ((2 * Real.pi) : ℝ) = (k : ℝ) * (2 * Real.pi) := by
        exact zsmul_eq_mul k (2 * Real.pi)
      _ = 2 * Real.pi * (k : ℝ) := by
        ring
  exact
    Eq.subst
      (motive := fun r : ℝ =>
        θ - r = toIocMod Real.two_pi_pos (-Real.pi) θ)
      hzsmul
      howner

/-- Chord estimate for a reduced angle in `(-π, π]`. -/
theorem Complex.realPhase_reducedAngle_le_two_mul_chord_norm
    {ψ : ℝ}
    (hψ : ψ ∈ Set.Ioc (-Real.pi) Real.pi) :
    ‖ψ‖ ≤
      2 * ‖1 - Complex.exp (Complex.I * (ψ : ℂ))‖ := by
  have hψ_mod :
      toIocMod Real.two_pi_pos (-Real.pi) ψ = ψ := by
    exact (toIocMod_eq_self Real.two_pi_pos).mpr
      (by
        convert hψ using 1
        ring)
  have hangle :
      Complex.angle (Complex.exp ((ψ : ℂ) * Complex.I)) 1 = ‖ψ‖ := by
    have hangle_abs :
        Complex.angle (Complex.exp ((ψ : ℂ) * Complex.I)) 1 =
          |toIocMod Real.two_pi_pos (-Real.pi) ψ| :=
      Complex.angle_exp_one ψ
    have habs_norm :
        |toIocMod Real.two_pi_pos (-Real.pi) ψ| = ‖ψ‖ := by
      calc
        |toIocMod Real.two_pi_pos (-Real.pi) ψ| = |ψ| :=
          congrArg abs hψ_mod
        _ = ‖ψ‖ :=
          (Real.norm_eq_abs ψ).symm
    exact hangle_abs.trans habs_norm
  have hunit :
      ‖Complex.exp ((ψ : ℂ) * Complex.I)‖ = 1 := by
    have hcomm :
        Complex.exp ((ψ : ℂ) * Complex.I) =
          Complex.exp (Complex.I * (ψ : ℂ)) :=
      congrArg Complex.exp (mul_comm (ψ : ℂ) Complex.I)
    exact Eq.subst
      (motive := fun z : ℂ => ‖z‖ = 1)
      hcomm.symm
      (Complex.realPhase_exp_I_norm (fun _ : ℝ => ψ) 0)
  have harc :
      ‖ψ‖ ≤
        Real.pi / 2 *
          ‖Complex.exp ((ψ : ℂ) * Complex.I) - 1‖ := by
    exact Eq.subst
      (motive := fun r : ℝ =>
        r ≤ Real.pi / 2 *
          ‖Complex.exp ((ψ : ℂ) * Complex.I) - 1‖)
      hangle
      (Complex.angle_le_mul_norm_sub hunit norm_one)
  have hconstant :
      Real.pi / 2 *
          ‖Complex.exp ((ψ : ℂ) * Complex.I) - 1‖ ≤
        2 * ‖Complex.exp ((ψ : ℂ) * Complex.I) - 1‖ := by
    have hpi_half : Real.pi / 2 ≤ (2 : ℝ) := by
      exact (div_le_iff₀' (by norm_num : (0 : ℝ) < 2)).mpr
        (by
          calc
            Real.pi ≤ (4 : ℝ) :=
              Real.pi_le_four
            _ = 2 * 2 := by
              norm_num)
    exact mul_le_mul_of_nonneg_right hpi_half
      (norm_nonneg (Complex.exp ((ψ : ℂ) * Complex.I) - 1))
  have hnorm_transport :
      2 * ‖Complex.exp ((ψ : ℂ) * Complex.I) - 1‖ =
        2 * ‖1 - Complex.exp (Complex.I * (ψ : ℂ))‖ := by
    have hcomm_exp :
        Complex.exp ((ψ : ℂ) * Complex.I) =
          Complex.exp (Complex.I * (ψ : ℂ)) :=
      congrArg Complex.exp (mul_comm (ψ : ℂ) Complex.I)
    have hnorm :
        ‖Complex.exp ((ψ : ℂ) * Complex.I) - 1‖ =
          ‖1 - Complex.exp (Complex.I * (ψ : ℂ))‖ := by
      calc
        ‖Complex.exp ((ψ : ℂ) * Complex.I) - 1‖ =
            ‖Complex.exp (Complex.I * (ψ : ℂ)) - 1‖ :=
          congrArg (fun z : ℂ => ‖z - 1‖) hcomm_exp
        _ = ‖-(1 - Complex.exp (Complex.I * (ψ : ℂ)))‖ := by
          congr 1
          ring
        _ = ‖1 - Complex.exp (Complex.I * (ψ : ℂ))‖ :=
          norm_neg (1 - Complex.exp (Complex.I * (ψ : ℂ)))
    exact congrArg (fun r : ℝ => 2 * r) hnorm
  exact le_trans harc
    (Eq.subst
      (motive := fun target : ℝ =>
        Real.pi / 2 *
          ‖Complex.exp ((ψ : ℂ) * Complex.I) - 1‖ ≤ target)
      hnorm_transport
      hconstant)

/-- Period transport for the chord denominator. -/
theorem Complex.realPhase_geometricDenominator_norm_eq_toIocMod
    (θ : ℝ) :
    ‖1 - Complex.exp (Complex.I * (θ : ℂ))‖ =
      ‖1 -
        Complex.exp
          (Complex.I *
            (toIocMod Real.two_pi_pos (-Real.pi) θ : ℂ))‖ := by
  let k : ℤ := toIocDiv Real.two_pi_pos (-Real.pi) θ
  have hmod :
      θ - k • ((2 * Real.pi) : ℝ) =
        toIocMod Real.two_pi_pos (-Real.pi) θ :=
    self_sub_toIocDiv_zsmul Real.two_pi_pos (-Real.pi) θ
  have hperiod :
      Complex.exp
          ((toIocMod Real.two_pi_pos (-Real.pi) θ : ℂ) * Complex.I) =
        Complex.exp ((θ : ℂ) * Complex.I) := by
    have hraw :
        Complex.exp (((θ - k • ((2 * Real.pi) : ℝ) : ℝ) : ℂ) * Complex.I) =
          Complex.exp ((θ : ℂ) * Complex.I) := by
      exact Complex.exp_mul_I_periodic.sub_zsmul_eq k
    exact Eq.subst
      (motive := fun x : ℝ =>
        Complex.exp ((x : ℂ) * Complex.I) =
          Complex.exp ((θ : ℂ) * Complex.I))
      hmod
      hraw
  have hleft_comm :
      Complex.exp (Complex.I * (θ : ℂ)) =
        Complex.exp ((θ : ℂ) * Complex.I) := by
    exact congrArg Complex.exp (mul_comm Complex.I (θ : ℂ))
  have hright_comm :
      Complex.exp
          (Complex.I * (toIocMod Real.two_pi_pos (-Real.pi) θ : ℂ)) =
        Complex.exp
          ((toIocMod Real.two_pi_pos (-Real.pi) θ : ℂ) * Complex.I) := by
    exact congrArg Complex.exp
      (mul_comm Complex.I (toIocMod Real.two_pi_pos (-Real.pi) θ : ℂ))
  have hexp :
      Complex.exp (Complex.I * (θ : ℂ)) =
        Complex.exp
          (Complex.I * (toIocMod Real.two_pi_pos (-Real.pi) θ : ℂ)) := by
    exact Eq.trans hleft_comm (Eq.trans hperiod hright_comm.symm)
  exact congrArg (fun z : ℂ => ‖1 - z‖) hexp

/-- Nearest-period representative chord estimate for the real unit circle. -/
theorem Complex.realPhase_twoPi_integerDistance_le_two_mul_chord_norm
    (θ : ℝ) :
    ∃ k : ℤ,
      ‖θ - (2 * Real.pi * (k : ℝ))‖ ≤
        2 * ‖1 - Complex.exp (Complex.I * (θ : ℂ))‖ := by
  rcases Complex.realPhase_twoPi_toIocMod_integerDistance θ with ⟨k, hk⟩
  refine ⟨k, ?_⟩
  have hmem :
      toIocMod Real.two_pi_pos (-Real.pi) θ ∈ Set.Ioc (-Real.pi) Real.pi := by
    convert toIocMod_mem_Ioc Real.two_pi_pos (-Real.pi) θ using 1
    ring
  have hred :
      ‖toIocMod Real.two_pi_pos (-Real.pi) θ‖ ≤
        2 *
          ‖1 -
            Complex.exp
              (Complex.I *
                (toIocMod Real.two_pi_pos (-Real.pi) θ : ℂ))‖ :=
    Complex.realPhase_reducedAngle_le_two_mul_chord_norm hmem
  have hperiod :
      2 *
          ‖1 -
            Complex.exp
              (Complex.I *
                (toIocMod Real.two_pi_pos (-Real.pi) θ : ℂ))‖ =
        2 * ‖1 - Complex.exp (Complex.I * (θ : ℂ))‖ := by
    exact congrArg (fun r : ℝ => 2 * r)
      (Complex.realPhase_geometricDenominator_norm_eq_toIocMod θ).symm
  exact
    Eq.subst
      (motive := fun x : ℝ =>
        ‖x‖ ≤ 2 * ‖1 - Complex.exp (Complex.I * (θ : ℂ))‖)
      hk.symm
      (Eq.subst
        (motive := fun target : ℝ =>
          ‖toIocMod Real.two_pi_pos (-Real.pi) θ‖ ≤ target)
        hperiod
        hred)

/-- Chord lower bound on the unit circle from separation from `2πℤ`.

This is the real trigonometric core behind the geometric denominator estimate:
the nearest `2πℤ` distance to `θ` is controlled by the chord length
`|1 - exp(iθ)|`. -/
theorem Complex.realPhase_twoPiSeparation_le_two_mul_geometricDenominator_norm
    {θ λ : ℝ}
    (hλ_pos : 0 < λ)
    (hsep : ∀ k : ℤ, λ ≤ ‖θ - (2 * Real.pi * (k : ℝ))‖) :
    λ ≤ 2 * ‖1 - Complex.exp (Complex.I * (θ : ℂ))‖ := by
  rcases Complex.realPhase_twoPi_integerDistance_le_two_mul_chord_norm θ with
    ⟨k, hk⟩
  exact le_trans (hsep k) hk

/-- Geometric denominator lower bound from separation from all `2πℤ`
frequencies.

The classical estimate is
`|1 - exp(iθ)| = 2 |sin(θ/2)|`, together with the chord lower bound on the
circle and `π ≤ 4`; the stated reciprocal form is the one used by the finite
Dirichlet-test assembly. -/
theorem Complex.realPhase_geometricDenominator_inv_norm_bound
    {θ λ : ℝ}
    (hλ_pos : 0 < λ)
    (hsep : ∀ k : ℤ, λ ≤ ‖θ - (2 * Real.pi * (k : ℝ))‖) :
    ‖(1 - Complex.exp (Complex.I * (θ : ℂ)))⁻¹‖ ≤
      2 * λ⁻¹ := by
  exact
    Complex.realPhase_inv_norm_le_of_denominator_lower_bound
      hλ_pos
      (Complex.realPhase_twoPiSeparation_le_two_mul_geometricDenominator_norm
        hλ_pos hsep)

/-- Endpoint contribution in the finite monotone-increment Dirichlet test. -/
theorem Complex.realPhase_monotoneIncrement_dirichlet_endpoint_bound
    {λ : ℝ}
    (hλ_pos : 0 < λ) :
    (1 : ℝ) ≤ 2 * (λ⁻¹ + 1) := by
  have hλ_inv_nonneg : 0 ≤ λ⁻¹ :=
    inv_nonneg.mpr hλ_pos.le
  have hone_le_sum : (1 : ℝ) ≤ λ⁻¹ + 1 :=
    le_add_of_nonneg_left hλ_inv_nonneg
  exact le_trans hone_le_sum
    (by
      have hsum_nonneg : 0 ≤ λ⁻¹ + 1 :=
        add_nonneg hλ_inv_nonneg zero_le_one
      calc
        λ⁻¹ + 1 ≤ 2 * (λ⁻¹ + 1) := by
          exact (le_mul_iff_one_le_left hsum_nonneg).mpr (by norm_num)
        _ = 2 * (λ⁻¹ + 1) := rfl)

/-- Finite Abel-transform norm assembly for one prefix. -/
theorem Complex.realPhase_monotoneIncrement_prefix_abel_norm_assembly
    {S boundary variation : ℂ}
    {λ : ℝ}
    (hS : S = boundary + variation)
    (hboundary : ‖boundary‖ ≤ 4 * (λ⁻¹ + 1))
    (hvariation : ‖variation‖ ≤ 4 * (λ⁻¹ + 1)) :
    ‖S‖ ≤ 8 * (λ⁻¹ + 1) := by
  have hnorm :
      ‖S‖ ≤ ‖boundary‖ + ‖variation‖ := by
    exact Eq.subst
      (motive := fun z : ℂ => ‖z‖ ≤ ‖boundary‖ + ‖variation‖)
      hS.symm
      (norm_add_le boundary variation)
  have hsum :
      ‖boundary‖ + ‖variation‖ ≤
        4 * (λ⁻¹ + 1) + 4 * (λ⁻¹ + 1) :=
    add_le_add hboundary hvariation
  have hcombine :
      4 * (λ⁻¹ + 1) + 4 * (λ⁻¹ + 1) =
        8 * (λ⁻¹ + 1) := by
    ring
  exact le_trans hnorm
    (Eq.subst
      (motive := fun target : ℝ =>
        ‖boundary‖ + ‖variation‖ ≤ target)
      hcombine.symm
      hsum)

/-- Singleton prefix in the finite Abel transform: the whole prefix is an
endpoint term and the variation term is zero. -/
theorem Complex.realPhase_monotoneIncrement_singleton_prefix_abel_terms_bounded
    (φ : ℝ → ℝ)
    (a : ℕ)
    {λ : ℝ}
    (hλ_pos : 0 < λ) :
    ∃ boundary variation : ℂ,
      (∑ n ∈ Finset.Icc a a,
        Complex.exp (Complex.I * (φ n : ℂ))) =
          boundary + variation ∧
      ‖boundary‖ ≤ 4 * (λ⁻¹ + 1) ∧
      ‖variation‖ ≤ 4 * (λ⁻¹ + 1) := by
  let boundary : ℂ :=
    ∑ n ∈ Finset.Icc a a,
      Complex.exp (Complex.I * (φ n : ℂ))
  let variation : ℂ := 0
  refine ⟨boundary, variation, ?_, ?_, ?_⟩
  · exact (add_zero boundary).symm
  · have hblock :
        ‖∑ n ∈ Finset.Icc a a,
          Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
            ((Finset.Icc a a).card : ℝ) :=
      Complex.realPhase_integer_block_bound_by_card φ
    have hcard : ((Finset.Icc a a).card : ℝ) = 1 := by
      have hIcc : Finset.Icc a a = ({a} : Finset ℕ) :=
        Finset.Icc_self a
      have hcard_nat : (Finset.Icc a a).card = 1 := by
        calc
          (Finset.Icc a a).card = ({a} : Finset ℕ).card :=
            congrArg Finset.card hIcc
          _ = 1 :=
            Finset.card_singleton a
      exact congrArg Nat.cast hcard_nat
    have hone_bound :
        (1 : ℝ) ≤ 2 * (λ⁻¹ + 1) :=
      Complex.realPhase_monotoneIncrement_dirichlet_endpoint_bound hλ_pos
    exact le_trans hblock
      (Eq.subst
        (motive := fun c : ℝ => c ≤ 4 * (λ⁻¹ + 1))
        hcard.symm
        (le_trans hone_bound
          (by
            have hsum_nonneg : 0 ≤ λ⁻¹ + 1 :=
              add_nonneg (inv_nonneg.mpr hλ_pos.le) zero_le_one
            exact mul_le_mul_of_nonneg_right
              (by norm_num : (2 : ℝ) ≤ 4)
              hsum_nonneg)))
  · have hλ_inv_nonneg : 0 ≤ λ⁻¹ :=
      inv_nonneg.mpr hλ_pos.le
    have hsum_nonneg : 0 ≤ λ⁻¹ + 1 :=
      add_nonneg hλ_inv_nonneg zero_le_one
    have htarget_nonneg : 0 ≤ 4 * (λ⁻¹ + 1) :=
      mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hsum_nonneg
    exact Eq.subst
      (motive := fun r : ℝ => r ≤ 4 * (λ⁻¹ + 1))
      (norm_zero : ‖(0 : ℂ)‖ = 0).symm
      htarget_nonneg

/-- Separation from `2πℤ` makes the finite Abel geometric denominator
nonzero. -/
theorem Complex.realPhase_geometricDenominator_ne_zero_of_separatedIncrement
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    {λ : ℝ}
    (hλ_pos : 0 < λ)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b λ)
    (hn : n ∈ Finset.Ico a b) :
    (1 -
      Complex.exp
        (Complex.I *
          (Complex.realPhase_integerIncrement φ n : ℂ))) ≠ 0 := by
  intro hzero
  have hlower :
      λ ≤
        2 *
          ‖1 -
            Complex.exp
              (Complex.I *
                (Complex.realPhase_integerIncrement φ n : ℂ))‖ :=
    Complex.realPhase_twoPiSeparation_le_two_mul_geometricDenominator_norm
      hλ_pos
      (hsep n hn)
  have hright_zero :
      2 *
          ‖1 -
            Complex.exp
              (Complex.I *
                (Complex.realPhase_integerIncrement φ n : ℂ))‖ =
        0 := by
    exact congrArg (fun z : ℂ => 2 * ‖z‖) hzero
  have hλ_nonpos : λ ≤ 0 :=
    Eq.subst
      (motive := fun r : ℝ => λ ≤ r)
      hright_zero
      hlower
  exact (not_le_of_gt hλ_pos) hλ_nonpos

/-- The one-step geometric denominator inverts the finite phase difference. -/
theorem Complex.realPhase_geometricDenominator_inv_mul_step_difference
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    {λ : ℝ}
    (hλ_pos : 0 < λ)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b λ)
    (hn : n ∈ Finset.Ico a b) :
    ((1 -
      Complex.exp
        (Complex.I *
          (Complex.realPhase_integerIncrement φ n : ℂ)))⁻¹) *
      (Complex.exp (Complex.I * (φ n : ℂ)) -
        Complex.exp (Complex.I * (φ (n + 1 : ℕ) : ℂ))) =
        Complex.exp (Complex.I * (φ n : ℂ)) := by
  let u : ℂ := Complex.exp (Complex.I * (φ n : ℂ))
  let r : ℂ :=
    Complex.exp
      (Complex.I *
        (Complex.realPhase_integerIncrement φ n : ℂ))
  have hstep :
      Complex.exp (Complex.I * (φ (n + 1 : ℕ) : ℂ)) = u * r := by
    have hphase :
        Complex.I * (φ (n + 1 : ℕ) : ℂ) =
          Complex.I * (φ n : ℂ) +
            Complex.I *
              (Complex.realPhase_integerIncrement φ n : ℂ) := by
      unfold Complex.realPhase_integerIncrement
      push_cast
      ring
    calc
      Complex.exp (Complex.I * (φ (n + 1 : ℕ) : ℂ)) =
          Complex.exp
            (Complex.I * (φ n : ℂ) +
              Complex.I *
                (Complex.realPhase_integerIncrement φ n : ℂ)) := by
        exact congrArg Complex.exp hphase
      _ = u * r :=
        Complex.exp_add
          (Complex.I * (φ n : ℂ))
          (Complex.I *
            (Complex.realPhase_integerIncrement φ n : ℂ))
  have hden_ne :
      (1 - r) ≠ 0 := by
    exact
      Complex.realPhase_geometricDenominator_ne_zero_of_separatedIncrement
        φ hλ_pos hsep hn
  calc
    ((1 - r)⁻¹) *
        (u - Complex.exp (Complex.I * (φ (n + 1 : ℕ) : ℂ))) =
        ((1 - r)⁻¹) * (u - u * r) := by
      exact congrArg (fun z : ℂ => ((1 - r)⁻¹) * (u - z)) hstep
    _ = ((1 - r)⁻¹) * (u * (1 - r)) := by
      congr 1
      ring
    _ = u := by
      field_simp [hden_ne]

/-- Inverse geometric denominator attached to an adjacent integer phase
increment. -/
def Complex.realPhase_inverseGeometricDenominator
    (φ : ℝ → ℝ)
    (n : ℕ) : ℂ :=
  (1 -
    Complex.exp
      (Complex.I *
        (Complex.realPhase_integerIncrement φ n : ℂ)))⁻¹

/-- Unit-modulus phase sample used in the finite Abel transform. -/
def Complex.realPhase_integerUnit
    (φ : ℝ → ℝ)
    (n : ℕ) : ℂ :=
  Complex.exp (Complex.I * (φ n : ℂ))

/-- Endpoint term in the non-singleton finite Abel transform. -/
def Complex.realPhase_prefixAbelBoundary
    (φ : ℝ → ℝ)
    (a m : ℕ) : ℂ :=
  Complex.realPhase_inverseGeometricDenominator φ a *
      Complex.realPhase_integerUnit φ a +
    (1 - Complex.realPhase_inverseGeometricDenominator φ (m - 1)) *
      Complex.realPhase_integerUnit φ m

/-- Variation term in the non-singleton finite Abel transform. -/
def Complex.realPhase_prefixAbelVariation
    (φ : ℝ → ℝ)
    (a m : ℕ) : ℂ :=
  ∑ n ∈ Finset.Ioo a m,
    (Complex.realPhase_inverseGeometricDenominator φ n -
        Complex.realPhase_inverseGeometricDenominator φ (n - 1)) *
      Complex.realPhase_integerUnit φ n

/-- Generic finite Abel telescoping identity over `Ico`. -/
theorem Complex.finiteAbel_Ico_mul_sub_telescope
    (A u : ℕ → ℂ)
    {a m : ℕ}
    (ham : a < m) :
    (∑ n ∈ Finset.Ico a m, A n * (u n - u (n + 1))) =
      A a * u a - A (m - 1) * u m +
        ∑ n ∈ Finset.Ioo a m, (A n - A (n - 1)) * u n := by
  sorry

/-- Exact `Ico` telescoping form of the finite Abel transform. -/
theorem Complex.realPhase_prefixAbel_Ico_telescope
    (φ : ℝ → ℝ)
    {a b m : ℕ}
    {λ : ℝ}
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hλ_pos : 0 < λ)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b λ) :
    (∑ n ∈ Finset.Ico a m,
      Complex.realPhase_integerUnit φ n) =
        Complex.realPhase_inverseGeometricDenominator φ a *
          Complex.realPhase_integerUnit φ a -
          Complex.realPhase_inverseGeometricDenominator φ (m - 1) *
          Complex.realPhase_integerUnit φ m +
        Complex.realPhase_prefixAbelVariation φ a m := by
  let A : ℕ → ℂ := Complex.realPhase_inverseGeometricDenominator φ
  let u : ℕ → ℂ := Complex.realPhase_integerUnit φ
  have hm_bounds : a ≤ m ∧ m ≤ b :=
    Finset.mem_Icc.mp hm
  have hterm :
      (∑ n ∈ Finset.Ico a m, u n) =
        ∑ n ∈ Finset.Ico a m, A n * (u n - u (n + 1)) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hn_bounds : a ≤ n ∧ n < m :=
      Finset.mem_Ico.mp hn
    have hn_block : n ∈ Finset.Ico a b :=
      Finset.mem_Ico.mpr
        ⟨hn_bounds.1, lt_of_lt_of_le hn_bounds.2 hm_bounds.2⟩
    have hstep :
        A n * (u n - u (n + 1)) = u n := by
      unfold A u Complex.realPhase_inverseGeometricDenominator
        Complex.realPhase_integerUnit
      exact
        Complex.realPhase_geometricDenominator_inv_mul_step_difference
          φ hλ_pos hsep hn_block
    exact hstep.symm
  have htelescope :
      (∑ n ∈ Finset.Ico a m, A n * (u n - u (n + 1))) =
        A a * u a - A (m - 1) * u m +
          ∑ n ∈ Finset.Ioo a m, (A n - A (n - 1)) * u n :=
    Complex.finiteAbel_Ico_mul_sub_telescope A u ham
  calc
    (∑ n ∈ Finset.Ico a m,
      Complex.realPhase_integerUnit φ n) =
        (∑ n ∈ Finset.Ico a m, u n) := by
      rfl
    _ = ∑ n ∈ Finset.Ico a m, A n * (u n - u (n + 1)) :=
      hterm
    _ =
        A a * u a - A (m - 1) * u m +
          ∑ n ∈ Finset.Ioo a m, (A n - A (n - 1)) * u n :=
      htelescope
    _ =
        Complex.realPhase_inverseGeometricDenominator φ a *
          Complex.realPhase_integerUnit φ a -
        Complex.realPhase_inverseGeometricDenominator φ (m - 1) *
          Complex.realPhase_integerUnit φ m +
        Complex.realPhase_prefixAbelVariation φ a m := by
      unfold A u Complex.realPhase_prefixAbelVariation
      rfl

/-- The exact finite Abel identity for the non-singleton phase prefix. -/
theorem Complex.realPhase_prefixAbel_identity
    (φ : ℝ → ℝ)
    {a b m : ℕ}
    {λ : ℝ}
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hλ_pos : 0 < λ)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b λ) :
    (∑ n ∈ Finset.Icc a m,
      Complex.realPhase_integerUnit φ n) =
        Complex.realPhase_prefixAbelBoundary φ a m +
          Complex.realPhase_prefixAbelVariation φ a m := by
  have hm_bounds : a ≤ m ∧ m ≤ b :=
    Finset.mem_Icc.mp hm
  have hsplit :
      (∑ n ∈ Finset.Icc a m,
        Complex.realPhase_integerUnit φ n) =
          (∑ n ∈ Finset.Ico a m,
            Complex.realPhase_integerUnit φ n) +
            Complex.realPhase_integerUnit φ m := by
    have hinsert :
        Finset.insert m (Finset.Ico a m) = Finset.Icc a m :=
      Finset.Ico_insert_right hm_bounds.1
    have hnot : m ∉ Finset.Ico a m :=
      Finset.right_not_mem_Ico
    calc
      (∑ n ∈ Finset.Icc a m,
        Complex.realPhase_integerUnit φ n) =
          ∑ n ∈ Finset.insert m (Finset.Ico a m),
            Complex.realPhase_integerUnit φ n := by
        exact congrArg
          (fun s : Finset ℕ =>
            ∑ n ∈ s, Complex.realPhase_integerUnit φ n)
          hinsert.symm
      _ =
          Complex.realPhase_integerUnit φ m +
            ∑ n ∈ Finset.Ico a m,
              Complex.realPhase_integerUnit φ n :=
        Finset.sum_insert hnot
      _ =
          (∑ n ∈ Finset.Ico a m,
            Complex.realPhase_integerUnit φ n) +
            Complex.realPhase_integerUnit φ m :=
        add_comm _ _
  have htelescope :
      (∑ n ∈ Finset.Ico a m,
        Complex.realPhase_integerUnit φ n) =
          Complex.realPhase_inverseGeometricDenominator φ a *
            Complex.realPhase_integerUnit φ a -
          Complex.realPhase_inverseGeometricDenominator φ (m - 1) *
            Complex.realPhase_integerUnit φ m +
          Complex.realPhase_prefixAbelVariation φ a m :=
    Complex.realPhase_prefixAbel_Ico_telescope
      φ ham hm hλ_pos hsep
  calc
    (∑ n ∈ Finset.Icc a m,
      Complex.realPhase_integerUnit φ n) =
        (∑ n ∈ Finset.Ico a m,
          Complex.realPhase_integerUnit φ n) +
          Complex.realPhase_integerUnit φ m :=
      hsplit
    _ =
        (Complex.realPhase_inverseGeometricDenominator φ a *
            Complex.realPhase_integerUnit φ a -
          Complex.realPhase_inverseGeometricDenominator φ (m - 1) *
            Complex.realPhase_integerUnit φ m +
          Complex.realPhase_prefixAbelVariation φ a m) +
          Complex.realPhase_integerUnit φ m := by
      exact congrArg
        (fun z : ℂ => z + Complex.realPhase_integerUnit φ m)
        htelescope
    _ =
        Complex.realPhase_prefixAbelBoundary φ a m +
          Complex.realPhase_prefixAbelVariation φ a m := by
      unfold Complex.realPhase_prefixAbelBoundary
      ring

/-- Endpoint estimate for the explicit finite Abel boundary term. -/
theorem Complex.realPhase_prefixAbelBoundary_norm_bound
    (φ : ℝ → ℝ)
    {a b m : ℕ}
    {λ : ℝ}
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hλ_pos : 0 < λ)
    (hden :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖Complex.realPhase_inverseGeometricDenominator φ n‖ ≤
            2 * λ⁻¹) :
    ‖Complex.realPhase_prefixAbelBoundary φ a m‖ ≤
      4 * (λ⁻¹ + 1) := by
  have hm_bounds : a ≤ m ∧ m ≤ b :=
    Finset.mem_Icc.mp hm
  have ha_mem : a ∈ Finset.Ico a b :=
    Finset.mem_Ico.mpr ⟨le_rfl, lt_of_lt_of_le ham hm_bounds.2⟩
  have hm_pred_mem : m - 1 ∈ Finset.Ico a b := by
    have ha_pred : a ≤ m - 1 :=
      Nat.le_pred_of_lt ham
    have hm_pos : 0 < m :=
      lt_of_le_of_lt (Nat.zero_le a) ham
    have hpred_lt_m : m - 1 < m :=
      Nat.pred_lt hm_pos
    have hpred_lt_b : m - 1 < b :=
      lt_of_lt_of_le hpred_lt_m hm_bounds.2
    exact Finset.mem_Ico.mpr ⟨ha_pred, hpred_lt_b⟩
  have ha_den :
      ‖Complex.realPhase_inverseGeometricDenominator φ a‖ ≤
        2 * λ⁻¹ :=
    hden a ha_mem
  have hm_den :
      ‖Complex.realPhase_inverseGeometricDenominator φ (m - 1)‖ ≤
        2 * λ⁻¹ :=
    hden (m - 1) hm_pred_mem
  have ha_unit :
      ‖Complex.realPhase_integerUnit φ a‖ = 1 :=
    Complex.realPhase_exp_I_norm φ a
  have hm_unit :
      ‖Complex.realPhase_integerUnit φ m‖ = 1 :=
    Complex.realPhase_exp_I_norm φ m
  have hfirst :
      ‖Complex.realPhase_inverseGeometricDenominator φ a *
        Complex.realPhase_integerUnit φ a‖ ≤ 2 * λ⁻¹ := by
    calc
      ‖Complex.realPhase_inverseGeometricDenominator φ a *
        Complex.realPhase_integerUnit φ a‖ =
          ‖Complex.realPhase_inverseGeometricDenominator φ a‖ *
            ‖Complex.realPhase_integerUnit φ a‖ :=
        norm_mul
          (Complex.realPhase_inverseGeometricDenominator φ a)
          (Complex.realPhase_integerUnit φ a)
      _ = ‖Complex.realPhase_inverseGeometricDenominator φ a‖ * 1 := by
        exact congrArg
          (fun r : ℝ =>
            ‖Complex.realPhase_inverseGeometricDenominator φ a‖ * r)
          ha_unit
      _ = ‖Complex.realPhase_inverseGeometricDenominator φ a‖ :=
        mul_one _
      _ ≤ 2 * λ⁻¹ :=
        ha_den
  have hsecond :
      ‖(1 - Complex.realPhase_inverseGeometricDenominator φ (m - 1)) *
        Complex.realPhase_integerUnit φ m‖ ≤ 1 + 2 * λ⁻¹ := by
    have hfactor :
        ‖1 - Complex.realPhase_inverseGeometricDenominator φ (m - 1)‖ ≤
          1 + 2 * λ⁻¹ := by
      calc
        ‖1 - Complex.realPhase_inverseGeometricDenominator φ (m - 1)‖ ≤
            ‖(1 : ℂ)‖ +
              ‖Complex.realPhase_inverseGeometricDenominator φ (m - 1)‖ := by
          exact norm_sub_le 1
            (Complex.realPhase_inverseGeometricDenominator φ (m - 1))
        _ = 1 +
              ‖Complex.realPhase_inverseGeometricDenominator φ (m - 1)‖ := by
          exact congrArg
            (fun r : ℝ =>
              r + ‖Complex.realPhase_inverseGeometricDenominator φ (m - 1)‖)
            norm_one
        _ ≤ 1 + 2 * λ⁻¹ :=
          add_le_add_left hm_den 1
    calc
      ‖(1 - Complex.realPhase_inverseGeometricDenominator φ (m - 1)) *
        Complex.realPhase_integerUnit φ m‖ =
          ‖1 - Complex.realPhase_inverseGeometricDenominator φ (m - 1)‖ *
            ‖Complex.realPhase_integerUnit φ m‖ :=
        norm_mul
          (1 - Complex.realPhase_inverseGeometricDenominator φ (m - 1))
          (Complex.realPhase_integerUnit φ m)
      _ = ‖1 - Complex.realPhase_inverseGeometricDenominator φ (m - 1)‖ * 1 := by
        exact congrArg
          (fun r : ℝ =>
            ‖1 - Complex.realPhase_inverseGeometricDenominator φ (m - 1)‖ * r)
          hm_unit
      _ = ‖1 - Complex.realPhase_inverseGeometricDenominator φ (m - 1)‖ :=
        mul_one _
      _ ≤ 1 + 2 * λ⁻¹ :=
        hfactor
  have hboundary :
      ‖Complex.realPhase_prefixAbelBoundary φ a m‖ ≤
        2 * λ⁻¹ + (1 + 2 * λ⁻¹) := by
    unfold Complex.realPhase_prefixAbelBoundary
    exact le_trans
      (norm_add_le
        (Complex.realPhase_inverseGeometricDenominator φ a *
          Complex.realPhase_integerUnit φ a)
        ((1 - Complex.realPhase_inverseGeometricDenominator φ (m - 1)) *
          Complex.realPhase_integerUnit φ m))
      (add_le_add hfirst hsecond)
  have hλ_inv_nonneg : 0 ≤ λ⁻¹ :=
    inv_nonneg.mpr hλ_pos.le
  have htarget :
      2 * λ⁻¹ + (1 + 2 * λ⁻¹) ≤
        4 * (λ⁻¹ + 1) := by
    nlinarith
  exact le_trans hboundary htarget

/-- Monotone separated increments control the total variation of the inverse
geometric denominators appearing in the finite Abel transform. -/
theorem Complex.realPhase_monotoneSeparated_inverseGeometricDenominator_variation_bound
    (φ : ℝ → ℝ)
    {a b m : ℕ}
    {λ : ℝ}
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hλ_pos : 0 < λ)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b λ)
    (hden :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖Complex.realPhase_inverseGeometricDenominator φ n‖ ≤
            2 * λ⁻¹) :
    (∑ n ∈ Finset.Ioo a m,
      ‖Complex.realPhase_inverseGeometricDenominator φ n -
        Complex.realPhase_inverseGeometricDenominator φ (n - 1)‖) ≤
        4 * (λ⁻¹ + 1) := by
  sorry

/-- Variation estimate for the explicit finite Abel variation term. -/
theorem Complex.realPhase_prefixAbelVariation_norm_bound
    (φ : ℝ → ℝ)
    {a b m : ℕ}
    {λ : ℝ}
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hλ_pos : 0 < λ)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b λ)
    (hden :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖Complex.realPhase_inverseGeometricDenominator φ n‖ ≤
            2 * λ⁻¹) :
    ‖Complex.realPhase_prefixAbelVariation φ a m‖ ≤
      4 * (λ⁻¹ + 1) := by
  have hsum_norm :
      ‖Complex.realPhase_prefixAbelVariation φ a m‖ ≤
        ∑ n ∈ Finset.Ioo a m,
          ‖(Complex.realPhase_inverseGeometricDenominator φ n -
              Complex.realPhase_inverseGeometricDenominator φ (n - 1)) *
            Complex.realPhase_integerUnit φ n‖ := by
    unfold Complex.realPhase_prefixAbelVariation
    exact norm_sum_le (Finset.Ioo a m)
      (fun n =>
        (Complex.realPhase_inverseGeometricDenominator φ n -
            Complex.realPhase_inverseGeometricDenominator φ (n - 1)) *
          Complex.realPhase_integerUnit φ n)
  have hunit :
      (∑ n ∈ Finset.Ioo a m,
          ‖(Complex.realPhase_inverseGeometricDenominator φ n -
              Complex.realPhase_inverseGeometricDenominator φ (n - 1)) *
            Complex.realPhase_integerUnit φ n‖) =
        ∑ n ∈ Finset.Ioo a m,
          ‖Complex.realPhase_inverseGeometricDenominator φ n -
            Complex.realPhase_inverseGeometricDenominator φ (n - 1)‖ := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hunit_norm :
        ‖Complex.realPhase_integerUnit φ n‖ = 1 := by
      exact Complex.realPhase_exp_I_norm φ n
    calc
      ‖(Complex.realPhase_inverseGeometricDenominator φ n -
          Complex.realPhase_inverseGeometricDenominator φ (n - 1)) *
        Complex.realPhase_integerUnit φ n‖ =
          ‖Complex.realPhase_inverseGeometricDenominator φ n -
            Complex.realPhase_inverseGeometricDenominator φ (n - 1)‖ *
            ‖Complex.realPhase_integerUnit φ n‖ :=
        norm_mul
          (Complex.realPhase_inverseGeometricDenominator φ n -
            Complex.realPhase_inverseGeometricDenominator φ (n - 1))
          (Complex.realPhase_integerUnit φ n)
      _ =
          ‖Complex.realPhase_inverseGeometricDenominator φ n -
            Complex.realPhase_inverseGeometricDenominator φ (n - 1)‖ * 1 := by
        exact congrArg
          (fun r : ℝ =>
            ‖Complex.realPhase_inverseGeometricDenominator φ n -
              Complex.realPhase_inverseGeometricDenominator φ (n - 1)‖ * r)
          hunit_norm
      _ =
          ‖Complex.realPhase_inverseGeometricDenominator φ n -
            Complex.realPhase_inverseGeometricDenominator φ (n - 1)‖ :=
        mul_one _
  have hvariation :
      (∑ n ∈ Finset.Ioo a m,
        ‖Complex.realPhase_inverseGeometricDenominator φ n -
          Complex.realPhase_inverseGeometricDenominator φ (n - 1)‖) ≤
          4 * (λ⁻¹ + 1) :=
    Complex.realPhase_monotoneSeparated_inverseGeometricDenominator_variation_bound
      φ ham hm hλ_pos hinc_mono hsep hden
  exact le_trans hsum_norm
    (Eq.subst
      (motive := fun r : ℝ => r ≤ 4 * (λ⁻¹ + 1))
      hunit.symm
      hvariation)

/-- Non-singleton prefix in the finite Abel transform.  This is the remaining
finite summation-by-parts identity plus monotone-variation estimate. -/
theorem Complex.realPhase_monotoneIncrement_prefix_abel_terms_bounded_of_lt
    (φ : ℝ → ℝ)
    {a b m : ℕ}
    {λ : ℝ}
    (ha : 1 ≤ a)
    (hab_lt : a < b)
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hλ_pos : 0 < λ)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b λ)
    (hden :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖(1 -
            Complex.exp
              (Complex.I *
                (Complex.realPhase_integerIncrement φ n : ℂ)))⁻¹‖ ≤
            2 * λ⁻¹) :
    ∃ boundary variation : ℂ,
      (∑ n ∈ Finset.Icc a m,
        Complex.exp (Complex.I * (φ n : ℂ))) =
          boundary + variation ∧
      ‖boundary‖ ≤ 4 * (λ⁻¹ + 1) ∧
      ‖variation‖ ≤ 4 * (λ⁻¹ + 1) := by
  let boundary : ℂ := Complex.realPhase_prefixAbelBoundary φ a m
  let variation : ℂ := Complex.realPhase_prefixAbelVariation φ a m
  refine ⟨boundary, variation, ?_, ?_, ?_⟩
  · have hidentity :
        (∑ n ∈ Finset.Icc a m,
          Complex.realPhase_integerUnit φ n) =
            boundary + variation :=
      Complex.realPhase_prefixAbel_identity
        φ ham hm hλ_pos hsep
    exact hidentity
  · have hden' :
        ∀ n : ℕ,
          n ∈ Finset.Ico a b →
            ‖Complex.realPhase_inverseGeometricDenominator φ n‖ ≤
              2 * λ⁻¹ := by
      intro n hn
      exact hden n hn
    exact
      Complex.realPhase_prefixAbelBoundary_norm_bound
        φ ham hm hλ_pos hden'
  · have hden' :
        ∀ n : ℕ,
          n ∈ Finset.Ico a b →
            ‖Complex.realPhase_inverseGeometricDenominator φ n‖ ≤
              2 * λ⁻¹ := by
      intro n hn
      exact hden n hn
    exact
      Complex.realPhase_prefixAbelVariation_norm_bound
        φ ham hm hλ_pos hinc_mono hsep hden'

/-- The finite Abel transform supplies boundary and variation terms satisfying
the needed prefix bounds. -/
theorem Complex.realPhase_monotoneIncrement_prefix_abel_terms_bounded
    (φ : ℝ → ℝ)
    {a b m : ℕ}
    {λ : ℝ}
    (ha : 1 ≤ a)
    (hab_lt : a < b)
    (hm : m ∈ Finset.Icc a b)
    (hλ_pos : 0 < λ)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b λ)
    (hden :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖(1 -
            Complex.exp
              (Complex.I *
                (Complex.realPhase_integerIncrement φ n : ℂ)))⁻¹‖ ≤
            2 * λ⁻¹) :
    ∃ boundary variation : ℂ,
      (∑ n ∈ Finset.Icc a m,
        Complex.exp (Complex.I * (φ n : ℂ))) =
          boundary + variation ∧
      ‖boundary‖ ≤ 4 * (λ⁻¹ + 1) ∧
      ‖variation‖ ≤ 4 * (λ⁻¹ + 1) := by
  by_cases hma : m = a
  · exact Eq.subst
      (motive := fun r : ℕ =>
        ∃ boundary variation : ℂ,
          (∑ n ∈ Finset.Icc a r,
            Complex.exp (Complex.I * (φ n : ℂ))) =
              boundary + variation ∧
          ‖boundary‖ ≤ 4 * (λ⁻¹ + 1) ∧
          ‖variation‖ ≤ 4 * (λ⁻¹ + 1))
      hma.symm
      (Complex.realPhase_monotoneIncrement_singleton_prefix_abel_terms_bounded
        φ a hλ_pos)
  · have hm_bounds : a ≤ m ∧ m ≤ b :=
      Finset.mem_Icc.mp hm
    have ham : a < m :=
      lt_of_le_of_ne hm_bounds.1 (Ne.symm hma)
    exact
      Complex.realPhase_monotoneIncrement_prefix_abel_terms_bounded_of_lt
        φ ha hab_lt ham hm hλ_pos hinc_mono hsep hden

/-- Prefix-sum form of the finite monotone-increment Dirichlet estimate.

This is the actual finite summation-by-parts theorem: every initial segment of
the block is controlled by the same endpoint and variation bound. -/
theorem Complex.realPhase_monotoneIncrement_partialSummation_prefix_bound
    (φ : ℝ → ℝ)
    {a b m : ℕ}
    {λ : ℝ}
    (ha : 1 ≤ a)
    (hab_lt : a < b)
    (hm : m ∈ Finset.Icc a b)
    (hλ_pos : 0 < λ)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b λ)
    (hden :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖(1 -
            Complex.exp
              (Complex.I *
                (Complex.realPhase_integerIncrement φ n : ℂ)))⁻¹‖ ≤
            2 * λ⁻¹) :
    ‖∑ n ∈ Finset.Icc a m,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        8 * (λ⁻¹ + 1) := by
  rcases
    Complex.realPhase_monotoneIncrement_prefix_abel_terms_bounded
      φ ha hab_lt hm hλ_pos hinc_mono hsep hden with
    ⟨boundary, variation, hS, hboundary, hvariation⟩
  exact
    Complex.realPhase_monotoneIncrement_prefix_abel_norm_assembly
      hS hboundary hvariation

/-- Norm estimate after the finite Abel transform for monotone adjacent
frequencies. -/
theorem Complex.realPhase_monotoneIncrement_abel_transform_norm_bound
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {λ : ℝ}
    (ha : 1 ≤ a)
    (hab_lt : a < b)
    (hλ_pos : 0 < λ)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b λ)
    (hden :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖(1 -
            Complex.exp
              (Complex.I *
                (Complex.realPhase_integerIncrement φ n : ℂ)))⁻¹‖ ≤
            2 * λ⁻¹) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        8 * (λ⁻¹ + 1) := by
  have hb_mem : b ∈ Finset.Icc a b :=
    Finset.mem_Icc.mpr ⟨le_of_lt hab_lt, le_rfl⟩
  exact
    Complex.realPhase_monotoneIncrement_partialSummation_prefix_bound
      φ ha hab_lt hb_mem hλ_pos hinc_mono hsep hden

/-- Monotone-frequency finite Dirichlet-test core.

This is the summation-by-parts/variation step: once every adjacent frequency
has a geometric denominator bounded by `2 / λ`, monotonicity of the increments
controls the boundary and variation terms. -/
theorem Complex.realPhase_monotoneIncrement_dirichlet_variation_bound
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {λ : ℝ}
    (ha : 1 ≤ a)
    (hab_lt : a < b)
    (hλ_pos : 0 < λ)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b λ)
    (hden :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖(1 -
            Complex.exp
              (Complex.I *
                (Complex.realPhase_integerIncrement φ n : ℂ)))⁻¹‖ ≤
            2 * λ⁻¹) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        8 * (λ⁻¹ + 1) := by
  exact
    Complex.realPhase_monotoneIncrement_abel_transform_norm_bound
      φ ha hab_lt hλ_pos hinc_mono hsep hden

/-- Nontrivial monotone separated-increment Dirichlet-test primitive.

This is the genuine finite summation-by-parts case: at least one adjacent
increment is present, so the separation hypothesis supplies the geometric
denominators and monotonicity controls the variation term. -/
theorem Complex.realPhase_monotoneSeparatedIncrement_dirichlet_bound_of_lt
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {λ : ℝ}
    (ha : 1 ≤ a)
    (hab_lt : a < b)
    (hλ_pos : 0 < λ)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b λ) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        8 * (λ⁻¹ + 1) := by
  have hden :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖(1 -
            Complex.exp
              (Complex.I *
                (Complex.realPhase_integerIncrement φ n : ℂ)))⁻¹‖ ≤
            2 * λ⁻¹ := by
    intro n hn
    exact
      Complex.realPhase_geometricDenominator_inv_norm_bound
        hλ_pos
        (hsep n hn)
  exact
    Complex.realPhase_monotoneIncrement_dirichlet_variation_bound
      φ ha hab_lt hλ_pos hinc_mono hsep hden

/-- Finite Dirichlet-test primitive for monotone separated increments.

This is the discrete summation core behind Kusmin-Landau: the adjacent
increments must move monotonically through frequency space and stay separated
from every `2πℤ` resonance by at least `λ`.  The endpoint `+1` is necessary
for singleton blocks, where the separation hypothesis is vacuous. -/
theorem Complex.realPhase_monotoneSeparatedIncrement_dirichlet_bound
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {λ : ℝ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hλ_pos : 0 < λ)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b λ) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        8 * (λ⁻¹ + 1) := by
  rcases lt_or_eq_of_le hab with hab_lt | hab_eq
  · exact
      Complex.realPhase_monotoneSeparatedIncrement_dirichlet_bound_of_lt
        φ ha hab_lt hλ_pos hinc_mono hsep
  · exact
      Eq.subst
        (motive := fun c : ℕ =>
          ‖∑ n ∈ Finset.Icc a c,
            Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
              8 * (λ⁻¹ + 1))
        hab_eq
        (Complex.realPhase_singleton_integer_block_bound φ a hλ_pos)

/-- Finite monotone separated-increment exponential-sum primitive.

This is the public finite-difference Kusmin-Landau surface.  It is a thin
wrapper over the Dirichlet-test primitive with the boundary-safe constant
`8 * (λ⁻¹ + 1)`. -/
theorem Complex.realPhase_separatedIncrement_integer_block_bound
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {λ : ℝ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hλ_pos : 0 < λ)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b λ) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        8 * (λ⁻¹ + 1) := by
  exact
    Complex.realPhase_monotoneSeparatedIncrement_dirichlet_bound
      φ ha hab hλ_pos hinc_mono hsep

/-- Honest Kusmin-Landau block estimate with the required monotone separated
finite-difference hypothesis. -/
theorem Complex.realPhase_kusminLandau_integer_block_bound_of_separatedIncrement
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {λ : ℝ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hλ_pos : 0 < λ)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ => ‖deriv φ x‖)
        (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
          λ ≤ ‖deriv φ x‖)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b λ) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        8 * (λ⁻¹ + 1) := by
  exact
    Complex.realPhase_separatedIncrement_integer_block_bound
      φ ha hab hλ_pos hinc_mono hsep

/-- Kusmin-Landau/van der Corput finite first-derivative core for real phases.

This is the genuine oscillatory analytic primitive: the phase derivative stays
monotone with fixed sign modulo the frequency lattice and is separated from
`2πℤ`, so cancellation gives a reciprocal-derivative bound independent of the
length of the block.  A lower bound on `|φ'|` alone is not enough, because it
does not separate the integer increments from resonant multiples of `2π`. -/
theorem Complex.realPhase_kusminLandau_integer_block_bound
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {λ : ℝ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hλ_pos : 0 < λ)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ => ‖deriv φ x‖)
        (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
          λ ≤ ‖deriv φ x‖)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b λ) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        8 * (λ⁻¹ + 1) := by
  exact
    Complex.realPhase_kusminLandau_integer_block_bound_of_separatedIncrement
      φ ha hab hλ_pos hderiv_antitone hderiv_lower hinc_mono hsep

/-- General finite first-derivative estimate for a real phase sampled on an
integer block.

This is the owner-level van der Corput primitive needed by the logarithmic
phase.  The assumptions record the actual analytic input: monotonicity of the
absolute derivative and a positive lower bound throughout the containing real
interval. -/
theorem Complex.realPhase_firstDerivative_integer_block_bound
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {λ : ℝ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hλ_pos : 0 < λ)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ => ‖deriv φ x‖)
        (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
          λ ≤ ‖deriv φ x‖)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b λ) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        8 * (λ⁻¹ + 1) := by
  have hosc :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
          8 * (λ⁻¹ + 1) :=
    Complex.realPhase_kusminLandau_integer_block_bound
      φ ha hab hλ_pos hderiv_antitone hderiv_lower hinc_mono hsep
  exact hosc

/-- The logarithmic block lower-bound parameter is positive away from
zero frequency. -/
theorem Complex.logarithmicPhase_block_lowerParameter_pos
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (b : ℕ) :
    0 < (‖t‖ : ℝ) / ((b + 1 : ℕ) : ℝ) := by
  have ht_pos : 0 < ‖t‖ :=
    lt_of_lt_of_le zero_lt_one ht
  have hb_pos_nat : 0 < b + 1 :=
    Nat.succ_pos b
  have hb_pos_real : 0 < ((b + 1 : ℕ) : ℝ) := by
    exact_mod_cast hb_pos_nat
  exact div_pos ht_pos hb_pos_real

/-- The reciprocal of the logarithmic block lower-bound parameter is the block
length scale divided by `|t|`. -/
theorem Complex.logarithmicPhase_block_lowerParameter_inv_eq
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (b : ℕ) :
    (((‖t‖ : ℝ) / ((b + 1 : ℕ) : ℝ))⁻¹) =
      ((b + 1 : ℕ) : ℝ) / ‖t‖ := by
  have ht_ne : (‖t‖ : ℝ) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one ht)
  have hb_ne : (((b + 1 : ℕ) : ℝ)) ≠ 0 := by
    have hb_pos_nat : 0 < b + 1 :=
      Nat.succ_pos b
    exact_mod_cast (Nat.ne_of_gt hb_pos_nat)
  calc
    (((‖t‖ : ℝ) / ((b + 1 : ℕ) : ℝ))⁻¹) =
        ((b + 1 : ℕ) : ℝ) / ‖t‖ :=
      inv_div ((‖t‖ : ℝ)) (((b + 1 : ℕ) : ℝ))

/-- Real first-derivative-test primitive for the logarithmic scalar phase on
one integer block. -/
theorem Complex.logarithmicPhaseRealPhase_firstDerivative_integer_block_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ =>
          ‖deriv
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x‖)
        (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
          ((‖t‖ : ℝ) / ((b + 1 : ℕ) : ℝ)) ≤
            ‖deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) x‖)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b)
    (hsep :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b
        (‖t‖ / ((b + 1 : ℕ) : ℝ))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
        8 * (((b + 1 : ℕ) : ℝ) / ‖t‖ + 1) := by
  let λ : ℝ := ‖t‖ / ((b + 1 : ℕ) : ℝ)
  have hλ_pos : 0 < λ :=
    Complex.logarithmicPhase_block_lowerParameter_pos t ht b
  have hfirst :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
          8 * (λ⁻¹ + 1) :=
    Complex.realPhase_firstDerivative_integer_block_bound
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      ha hab hλ_pos
      hderiv_antitone
      hderiv_lower
      hinc_mono
      hsep
  have hλ_inv :
      λ⁻¹ = ((b + 1 : ℕ) : ℝ) / ‖t‖ :=
    Complex.logarithmicPhase_block_lowerParameter_inv_eq t ht b
  exact Eq.subst
    (motive := fun scale : ℝ =>
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
          8 * (scale + 1))
    hλ_inv
    hfirst

/-- Continuous first-derivative-test primitive for the sampled logarithmic
phase on one integer block.

This is the exact analytic theorem still needed from the van der Corput
first-derivative method after all concrete derivative computations have been
peeled into owner lemmas above. -/
theorem Complex.logarithmicPhase_firstDerivative_integer_block_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hderiv_antitone :
      AntitoneOn
        (fun x : ℝ =>
          ‖deriv
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t) x‖)
        (Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)))
    (hderiv_lower :
      ∀ x : ℝ,
        x ∈ Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) →
          ((‖t‖ : ℝ) / ((b + 1 : ℕ) : ℝ)) ≤
            ‖deriv
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t) x‖)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b)
    (hsep :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b
        (‖t‖ / ((b + 1 : ℕ) : ℝ))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t n‖ ≤
        8 * (((b + 1 : ℕ) : ℝ) / ‖t‖ + 1) := by
  have hphase :
      (∑ n ∈ Finset.Icc a b,
        Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t n) =
        ∑ n ∈ Finset.Icc a b,
          Complex.exp
            (Complex.I *
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ)) := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    exact
      Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_eq_realPhase
        t n
  have hreal_block :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
          8 * (((b + 1 : ℕ) : ℝ) / ‖t‖ + 1) :=
    Complex.logarithmicPhaseRealPhase_firstDerivative_integer_block_bound
      t ht ha hab
      (Complex.logarithmicPhaseRealPhase_deriv_norm_antitoneOn_integer_block t ha hab)
      (fun x hx =>
        Complex.logarithmicPhaseRealPhase_deriv_norm_block_lower_bound t ha hab hx)
      hinc_mono
      hsep
  exact Eq.subst
    (motive := fun S : ℂ =>
      ‖S‖ ≤ 8 * (((b + 1 : ℕ) : ℝ) / ‖t‖ + 1))
    hphase.symm
    hreal_block

/-- Standard first-derivative estimate on one monotone logarithmic-phase block.

This is the local van der Corput input: if the phase derivative has monotone
magnitude and is bounded below by `λ` on `[a,b]`, then the sampled exponential
sum over the block has the stated reciprocal-derivative bound. -/
theorem Complex.logarithmicPhase_monotone_firstDerivative_block_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b)
    (hsep :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b
        (‖t‖ / ((b + 1 : ℕ) : ℝ))) :
    ‖∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        8 * (((b + 1 : ℕ) : ℝ) / ‖t‖ + 1) := by
  have hsample :
      (∑ n ∈ Finset.Icc a b,
        ((n : ℂ) ^ (-(t : ℂ) * Complex.I))) =
        ∑ n ∈ Finset.Icc a b,
          Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t n := by
    refine Finset.sum_congr rfl ?_
    intro n hn_mem
    have hn_one : 1 ≤ n :=
      (Finset.mem_Icc.mp hn_mem).1
    have hn_pos : 0 < n :=
      Nat.lt_of_succ_le hn_one
    exact
      (Complex.logarithmicPhase_integer_sample_eq t hn_pos).symm
  have hblock :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t n‖ ≤
          8 * (((b + 1 : ℕ) : ℝ) / ‖t‖ + 1) :=
    Complex.logarithmicPhase_firstDerivative_integer_block_bound
      t ht ha hab
      (Complex.logarithmicPhase_deriv_norm_antitoneOn_integer_block t ha hab)
      (fun x hx =>
        Complex.logarithmicPhase_deriv_norm_block_lower_bound t ha hab hx)
      hinc_mono
      hsep
  exact Eq.subst
    (motive := fun S : ℂ =>
      ‖S‖ ≤ 8 * (((b + 1 : ℕ) : ℝ) / ‖t‖ + 1))
    hsample.symm
    hblock

/-- The one-block estimate is already bounded by the dyadic-cover expression
used by the global theorem. -/
theorem Complex.logarithmicPhase_single_block_le_dyadic_cover_expression
    (t : ℝ)
    (N : ℕ) :
    8 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + 1) ≤
      8 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1) := by
  have hlog_nonneg : (0 : ℝ) ≤ (Nat.log2 (N + 1) : ℝ) :=
    Nat.cast_nonneg (Nat.log2 (N + 1))
  have hinside :
      ((N + 1 : ℕ) : ℝ) / ‖t‖ + 1 ≤
        ((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1 := by
    calc
      ((N + 1 : ℕ) : ℝ) / ‖t‖ + 1 ≤
          ((N + 1 : ℕ) : ℝ) / ‖t‖ + (Nat.log2 (N + 1) : ℝ) + 1 := by
        exact add_le_add_right
          (le_add_of_nonneg_right hlog_nonneg)
          1
      _ = ((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1 :=
        rfl
  exact mul_le_mul_of_nonneg_left hinside (Nat.cast_nonneg 8)

/-- Dyadic block cover primitive for logarithmic-phase partial sums.

This isolates the finite combinatorics of decomposing `[1,N]` into dyadic
blocks and applying the one-block estimate on each block. -/
theorem Complex.logarithmicPhase_dyadic_block_cover_bound
    (hblock :
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ {a b : ℕ},
            1 ≤ a →
              a ≤ b →
                ‖∑ n ∈ Finset.Icc a b,
                  ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                  8 * (((b + 1 : ℕ) : ℝ) / ‖t‖ + 1)) :
    ∀ t : ℝ,
      1 ≤ ‖t‖ →
        ∀ N : ℕ,
          ‖∑ n ∈ Finset.Icc 1 N,
            ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
              8 *
                (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1) := by
  intro t ht N
  by_cases hN : N = 0
  · have hsum_zero :
        (∑ n ∈ Finset.Icc 1 N,
          ((n : ℂ) ^ (-(t : ℂ) * Complex.I))) = 0 := by
      exact Finset.sum_eq_zero
        (fun n hn => by
          have hn_bounds : 1 ≤ n ∧ n ≤ N :=
            Finset.mem_Icc.mp hn
          have hn_le_zero : n ≤ 0 :=
            Eq.subst (motive := fun k : ℕ => n ≤ k) hN hn_bounds.2
          have hn_not_one : ¬ 1 ≤ n :=
            Nat.not_succ_le_zero n hn_le_zero
          exact False.elim (hn_not_one hn_bounds.1))
    have htarget_nonneg :
        0 ≤ 8 *
          (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1) := by
      have hnorm_pos : 0 < ‖t‖ :=
        lt_of_lt_of_le zero_lt_one ht
      have hquot_nonneg :
          0 ≤ ((N + 1 : ℕ) : ℝ) / ‖t‖ :=
        div_nonneg (Nat.cast_nonneg (N + 1)) hnorm_pos.le
      have hlog_nonneg : 0 ≤ (Nat.log2 (N + 1) : ℝ) :=
        Nat.cast_nonneg (Nat.log2 (N + 1))
      have hinside_nonneg :
          0 ≤ ((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1 :=
        add_nonneg (add_nonneg hquot_nonneg hlog_nonneg) zero_le_one
      exact mul_nonneg (Nat.cast_nonneg 8) hinside_nonneg
    exact Eq.subst
      (motive := fun S : ℂ =>
        ‖S‖ ≤
          8 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1))
      hsum_zero.symm
      htarget_nonneg
  · have hN_pos : 1 ≤ N :=
      Nat.succ_le_of_lt (Nat.pos_of_ne_zero hN)
    have hsingle :
        ‖∑ n ∈ Finset.Icc 1 N,
          ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
            8 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + 1) :=
      hblock t ht (by decide : 1 ≤ 1) hN_pos
    have hcover :
        8 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + 1) ≤
          8 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1) :=
      Complex.logarithmicPhase_single_block_le_dyadic_cover_expression t N
    exact le_trans hsingle hcover

/-- Numerical lower bound used to show `log (2+N)` is uniformly positive. -/
theorem Complex.real_exp_half_le_two :
    Real.exp (1 / 2 : ℝ) ≤ 2 := by
  have hexp_one_le_four : Real.exp (1 : ℝ) ≤ 4 :=
    le_trans
      (le_of_lt Real.exp_one_lt_d9)
      (by norm_num)
  have hsqrt_le_two : Real.sqrt (Real.exp (1 : ℝ)) ≤ 2 :=
    (Real.sqrt_le_left (by norm_num : (0 : ℝ) ≤ 2)).mpr
      (by
        calc
          Real.exp (1 : ℝ) ≤ 4 := hexp_one_le_four
          _ = (2 : ℝ) ^ 2 := by norm_num)
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ 2)
      (Real.exp_half (1 : ℝ)).symm
      hsqrt_le_two

/-- The standard logarithmic factor is bounded below uniformly on natural
cutoffs. -/
theorem Complex.logarithmicPhase_standardLog_half_le
    (N : ℕ) :
    (1 / 2 : ℝ) ≤ Real.log (2 + N) := by
  have hpos : 0 < (2 : ℝ) + N :=
    lt_of_lt_of_le zero_lt_two (le_add_of_nonneg_right (Nat.cast_nonneg N))
  have hexp_le : Real.exp (1 / 2 : ℝ) ≤ (2 : ℝ) + N :=
    le_trans Complex.real_exp_half_le_two
      (le_add_of_nonneg_right (Nat.cast_nonneg N))
  exact (Real.le_log_iff_exp_le hpos).mpr hexp_le

/-- Absorb the successor in the dyadic logarithm by multiplying the argument
by the base. -/
theorem Complex.nat_log2_add_one_eq_nat_log_two_mul_succ
    (N : ℕ) :
    Nat.log2 (N + 1) + 1 = Nat.log 2 ((N + 1) * 2) := by
  calc
    Nat.log2 (N + 1) + 1 = Nat.log 2 (N + 1) + 1 := by
      exact congrArg (fun k : ℕ => k + 1) Nat.log2_eq_log_two
    _ = Nat.log 2 ((N + 1) * 2) := by
      exact (Nat.log_mul_base Nat.one_lt_two (Nat.succ_ne_zero N)).symm

/-- Positivity of the natural logarithm of the dyadic base. -/
theorem Complex.real_log_two_pos :
    0 < Real.log (2 : ℝ) := by
  exact Real.log_pos one_lt_two

/-- Upper numerical bound for `log 2`. -/
theorem Complex.real_log_two_le_one :
    Real.log (2 : ℝ) ≤ 1 := by
  have htwo_pos : (0 : ℝ) < 2 :=
    zero_lt_two
  have htwo_le_exp : (2 : ℝ) ≤ Real.exp (1 : ℝ) :=
    le_of_lt (lt_trans (by norm_num : (2 : ℝ) < 2.7182818283) Real.exp_one_gt_d9)
  exact (Real.log_le_iff_le_exp htwo_pos).mpr htwo_le_exp

/-- Lower numerical bound for `log 2`. -/
theorem Complex.one_half_le_real_log_two :
    (1 / 2 : ℝ) ≤ Real.log (2 : ℝ) := by
  exact Complex.logarithmicPhase_standardLog_half_le 0

/-- Strict lower numerical bound for `log 2`. -/
theorem Complex.one_half_lt_real_log_two :
    (1 / 2 : ℝ) < Real.log (2 : ℝ) := by
  have hexp_one_lt_four : Real.exp (1 : ℝ) < 4 :=
    lt_trans Real.exp_one_lt_d9 (by norm_num)
  have hexp_half_lt_two : Real.exp (1 / 2 : ℝ) < 2 := by
    have hsqrt : Real.sqrt (Real.exp (1 : ℝ)) < 2 :=
      (Real.sqrt_lt' zero_lt_two).mpr
        (by
          calc
            Real.exp (1 : ℝ) < 4 := hexp_one_lt_four
            _ = (2 : ℝ) ^ 2 := by norm_num)
    exact Eq.subst
      (motive := fun y : ℝ => y < 2)
      (Real.exp_half (1 : ℝ)).symm
      hsqrt
  have htwo_pos : (0 : ℝ) < 2 :=
    zero_lt_two
  exact (Real.log_lt_iff_lt_exp htwo_pos).mpr hexp_half_lt_two

/-- A rational lower bound for `log 2` used at the dyadic entropy checkpoint. -/
theorem Complex.two_thirds_le_real_log_two :
    (2 / 3 : ℝ) ≤ Real.log (2 : ℝ) := by
  have hexp_two_le_eight : Real.exp (2 : ℝ) ≤ 8 := by
    have hsq :
        Real.exp (2 : ℝ) = Real.exp (1 : ℝ) ^ 2 := by
      calc
        Real.exp (2 : ℝ) = Real.exp ((2 : ℕ) * (1 : ℝ)) := by norm_num
        _ = Real.exp (1 : ℝ) ^ 2 :=
          Real.exp_nat_mul (1 : ℝ) 2
    have hsq_bound : Real.exp (1 : ℝ) ^ 2 < (8 : ℝ) := by
      calc
        Real.exp (1 : ℝ) ^ 2 < (2.7182818286 : ℝ) ^ 2 := by
          exact pow_lt_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9 (by decide : 0 < 2)
        _ < (8 : ℝ) := by norm_num
    exact le_of_lt (Eq.subst (motive := fun z : ℝ => z < 8) hsq.symm hsq_bound)
  have hlog_eight : (2 : ℝ) ≤ Real.log (8 : ℝ) :=
    (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 8)).mpr hexp_two_le_eight
  have hlog_pow :
      Real.log (8 : ℝ) = 3 * Real.log (2 : ℝ) := by
    calc
      Real.log (8 : ℝ) = Real.log ((2 : ℝ) ^ 3) := by norm_num
      _ = (3 : ℝ) * Real.log (2 : ℝ) :=
        Real.log_pow (2 : ℝ) 3
  have htwo_le_three_log : (2 : ℝ) ≤ 3 * Real.log (2 : ℝ) :=
    Eq.subst (motive := fun target : ℝ => (2 : ℝ) ≤ target) hlog_pow hlog_eight
  exact (div_le_iff₀' (by norm_num : (0 : ℝ) < 3)).mp htwo_le_three_log

/-- The denominator in the explicit critical point is nonnegative. -/
theorem Complex.realLogDyadicComparisonCriticalPoint_den_nonneg :
    0 ≤ 2 * Real.log (2 : ℝ) - 1 := by
  have hhalf : (1 / 2 : ℝ) ≤ Real.log (2 : ℝ) :=
    Complex.one_half_le_real_log_two
  have htwice : (1 : ℝ) ≤ 2 * Real.log (2 : ℝ) := by
    exact (le_div_iff₀' zero_lt_two).mp hhalf
  exact sub_nonneg.mpr htwice

/-- Strict positivity of the critical-point denominator. -/
theorem Complex.realLogDyadicComparisonCriticalPoint_den_pos :
    0 < 2 * Real.log (2 : ℝ) - 1 := by
  have hhalf : (1 / 2 : ℝ) < Real.log (2 : ℝ) :=
    Complex.one_half_lt_real_log_two
  have htwice : (1 : ℝ) < 2 * Real.log (2 : ℝ) := by
    exact (div_lt_iff₀' zero_lt_two).mp hhalf
  exact sub_pos.mpr htwice

/-- The numerator in the explicit critical point is nonnegative. -/
theorem Complex.realLogDyadicComparisonCriticalPoint_num_nonneg :
    0 ≤ 2 - 2 * Real.log (2 : ℝ) := by
  have hlog_le_one : Real.log (2 : ℝ) ≤ 1 :=
    Complex.real_log_two_le_one
  have htwice : 2 * Real.log (2 : ℝ) ≤ (2 : ℝ) * 1 :=
    mul_le_mul_of_nonneg_left hlog_le_one zero_le_two
  have htwice' : 2 * Real.log (2 : ℝ) ≤ 2 := by
    exact Eq.subst (motive := fun rhs : ℝ => 2 * Real.log (2 : ℝ) ≤ rhs) (mul_one 2) htwice
  exact sub_nonneg.mpr htwice'

/-- Defect function for the sharp dyadic-log comparison.  The target inequality
is exactly nonnegativity of this function on `[0,∞)`. -/
def Complex.realLogDyadicComparisonDefect
    (x : ℝ) : ℝ :=
  (2 * Real.log (x + 2)) * Real.log (2 : ℝ) -
    Real.log (2 * (x + 1))

/-- Critical point of the dyadic-log comparison defect. -/
def Complex.realLogDyadicComparisonCriticalPoint : ℝ :=
  (2 - 2 * Real.log (2 : ℝ)) / (2 * Real.log (2 : ℝ) - 1)

/-- The dyadic-log comparison critical point lies in the nonnegative interval. -/
theorem Complex.realLogDyadicComparisonCriticalPoint_nonneg :
    0 ≤ Complex.realLogDyadicComparisonCriticalPoint := by
  exact div_nonneg
    Complex.realLogDyadicComparisonCriticalPoint_num_nonneg
    Complex.realLogDyadicComparisonCriticalPoint_den_nonneg

/-- Elementary cancellation used in the derivative of `log (2 * (x + 1))`. -/
theorem Complex.two_div_two_mul_eq_one_div
    {u : ℝ}
    (hu : u ≠ 0) :
    (2 : ℝ) / (2 * u) = 1 / u := by
  calc
    (2 : ℝ) / (2 * u) = (2 : ℝ) * (2 * u)⁻¹ :=
      div_eq_mul_inv 2 (2 * u)
    _ = (2 : ℝ) * (u⁻¹ * (2 : ℝ)⁻¹) := by
      exact congrArg (fun z : ℝ => (2 : ℝ) * z) (mul_inv_rev 2 u)
    _ = ((2 : ℝ) * (2 : ℝ)⁻¹) * u⁻¹ := by
      ring
    _ = (1 : ℝ) * u⁻¹ := by
      exact congrArg (fun z : ℝ => z * u⁻¹) (mul_inv_cancel₀ two_ne_zero)
    _ = u⁻¹ :=
      one_mul u⁻¹
    _ = 1 / u :=
      (one_div u).symm

/-- Positive denominator for the dyadic defect derivative on `[0,∞)`. -/
theorem Complex.realLogDyadicComparisonDefect_deriv_den_pos
    {x : ℝ}
    (hx : 0 ≤ x) :
    0 < (x + 2) * (x + 1) := by
  have hx_two : 0 < x + 2 := by linarith
  have hx_one : 0 < x + 1 := by linarith
  exact mul_pos hx_two hx_one

/-- Exact factorization of the dyadic defect derivative around the critical
point. -/
theorem Complex.realLogDyadicComparisonDefect_deriv_factorization
    {x : ℝ}
    (hx : 0 ≤ x) :
    2 * Real.log (2 : ℝ) / (x + 2) - 1 / (x + 1) =
      ((2 * Real.log (2 : ℝ) - 1) *
        (x - Complex.realLogDyadicComparisonCriticalPoint)) /
          ((x + 2) * (x + 1)) := by
  have hx_two_ne : x + 2 ≠ 0 :=
    ne_of_gt (by linarith : 0 < x + 2)
  have hx_one_ne : x + 1 ≠ 0 :=
    ne_of_gt (by linarith : 0 < x + 1)
  have hcrit_den_ne : 2 * Real.log (2 : ℝ) - 1 ≠ 0 :=
    ne_of_gt Complex.realLogDyadicComparisonCriticalPoint_den_pos
  unfold Complex.realLogDyadicComparisonCriticalPoint
  field_simp [hx_two_ne, hx_one_ne, hcrit_den_ne]
  ring

/-- Derivative formula for the dyadic-log comparison defect on `(0,∞)`. -/
theorem Complex.realLogDyadicComparisonDefect_hasDerivAt
    {x : ℝ}
    (hx : 0 ≤ x) :
    HasDerivAt
      Complex.realLogDyadicComparisonDefect
      (2 * Real.log (2 : ℝ) / (x + 2) - 1 / (x + 1))
      x := by
  have hx_two_pos : 0 < x + 2 := by linarith
  have hx_one_pos : 0 < x + 1 := by linarith
  have hlog_shift :
      HasDerivAt (fun y : ℝ => Real.log (y + 2)) (1 / (x + 2)) x := by
    have hshift : HasDerivAt (fun y : ℝ => y + 2) 1 x :=
      (hasDerivAt_id x).add_const 2
    have hne : x + 2 ≠ 0 :=
      ne_of_gt hx_two_pos
    exact hshift.log hne
  have hleft :
      HasDerivAt
        (fun y : ℝ => (2 * Real.log (y + 2)) * Real.log (2 : ℝ))
        (2 * Real.log (2 : ℝ) / (x + 2))
        x := by
    have hscaled :
        HasDerivAt
          (fun y : ℝ => (2 * Real.log (y + 2)) * Real.log (2 : ℝ))
          ((2 * (1 / (x + 2))) * Real.log (2 : ℝ))
          x :=
      (hlog_shift.const_mul 2).const_mul (Real.log (2 : ℝ))
    have hderiv :
        ((2 * (1 / (x + 2))) * Real.log (2 : ℝ)) =
          2 * Real.log (2 : ℝ) / (x + 2) := by
      ring
    exact Eq.subst
      (motive := fun d : ℝ =>
        HasDerivAt
          (fun y : ℝ => (2 * Real.log (y + 2)) * Real.log (2 : ℝ))
          d
          x)
      hderiv
      hscaled
  have hlog_linear :
      HasDerivAt (fun y : ℝ => Real.log (2 * (y + 1))) (1 / (x + 1)) x := by
    have hshift : HasDerivAt (fun y : ℝ => y + 1) 1 x :=
      (hasDerivAt_id x).add_const 1
    have hlinear : HasDerivAt (fun y : ℝ => 2 * (y + 1)) 2 x := by
      have hscaled : HasDerivAt (fun y : ℝ => 2 * (y + 1)) (2 * 1) x :=
        hshift.const_mul 2
      exact Eq.subst
        (motive := fun d : ℝ => HasDerivAt (fun y : ℝ => 2 * (y + 1)) d x)
        (mul_one 2)
        hscaled
    have hne : 2 * (x + 1) ≠ 0 :=
      mul_ne_zero two_ne_zero (ne_of_gt hx_one_pos)
    have hlog : HasDerivAt (fun y : ℝ => Real.log (2 * (y + 1))) (2 / (2 * (x + 1))) x :=
      hlinear.log hne
    have hderiv : 2 / (2 * (x + 1)) = 1 / (x + 1) := by
      exact Complex.two_div_two_mul_eq_one_div (ne_of_gt hx_one_pos)
    exact Eq.subst
      (motive := fun d : ℝ =>
        HasDerivAt (fun y : ℝ => Real.log (2 * (y + 1))) d x)
      hderiv
      hlog
  have hsub :
      HasDerivAt
        (fun y : ℝ =>
          (2 * Real.log (y + 2)) * Real.log (2 : ℝ) -
            Real.log (2 * (y + 1)))
        (2 * Real.log (2 : ℝ) / (x + 2) - 1 / (x + 1))
        x :=
    hleft.sub hlog_linear
  exact hsub

/-- Algebraic sign of the dyadic defect derivative before the critical point. -/
theorem Complex.realLogDyadicComparisonDefect_deriv_nonpos_on_left
    {x : ℝ}
    (hx : x ∈ Set.Icc 0 Complex.realLogDyadicComparisonCriticalPoint) :
    2 * Real.log (2 : ℝ) / (x + 2) - 1 / (x + 1) ≤ 0 := by
  have hfactor :
      2 * Real.log (2 : ℝ) / (x + 2) - 1 / (x + 1) =
        ((2 * Real.log (2 : ℝ) - 1) *
          (x - Complex.realLogDyadicComparisonCriticalPoint)) /
            ((x + 2) * (x + 1)) :=
    Complex.realLogDyadicComparisonDefect_deriv_factorization hx.1
  have hnum_nonpos :
      (2 * Real.log (2 : ℝ) - 1) *
          (x - Complex.realLogDyadicComparisonCriticalPoint) ≤ 0 := by
    have hden_nonneg : 0 ≤ 2 * Real.log (2 : ℝ) - 1 :=
      le_of_lt Complex.realLogDyadicComparisonCriticalPoint_den_pos
    have hdiff_nonpos : x - Complex.realLogDyadicComparisonCriticalPoint ≤ 0 :=
      sub_nonpos.mpr hx.2
    exact mul_nonpos_of_nonneg_of_nonpos hden_nonneg hdiff_nonpos
  have hden_pos : 0 < (x + 2) * (x + 1) :=
    Complex.realLogDyadicComparisonDefect_deriv_den_pos hx.1
  have hquot_nonpos :
      ((2 * Real.log (2 : ℝ) - 1) *
          (x - Complex.realLogDyadicComparisonCriticalPoint)) /
            ((x + 2) * (x + 1)) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg hnum_nonpos hden_pos.le
  exact Eq.subst (motive := fun d : ℝ => d ≤ 0) hfactor.symm hquot_nonpos

/-- Algebraic sign of the dyadic defect derivative after the critical point. -/
theorem Complex.realLogDyadicComparisonDefect_deriv_nonneg_on_right
    {x : ℝ}
    (hx : x ∈ Set.Ici Complex.realLogDyadicComparisonCriticalPoint) :
    0 ≤ 2 * Real.log (2 : ℝ) / (x + 2) - 1 / (x + 1) := by
  have hx_nonneg : 0 ≤ x :=
    le_trans Complex.realLogDyadicComparisonCriticalPoint_nonneg hx
  have hfactor :
      2 * Real.log (2 : ℝ) / (x + 2) - 1 / (x + 1) =
        ((2 * Real.log (2 : ℝ) - 1) *
          (x - Complex.realLogDyadicComparisonCriticalPoint)) /
            ((x + 2) * (x + 1)) :=
    Complex.realLogDyadicComparisonDefect_deriv_factorization hx_nonneg
  have hnum_nonneg :
      0 ≤
        (2 * Real.log (2 : ℝ) - 1) *
          (x - Complex.realLogDyadicComparisonCriticalPoint) := by
    have hden_nonneg : 0 ≤ 2 * Real.log (2 : ℝ) - 1 :=
      le_of_lt Complex.realLogDyadicComparisonCriticalPoint_den_pos
    have hdiff_nonneg : 0 ≤ x - Complex.realLogDyadicComparisonCriticalPoint :=
      sub_nonneg.mpr hx
    exact mul_nonneg hden_nonneg hdiff_nonneg
  have hden_pos : 0 < (x + 2) * (x + 1) :=
    Complex.realLogDyadicComparisonDefect_deriv_den_pos hx_nonneg
  have hquot_nonneg :
      0 ≤
        ((2 * Real.log (2 : ℝ) - 1) *
          (x - Complex.realLogDyadicComparisonCriticalPoint)) /
            ((x + 2) * (x + 1)) :=
    div_nonneg hnum_nonneg hden_pos.le
  exact Eq.subst (motive := fun d : ℝ => 0 ≤ d) hfactor.symm hquot_nonneg

/-- The dyadic-log comparison defect is antitone until its critical point. -/
theorem Complex.realLogDyadicComparisonDefect_antitoneOn_left :
    AntitoneOn
      Complex.realLogDyadicComparisonDefect
      (Set.Icc 0 Complex.realLogDyadicComparisonCriticalPoint) := by
  exact
    antitoneOn_of_deriv_nonpos
      (convex_Icc 0 Complex.realLogDyadicComparisonCriticalPoint)
      (fun x hx =>
        (Complex.realLogDyadicComparisonDefect_hasDerivAt hx.1).continuousAt.continuousWithinAt)
      (fun x hx =>
        (Complex.realLogDyadicComparisonDefect_hasDerivAt hx.1).differentiableAt.differentiableWithinAt)
      (fun x hx =>
        Eq.subst
          (motive := fun d : ℝ => d ≤ 0)
          (Complex.realLogDyadicComparisonDefect_hasDerivAt hx.1).deriv.symm
          (Complex.realLogDyadicComparisonDefect_deriv_nonpos_on_left hx))

/-- The dyadic-log comparison defect is monotone after its critical point. -/
theorem Complex.realLogDyadicComparisonDefect_monotoneOn_right :
    MonotoneOn
      Complex.realLogDyadicComparisonDefect
      (Set.Ici Complex.realLogDyadicComparisonCriticalPoint) := by
  exact
    monotoneOn_of_deriv_nonneg
      (convex_Ici Complex.realLogDyadicComparisonCriticalPoint)
      (fun x hx =>
        (Complex.realLogDyadicComparisonDefect_hasDerivAt
          (le_trans Complex.realLogDyadicComparisonCriticalPoint_nonneg hx)).continuousAt.continuousWithinAt)
      (fun x hx =>
        (Complex.realLogDyadicComparisonDefect_hasDerivAt
          (le_trans Complex.realLogDyadicComparisonCriticalPoint_nonneg hx)).differentiableAt.differentiableWithinAt)
      (fun x hx =>
        Eq.subst
          (motive := fun d : ℝ => 0 ≤ d)
          (Complex.realLogDyadicComparisonDefect_hasDerivAt
            (le_trans Complex.realLogDyadicComparisonCriticalPoint_nonneg hx)).deriv.symm
          (Complex.realLogDyadicComparisonDefect_deriv_nonneg_on_right hx))

/-- The endpoint value of the dyadic-log comparison defect is nonnegative. -/
theorem Complex.realLogDyadicComparisonDefect_zero_nonneg :
    0 ≤ Complex.realLogDyadicComparisonDefect 0 := by
  have hdef :
      Complex.realLogDyadicComparisonDefect 0 =
        (2 * Real.log (2 : ℝ)) * Real.log (2 : ℝ) -
          Real.log (2 : ℝ) := by
    have harg_two : (0 : ℝ) + 2 = 2 := by ring
    have hmul : (2 : ℝ) * (0 + 1) = 2 := by ring
    calc
      Complex.realLogDyadicComparisonDefect 0 =
          (2 * Real.log ((0 : ℝ) + 2)) * Real.log (2 : ℝ) -
            Real.log ((2 : ℝ) * (0 + 1)) := by
        rfl
      _ = (2 * Real.log (2 : ℝ)) * Real.log (2 : ℝ) -
            Real.log ((2 : ℝ) * (0 + 1)) := by
        exact congrArg
          (fun z : ℝ => (2 * Real.log z) * Real.log (2 : ℝ) -
            Real.log ((2 : ℝ) * (0 + 1)))
          harg_two
      _ = (2 * Real.log (2 : ℝ)) * Real.log (2 : ℝ) -
            Real.log (2 : ℝ) := by
        exact congrArg
          (fun z : ℝ => (2 * Real.log (2 : ℝ)) * Real.log (2 : ℝ) -
            Real.log z)
          hmul
  have hlog_nonneg : 0 ≤ Real.log (2 : ℝ) :=
    le_of_lt Complex.real_log_two_pos
  have hfactor_nonneg : 0 ≤ 2 * Real.log (2 : ℝ) - 1 :=
    Complex.realLogDyadicComparisonCriticalPoint_den_nonneg
  have hprod :
      0 ≤ Real.log (2 : ℝ) * (2 * Real.log (2 : ℝ) - 1) :=
    mul_nonneg hlog_nonneg hfactor_nonneg
  have halg :
      (2 * Real.log (2 : ℝ)) * Real.log (2 : ℝ) -
          Real.log (2 : ℝ) =
        Real.log (2 : ℝ) * (2 * Real.log (2 : ℝ) - 1) := by
    ring
  exact Eq.subst
    (motive := fun target : ℝ => 0 ≤ target)
    hdef.symm
    (Eq.subst (motive := fun target : ℝ => 0 ≤ target) halg.symm hprod)

/-- At the critical point, the shifted `x+1` denominator has this explicit
value. -/
theorem Complex.realLogDyadicComparisonCriticalPoint_add_one_eq :
    Complex.realLogDyadicComparisonCriticalPoint + 1 =
      1 / (2 * Real.log (2 : ℝ) - 1) := by
  have hden_ne : 2 * Real.log (2 : ℝ) - 1 ≠ 0 :=
    ne_of_gt Complex.realLogDyadicComparisonCriticalPoint_den_pos
  unfold Complex.realLogDyadicComparisonCriticalPoint
  field_simp [hden_ne]
  ring

/-- At the critical point, the shifted `x+2` denominator has this explicit
value. -/
theorem Complex.realLogDyadicComparisonCriticalPoint_add_two_eq :
    Complex.realLogDyadicComparisonCriticalPoint + 2 =
      (2 * Real.log (2 : ℝ)) / (2 * Real.log (2 : ℝ) - 1) := by
  have hden_ne : 2 * Real.log (2 : ℝ) - 1 ≠ 0 :=
    ne_of_gt Complex.realLogDyadicComparisonCriticalPoint_den_pos
  unfold Complex.realLogDyadicComparisonCriticalPoint
  field_simp [hden_ne]
  ring

/-- Entropy-form expression behind the dyadic critical value. -/
def Complex.realLogDyadicEntropyExpression
    (y : ℝ) : ℝ :=
  y * Real.log y - (y - 1) * Real.log (y - 1)

/-- Derivative formula for the entropy-form expression. -/
theorem Complex.realLogDyadicEntropyExpression_hasDerivAt
    {y : ℝ}
    (hy : 1 < y) :
    HasDerivAt
      Complex.realLogDyadicEntropyExpression
      (Real.log y - Real.log (y - 1))
      y := by
  have hy_ne : y ≠ 0 :=
    ne_of_gt (lt_trans zero_lt_one hy)
  have hy_sub_pos : 0 < y - 1 :=
    sub_pos.mpr hy
  have hy_sub_ne : y - 1 ≠ 0 :=
    ne_of_gt hy_sub_pos
  have hleft :
      HasDerivAt (fun z : ℝ => z * Real.log z) (Real.log y + 1) y :=
    Real.hasDerivAt_mul_log hy_ne
  have hshift : HasDerivAt (fun z : ℝ => z - 1) 1 y :=
    (hasDerivAt_id y).sub_const 1
  have hright :
      HasDerivAt
        (fun z : ℝ => (z - 1) * Real.log (z - 1))
        (Real.log (y - 1) + 1)
        y := by
    have hmul_log :
        HasDerivAt (fun u : ℝ => u * Real.log u)
          (Real.log (y - 1) + 1)
          (y - 1) :=
      Real.hasDerivAt_mul_log hy_sub_ne
    have hcomp :
        HasDerivAt
          (fun z : ℝ => (fun u : ℝ => u * Real.log u) (z - 1))
          ((Real.log (y - 1) + 1) * 1)
          y :=
      hmul_log.comp y hshift
    exact Eq.subst
      (motive := fun d : ℝ =>
        HasDerivAt
          (fun z : ℝ => (z - 1) * Real.log (z - 1))
          d
          y)
      (mul_one (Real.log (y - 1) + 1))
      hcomp
  have hsub :
      HasDerivAt
        (fun z : ℝ => z * Real.log z - (z - 1) * Real.log (z - 1))
        ((Real.log y + 1) - (Real.log (y - 1) + 1))
        y :=
    hleft.sub hright
  have hderiv :
      (Real.log y + 1) - (Real.log (y - 1) + 1) =
        Real.log y - Real.log (y - 1) := by
    ring
  exact Eq.subst
    (motive := fun d : ℝ =>
      HasDerivAt Complex.realLogDyadicEntropyExpression d y)
    hderiv
    hsub

/-- The entropy-form derivative is nonnegative on `(1,∞)`. -/
theorem Complex.realLogDyadicEntropyExpression_deriv_nonneg
    {y : ℝ}
    (hy : 1 < y) :
    0 ≤ Real.log y - Real.log (y - 1) := by
  have hy_sub_pos : 0 < y - 1 :=
    sub_pos.mpr hy
  have hsub_le_y : y - 1 ≤ y := by
    linarith
  have hlog_le : Real.log (y - 1) ≤ Real.log y :=
    Real.log_le_log hy_sub_pos hsub_le_y
  exact sub_nonneg.mpr hlog_le

/-- The entropy-form expression is monotone on the interval actually used by
the critical-point argument. -/
theorem Complex.realLogDyadicEntropyExpression_monotoneOn_Ici_two_log :
    MonotoneOn
      Complex.realLogDyadicEntropyExpression
      (Set.Ici (2 * Real.log (2 : ℝ))) := by
  exact
    monotoneOn_of_deriv_nonneg
      (convex_Ici (2 * Real.log (2 : ℝ)))
      (fun y hy =>
        (Complex.realLogDyadicEntropyExpression_hasDerivAt
          (lt_of_lt_of_le
            (sub_pos.mp Complex.realLogDyadicComparisonCriticalPoint_den_pos)
            hy)).continuousAt.continuousWithinAt)
      (fun y hy =>
        (Complex.realLogDyadicEntropyExpression_hasDerivAt
          (lt_of_lt_of_le
            (sub_pos.mp Complex.realLogDyadicComparisonCriticalPoint_den_pos)
            hy)).differentiableAt.differentiableWithinAt)
      (fun y hy =>
        Eq.subst
          (motive := fun d : ℝ => 0 ≤ d)
          (Complex.realLogDyadicEntropyExpression_hasDerivAt
            (lt_of_lt_of_le
              (sub_pos.mp Complex.realLogDyadicComparisonCriticalPoint_den_pos)
              hy)).deriv.symm
          (Complex.realLogDyadicEntropyExpression_deriv_nonneg
            (lt_of_lt_of_le
              (sub_pos.mp Complex.realLogDyadicComparisonCriticalPoint_den_pos)
              hy)))

/-- The entropy-form expression is monotone on any interval `[a,∞)` with
`1 < a`. -/
theorem Complex.realLogDyadicEntropyExpression_monotoneOn_Ici_of_one_lt
    {a : ℝ}
    (ha : 1 < a) :
    MonotoneOn Complex.realLogDyadicEntropyExpression (Set.Ici a) := by
  exact
    monotoneOn_of_deriv_nonneg
      (convex_Ici a)
      (fun y hy =>
        (Complex.realLogDyadicEntropyExpression_hasDerivAt
          (lt_of_lt_of_le ha hy)).continuousAt.continuousWithinAt)
      (fun y hy =>
        (Complex.realLogDyadicEntropyExpression_hasDerivAt
          (lt_of_lt_of_le ha hy)).differentiableAt.differentiableWithinAt)
      (fun y hy =>
        Eq.subst
          (motive := fun d : ℝ => 0 ≤ d)
          (Complex.realLogDyadicEntropyExpression_hasDerivAt
            (lt_of_lt_of_le ha hy)).deriv.symm
          (Complex.realLogDyadicEntropyExpression_deriv_nonneg
            (lt_of_lt_of_le ha hy)))

/-- Rational checkpoint for the entropy-form expression. -/
theorem Complex.real_log_two_le_entropyExpression_at_four_thirds :
    Real.log (2 : ℝ) ≤
      Complex.realLogDyadicEntropyExpression (4 / 3 : ℝ) := by
  have hlog_three_le :
      Real.log (3 : ℝ) ≤ (5 / 3 : ℝ) * Real.log (2 : ℝ) := by
    have hlog_27_le_32 : Real.log (27 : ℝ) ≤ Real.log (32 : ℝ) :=
      Real.log_le_log (by norm_num : (0 : ℝ) < 27) (by norm_num : (27 : ℝ) ≤ 32)
    have hlog_27 : Real.log (27 : ℝ) = (3 : ℝ) * Real.log (3 : ℝ) := by
      calc
        Real.log (27 : ℝ) = Real.log ((3 : ℝ) ^ 3) := by norm_num
        _ = (3 : ℝ) * Real.log (3 : ℝ) :=
          Real.log_pow (3 : ℝ) 3
    have hlog_32 : Real.log (32 : ℝ) = (5 : ℝ) * Real.log (2 : ℝ) := by
      calc
        Real.log (32 : ℝ) = Real.log ((2 : ℝ) ^ 5) := by norm_num
        _ = (5 : ℝ) * Real.log (2 : ℝ) :=
          Real.log_pow (2 : ℝ) 5
    have hthree :
        (3 : ℝ) * Real.log (3 : ℝ) ≤ (5 : ℝ) * Real.log (2 : ℝ) :=
      Eq.subst
        (motive := fun lhs : ℝ => lhs ≤ (5 : ℝ) * Real.log (2 : ℝ))
        hlog_27
        (Eq.subst
          (motive := fun rhs : ℝ => Real.log (27 : ℝ) ≤ rhs)
          hlog_32
          hlog_27_le_32)
    exact (le_div_iff₀' (by norm_num : (0 : ℝ) < 3)).mp hthree
  have hvalue :
      Complex.realLogDyadicEntropyExpression (4 / 3 : ℝ) =
        (8 / 3 : ℝ) * Real.log (2 : ℝ) - Real.log (3 : ℝ) := by
    have hfour_ne : (4 / 3 : ℝ) ≠ 0 := by norm_num
    have hone_ne : ((4 / 3 : ℝ) - 1) ≠ 0 := by norm_num
    have hlog_four_thirds :
        Real.log (4 / 3 : ℝ) = 2 * Real.log (2 : ℝ) - Real.log (3 : ℝ) := by
      calc
        Real.log (4 / 3 : ℝ) = Real.log ((4 : ℝ) / 3) := by norm_num
        _ = Real.log (4 : ℝ) - Real.log (3 : ℝ) :=
          Real.log_div (by norm_num : (4 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)
        _ = 2 * Real.log (2 : ℝ) - Real.log (3 : ℝ) := by
          have hlog_four : Real.log (4 : ℝ) = 2 * Real.log (2 : ℝ) := by
            calc
              Real.log (4 : ℝ) = Real.log ((2 : ℝ) ^ 2) := by norm_num
              _ = (2 : ℝ) * Real.log (2 : ℝ) :=
                Real.log_pow (2 : ℝ) 2
          exact congrArg (fun z : ℝ => z - Real.log (3 : ℝ)) hlog_four
    have hlog_one_third :
        Real.log ((4 / 3 : ℝ) - 1) = - Real.log (3 : ℝ) := by
      calc
        Real.log ((4 / 3 : ℝ) - 1) = Real.log ((1 : ℝ) / 3) := by norm_num
        _ = Real.log (1 : ℝ) - Real.log (3 : ℝ) :=
          Real.log_div one_ne_zero (by norm_num : (3 : ℝ) ≠ 0)
        _ = - Real.log (3 : ℝ) := by
          rw [Real.log_one, zero_sub]
    calc
      Complex.realLogDyadicEntropyExpression (4 / 3 : ℝ) =
          (4 / 3 : ℝ) * Real.log (4 / 3 : ℝ) -
            ((4 / 3 : ℝ) - 1) * Real.log ((4 / 3 : ℝ) - 1) := by
        rfl
      _ = (4 / 3 : ℝ) * (2 * Real.log (2 : ℝ) - Real.log (3 : ℝ)) -
            ((4 / 3 : ℝ) - 1) * (- Real.log (3 : ℝ)) := by
        exact congrArg₂ Sub.sub
          (congrArg (fun z : ℝ => (4 / 3 : ℝ) * z) hlog_four_thirds)
          (congrArg (fun z : ℝ => ((4 / 3 : ℝ) - 1) * z) hlog_one_third)
      _ = (8 / 3 : ℝ) * Real.log (2 : ℝ) - Real.log (3 : ℝ) := by
        ring
  have htarget :
      Real.log (2 : ℝ) ≤ (8 / 3 : ℝ) * Real.log (2 : ℝ) - Real.log (3 : ℝ) := by
    have hmove :
        Real.log (2 : ℝ) + Real.log (3 : ℝ) ≤
          (8 / 3 : ℝ) * Real.log (2 : ℝ) := by
      have hsum :
          Real.log (2 : ℝ) + Real.log (3 : ℝ) ≤
            Real.log (2 : ℝ) + (5 / 3 : ℝ) * Real.log (2 : ℝ) :=
        add_le_add_left hlog_three_le (Real.log (2 : ℝ))
      have halg :
          Real.log (2 : ℝ) + (5 / 3 : ℝ) * Real.log (2 : ℝ) =
            (8 / 3 : ℝ) * Real.log (2 : ℝ) := by
        ring
      exact Eq.subst
        (motive := fun rhs : ℝ => Real.log (2 : ℝ) + Real.log (3 : ℝ) ≤ rhs)
        halg
        hsum
    exact (le_sub_iff_add_le).mpr hmove
  exact Eq.subst
    (motive := fun target : ℝ => Real.log (2 : ℝ) ≤ target)
    hvalue.symm
    htarget

/-- The entropy-form inequality at the lower endpoint `2 log 2`. -/
theorem Complex.real_log_two_le_entropyExpression_at_two_log :
    Real.log (2 : ℝ) ≤
      Complex.realLogDyadicEntropyExpression (2 * Real.log (2 : ℝ)) := by
  have hfour_thirds_lt : (1 : ℝ) < 4 / 3 := by norm_num
  have hfour_thirds_le :
      (4 / 3 : ℝ) ≤ 2 * Real.log (2 : ℝ) := by
    have hlog : (2 / 3 : ℝ) ≤ Real.log (2 : ℝ) :=
      Complex.two_thirds_le_real_log_two
    exact (le_div_iff₀' zero_lt_two).mp hlog
  have hmono :
      Complex.realLogDyadicEntropyExpression (4 / 3 : ℝ) ≤
        Complex.realLogDyadicEntropyExpression (2 * Real.log (2 : ℝ)) :=
    Complex.realLogDyadicEntropyExpression_monotoneOn_Ici_of_one_lt
      hfour_thirds_lt
      le_rfl
      hfour_thirds_le
      hfour_thirds_le
  exact le_trans
    Complex.real_log_two_le_entropyExpression_at_four_thirds
    hmono

/-- Entropy-form inequality behind the dyadic critical value on the true
interval needed by the critical point: `2 log 2 ≤ y ≤ 2`.

The stronger-looking statement on all of `(1,2]` is false, since the
entropy-form expression is increasing and tends to `0` as `y → 1+`. -/
theorem Complex.real_log_two_le_entropyExpression_on_two_log_two
    {y : ℝ}
    (hy_lower : 2 * Real.log (2 : ℝ) ≤ y)
    (hy_two : y ≤ 2) :
    Real.log (2 : ℝ) ≤ y * Real.log y - (y - 1) * Real.log (y - 1) := by
  have hbase :
      Real.log (2 : ℝ) ≤
        Complex.realLogDyadicEntropyExpression (2 * Real.log (2 : ℝ)) :=
    Complex.real_log_two_le_entropyExpression_at_two_log
  have hmono :
      Complex.realLogDyadicEntropyExpression (2 * Real.log (2 : ℝ)) ≤
        Complex.realLogDyadicEntropyExpression y :=
    Complex.realLogDyadicEntropyExpression_monotoneOn_Ici_two_log
      le_rfl
      hy_lower
      hy_lower
  have hdef :
      Complex.realLogDyadicEntropyExpression y =
        y * Real.log y - (y - 1) * Real.log (y - 1) := by
    rfl
  exact Eq.subst
    (motive := fun target : ℝ => Real.log (2 : ℝ) ≤ target)
    hdef
    (le_trans hbase hmono)

/-- The critical expression is the entropy-form expression at
`y = 2 log 2`. -/
theorem Complex.realLogDyadicComparisonCriticalExpression_eq_entropy :
    (2 *
        Real.log
          ((2 * Real.log (2 : ℝ)) / (2 * Real.log (2 : ℝ) - 1))) *
          Real.log (2 : ℝ) -
        Real.log (2 / (2 * Real.log (2 : ℝ) - 1)) =
      (2 * Real.log (2 : ℝ)) * Real.log (2 * Real.log (2 : ℝ)) -
        ((2 * Real.log (2 : ℝ)) - 1) *
          Real.log ((2 * Real.log (2 : ℝ)) - 1) -
        Real.log (2 : ℝ) := by
  have hL_pos : 0 < Real.log (2 : ℝ) :=
    Complex.real_log_two_pos
  have hY_pos : 0 < 2 * Real.log (2 : ℝ) :=
    mul_pos zero_lt_two hL_pos
  have hD_pos : 0 < 2 * Real.log (2 : ℝ) - 1 :=
    Complex.realLogDyadicComparisonCriticalPoint_den_pos
  have hY_ne : 2 * Real.log (2 : ℝ) ≠ 0 :=
    ne_of_gt hY_pos
  have hD_ne : 2 * Real.log (2 : ℝ) - 1 ≠ 0 :=
    ne_of_gt hD_pos
  have htwo_ne : (2 : ℝ) ≠ 0 :=
    two_ne_zero
  have hlog_y_div :
      Real.log ((2 * Real.log (2 : ℝ)) / (2 * Real.log (2 : ℝ) - 1)) =
        Real.log (2 * Real.log (2 : ℝ)) -
          Real.log (2 * Real.log (2 : ℝ) - 1) :=
    Real.log_div hY_ne hD_ne
  have hlog_two_div :
      Real.log (2 / (2 * Real.log (2 : ℝ) - 1)) =
        Real.log (2 : ℝ) - Real.log (2 * Real.log (2 : ℝ) - 1) :=
    Real.log_div htwo_ne hD_ne
  calc
    (2 *
        Real.log
          ((2 * Real.log (2 : ℝ)) / (2 * Real.log (2 : ℝ) - 1))) *
          Real.log (2 : ℝ) -
        Real.log (2 / (2 * Real.log (2 : ℝ) - 1)) =
        (2 *
          (Real.log (2 * Real.log (2 : ℝ)) -
            Real.log (2 * Real.log (2 : ℝ) - 1))) *
            Real.log (2 : ℝ) -
          (Real.log (2 : ℝ) - Real.log (2 * Real.log (2 : ℝ) - 1)) := by
      exact congrArg₂ Sub.sub
        (congrArg (fun z : ℝ => (2 * z) * Real.log (2 : ℝ)) hlog_y_div)
        hlog_two_div
    _ =
      (2 * Real.log (2 : ℝ)) * Real.log (2 * Real.log (2 : ℝ)) -
        ((2 * Real.log (2 : ℝ)) - 1) *
          Real.log ((2 * Real.log (2 : ℝ)) - 1) -
        Real.log (2 : ℝ) := by
      ring

/-- Numerical inequality for the dyadic-log defect at its critical point,
written only in terms of `log 2`. -/
theorem Complex.realLogDyadicComparisonCriticalExpression_nonneg :
    0 ≤
      (2 *
        Real.log
          ((2 * Real.log (2 : ℝ)) / (2 * Real.log (2 : ℝ) - 1))) *
          Real.log (2 : ℝ) -
        Real.log (2 / (2 * Real.log (2 : ℝ) - 1)) := by
  have hY_one : 1 < 2 * Real.log (2 : ℝ) := by
    exact sub_pos.mp Complex.realLogDyadicComparisonCriticalPoint_den_pos
  have hY_two : 2 * Real.log (2 : ℝ) ≤ 2 := by
    have hlog : Real.log (2 : ℝ) ≤ 1 :=
      Complex.real_log_two_le_one
    have htwice : 2 * Real.log (2 : ℝ) ≤ (2 : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left hlog zero_le_two
    exact Eq.subst (motive := fun rhs : ℝ => 2 * Real.log (2 : ℝ) ≤ rhs) (mul_one 2) htwice
  have hentropy :
      Real.log (2 : ℝ) ≤
        (2 * Real.log (2 : ℝ)) * Real.log (2 * Real.log (2 : ℝ)) -
          ((2 * Real.log (2 : ℝ)) - 1) *
            Real.log ((2 * Real.log (2 : ℝ)) - 1) :=
    Complex.real_log_two_le_entropyExpression_on_two_log_two le_rfl hY_two
  have hnormalized_nonneg :
      0 ≤
        (2 * Real.log (2 : ℝ)) * Real.log (2 * Real.log (2 : ℝ)) -
          ((2 * Real.log (2 : ℝ)) - 1) *
            Real.log ((2 * Real.log (2 : ℝ)) - 1) -
          Real.log (2 : ℝ) :=
    sub_nonneg.mpr hentropy
  exact Eq.subst
    (motive := fun target : ℝ => 0 ≤ target)
    Complex.realLogDyadicComparisonCriticalExpression_eq_entropy.symm
    hnormalized_nonneg

/-- The defect value at the critical point is the explicit numeric critical
expression. -/
theorem Complex.realLogDyadicComparisonDefect_critical_eq_expression :
    Complex.realLogDyadicComparisonDefect
        Complex.realLogDyadicComparisonCriticalPoint =
      (2 *
        Real.log
          ((2 * Real.log (2 : ℝ)) / (2 * Real.log (2 : ℝ) - 1))) *
          Real.log (2 : ℝ) -
        Real.log (2 / (2 * Real.log (2 : ℝ) - 1)) := by
  have hadd_two :
      Complex.realLogDyadicComparisonCriticalPoint + 2 =
        (2 * Real.log (2 : ℝ)) / (2 * Real.log (2 : ℝ) - 1) :=
    Complex.realLogDyadicComparisonCriticalPoint_add_two_eq
  have hadd_one :
      Complex.realLogDyadicComparisonCriticalPoint + 1 =
        1 / (2 * Real.log (2 : ℝ) - 1) :=
    Complex.realLogDyadicComparisonCriticalPoint_add_one_eq
  have hmul :
      2 * (Complex.realLogDyadicComparisonCriticalPoint + 1) =
        2 / (2 * Real.log (2 : ℝ) - 1) := by
    calc
      2 * (Complex.realLogDyadicComparisonCriticalPoint + 1) =
          2 * (1 / (2 * Real.log (2 : ℝ) - 1)) := by
        exact congrArg (fun z : ℝ => 2 * z) hadd_one
      _ = 2 / (2 * Real.log (2 : ℝ) - 1) := by
        exact (mul_one_div 2 (2 * Real.log (2 : ℝ) - 1)).symm
  calc
    Complex.realLogDyadicComparisonDefect
        Complex.realLogDyadicComparisonCriticalPoint =
        (2 * Real.log (Complex.realLogDyadicComparisonCriticalPoint + 2)) *
          Real.log (2 : ℝ) -
          Real.log (2 * (Complex.realLogDyadicComparisonCriticalPoint + 1)) := by
      rfl
    _ =
        (2 *
          Real.log
            ((2 * Real.log (2 : ℝ)) / (2 * Real.log (2 : ℝ) - 1))) *
            Real.log (2 : ℝ) -
          Real.log (2 * (Complex.realLogDyadicComparisonCriticalPoint + 1)) := by
      exact congrArg
        (fun z : ℝ => (2 * Real.log z) * Real.log (2 : ℝ) -
          Real.log (2 * (Complex.realLogDyadicComparisonCriticalPoint + 1)))
        hadd_two
    _ =
        (2 *
          Real.log
            ((2 * Real.log (2 : ℝ)) / (2 * Real.log (2 : ℝ) - 1))) *
            Real.log (2 : ℝ) -
          Real.log (2 / (2 * Real.log (2 : ℝ) - 1)) := by
      exact congrArg
        (fun z : ℝ =>
          (2 *
            Real.log
              ((2 * Real.log (2 : ℝ)) / (2 * Real.log (2 : ℝ) - 1))) *
              Real.log (2 : ℝ) -
            Real.log z)
        hmul

/-- The critical value of the dyadic-log comparison defect is nonnegative. -/
theorem Complex.realLogDyadicComparisonDefect_critical_nonneg :
    0 ≤
      Complex.realLogDyadicComparisonDefect
        Complex.realLogDyadicComparisonCriticalPoint := by
  exact Eq.subst
    (motive := fun target : ℝ => 0 ≤ target)
    Complex.realLogDyadicComparisonDefect_critical_eq_expression.symm
    Complex.realLogDyadicComparisonCriticalExpression_nonneg

/-- One-variable calculus root for the sharp dyadic-log comparison.

The derivative is
`2 log 2 / (x + 2) - 1 / (x + 1)`, so the unique critical point on
`[0,∞)` gives the global minimum; evaluating there is positive. -/
theorem Complex.realLogDyadicComparisonDefect_nonneg
    {x : ℝ}
    (hx : 0 ≤ x) :
    0 ≤ Complex.realLogDyadicComparisonDefect x := by
  by_cases hx_left : x ≤ Complex.realLogDyadicComparisonCriticalPoint
  · have hanti :
        Complex.realLogDyadicComparisonDefect
            Complex.realLogDyadicComparisonCriticalPoint ≤
          Complex.realLogDyadicComparisonDefect x :=
      Complex.realLogDyadicComparisonDefect_antitoneOn_left
        ⟨hx, hx_left⟩
        ⟨Complex.realLogDyadicComparisonCriticalPoint_nonneg, le_rfl⟩
        hx_left
    exact le_trans Complex.realLogDyadicComparisonDefect_critical_nonneg hanti
  · have hx_right :
        Complex.realLogDyadicComparisonCriticalPoint ≤ x :=
      (lt_of_not_ge hx_left).le
    have hmono :
        Complex.realLogDyadicComparisonDefect
            Complex.realLogDyadicComparisonCriticalPoint ≤
          Complex.realLogDyadicComparisonDefect x :=
      Complex.realLogDyadicComparisonDefect_monotoneOn_right
        (show Complex.realLogDyadicComparisonCriticalPoint ∈
            Set.Ici Complex.realLogDyadicComparisonCriticalPoint from le_rfl)
        hx_right
        hx_right
    exact le_trans Complex.realLogDyadicComparisonDefect_critical_nonneg hmono

/-- The exact real inequality behind the dyadic-log comparison.

Equivalently, `log (2 * (x + 1)) / log 2 ≤ 2 log (x + 2)` for `x ≥ 0`.
This is the monotonic one-variable estimate needed to keep the downstream
constant `2`. -/
theorem Complex.real_log_two_mul_one_add_le_two_log_shift_mul_log_two
    {x : ℝ}
    (hx : 0 ≤ x) :
    Real.log (2 * (x + 1)) ≤
      (2 * Real.log (x + 2)) * Real.log (2 : ℝ) := by
  have hdefect :
      0 ≤
        (2 * Real.log (x + 2)) * Real.log (2 : ℝ) -
          Real.log (2 * (x + 1)) := by
    exact Complex.realLogDyadicComparisonDefect_nonneg hx
  exact sub_nonneg.mp hdefect

/-- Natural-number specialization of the real logarithmic comparison behind
the dyadic-log estimate. -/
theorem Complex.real_log_two_mul_nat_succ_le_two_log_shift_mul_log_two
    (N : ℕ) :
    Real.log ((((N + 1) * 2 : ℕ) : ℝ)) ≤
      (2 * Real.log (2 + N)) * Real.log (2 : ℝ) := by
  have hreal :
      Real.log (2 * (((N : ℝ) + 1))) ≤
        (2 * Real.log ((N : ℝ) + 2)) * Real.log (2 : ℝ) :=
    Complex.real_log_two_mul_one_add_le_two_log_shift_mul_log_two
      (Nat.cast_nonneg N)
  have harg :
      ((((N + 1) * 2 : ℕ) : ℝ)) = 2 * (((N : ℝ) + 1)) := by
    norm_num [Nat.cast_add, Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc]
  have hshift :
      ((N : ℝ) + 2) = 2 + N := by
    ring
  exact Eq.subst
    (motive := fun arg : ℝ =>
      Real.log arg ≤ (2 * Real.log (2 + N)) * Real.log (2 : ℝ))
    harg.symm
    (Eq.subst
      (motive := fun shift : ℝ =>
        Real.log (2 * ((N : ℝ) + 1)) ≤
          (2 * Real.log shift) * Real.log (2 : ℝ))
      hshift
      hreal)

/-- Real-logarithm comparison for the doubled shifted natural cutoff. -/
theorem Complex.real_logb_two_mul_nat_succ_le_two_log_shift
    (N : ℕ) :
    Real.logb (2 : ℝ) (((N + 1) * 2 : ℕ) : ℝ) ≤
      2 * Real.log (2 + N) := by
  have hlog2_pos : 0 < Real.log (2 : ℝ) :=
    Complex.real_log_two_pos
  have hraw :
      Real.log ((((N + 1) * 2 : ℕ) : ℝ)) ≤
        (2 * Real.log (2 + N)) * Real.log (2 : ℝ) :=
    Complex.real_log_two_mul_nat_succ_le_two_log_shift_mul_log_two N
  have hdiv :
      Real.log ((((N + 1) * 2 : ℕ) : ℝ)) / Real.log (2 : ℝ) ≤
        2 * Real.log (2 + N) := by
    exact (div_le_iff₀ hlog2_pos).mpr hraw
  have hlogb :
      Real.logb (2 : ℝ) (((N + 1) * 2 : ℕ) : ℝ) =
        Real.log ((((N + 1) * 2 : ℕ) : ℝ)) / Real.log (2 : ℝ) := by
    rfl
  exact Eq.subst
    (motive := fun lhs : ℝ => lhs ≤ 2 * Real.log (2 + N))
    hlogb.symm
    hdiv


/-- Dyadic integer logarithm is dominated by twice the natural logarithm on the
shifted natural cutoff. -/
theorem Complex.nat_log2_add_one_le_two_log
    (N : ℕ) :
    (Nat.log2 (N + 1) : ℝ) + 1 ≤ 2 * Real.log (2 + N) := by
  have hnat_eq :
      Nat.log2 (N + 1) + 1 = Nat.log 2 ((N + 1) * 2) :=
    Complex.nat_log2_add_one_eq_nat_log_two_mul_succ N
  have hcast_eq :
      ((Nat.log2 (N + 1) : ℝ) + 1) =
        (Nat.log 2 ((N + 1) * 2) : ℝ) := by
    exact_mod_cast hnat_eq
  have hbridge :
      (Nat.log 2 ((N + 1) * 2) : ℝ) ≤
        Real.logb (2 : ℝ) (((N + 1) * 2 : ℕ) : ℝ) :=
    Real.natLog_le_logb ((N + 1) * 2) 2
  have hreal :
      Real.logb (2 : ℝ) (((N + 1) * 2 : ℕ) : ℝ) ≤
        2 * Real.log (2 + N) :=
    Complex.real_logb_two_mul_nat_succ_le_two_log_shift N
  exact Eq.subst
    (motive := fun lhs : ℝ => lhs ≤ 2 * Real.log (2 + N))
    hcast_eq.symm
    (le_trans hbridge hreal)

/-- The transition square-root factor is at least `2` at nonzero boundary
frequency. -/
theorem Complex.two_le_two_mul_sqrt_one_add_norm
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    2 ≤ 2 * Real.sqrt (1 + ‖t‖) := by
  have hone_le : (1 : ℝ) ≤ Real.sqrt (1 + ‖t‖) := by
    have hone_arg : (1 : ℝ) ≤ 1 + ‖t‖ :=
      le_add_of_nonneg_right (norm_nonneg t)
    exact (Real.one_le_sqrt).mpr hone_arg
  exact
    Eq.subst
      (motive := fun lhs : ℝ => lhs ≤ 2 * Real.sqrt (1 + ‖t‖))
      (mul_one 2).symm
      (mul_le_mul_of_nonneg_left hone_le zero_le_two)

/-- The dyadic counting term is absorbed by the standard
`sqrt(1 + |t|) log(2+N)` transition factor. -/
theorem Complex.logarithmicPhase_log2_add_one_le_sqrt_transition
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (N : ℕ) :
    (Nat.log2 (N + 1) : ℝ) + 1 ≤
      2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + N) := by
  have hlog2 :
      (Nat.log2 (N + 1) : ℝ) + 1 ≤ 2 * Real.log (2 + N) :=
    Complex.nat_log2_add_one_le_two_log N
  have htarget :
      2 * Real.log (2 + N) ≤
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + N) := by
    have hlog_nonneg : 0 ≤ Real.log (2 + N) :=
      le_trans (show (0 : ℝ) ≤ 1 / 2 by norm_num)
        (Complex.logarithmicPhase_standardLog_half_le N)
    have hsqrt_factor : 2 ≤ 2 * Real.sqrt (1 + ‖t‖) :=
      Complex.two_le_two_mul_sqrt_one_add_norm t ht
    exact mul_le_mul_of_nonneg_right hsqrt_factor hlog_nonneg
  exact le_trans hlog2 htarget

/-- The quotient term in the dyadic-cover expression is absorbed by the
standard logarithmic factor. -/
theorem Complex.logarithmicPhase_quotient_term_le_standard
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (N : ℕ) :
    8 * (((N + 1 : ℕ) : ℝ) / ‖t‖) ≤
      16 * (((N + 1 : ℕ) : ℝ) / ‖t‖) * Real.log (2 + N) := by
  have hlog_half : (1 / 2 : ℝ) ≤ Real.log (2 + N) :=
    Complex.logarithmicPhase_standardLog_half_le N
  have hquot_nonneg : 0 ≤ (((N + 1 : ℕ) : ℝ) / ‖t‖) := by
    have ht_pos : 0 < ‖t‖ :=
      lt_of_lt_of_le zero_lt_one ht
    exact div_nonneg (Nat.cast_nonneg (N + 1)) ht_pos.le
  have hscaled :
      16 * (((N + 1 : ℕ) : ℝ) / ‖t‖) * (1 / 2 : ℝ) ≤
        16 * (((N + 1 : ℕ) : ℝ) / ‖t‖) * Real.log (2 + N) := by
    have hfactor_nonneg : 0 ≤ 16 * (((N + 1 : ℕ) : ℝ) / ‖t‖) :=
      mul_nonneg (Nat.cast_nonneg 16) hquot_nonneg
    exact mul_le_mul_of_nonneg_left hlog_half hfactor_nonneg
  have hleft :
      8 * (((N + 1 : ℕ) : ℝ) / ‖t‖) =
        16 * (((N + 1 : ℕ) : ℝ) / ‖t‖) * (1 / 2 : ℝ) := by
    ring
  exact Eq.subst
    (motive := fun lhs : ℝ =>
      lhs ≤ 16 * (((N + 1 : ℕ) : ℝ) / ‖t‖) * Real.log (2 + N))
    hleft.symm
    hscaled

/-- The dyadic counting term in the cover expression is absorbed by the
standard transition factor. -/
theorem Complex.logarithmicPhase_counting_term_le_standard
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (N : ℕ) :
    8 * ((Nat.log2 (N + 1) : ℝ) + 1) ≤
      16 * Real.sqrt (1 + ‖t‖) * Real.log (2 + N) := by
  have htransition :
      (Nat.log2 (N + 1) : ℝ) + 1 ≤
        2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + N) :=
    Complex.logarithmicPhase_log2_add_one_le_sqrt_transition t ht N
  have hleft_nonneg : (0 : ℝ) ≤ 8 :=
    Nat.cast_nonneg 8
  have hscaled :
      8 * ((Nat.log2 (N + 1) : ℝ) + 1) ≤
        8 * (2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + N)) :=
    mul_le_mul_of_nonneg_left htransition hleft_nonneg
  have hright :
      8 * (2 * Real.sqrt (1 + ‖t‖) * Real.log (2 + N)) =
        16 * Real.sqrt (1 + ‖t‖) * Real.log (2 + N) := by
    ring
  exact Eq.subst
    (motive := fun rhs : ℝ =>
      8 * ((Nat.log2 (N + 1) : ℝ) + 1) ≤ rhs)
    hright
    hscaled

/-- Elementary comparison from the dyadic block-cover expression to the
standard logarithmic first-derivative bound. -/
theorem Complex.logarithmicPhase_dyadic_cover_expression_le_standard
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (N : ℕ) :
    8 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1) ≤
      16 *
        (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
          Real.log (2 + N) := by
  have hquot :
      8 * (((N + 1 : ℕ) : ℝ) / ‖t‖) ≤
        16 * (((N + 1 : ℕ) : ℝ) / ‖t‖) * Real.log (2 + N) :=
    Complex.logarithmicPhase_quotient_term_le_standard t ht N
  have hcount :
      8 * ((Nat.log2 (N + 1) : ℝ) + 1) ≤
        16 * Real.sqrt (1 + ‖t‖) * Real.log (2 + N) :=
    Complex.logarithmicPhase_counting_term_le_standard t ht N
  have hsum :
      8 * (((N + 1 : ℕ) : ℝ) / ‖t‖) +
          8 * ((Nat.log2 (N + 1) : ℝ) + 1) ≤
        16 * (((N + 1 : ℕ) : ℝ) / ‖t‖) * Real.log (2 + N) +
          16 * Real.sqrt (1 + ‖t‖) * Real.log (2 + N) :=
    add_le_add hquot hcount
  have hleft :
      8 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1) =
        8 * (((N + 1 : ℕ) : ℝ) / ‖t‖) +
          8 * ((Nat.log2 (N + 1) : ℝ) + 1) := by
    ring
  have hright :
      16 * (((N + 1 : ℕ) : ℝ) / ‖t‖) * Real.log (2 + N) +
          16 * Real.sqrt (1 + ‖t‖) * Real.log (2 + N) =
        16 *
          (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
            Real.log (2 + N) := by
    ring
  exact Eq.subst
    (motive := fun lhs : ℝ =>
      lhs ≤
        16 *
          (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
            Real.log (2 + N))
    hleft.symm
    (Eq.subst
      (motive := fun rhs : ℝ =>
        8 * (((N + 1 : ℕ) : ℝ) / ‖t‖) +
            8 * ((Nat.log2 (N + 1) : ℝ) + 1) ≤ rhs)
      hright
      hsum)

/-- Dyadic summation primitive that turns the one-block first-derivative
estimate into the global logarithmic-phase partial-sum estimate. -/
theorem Complex.logarithmicPhase_dyadic_decomposition_bound_of_block
    (hblock :
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ {a b : ℕ},
            1 ≤ a →
              a ≤ b →
                ‖∑ n ∈ Finset.Icc a b,
                  ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                  8 * (((b + 1 : ℕ) : ℝ) / ‖t‖ + 1)) :
    ∀ t : ℝ,
      1 ≤ ‖t‖ →
        ∀ N : ℕ,
          ‖∑ n ∈ Finset.Icc 1 N,
            ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
              16 *
                (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
                  Real.log (2 + N) := by
  intro t ht N
  have hcover :
      ‖∑ n ∈ Finset.Icc 1 N,
        ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
          8 *
            (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1) :=
    Complex.logarithmicPhase_dyadic_block_cover_bound hblock t ht N
  have hcomparison :
      8 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1) ≤
        16 *
          (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
            Real.log (2 + N) :=
    Complex.logarithmicPhase_dyadic_cover_expression_le_standard t ht N
  exact le_trans hcover hcomparison

/-- Dyadic decomposition form of the first-derivative estimate for the
logarithmic phase. -/
theorem Complex.logarithmicPhase_dyadic_firstDerivative_sum_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hfiniteDifference :
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ {a b : ℕ},
            1 ≤ a →
              a ≤ b →
                Complex.realPhase_integerIncrementMonotoneOn
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b ∧
                Complex.realPhase_integerIncrementSeparatedOn
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b
                  (‖t‖ / ((b + 1 : ℕ) : ℝ)))
    (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        16 *
          (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
            Real.log (2 + N) := by
  exact
    Complex.logarithmicPhase_dyadic_decomposition_bound_of_block
      (fun t ht {a} {b} ha hab =>
        let hfd := hfiniteDifference t ht ha hab
        Complex.logarithmicPhase_monotone_firstDerivative_block_bound
          t ht ha hab hfd.1 hfd.2)
      t ht N

/-- Classical first-derivative estimate for the concrete logarithmic phase
`x ↦ exp(-it log x)` after the required finite-difference arithmetic is
available.

This is the remaining van der Corput/first-derivative-test input after the
phase derivative and derivative norm have been computed from the definition. -/
theorem Complex.logarithmicPhase_firstDerivativeTest_partialSum_bound_of_finiteDifference
    (hfiniteDifference :
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ {a b : ℕ},
            1 ≤ a →
              a ≤ b →
                Complex.realPhase_integerIncrementMonotoneOn
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b ∧
                Complex.realPhase_integerIncrementSeparatedOn
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b
                  (‖t‖ / ((b + 1 : ℕ) : ℝ))) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            ‖∑ n ∈ Finset.Icc 1 N,
              ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                A *
                  (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
                    Real.log (2 + N) := by
  refine ⟨16, ?_, ?_⟩
  · exact Nat.cast_pos.mpr (by decide : (0 : ℕ) < 16)
  · intro t ht N
    exact
      Complex.logarithmicPhase_dyadic_firstDerivative_sum_bound
        t ht (hfiniteDifference t ht) N

/-- The first-derivative-test root after the concrete derivative and derivative
norm have been isolated. -/
theorem Complex.logarithmicPhase_firstDerivativeTest_partialSum_bound_of_derivative_control
    (hderiv :
      ∀ t : ℝ, ∀ {x : ℝ}, 0 < x →
        deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t) x =
          (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
            Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t x))
    (hderiv_norm :
      ∀ t : ℝ, ∀ {x : ℝ}, 0 < x →
        ‖deriv (Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t) x‖ =
          ‖t‖ / x)
    (hfiniteDifference :
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ {a b : ℕ},
            1 ≤ a →
              a ≤ b →
                Complex.realPhase_integerIncrementMonotoneOn
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b ∧
                Complex.realPhase_integerIncrementSeparatedOn
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b
                  (‖t‖ / ((b + 1 : ℕ) : ℝ))) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            ‖∑ n ∈ Finset.Icc 1 N,
              ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                A *
                  (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
                    Real.log (2 + N) := by
  exact
    Complex.logarithmicPhase_firstDerivativeTest_partialSum_bound_of_finiteDifference
      hfiniteDifference

/-- The standard first-derivative-test owner root for the concrete logarithmic
phase.  This is the analytic input behind the Euler-Maclaurin boundary
package; cf. Titchmarsh, *The Theory of the Riemann Zeta-function*, §3.5. -/
theorem Complex.logarithmicPhase_firstDerivativeTest_partialSum_bound
    (hfiniteDifference :
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ {a b : ℕ},
            1 ≤ a →
              a ≤ b →
                Complex.realPhase_integerIncrementMonotoneOn
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b ∧
                Complex.realPhase_integerIncrementSeparatedOn
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b
                  (‖t‖ / ((b + 1 : ℕ) : ℝ))) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            ‖∑ n ∈ Finset.Icc 1 N,
              ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                A *
                  (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
                    Real.log (2 + N) := by
  exact
    Complex.logarithmicPhase_firstDerivativeTest_partialSum_bound_of_derivative_control
      (fun t hx =>
        Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_deriv_eq t hx)
      (fun t hx =>
        Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction_deriv_norm_eq t hx)
      hfiniteDifference

/-- First-derivative estimate for the logarithmic phase sums on the boundary
line.

The previous scaffold stated an `O(log N)` bound for the unweighted sums
`∑ n^{-it}`.  The owner-level first-derivative estimate has the standard
oscillatory-sum size shown here; the reciprocal Abel weight is introduced in
`AbelTail`. -/
theorem Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum_bound :
    (∀ t : ℝ,
      1 ≤ ‖t‖ →
        ∀ {a b : ℕ},
          1 ≤ a →
            a ≤ b →
              Complex.realPhase_integerIncrementMonotoneOn
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b ∧
              Complex.realPhase_integerIncrementSeparatedOn
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b
                (‖t‖ / ((b + 1 : ℕ) : ℝ))) →
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            ‖∑ n ∈ Finset.Icc 1 N,
              ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                A *
                  (((N + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)) *
                    Real.log (2 + N) := by
  intro hfiniteDifference
  exact
    Complex.logarithmicPhase_firstDerivativeTest_partialSum_bound
      hfiniteDifference

end

end LFunctions
end Boundary
