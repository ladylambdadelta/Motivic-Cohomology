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

/-- Adjacent phase increment reduced to the fundamental interval `(-π, π]`.

This is the no-winding coordinate needed by the Abel-variation proof.  Raw
monotonicity of increments is not enough: the inverse denominator is periodic
and can wind around `2πℤ` many times. -/
def Complex.realPhase_reducedIntegerIncrement
    (φ : ℝ → ℝ)
    (n : ℕ) : ℝ :=
  toIocMod Real.two_pi_pos (-Real.pi)
    (Complex.realPhase_integerIncrement φ n)

/-- No-winding monotonicity of adjacent increments after reduction to
`(-π, π]`. -/
def Complex.realPhase_reducedIntegerIncrementMonotoneOn
    (φ : ℝ → ℝ)
    (a b : ℕ) : Prop :=
  MonotoneOn
    (fun n : ℕ => Complex.realPhase_reducedIntegerIncrement φ n)
    (Finset.Ico a b : Set ℕ) ∨
  AntitoneOn
    (fun n : ℕ => Complex.realPhase_reducedIntegerIncrement φ n)
    (Finset.Ico a b : Set ℕ)

/-- Endpoint control for a one-point exponential block. -/
theorem Complex.realPhase_singleton_integer_block_bound
    (φ : ℝ → ℝ)
    (a : ℕ)
    {λ : ℝ}
    (hλ_pos : 0 < λ) :
    ‖∑ n ∈ Finset.Icc a a,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        4 * (λ⁻¹ + 1) + 4 * Real.pi * λ⁻¹ := by
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
  have hone_le_four : (1 : ℝ) ≤ 4 * 1 := by
    norm_num
  have hone_le_endpoint : (1 : ℝ) ≤ 4 * (λ⁻¹ + 1) := by
    have hone_le_sum : (1 : ℝ) ≤ λ⁻¹ + 1 :=
      le_add_of_nonneg_left hλ_inv_nonneg
    exact le_trans hone_le_four
      (mul_le_mul_of_nonneg_left hone_le_sum (by norm_num : (0 : ℝ) ≤ 4))
  have hvariation_nonneg : 0 ≤ 4 * Real.pi * λ⁻¹ := by
    positivity
  have hone_le_target :
      (1 : ℝ) ≤ 4 * (λ⁻¹ + 1) + 4 * Real.pi * λ⁻¹ :=
    le_trans hone_le_endpoint
      (le_add_of_nonneg_right hvariation_nonneg)
  exact le_trans hblock
    (Eq.subst
      (motive := fun c : ℝ =>
        c ≤ 4 * (λ⁻¹ + 1) + 4 * Real.pi * λ⁻¹)
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
    (hvariation : ‖variation‖ ≤ 4 * Real.pi * λ⁻¹) :
    ‖S‖ ≤ 4 * (λ⁻¹ + 1) + 4 * Real.pi * λ⁻¹ := by
  have hnorm :
      ‖S‖ ≤ ‖boundary‖ + ‖variation‖ := by
    exact Eq.subst
      (motive := fun z : ℂ => ‖z‖ ≤ ‖boundary‖ + ‖variation‖)
      hS.symm
      (norm_add_le boundary variation)
  have hsum :
      ‖boundary‖ + ‖variation‖ ≤
        4 * (λ⁻¹ + 1) + 4 * Real.pi * λ⁻¹ :=
    add_le_add hboundary hvariation
  exact le_trans hnorm hsum

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
      ‖variation‖ ≤ 4 * Real.pi * λ⁻¹ := by
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
    have hpi_nonneg : 0 ≤ Real.pi :=
      le_of_lt Real.pi_pos
    have htarget_nonneg : 0 ≤ 4 * Real.pi * λ⁻¹ := by
      positivity
    exact Eq.subst
      (motive := fun r : ℝ => r ≤ 4 * Real.pi * λ⁻¹)
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
  revert a
  induction m with
  | zero =>
      intro a ham
      exact False.elim ((Nat.not_lt_zero a) ham)
  | succ m ih =>
      intro a ham
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ ham) with ham_strict | rfl
      · have hIco :
            Finset.Ico a (m + 1) = Finset.insert m (Finset.Ico a m) := by
          exact Nat.Ico_succ_right_eq_insert_Ico (Nat.le_of_lt ham_strict)
        have hIoo :
            Finset.Ioo a (m + 1) = Finset.insert m (Finset.Ioo a m) := by
          ext n
          constructor
          · intro hn
            rcases hn with ⟨hna, hnm1⟩
            by_cases hnm : n = m
            · subst hnm
              right
              exact ⟨by omega, by omega⟩
            · left
              exact ⟨hna, by omega⟩
          · intro hn
            rcases hn with rfl | hn
            · constructor
              · omega
              · omega
            · exact hn
        have hm_not_Ico : m ∉ Finset.Ico a m :=
          Finset.right_not_mem_Ico
        have hm_not_Ioo : m ∉ Finset.Ioo a m := by
          exact (Finset.mem_Ioo.not.mpr (by omega))
        have hind :
            (∑ n ∈ Finset.Ico a m, A n * (u n - u (n + 1))) =
              A a * u a - A (m - 1) * u m +
                ∑ n ∈ Finset.Ioo a m, (A n - A (n - 1)) * u n :=
          ih a ham_strict
        calc
          (∑ n ∈ Finset.Ico a (m + 1), A n * (u n - u (n + 1))) =
              ∑ n ∈ Finset.insert m (Finset.Ico a m),
                A n * (u n - u (n + 1)) := by
            exact congrArg
              (fun s : Finset ℕ =>
                ∑ n ∈ s, A n * (u n - u (n + 1)))
              hIco
          _ =
              A m * (u m - u (m + 1)) +
                ∑ n ∈ Finset.Ico a m, A n * (u n - u (n + 1)) :=
            Finset.sum_insert hm_not_Ico
          _ =
              A m * (u m - u (m + 1)) +
                (A a * u a - A (m - 1) * u m +
                  ∑ n ∈ Finset.Ioo a m, (A n - A (n - 1)) * u n) := by
            exact congrArg
              (fun z : ℂ => A m * (u m - u (m + 1)) + z)
              hind
          _ =
              A a * u a - A m * u (m + 1) +
                ∑ n ∈ Finset.insert m (Finset.Ioo a m),
                  (A n - A (n - 1)) * u n := by
            calc
              A m * (u m - u (m + 1)) +
                  (A a * u a - A (m - 1) * u m +
                    ∑ n ∈ Finset.Ioo a m, (A n - A (n - 1)) * u n)
                  =
                  A a * u a - A m * u (m + 1) +
                    (A m * u m - A (m - 1) * u m) +
                      ∑ n ∈ Finset.Ioo a m, (A n - A (n - 1)) * u n := by
                ring
              _ =
                  A a * u a - A m * u (m + 1) +
                    ∑ n ∈ Finset.insert m (Finset.Ioo a m),
                      (A n - A (n - 1)) * u n := by
                exact Eq.symm (Finset.sum_insert hm_not_Ioo)
          _ =
              A a * u a - A ((m + 1) - 1) * u (m + 1) +
                ∑ n ∈ Finset.Ioo a (m + 1), (A n - A (n - 1)) * u n := by
            calc
              A a * u a - A m * u (m + 1) +
                ∑ n ∈ Finset.insert m (Finset.Ioo a m),
                  (A n - A (n - 1)) * u n
                  =
                  A a * u a - A ((m + 1) - 1) * u (m + 1) +
                    ∑ n ∈ Finset.Ioo a (m + 1), (A n - A (n - 1)) * u n := by
                exact
                  congrArg
                    (fun s : Finset ℕ =>
                      A a * u a - A m * u (m + 1) +
                        ∑ n ∈ s, (A n - A (n - 1)) * u n)
                    hIoo
      · have hIco : Finset.Ico m (m + 1) = ({m} : Finset ℕ) :=
          Nat.Ico_succ_singleton
        have hIoo : Finset.Ioo m (m + 1) = (∅ : Finset ℕ) := by
          exact Finset.Ioo_eq_empty (by omega)
        calc
          (∑ n ∈ Finset.Ico m (m + 1), A n * (u n - u (n + 1))) =
              A m * (u m - u (m + 1)) := by
            calc
              ∑ n ∈ Finset.Ico m (m + 1), A n * (u n - u (n + 1))
                  = ∑ n ∈ ({m} : Finset ℕ), A n * (u n - u (n + 1)) := by
                exact congrArg (fun s : Finset ℕ => ∑ n ∈ s, A n * (u n - u (n + 1))) hIco
              _ = A m * (u m - u (m + 1)) := by
                exact Finset.sum_singleton m (fun n : ℕ => A n * (u n - u (n + 1)))
          _ =
              A m * u m - A ((m + 1) - 1) * u (m + 1) +
                ∑ n ∈ Finset.Ioo m (m + 1), (A n - A (n - 1)) * u n := by
            calc
              A m * (u m - u (m + 1))
                  = A m * u m - A ((m + 1) - 1) * u (m + 1) := by
                    ring
              _ = A m * u m - A ((m + 1) - 1) * u (m + 1) +
                  ∑ n ∈ Finset.Ioo m (m + 1), (A n - A (n - 1)) * u n := by
                exact Eq.symm
                  (by
                    exact Finset.sum_empty
                      (fun n : ℕ => (A n - A (n - 1)) * u n))

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
    have hone_le_four : (1 : ℝ) ≤ 4 :=
      one_le_ofNat
    have hleft_reorder :
        2 * λ⁻¹ + (1 + 2 * λ⁻¹) =
          (2 * λ⁻¹ + 2 * λ⁻¹) + 1 := by
      calc
        2 * λ⁻¹ + (1 + 2 * λ⁻¹) =
            2 * λ⁻¹ + (2 * λ⁻¹ + 1) :=
          congrArg (fun r : ℝ => 2 * λ⁻¹ + r)
            (add_comm 1 (2 * λ⁻¹))
        _ = (2 * λ⁻¹ + 2 * λ⁻¹) + 1 :=
          (add_assoc (2 * λ⁻¹) (2 * λ⁻¹) 1).symm
    have hleft_fold :
        (2 * λ⁻¹ + 2 * λ⁻¹) + 1 =
          4 * λ⁻¹ + 1 :=
      congrArg (fun r : ℝ => r + 1)
        (Real.two_mul_add_two_mul_eq_four_mul λ⁻¹)
    have hleft_eq :
        2 * λ⁻¹ + (1 + 2 * λ⁻¹) =
          4 * λ⁻¹ + 1 :=
      Eq.trans hleft_reorder hleft_fold
    have htarget_expand :
        4 * (λ⁻¹ + 1) = 4 * λ⁻¹ + 4 := by
      calc
        4 * (λ⁻¹ + 1) = 4 * λ⁻¹ + 4 * 1 :=
          mul_add (4 : ℝ) λ⁻¹ 1
        _ = 4 * λ⁻¹ + 4 :=
          congrArg (fun r : ℝ => 4 * λ⁻¹ + r)
            (mul_one (4 : ℝ))
    have hcore :
        4 * λ⁻¹ + 1 ≤ 4 * λ⁻¹ + 4 :=
      add_le_add_left hone_le_four (4 * λ⁻¹)
    exact Eq.subst
      (motive := fun left : ℝ =>
        left ≤ 4 * (λ⁻¹ + 1))
      hleft_eq.symm
      (Eq.subst
        (motive := fun right : ℝ =>
          4 * λ⁻¹ + 1 ≤ right)
        htarget_expand.symm
        hcore)
  exact le_trans hboundary htarget

/-- Separation from `2πℤ` descends to separation of the reduced increment from
zero in the fundamental interval. -/
theorem Complex.realPhase_reducedIntegerIncrement_norm_lower_bound
    (φ : ℝ → ℝ)
    {a b n : ℕ}
    {λ : ℝ}
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b λ)
    (hn : n ∈ Finset.Ico a b) :
    λ ≤ ‖Complex.realPhase_reducedIntegerIncrement φ n‖ := by
  rcases
    Complex.realPhase_twoPi_toIocMod_integerDistance
      (Complex.realPhase_integerIncrement φ n) with
    ⟨k, hk⟩
  have hsep_k :
      λ ≤
        ‖Complex.realPhase_integerIncrement φ n -
          (2 * Real.pi * (k : ℝ))‖ :=
    hsep n hn k
  exact Eq.subst
    (motive := fun x : ℝ => λ ≤ ‖x‖)
    hk
    hsep_k

/-- The inverse geometric denominator is unchanged by reducing the increment
to the fundamental interval. -/
theorem Complex.realPhase_inverseGeometricDenominator_eq_reduced
    (φ : ℝ → ℝ)
    (n : ℕ) :
    Complex.realPhase_inverseGeometricDenominator φ n =
      (1 -
        Complex.exp
          (Complex.I *
            (Complex.realPhase_reducedIntegerIncrement φ n : ℂ)))⁻¹ := by
  unfold Complex.realPhase_inverseGeometricDenominator
    Complex.realPhase_reducedIntegerIncrement
  let θ : ℝ := Complex.realPhase_integerIncrement φ n
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
        Complex.exp ((θ : ℂ) * Complex.I) :=
    congrArg Complex.exp (mul_comm Complex.I (θ : ℂ))
  have hright_comm :
      Complex.exp
          (Complex.I * (toIocMod Real.two_pi_pos (-Real.pi) θ : ℂ)) =
        Complex.exp
          ((toIocMod Real.two_pi_pos (-Real.pi) θ : ℂ) * Complex.I) :=
    congrArg Complex.exp
      (mul_comm Complex.I (toIocMod Real.two_pi_pos (-Real.pi) θ : ℂ))
  have hexp :
      Complex.exp (Complex.I * (θ : ℂ)) =
        Complex.exp
          (Complex.I * (toIocMod Real.two_pi_pos (-Real.pi) θ : ℂ)) :=
    Eq.trans hleft_comm (Eq.trans hperiod hright_comm.symm)
  exact congrArg Inv.inv
    (congrArg (fun z : ℂ => 1 - z) hexp)

/-- The inverse chord map on the reduced logarithmic-phase arc. -/
def Complex.reducedArc_inverseGeometricDenominator
    (ψ : ℝ) : ℂ :=
  (1 - Complex.exp (Complex.I * (ψ : ℂ)))⁻¹

/-- Definitional expansion of the reduced-arc inverse chord map. -/
theorem Complex.reducedArc_inverseGeometricDenominator_eq
    (ψ : ℝ) :
    Complex.reducedArc_inverseGeometricDenominator ψ =
      (1 - Complex.exp (Complex.I * (ψ : ℂ)))⁻¹ := by
  rfl

/-- The real coordinate of the inverse chord map on a reduced arc. -/
def Complex.reducedArc_inverseGeometricDenominator_imCoord
    (ψ : ℝ) : ℝ :=
  (Complex.reducedArc_inverseGeometricDenominator ψ).im

/-- The real coordinate of a point written as `1 / 2 + I * y`. -/
theorem Complex.half_add_I_mul_ofReal_re
    (y : ℝ) :
    ((((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ)).re) = 1 / 2 := by
  have himaginary_re :
      (Complex.I * (y : ℂ)).re = 0 := by
    have hmul :
        (Complex.I * (y : ℂ)).re = (-(y : ℂ).im) :=
      congrArg Complex.re (Complex.I_mul (y : ℂ))
    exact Eq.trans hmul (neg_eq_zero.mpr (Complex.ofReal_im y))
  calc
    ((((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ)).re) =
        (((1 / 2 : ℝ) : ℂ).re) + (Complex.I * (y : ℂ)).re :=
      Complex.add_re ((1 / 2 : ℝ) : ℂ) (Complex.I * (y : ℂ))
    _ = (1 / 2 : ℝ) + (Complex.I * (y : ℂ)).re := by
      exact congrArg
        (fun x : ℝ => x + (Complex.I * (y : ℂ)).re)
        (Complex.ofReal_re (1 / 2 : ℝ))
    _ = (1 / 2 : ℝ) + 0 := by
      exact congrArg (fun x : ℝ => (1 / 2 : ℝ) + x) himaginary_re
    _ = 1 / 2 :=
      add_zero (1 / 2 : ℝ)

/-- The imaginary coordinate of a point written as `1 / 2 + I * y`. -/
theorem Complex.half_add_I_mul_ofReal_im
    (y : ℝ) :
    ((((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ)).im) = y := by
  have hreal_im :
      (((1 / 2 : ℝ) : ℂ).im) = 0 :=
    Complex.ofReal_im (1 / 2 : ℝ)
  have himaginary_im :
      (Complex.I * (y : ℂ)).im = y := by
    have hmul :
        (Complex.I * (y : ℂ)).im = (y : ℂ).re :=
      congrArg Complex.im (Complex.I_mul (y : ℂ))
    exact Eq.trans hmul (Complex.ofReal_re y)
  calc
    ((((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ)).im) =
        (((1 / 2 : ℝ) : ℂ).im) + (Complex.I * (y : ℂ)).im :=
      Complex.add_im ((1 / 2 : ℝ) : ℂ) (Complex.I * (y : ℂ))
    _ = 0 + (Complex.I * (y : ℂ)).im := by
      exact congrArg
        (fun x : ℝ => x + (Complex.I * (y : ℂ)).im)
        hreal_im
    _ = 0 + y := by
      exact congrArg (fun x : ℝ => 0 + x) himaginary_im
    _ = y :=
      zero_add y

/-- Real-coordinate subtraction on the vertical line `1 / 2 + I * ℝ`. -/
theorem Complex.half_add_I_mul_ofReal_sub_re
    (x y : ℝ) :
    (((1 / 2 : ℂ) + Complex.I * (x : ℂ)) -
        ((1 / 2 : ℂ) + Complex.I * (y : ℂ))).re =
      (Complex.I * ((x - y : ℝ) : ℂ)).re := by
  have hleft_first :
      ((1 / 2 : ℂ) + Complex.I * (x : ℂ)).re = 1 / 2 := by
    calc
      ((1 / 2 : ℂ) + Complex.I * (x : ℂ)).re =
          ((1 / 2 : ℚ) : ℂ).re + (Complex.I * (x : ℂ)).re :=
        Complex.add_re (1 / 2 : ℂ) (Complex.I * (x : ℂ))
      _ = (1 / 2 : ℝ) + (Complex.I * (x : ℂ)).re := by
        exact congrArg
          (fun r : ℝ => r + (Complex.I * (x : ℂ)).re)
          (Complex.ratCast_re (1 / 2 : ℚ))
      _ = (1 / 2 : ℝ) + (-(x : ℂ).im) := by
        exact congrArg
          (fun r : ℝ => (1 / 2 : ℝ) + r)
          (Complex.I_mul_re (x : ℂ))
      _ = (1 / 2 : ℝ) + (-0) := by
        exact congrArg
          (fun r : ℝ => (1 / 2 : ℝ) + (-r))
          (Complex.ofReal_im x)
      _ = (1 / 2 : ℝ) + 0 := by
        exact congrArg
          (fun r : ℝ => (1 / 2 : ℝ) + r)
          (neg_zero : -(0 : ℝ) = 0)
      _ = 1 / 2 :=
        add_zero (1 / 2 : ℝ)
  have hleft_second :
      ((1 / 2 : ℂ) + Complex.I * (y : ℂ)).re = 1 / 2 := by
    calc
      ((1 / 2 : ℂ) + Complex.I * (y : ℂ)).re =
          ((1 / 2 : ℚ) : ℂ).re + (Complex.I * (y : ℂ)).re :=
        Complex.add_re (1 / 2 : ℂ) (Complex.I * (y : ℂ))
      _ = (1 / 2 : ℝ) + (Complex.I * (y : ℂ)).re := by
        exact congrArg
          (fun r : ℝ => r + (Complex.I * (y : ℂ)).re)
          (Complex.ratCast_re (1 / 2 : ℚ))
      _ = (1 / 2 : ℝ) + (-(y : ℂ).im) := by
        exact congrArg
          (fun r : ℝ => (1 / 2 : ℝ) + r)
          (Complex.I_mul_re (y : ℂ))
      _ = (1 / 2 : ℝ) + (-0) := by
        exact congrArg
          (fun r : ℝ => (1 / 2 : ℝ) + (-r))
          (Complex.ofReal_im y)
      _ = (1 / 2 : ℝ) + 0 := by
        exact congrArg
          (fun r : ℝ => (1 / 2 : ℝ) + r)
          (neg_zero : -(0 : ℝ) = 0)
      _ = 1 / 2 :=
        add_zero (1 / 2 : ℝ)
  have hright :
      (Complex.I * ((x - y : ℝ) : ℂ)).re = 0 := by
    calc
      (Complex.I * ((x - y : ℝ) : ℂ)).re =
          (-(((x - y : ℝ) : ℂ).im)) :=
        Complex.I_mul_re (((x - y : ℝ) : ℂ))
      _ = -0 := by
        exact congrArg Neg.neg (Complex.ofReal_im (x - y))
      _ = 0 :=
        neg_zero
  calc
    (((1 / 2 : ℂ) + Complex.I * (x : ℂ)) -
        ((1 / 2 : ℂ) + Complex.I * (y : ℂ))).re =
        ((1 / 2 : ℂ) + Complex.I * (x : ℂ)).re -
          ((1 / 2 : ℂ) + Complex.I * (y : ℂ)).re :=
      Complex.sub_re
        ((1 / 2 : ℂ) + Complex.I * (x : ℂ))
        ((1 / 2 : ℂ) + Complex.I * (y : ℂ))
    _ = (1 / 2 : ℝ) - (1 / 2 : ℝ) := by
      exact congrArg₂ Sub.sub hleft_first hleft_second
    _ = 0 := by
      exact sub_self (1 / 2 : ℝ)
    _ = (Complex.I * ((x - y : ℝ) : ℂ)).re :=
      hright.symm

/-- Imaginary-coordinate subtraction on the vertical line `1 / 2 + I * ℝ`. -/
theorem Complex.half_add_I_mul_ofReal_sub_im
    (x y : ℝ) :
    (((1 / 2 : ℂ) + Complex.I * (x : ℂ)) -
        ((1 / 2 : ℂ) + Complex.I * (y : ℂ))).im =
      (Complex.I * ((x - y : ℝ) : ℂ)).im := by
  have hleft_first :
      ((1 / 2 : ℂ) + Complex.I * (x : ℂ)).im = x := by
    calc
      ((1 / 2 : ℂ) + Complex.I * (x : ℂ)).im =
          ((1 / 2 : ℚ) : ℂ).im + (Complex.I * (x : ℂ)).im :=
        Complex.add_im (1 / 2 : ℂ) (Complex.I * (x : ℂ))
      _ = 0 + (Complex.I * (x : ℂ)).im := by
        exact congrArg
          (fun r : ℝ => r + (Complex.I * (x : ℂ)).im)
          (Complex.ratCast_im (1 / 2 : ℚ))
      _ = 0 + (x : ℂ).re := by
        exact congrArg
          (fun r : ℝ => 0 + r)
          (Complex.I_mul_im (x : ℂ))
      _ = 0 + x := by
        exact congrArg (fun r : ℝ => 0 + r) (Complex.ofReal_re x)
      _ = x :=
        zero_add x
  have hleft_second :
      ((1 / 2 : ℂ) + Complex.I * (y : ℂ)).im = y := by
    calc
      ((1 / 2 : ℂ) + Complex.I * (y : ℂ)).im =
          ((1 / 2 : ℚ) : ℂ).im + (Complex.I * (y : ℂ)).im :=
        Complex.add_im (1 / 2 : ℂ) (Complex.I * (y : ℂ))
      _ = 0 + (Complex.I * (y : ℂ)).im := by
        exact congrArg
          (fun r : ℝ => r + (Complex.I * (y : ℂ)).im)
          (Complex.ratCast_im (1 / 2 : ℚ))
      _ = 0 + (y : ℂ).re := by
        exact congrArg
          (fun r : ℝ => 0 + r)
          (Complex.I_mul_im (y : ℂ))
      _ = 0 + y := by
        exact congrArg (fun r : ℝ => 0 + r) (Complex.ofReal_re y)
      _ = y :=
        zero_add y
  have hright :
      (Complex.I * ((x - y : ℝ) : ℂ)).im = x - y := by
    calc
      (Complex.I * ((x - y : ℝ) : ℂ)).im =
          (((x - y : ℝ) : ℂ).re) :=
        Complex.I_mul_im (((x - y : ℝ) : ℂ))
      _ = x - y :=
        Complex.ofReal_re (x - y)
  calc
    (((1 / 2 : ℂ) + Complex.I * (x : ℂ)) -
        ((1 / 2 : ℂ) + Complex.I * (y : ℂ))).im =
        ((1 / 2 : ℂ) + Complex.I * (x : ℂ)).im -
          ((1 / 2 : ℂ) + Complex.I * (y : ℂ)).im :=
      Complex.sub_im
        ((1 / 2 : ℂ) + Complex.I * (x : ℂ))
        ((1 / 2 : ℂ) + Complex.I * (y : ℂ))
    _ = x - y := by
      exact congrArg₂ Sub.sub hleft_first hleft_second
    _ = (Complex.I * ((x - y : ℝ) : ℂ)).im :=
      hright.symm

/-- Subtracting two points on the vertical line `1 / 2 + I * ℝ`. -/
theorem Complex.half_add_I_mul_ofReal_sub
    (x y : ℝ) :
    ((1 / 2 : ℂ) + Complex.I * (x : ℂ)) -
        ((1 / 2 : ℂ) + Complex.I * (y : ℂ)) =
      Complex.I * ((x - y : ℝ) : ℂ) := by
  exact Complex.ext
    (Complex.half_add_I_mul_ofReal_sub_re x y)
    (Complex.half_add_I_mul_ofReal_sub_im x y)

/-- The reduced arc lies inside the lower endpoint range for the standard
`cos = 1` criterion. -/
theorem Real.reducedArc_gt_neg_two_pi
    {ψ : ℝ}
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi) :
    -(2 * Real.pi) < ψ := by
  have hneg_pi_lt : -Real.pi < ψ :=
    hψ_mem.1
  have hpi_pos : 0 < Real.pi :=
    Real.pi_pos
  have hpi_lt_two_pi : Real.pi < 2 * Real.pi := by
    exact lt_two_mul_self hpi_pos
  have hneg_two_pi_lt_neg_pi : -(2 * Real.pi) < -Real.pi :=
    neg_lt_neg hpi_lt_two_pi
  exact lt_trans hneg_two_pi_lt_neg_pi hneg_pi_lt

/-- The reduced arc lies inside the upper endpoint range for the standard
`cos = 1` criterion. -/
theorem Real.reducedArc_lt_two_pi
    {ψ : ℝ}
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi) :
    ψ < 2 * Real.pi := by
  have hψ_le_pi : ψ ≤ Real.pi :=
    hψ_mem.2
  have hpi_pos : 0 < Real.pi :=
    Real.pi_pos
  have hpi_lt_two_pi : Real.pi < 2 * Real.pi := by
    exact lt_two_mul_self hpi_pos
  exact lt_of_le_of_lt hψ_le_pi hpi_lt_two_pi

/-- On the punctured reduced arc, `1 - cos ψ` is nonzero. -/
theorem Real.one_sub_cos_ne_zero_of_mem_reducedArc
    {ψ : ℝ}
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_ne : ψ ≠ 0) :
    1 - Real.cos ψ ≠ 0 := by
  have hψ_gt_neg_two_pi : -(2 * Real.pi) < ψ :=
    Real.reducedArc_gt_neg_two_pi hψ_mem
  have hψ_lt_two_pi : ψ < 2 * Real.pi :=
    Real.reducedArc_lt_two_pi hψ_mem
  intro hzero
  have hcos : Real.cos ψ = 1 :=
    sub_eq_zero.mp hzero
  have hψ_zero : ψ = 0 :=
    (Real.cos_eq_one_iff_of_lt_of_lt hψ_gt_neg_two_pi hψ_lt_two_pi).mp hcos
  exact hψ_ne hψ_zero

/-- The denominator in the inverse-chord imaginary coordinate is nonzero on the
punctured reduced arc. -/
theorem Real.two_mul_one_sub_cos_ne_zero_of_mem_reducedArc
    {ψ : ℝ}
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_ne : ψ ≠ 0) :
    2 * (1 - Real.cos ψ) ≠ 0 := by
  have htwo_ne : (2 : ℝ) ≠ 0 :=
    OfNat.ofNat_ne_zero
  have hone_sub_cos_ne : 1 - Real.cos ψ ≠ 0 :=
    Real.one_sub_cos_ne_zero_of_mem_reducedArc hψ_mem hψ_ne
  exact mul_ne_zero htwo_ne hone_sub_cos_ne

/-- Real coordinate of the elementary chord denominator written in trigonometric
coordinates. -/
theorem Complex.one_sub_cos_add_sin_mul_I_re
    (c s : ℝ) :
    (1 - ((c : ℂ) + (s : ℂ) * Complex.I)).re = 1 - c := by
  have hmul_re :
      ((s : ℂ) * Complex.I).re = 0 := by
    calc
      ((s : ℂ) * Complex.I).re =
          (s : ℂ).re * Complex.I.re - (s : ℂ).im * Complex.I.im :=
        Complex.mul_re (s : ℂ) Complex.I
      _ = s * Complex.I.re - (s : ℂ).im * Complex.I.im := by
        exact congrArg
          (fun r : ℝ => r * Complex.I.re - (s : ℂ).im * Complex.I.im)
          (Complex.ofReal_re s)
      _ = s * 0 - (s : ℂ).im * Complex.I.im := by
        exact congrArg
          (fun r : ℝ => s * r - (s : ℂ).im * Complex.I.im)
          Complex.I_re
      _ = 0 - (s : ℂ).im * Complex.I.im := by
        exact congrArg
          (fun r : ℝ => r - (s : ℂ).im * Complex.I.im)
          (mul_zero s)
      _ = 0 - 0 * Complex.I.im := by
        exact congrArg
          (fun r : ℝ => 0 - r * Complex.I.im)
          (Complex.ofReal_im s)
      _ = 0 - 0 := by
        exact congrArg (fun r : ℝ => 0 - r) (zero_mul Complex.I.im)
      _ = 0 :=
        sub_self 0
  have hadd_re :
      (((c : ℂ) + (s : ℂ) * Complex.I).re) = c := by
    calc
      (((c : ℂ) + (s : ℂ) * Complex.I).re) =
          (c : ℂ).re + ((s : ℂ) * Complex.I).re :=
        Complex.add_re (c : ℂ) ((s : ℂ) * Complex.I)
      _ = c + ((s : ℂ) * Complex.I).re := by
        exact congrArg
          (fun r : ℝ => r + ((s : ℂ) * Complex.I).re)
          (Complex.ofReal_re c)
      _ = c + 0 := by
        exact congrArg (fun r : ℝ => c + r) hmul_re
      _ = c :=
        add_zero c
  calc
    (1 - ((c : ℂ) + (s : ℂ) * Complex.I)).re =
        (1 : ℂ).re - ((c : ℂ) + (s : ℂ) * Complex.I).re :=
      Complex.sub_re (1 : ℂ) ((c : ℂ) + (s : ℂ) * Complex.I)
    _ = 1 - ((c : ℂ) + (s : ℂ) * Complex.I).re := by
      exact congrArg
        (fun r : ℝ => r - ((c : ℂ) + (s : ℂ) * Complex.I).re)
        Complex.one_re
    _ = 1 - c := by
      exact congrArg (fun r : ℝ => 1 - r) hadd_re

/-- Imaginary coordinate of the elementary chord denominator written in
trigonometric coordinates. -/
theorem Complex.one_sub_cos_add_sin_mul_I_im
    (c s : ℝ) :
    (1 - ((c : ℂ) + (s : ℂ) * Complex.I)).im = -s := by
  have hmul_im :
      ((s : ℂ) * Complex.I).im = s := by
    calc
      ((s : ℂ) * Complex.I).im =
          (s : ℂ).re * Complex.I.im + (s : ℂ).im * Complex.I.re :=
        Complex.mul_im (s : ℂ) Complex.I
      _ = s * Complex.I.im + (s : ℂ).im * Complex.I.re := by
        exact congrArg
          (fun r : ℝ => r * Complex.I.im + (s : ℂ).im * Complex.I.re)
          (Complex.ofReal_re s)
      _ = s * 1 + (s : ℂ).im * Complex.I.re := by
        exact congrArg
          (fun r : ℝ => s * r + (s : ℂ).im * Complex.I.re)
          Complex.I_im
      _ = s * 1 + 0 * Complex.I.re := by
        exact congrArg
          (fun r : ℝ => s * 1 + r * Complex.I.re)
          (Complex.ofReal_im s)
      _ = s + 0 * Complex.I.re := by
        exact congrArg (fun r : ℝ => r + 0 * Complex.I.re) (mul_one s)
      _ = s + 0 := by
        exact congrArg (fun r : ℝ => s + r) (zero_mul Complex.I.re)
      _ = s :=
        add_zero s
  have hadd_im :
      (((c : ℂ) + (s : ℂ) * Complex.I).im) = s := by
    calc
      (((c : ℂ) + (s : ℂ) * Complex.I).im) =
          (c : ℂ).im + ((s : ℂ) * Complex.I).im :=
        Complex.add_im (c : ℂ) ((s : ℂ) * Complex.I)
      _ = 0 + ((s : ℂ) * Complex.I).im := by
        exact congrArg
          (fun r : ℝ => r + ((s : ℂ) * Complex.I).im)
          (Complex.ofReal_im c)
      _ = 0 + s := by
        exact congrArg (fun r : ℝ => 0 + r) hmul_im
      _ = s :=
        zero_add s
  calc
    (1 - ((c : ℂ) + (s : ℂ) * Complex.I)).im =
        (1 : ℂ).im - ((c : ℂ) + (s : ℂ) * Complex.I).im :=
      Complex.sub_im (1 : ℂ) ((c : ℂ) + (s : ℂ) * Complex.I)
    _ = 0 - ((c : ℂ) + (s : ℂ) * Complex.I).im := by
      exact congrArg
        (fun r : ℝ => r - ((c : ℂ) + (s : ℂ) * Complex.I).im)
        Complex.one_im
    _ = 0 - s := by
      exact congrArg (fun r : ℝ => 0 - r) hadd_im
    _ = -s :=
      zero_sub s

/-- The real norm-square algebra behind the inverse chord formula. -/
theorem Real.inverseChord_normSq_formula
    (ψ : ℝ) :
    (1 - Real.cos ψ) * (1 - Real.cos ψ) +
        (-Real.sin ψ) * (-Real.sin ψ) =
      2 * (1 - Real.cos ψ) := by
  nlinarith [Real.sin_sq_add_cos_sq ψ]

/-- Cancelling the nonzero real chord denominator in the real coordinate. -/
theorem Real.one_sub_cos_div_two_mul_one_sub_cos
    {ψ : ℝ}
    (hone_sub_cos_ne : 1 - Real.cos ψ ≠ 0) :
    (1 - Real.cos ψ) / (2 * (1 - Real.cos ψ)) = 1 / 2 := by
  have htwo_ne : (2 : ℝ) ≠ 0 :=
    OfNat.ofNat_ne_zero
  have hden_ne : 2 * (1 - Real.cos ψ) ≠ 0 :=
    mul_ne_zero htwo_ne hone_sub_cos_ne
  exact (div_eq_div_iff hden_ne htwo_ne).mpr
    (Eq.trans
      (mul_comm (1 - Real.cos ψ) 2)
      (one_mul (2 * (1 - Real.cos ψ))).symm)

/-- Removing the double negation in the imaginary coordinate quotient. -/
theorem Real.neg_neg_sin_div
    (ψ : ℝ) :
    -(-Real.sin ψ) / (2 * (1 - Real.cos ψ)) =
      Real.sin ψ / (2 * (1 - Real.cos ψ)) := by
  exact congrArg
    (fun r : ℝ => r / (2 * (1 - Real.cos ψ)))
    (neg_neg (Real.sin ψ))

/-- Coordinate formula for the inverse chord map on the punctured reduced arc. -/
theorem Complex.reducedArc_inverseGeometricDenominator_eq_half_add_imCoordFormula
    {ψ : ℝ}
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_ne : ψ ≠ 0) :
    Complex.reducedArc_inverseGeometricDenominator ψ =
      ((1 / 2 : ℝ) : ℂ) +
        Complex.I *
          ((Real.sin ψ / (2 * (1 - Real.cos ψ)) : ℝ) : ℂ) := by
  have hone_sub_cos_ne : 1 - Real.cos ψ ≠ 0 := by
    exact Real.one_sub_cos_ne_zero_of_mem_reducedArc hψ_mem hψ_ne
  have hden_ne : 2 * (1 - Real.cos ψ) ≠ 0 := by
    exact Real.two_mul_one_sub_cos_ne_zero_of_mem_reducedArc hψ_mem hψ_ne
  have hexp :
      Complex.exp (Complex.I * (ψ : ℂ)) =
        (Real.cos ψ : ℂ) + (Real.sin ψ : ℂ) * Complex.I := by
    calc
      Complex.exp (Complex.I * (ψ : ℂ)) =
          Complex.exp ((ψ : ℂ) * Complex.I) := by
        exact congrArg Complex.exp (mul_comm Complex.I (ψ : ℂ))
      _ = Complex.cos (ψ : ℂ) + Complex.sin (ψ : ℂ) * Complex.I :=
        Complex.exp_mul_I (ψ : ℂ)
      _ = (Real.cos ψ : ℂ) + (Real.sin ψ : ℂ) * Complex.I := by
        exact congrArg₂ Add.add
          (Complex.ofReal_cos ψ).symm
          (congrArg (fun z : ℂ => z * Complex.I)
            (Complex.ofReal_sin ψ).symm)
  let z : ℂ := 1 - Complex.exp (Complex.I * (ψ : ℂ))
  have hz_re : z.re = 1 - Real.cos ψ := by
    unfold z
    calc
      (1 - Complex.exp (Complex.I * (ψ : ℂ))).re =
          (1 - ((Real.cos ψ : ℂ) + (Real.sin ψ : ℂ) * Complex.I)).re := by
        exact congrArg Complex.re (congrArg (fun w : ℂ => 1 - w) hexp)
      _ = 1 - Real.cos ψ := by
        exact Complex.one_sub_cos_add_sin_mul_I_re (Real.cos ψ) (Real.sin ψ)
  have hz_im : z.im = -Real.sin ψ := by
    unfold z
    calc
      (1 - Complex.exp (Complex.I * (ψ : ℂ))).im =
          (1 - ((Real.cos ψ : ℂ) + (Real.sin ψ : ℂ) * Complex.I)).im := by
        exact congrArg Complex.im (congrArg (fun w : ℂ => 1 - w) hexp)
      _ = -Real.sin ψ := by
        exact Complex.one_sub_cos_add_sin_mul_I_im (Real.cos ψ) (Real.sin ψ)
  have hnormSq :
      Complex.normSq z = 2 * (1 - Real.cos ψ) := by
    calc
      Complex.normSq z = z.re * z.re + z.im * z.im :=
        Complex.normSq_apply z
      _ = (1 - Real.cos ψ) * (1 - Real.cos ψ) +
            (-Real.sin ψ) * (-Real.sin ψ) := by
        exact congrArg₂ Add.add
          (congrArg₂ Mul.mul hz_re hz_re)
          (congrArg₂ Mul.mul hz_im hz_im)
      _ = 2 * (1 - Real.cos ψ) := by
        exact Real.inverseChord_normSq_formula ψ
  exact Complex.ext
    (by
      calc
      (Complex.reducedArc_inverseGeometricDenominator ψ).re =
          z⁻¹.re := by
        rfl
      _ = z.re / Complex.normSq z :=
        Complex.inv_re z
      _ = (1 - Real.cos ψ) / (2 * (1 - Real.cos ψ)) := by
        exact congrArg₂ Div.div hz_re hnormSq
      _ = 1 / 2 := by
        exact Real.one_sub_cos_div_two_mul_one_sub_cos hone_sub_cos_ne
      _ = ((((1 / 2 : ℝ) : ℂ) +
            Complex.I *
              ((Real.sin ψ / (2 * (1 - Real.cos ψ)) : ℝ) : ℂ)).re) := by
        exact (Complex.half_add_I_mul_ofReal_re
          (Real.sin ψ / (2 * (1 - Real.cos ψ)))).symm)
    (by
      calc
      (Complex.reducedArc_inverseGeometricDenominator ψ).im =
          z⁻¹.im := by
        rfl
      _ = -z.im / Complex.normSq z :=
        Complex.inv_im z
      _ = -(-Real.sin ψ) / (2 * (1 - Real.cos ψ)) := by
        exact congrArg₂ Div.div (congrArg Neg.neg hz_im) hnormSq
      _ = Real.sin ψ / (2 * (1 - Real.cos ψ)) := by
        exact Real.neg_neg_sin_div ψ
      _ = ((((1 / 2 : ℝ) : ℂ) +
            Complex.I *
              ((Real.sin ψ / (2 * (1 - Real.cos ψ)) : ℝ) : ℂ)).im) := by
        exact (Complex.half_add_I_mul_ofReal_im
          (Real.sin ψ / (2 * (1 - Real.cos ψ)))).symm)

/-- The inverse chord map has real part `1 / 2` on the reduced arc away from
zero. -/
theorem Complex.reducedArc_inverseGeometricDenominator_re_eq_half
    {ψ : ℝ}
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_ne : ψ ≠ 0) :
    (Complex.reducedArc_inverseGeometricDenominator ψ).re = 1 / 2 := by
  let y : ℝ := Real.sin ψ / (2 * (1 - Real.cos ψ))
  have hformula :
      Complex.reducedArc_inverseGeometricDenominator ψ =
        ((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ) :=
    Complex.reducedArc_inverseGeometricDenominator_eq_half_add_imCoordFormula
      hψ_mem hψ_ne
  have hproject :
      (((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ)).re = 1 / 2 :=
    Complex.half_add_I_mul_ofReal_re y
  exact Eq.trans (congrArg Complex.re hformula) hproject

/-- The inverse chord map is recovered from its imaginary coordinate on the
vertical line `re = 1 / 2`. -/
theorem Complex.reducedArc_inverseGeometricDenominator_eq_lineCoord
    {ψ : ℝ}
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_ne : ψ ≠ 0) :
    Complex.reducedArc_inverseGeometricDenominator ψ =
      (1 / 2 : ℂ) +
        Complex.I *
          (Complex.reducedArc_inverseGeometricDenominator_imCoord ψ : ℂ) := by
  let z : ℂ := Complex.reducedArc_inverseGeometricDenominator ψ
  have hz_re : z.re = 1 / 2 :=
    Complex.reducedArc_inverseGeometricDenominator_re_eq_half hψ_mem hψ_ne
  have hz_coord :
      z = (z.re : ℂ) + Complex.I * (z.im : ℂ) := by
    calc
      z = (z.re : ℂ) + z.im * Complex.I :=
        (Complex.re_add_im z).symm
      _ = (z.re : ℂ) + Complex.I * (z.im : ℂ) := by
        exact congrArg (fun w : ℂ => (z.re : ℂ) + w)
          (mul_comm (z.im : ℂ) Complex.I)
  have hz_target :
      z = (1 / 2 : ℂ) + Complex.I * (z.im : ℂ) := by
    exact Eq.subst
      (motive := fun r : ℝ =>
        z = (r : ℂ) + Complex.I * (z.im : ℂ))
      hz_re
      hz_coord
  exact hz_target

/-- Differences of reduced inverse denominators on the same vertical line have
norm equal to the absolute difference of their imaginary coordinates. -/
theorem Complex.reducedArc_inverseGeometricDenominator_sub_norm_eq_imCoord
    {ψ θ : ℝ}
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hθ_mem : θ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_ne : ψ ≠ 0)
    (hθ_ne : θ ≠ 0) :
      ‖Complex.reducedArc_inverseGeometricDenominator ψ -
        Complex.reducedArc_inverseGeometricDenominator θ‖ =
      ‖Complex.reducedArc_inverseGeometricDenominator_imCoord ψ -
        Complex.reducedArc_inverseGeometricDenominator_imCoord θ‖ := by
  let zψ : ℂ := Complex.reducedArc_inverseGeometricDenominator ψ
  let zθ : ℂ := Complex.reducedArc_inverseGeometricDenominator θ
  let yψ : ℝ := Complex.reducedArc_inverseGeometricDenominator_imCoord ψ
  let yθ : ℝ := Complex.reducedArc_inverseGeometricDenominator_imCoord θ
  have hψ_line : zψ = (1 / 2 : ℂ) + Complex.I * (yψ : ℂ) :=
    Complex.reducedArc_inverseGeometricDenominator_eq_lineCoord hψ_mem hψ_ne
  have hθ_line : zθ = (1 / 2 : ℂ) + Complex.I * (yθ : ℂ) :=
    Complex.reducedArc_inverseGeometricDenominator_eq_lineCoord hθ_mem hθ_ne
  have hdiff :
      zψ - zθ = Complex.I * ((yψ - yθ : ℝ) : ℂ) := by
    calc
      zψ - zθ =
          ((1 / 2 : ℂ) + Complex.I * (yψ : ℂ)) -
            ((1 / 2 : ℂ) + Complex.I * (yθ : ℂ)) := by
        exact congrArg₂ Sub.sub hψ_line hθ_line
      _ = Complex.I * ((yψ - yθ : ℝ) : ℂ) := by
        exact Complex.half_add_I_mul_ofReal_sub yψ yθ
  have hnorm :
      ‖Complex.I * ((yψ - yθ : ℝ) : ℂ)‖ = ‖yψ - yθ‖ := by
    calc
      ‖Complex.I * ((yψ - yθ : ℝ) : ℂ)‖ =
          ‖Complex.I‖ * ‖((yψ - yθ : ℝ) : ℂ)‖ :=
        norm_mul Complex.I ((yψ - yθ : ℝ) : ℂ)
      _ = 1 * ‖((yψ - yθ : ℝ) : ℂ)‖ := by
        exact congrArg (fun r : ℝ => r * ‖((yψ - yθ : ℝ) : ℂ)‖) norm_I
      _ = ‖((yψ - yθ : ℝ) : ℂ)‖ :=
        one_mul ‖((yψ - yθ : ℝ) : ℂ)‖
      _ = ‖yψ - yθ‖ :=
        RCLike.norm_ofReal (yψ - yθ)
  exact Eq.trans (congrArg norm hdiff) hnorm

/-- Explicit imaginary coordinate of the inverse chord map on the reduced arc
away from zero. -/
theorem Complex.reducedArc_inverseGeometricDenominator_imCoord_eq
    {ψ : ℝ}
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_ne : ψ ≠ 0) :
    Complex.reducedArc_inverseGeometricDenominator_imCoord ψ =
      Real.sin ψ / (2 * (1 - Real.cos ψ)) := by
  let y : ℝ := Real.sin ψ / (2 * (1 - Real.cos ψ))
  have hformula :
      Complex.reducedArc_inverseGeometricDenominator ψ =
        ((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ) :=
    Complex.reducedArc_inverseGeometricDenominator_eq_half_add_imCoordFormula
      hψ_mem hψ_ne
  have hproject :
      (((1 / 2 : ℝ) : ℂ) + Complex.I * (y : ℂ)).im = y :=
    Complex.half_add_I_mul_ofReal_im y
  exact Eq.trans (congrArg Complex.im hformula) hproject

/-- The inverse-chord denominator is nonzero on the positive reduced arc. -/
theorem Real.inverseChord_denominator_ne_zero_on_pos :
    ∀ ψ : ℝ,
      ψ ∈ Set.Ioc (0 : ℝ) Real.pi →
        2 * (1 - Real.cos ψ) ≠ 0 := by
  intro ψ hψ
  have hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨lt_trans (neg_lt_zero.mpr Real.pi_pos) hψ.1, hψ.2⟩
  have hψ_ne : ψ ≠ 0 :=
    ne_of_gt hψ.1
  exact Real.two_mul_one_sub_cos_ne_zero_of_mem_reducedArc hψ_mem hψ_ne

/-- The inverse-chord denominator is nonzero on the negative reduced arc. -/
theorem Real.inverseChord_denominator_ne_zero_on_neg :
    ∀ ψ : ℝ,
      ψ ∈ Set.Ioo (-Real.pi) (0 : ℝ) →
        2 * (1 - Real.cos ψ) ≠ 0 := by
  intro ψ hψ
  have hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨hψ.1, le_of_lt (lt_trans hψ.2 Real.pi_pos)⟩
  have hψ_ne : ψ ≠ 0 :=
    ne_of_lt hψ.2
  exact Real.two_mul_one_sub_cos_ne_zero_of_mem_reducedArc hψ_mem hψ_ne

/-- The inverse-chord denominator is positive on the punctured reduced arc. -/
theorem Real.inverseChord_denominator_pos_of_mem_reducedArc
    {ψ : ℝ}
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_ne : ψ ≠ 0) :
    0 < 2 * (1 - Real.cos ψ) := by
  have hcos_le_one : Real.cos ψ ≤ 1 :=
    Real.cos_le_one ψ
  have hone_sub_cos_nonneg : 0 ≤ 1 - Real.cos ψ :=
    sub_nonneg.mpr hcos_le_one
  have hone_sub_cos_ne : 1 - Real.cos ψ ≠ 0 :=
    Real.one_sub_cos_ne_zero_of_mem_reducedArc hψ_mem hψ_ne
  have hone_sub_cos_pos : 0 < 1 - Real.cos ψ :=
    lt_of_le_of_ne hone_sub_cos_nonneg hone_sub_cos_ne.symm
  exact mul_pos zero_lt_two hone_sub_cos_pos

/-- Raw quotient-rule derivative of the inverse-chord imaginary coordinate. -/
theorem Real.inverseChord_imCoordFormula_deriv_raw
    {ψ : ℝ}
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_ne : ψ ≠ 0) :
    deriv (fun θ : ℝ => Real.sin θ / (2 * (1 - Real.cos θ))) ψ =
      (deriv Real.sin ψ * (2 * (1 - Real.cos ψ)) -
          Real.sin ψ *
            deriv (fun θ : ℝ => 2 * (1 - Real.cos θ)) ψ) /
        (2 * (1 - Real.cos ψ)) ^ 2 := by
  have hnum :
      DifferentiableAt ℝ Real.sin ψ :=
    Real.differentiable_sin ψ
  have hcos :
      DifferentiableAt ℝ Real.cos ψ :=
    Real.differentiable_cos ψ
  have hden_base :
      DifferentiableAt ℝ
        (fun θ : ℝ => 1 - Real.cos θ) ψ :=
    (differentiableAt_const 1).sub hcos
  have hden :
      DifferentiableAt ℝ
        (fun θ : ℝ => 2 * (1 - Real.cos θ)) ψ :=
    (differentiableAt_const 2).mul hden_base
  have hden_ne : 2 * (1 - Real.cos ψ) ≠ 0 :=
    Real.two_mul_one_sub_cos_ne_zero_of_mem_reducedArc hψ_mem hψ_ne
  exact deriv_div hnum hden hden_ne

/-- Derivative of the inverse-chord denominator. -/
theorem Real.inverseChord_denominator_deriv_eq
    (ψ : ℝ) :
    deriv (fun θ : ℝ => 2 * (1 - Real.cos θ)) ψ =
      2 * Real.sin ψ := by
  have hinner :
      deriv (fun θ : ℝ => 1 - Real.cos θ) ψ =
        Real.sin ψ := by
    have hconst_sub :
        deriv (fun θ : ℝ => 1 - Real.cos θ) ψ =
          -deriv Real.cos ψ :=
      deriv_const_sub (f := Real.cos) (x := ψ) (1 : ℝ)
    have hcos :
        deriv Real.cos ψ = -Real.sin ψ :=
      congrFun Real.deriv_cos ψ
    have hneg_transport :
        -deriv Real.cos ψ = -(-Real.sin ψ) :=
      congrArg Neg.neg hcos
    have hneg :
        -(-Real.sin ψ) = Real.sin ψ :=
      neg_neg (Real.sin ψ)
    calc
      deriv (fun θ : ℝ => 1 - Real.cos θ) ψ =
          -deriv Real.cos ψ :=
        hconst_sub
      _ = -(-Real.sin ψ) :=
        hneg_transport
      _ = Real.sin ψ :=
        hneg
  calc
    deriv (fun θ : ℝ => 2 * (1 - Real.cos θ)) ψ =
        2 * deriv (fun θ : ℝ => 1 - Real.cos θ) ψ :=
      deriv_const_mul_field (v := fun θ : ℝ => 1 - Real.cos θ)
        (x := ψ) (2 : ℝ)
    _ = 2 * Real.sin ψ :=
      congrArg (fun r : ℝ => 2 * r) hinner

/-- Polynomial form of the inverse-chord derivative numerator identity. -/
theorem Real.inverseChord_deriv_trig_numerator_eq_of_unit_circle
    {s c : ℝ}
    (hunit : s ^ 2 + c ^ 2 = 1) :
    c * (2 * (1 - c)) - s * (2 * s) =
      -2 * (1 - c) := by
  nlinarith [hunit]

/-- Trigonometric numerator identity behind the inverse-chord derivative. -/
theorem Real.inverseChord_deriv_trig_numerator_eq
    (ψ : ℝ) :
    Real.cos ψ * (2 * (1 - Real.cos ψ)) -
        Real.sin ψ * (2 * Real.sin ψ) =
      -2 * (1 - Real.cos ψ) := by
  exact
    Real.inverseChord_deriv_trig_numerator_eq_of_unit_circle
      (s := Real.sin ψ)
      (c := Real.cos ψ)
      (Real.sin_sq_add_cos_sq ψ)

/-- Numerator simplification in the inverse-chord derivative. -/
theorem Real.inverseChord_deriv_raw_numerator_eq
    (ψ : ℝ) :
    deriv Real.sin ψ * (2 * (1 - Real.cos ψ)) -
        Real.sin ψ *
          deriv (fun θ : ℝ => 2 * (1 - Real.cos θ)) ψ =
      -2 * (1 - Real.cos ψ) := by
  have hsin_deriv :
      deriv Real.sin ψ = Real.cos ψ :=
    congrFun Real.deriv_sin ψ
  have hden_deriv :
      deriv (fun θ : ℝ => 2 * (1 - Real.cos θ)) ψ =
        2 * Real.sin ψ :=
    Real.inverseChord_denominator_deriv_eq ψ
  have htransport :
      deriv Real.sin ψ * (2 * (1 - Real.cos ψ)) -
          Real.sin ψ *
            deriv (fun θ : ℝ => 2 * (1 - Real.cos θ)) ψ =
        Real.cos ψ * (2 * (1 - Real.cos ψ)) -
          Real.sin ψ * (2 * Real.sin ψ) := by
    exact congrArg₂ Sub.sub
      (congrArg
        (fun r : ℝ => r * (2 * (1 - Real.cos ψ)))
        hsin_deriv)
      (congrArg
        (fun r : ℝ => Real.sin ψ * r)
        hden_deriv)
  exact Eq.trans htransport (Real.inverseChord_deriv_trig_numerator_eq ψ)

/-- Field identity used to cancel the derivative quotient. -/
theorem Real.neg_div_sq_eq_neg_inv
    {d : ℝ}
    (hd : d ≠ 0) :
    (-d) / d ^ 2 = -1 / d := by
  have hd_inv :
      d * d⁻¹ = 1 :=
    mul_inv_cancel₀ hd
  have hpow :
      d ^ 2 = d * d :=
    pow_two d
  have hmain :
      (-d) * (d ^ 2)⁻¹ = -1 * d⁻¹ := by
    calc
      (-d) * (d ^ 2)⁻¹ =
          -(d * (d ^ 2)⁻¹) :=
        neg_mul d (d ^ 2)⁻¹
      _ = -(d * (d * d)⁻¹) :=
        congrArg (fun r : ℝ => -(d * r⁻¹)) hpow
      _ = -(d * (d⁻¹ * d⁻¹)) := by
        exact congrArg (fun r : ℝ => -(d * r))
          (mul_inv_rev d d)
      _ = -((d * d⁻¹) * d⁻¹) := by
        exact congrArg Neg.neg (mul_assoc d d⁻¹ d⁻¹)
      _ = -(1 * d⁻¹) := by
        exact congrArg Neg.neg
          (congrArg (fun r : ℝ => r * d⁻¹) hd_inv)
      _ = -d⁻¹ := by
        exact congrArg Neg.neg (one_mul d⁻¹)
      _ = -((1 : ℝ) * d⁻¹) := by
        exact Eq.symm (congrArg Neg.neg (one_mul d⁻¹))
      _ = -1 * d⁻¹ :=
        neg_mul_eq_neg_mul 1 d⁻¹
  have hleft :
      (-d) / d ^ 2 = (-d) * (d ^ 2)⁻¹ :=
    div_eq_mul_inv (-d) (d ^ 2)
  have hright :
      -1 / d = -1 * d⁻¹ :=
    div_eq_mul_inv (-1 : ℝ) d
  exact Eq.trans hleft (Eq.trans hmain hright.symm)

/-- Quotient simplification in the inverse-chord derivative. -/
theorem Real.inverseChord_deriv_raw_quotient_eq
    {ψ : ℝ}
    (hone_sub_cos_ne : 1 - Real.cos ψ ≠ 0) :
    (-2 * (1 - Real.cos ψ)) / (2 * (1 - Real.cos ψ)) ^ 2 =
      -1 / (2 * (1 - Real.cos ψ)) := by
  let d : ℝ := 2 * (1 - Real.cos ψ)
  have htwo_ne : (2 : ℝ) ≠ 0 :=
    OfNat.ofNat_ne_zero
  have hd : d ≠ 0 :=
    mul_ne_zero htwo_ne hone_sub_cos_ne
  have hneg :
      -2 * (1 - Real.cos ψ) = -d := by
    calc
      -2 * (1 - Real.cos ψ) =
          -(2 * (1 - Real.cos ψ)) :=
        neg_mul_eq_neg_mul 2 (1 - Real.cos ψ)
      _ = -d := by
        exact congrArg Neg.neg (show 2 * (1 - Real.cos ψ) = d from rfl)
  have hfield :
      (-d) / d ^ 2 = -1 / d :=
    Real.neg_div_sq_eq_neg_inv hd
  exact Eq.trans
    (congrArg₂ Div.div hneg (congrArg (fun r : ℝ => r ^ 2) (show 2 * (1 - Real.cos ψ) = d from rfl)))
    hfield

/-- Scalar simplification of the raw inverse-chord derivative formula. -/
theorem Real.inverseChord_imCoordFormula_deriv_raw_simplifies
    {ψ : ℝ}
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_ne : ψ ≠ 0) :
    (deriv Real.sin ψ * (2 * (1 - Real.cos ψ)) -
        Real.sin ψ *
          deriv (fun θ : ℝ => 2 * (1 - Real.cos θ)) ψ) /
      (2 * (1 - Real.cos ψ)) ^ 2 =
      -1 / (2 * (1 - Real.cos ψ)) := by
  have hnumerator :
      deriv Real.sin ψ * (2 * (1 - Real.cos ψ)) -
          Real.sin ψ *
            deriv (fun θ : ℝ => 2 * (1 - Real.cos θ)) ψ =
        -2 * (1 - Real.cos ψ) :=
    Real.inverseChord_deriv_raw_numerator_eq ψ
  have hone_sub_cos_ne : 1 - Real.cos ψ ≠ 0 :=
    Real.one_sub_cos_ne_zero_of_mem_reducedArc hψ_mem hψ_ne
  have hquotient :
      (-2 * (1 - Real.cos ψ)) / (2 * (1 - Real.cos ψ)) ^ 2 =
        -1 / (2 * (1 - Real.cos ψ)) :=
    Real.inverseChord_deriv_raw_quotient_eq hone_sub_cos_ne
  exact Eq.trans
    (congrArg
      (fun numerator : ℝ =>
        numerator / (2 * (1 - Real.cos ψ)) ^ 2)
      hnumerator)
    hquotient

/-- Derivative formula for the inverse-chord imaginary coordinate. -/
theorem Real.inverseChord_imCoordFormula_deriv_eq
    {ψ : ℝ}
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_ne : ψ ≠ 0) :
    deriv (fun θ : ℝ => Real.sin θ / (2 * (1 - Real.cos θ))) ψ =
      -1 / (2 * (1 - Real.cos ψ)) := by
  exact Eq.trans
    (Real.inverseChord_imCoordFormula_deriv_raw hψ_mem hψ_ne)
    (Real.inverseChord_imCoordFormula_deriv_raw_simplifies hψ_mem hψ_ne)

/-- The inverse-chord imaginary-coordinate derivative is nonpositive on the
punctured reduced arc. -/
theorem Real.inverseChord_imCoordFormula_deriv_nonpos_of_mem_reducedArc
    {ψ : ℝ}
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_ne : ψ ≠ 0) :
    deriv (fun θ : ℝ => Real.sin θ / (2 * (1 - Real.cos θ))) ψ ≤ 0 := by
  have hderiv :
      deriv (fun θ : ℝ => Real.sin θ / (2 * (1 - Real.cos θ))) ψ =
        -1 / (2 * (1 - Real.cos ψ)) :=
    Real.inverseChord_imCoordFormula_deriv_eq hψ_mem hψ_ne
  have hden_pos : 0 < 2 * (1 - Real.cos ψ) :=
    Real.inverseChord_denominator_pos_of_mem_reducedArc hψ_mem hψ_ne
  have hinv_pos : 0 < (2 * (1 - Real.cos ψ))⁻¹ :=
    inv_pos.mpr hden_pos
  have hneg_nonpos : -(1 * (2 * (1 - Real.cos ψ))⁻¹) ≤ 0 :=
    neg_nonpos.mpr hinv_pos.le
  have hquot :
      -1 / (2 * (1 - Real.cos ψ)) =
        -(1 * (2 * (1 - Real.cos ψ))⁻¹) := by
    calc
      -1 / (2 * (1 - Real.cos ψ)) =
          (-1) * (2 * (1 - Real.cos ψ))⁻¹ :=
        div_eq_mul_inv (-1) (2 * (1 - Real.cos ψ))
      _ = -(1 * (2 * (1 - Real.cos ψ))⁻¹) :=
        neg_mul_eq_neg_mul 1 (2 * (1 - Real.cos ψ))⁻¹
  exact Eq.subst
    (motive := fun r : ℝ => r ≤ 0)
    hderiv.symm
    (Eq.subst
      (motive := fun r : ℝ => r ≤ 0)
      hquot.symm
      hneg_nonpos)

/-- The real inverse-chord imaginary coordinate formula is antitone on the
positive reduced arc. -/
theorem Real.inverseChord_imCoordFormula_continuousOn_pos :
    ContinuousOn
      (fun ψ : ℝ => Real.sin ψ / (2 * (1 - Real.cos ψ)))
      (Set.Ioc (0 : ℝ) Real.pi) := by
  have hnum :
      ContinuousOn Real.sin (Set.Ioc (0 : ℝ) Real.pi) :=
    Real.continuous_sin.continuousOn
  have hcos :
      ContinuousOn Real.cos (Set.Ioc (0 : ℝ) Real.pi) :=
    Real.continuous_cos.continuousOn
  have hden_base :
      ContinuousOn
        (fun ψ : ℝ => 1 - Real.cos ψ)
        (Set.Ioc (0 : ℝ) Real.pi) :=
    continuousOn_const.sub hcos
  have hden :
      ContinuousOn
        (fun ψ : ℝ => 2 * (1 - Real.cos ψ))
        (Set.Ioc (0 : ℝ) Real.pi) :=
    continuousOn_const.mul hden_base
  exact hnum.div hden Real.inverseChord_denominator_ne_zero_on_pos

theorem Real.inverseChord_imCoordFormula_differentiableOn_pos :
    DifferentiableOn ℝ
      (fun ψ : ℝ => Real.sin ψ / (2 * (1 - Real.cos ψ)))
      (interior (Set.Ioc (0 : ℝ) Real.pi)) := by
  have hnum :
      DifferentiableOn ℝ Real.sin (interior (Set.Ioc (0 : ℝ) Real.pi)) :=
    Real.differentiable_sin.differentiableOn
  have hcos :
      DifferentiableOn ℝ Real.cos (interior (Set.Ioc (0 : ℝ) Real.pi)) :=
    Real.differentiable_cos.differentiableOn
  have hden_base :
      DifferentiableOn ℝ
        (fun ψ : ℝ => 1 - Real.cos ψ)
        (interior (Set.Ioc (0 : ℝ) Real.pi)) :=
    (differentiableOn_const 1).sub hcos
  have hden :
      DifferentiableOn ℝ
        (fun ψ : ℝ => 2 * (1 - Real.cos ψ))
        (interior (Set.Ioc (0 : ℝ) Real.pi)) :=
    (differentiableOn_const 2).mul hden_base
  have hden_ne :
      ∀ ψ : ℝ,
        ψ ∈ interior (Set.Ioc (0 : ℝ) Real.pi) →
          2 * (1 - Real.cos ψ) ≠ 0 := by
    intro ψ hψ
    exact Real.inverseChord_denominator_ne_zero_on_pos ψ (interior_subset hψ)
  exact hnum.div hden hden_ne

theorem Real.inverseChord_imCoordFormula_deriv_nonpos_pos :
    ∀ ψ : ℝ,
      ψ ∈ interior (Set.Ioc (0 : ℝ) Real.pi) →
        deriv (fun θ : ℝ => Real.sin θ / (2 * (1 - Real.cos θ))) ψ ≤ 0 := by
  intro ψ hψ
  have hψ_side : ψ ∈ Set.Ioc (0 : ℝ) Real.pi :=
    interior_subset hψ
  have hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨lt_trans (neg_lt_zero.mpr Real.pi_pos) hψ_side.1, hψ_side.2⟩
  have hψ_ne : ψ ≠ 0 :=
    ne_of_gt hψ_side.1
  exact
    Real.inverseChord_imCoordFormula_deriv_nonpos_of_mem_reducedArc
      hψ_mem hψ_ne

theorem Real.inverseChord_imCoordFormula_antitoneOn_pos :
    AntitoneOn
      (fun ψ : ℝ => Real.sin ψ / (2 * (1 - Real.cos ψ)))
      (Set.Ioc (0 : ℝ) Real.pi) := by
  exact antitoneOn_of_deriv_nonpos
    (convex_Ioc (0 : ℝ) Real.pi)
    Real.inverseChord_imCoordFormula_continuousOn_pos
    Real.inverseChord_imCoordFormula_differentiableOn_pos
    Real.inverseChord_imCoordFormula_deriv_nonpos_pos

/-- The real inverse-chord imaginary coordinate formula is antitone on the
negative reduced arc. -/
theorem Real.inverseChord_imCoordFormula_continuousOn_neg :
    ContinuousOn
      (fun ψ : ℝ => Real.sin ψ / (2 * (1 - Real.cos ψ)))
      (Set.Ioo (-Real.pi) (0 : ℝ)) := by
  have hnum :
      ContinuousOn Real.sin (Set.Ioo (-Real.pi) (0 : ℝ)) :=
    Real.continuous_sin.continuousOn
  have hcos :
      ContinuousOn Real.cos (Set.Ioo (-Real.pi) (0 : ℝ)) :=
    Real.continuous_cos.continuousOn
  have hden_base :
      ContinuousOn
        (fun ψ : ℝ => 1 - Real.cos ψ)
        (Set.Ioo (-Real.pi) (0 : ℝ)) :=
    continuousOn_const.sub hcos
  have hden :
      ContinuousOn
        (fun ψ : ℝ => 2 * (1 - Real.cos ψ))
        (Set.Ioo (-Real.pi) (0 : ℝ)) :=
    continuousOn_const.mul hden_base
  exact hnum.div hden Real.inverseChord_denominator_ne_zero_on_neg

theorem Real.inverseChord_imCoordFormula_differentiableOn_neg :
    DifferentiableOn ℝ
      (fun ψ : ℝ => Real.sin ψ / (2 * (1 - Real.cos ψ)))
      (interior (Set.Ioo (-Real.pi) (0 : ℝ))) := by
  have hnum :
      DifferentiableOn ℝ Real.sin (interior (Set.Ioo (-Real.pi) (0 : ℝ))) :=
    Real.differentiable_sin.differentiableOn
  have hcos :
      DifferentiableOn ℝ Real.cos (interior (Set.Ioo (-Real.pi) (0 : ℝ))) :=
    Real.differentiable_cos.differentiableOn
  have hden_base :
      DifferentiableOn ℝ
        (fun ψ : ℝ => 1 - Real.cos ψ)
        (interior (Set.Ioo (-Real.pi) (0 : ℝ))) :=
    (differentiableOn_const 1).sub hcos
  have hden :
      DifferentiableOn ℝ
        (fun ψ : ℝ => 2 * (1 - Real.cos ψ))
        (interior (Set.Ioo (-Real.pi) (0 : ℝ))) :=
    (differentiableOn_const 2).mul hden_base
  have hden_ne :
      ∀ ψ : ℝ,
        ψ ∈ interior (Set.Ioo (-Real.pi) (0 : ℝ)) →
          2 * (1 - Real.cos ψ) ≠ 0 := by
    intro ψ hψ
    exact Real.inverseChord_denominator_ne_zero_on_neg ψ (interior_subset hψ)
  exact hnum.div hden hden_ne

theorem Real.inverseChord_imCoordFormula_deriv_nonpos_neg :
    ∀ ψ : ℝ,
      ψ ∈ interior (Set.Ioo (-Real.pi) (0 : ℝ)) →
        deriv (fun θ : ℝ => Real.sin θ / (2 * (1 - Real.cos θ))) ψ ≤ 0 := by
  intro ψ hψ
  have hψ_side : ψ ∈ Set.Ioo (-Real.pi) (0 : ℝ) :=
    interior_subset hψ
  have hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨hψ_side.1, le_of_lt (lt_trans hψ_side.2 Real.pi_pos)⟩
  have hψ_ne : ψ ≠ 0 :=
    ne_of_lt hψ_side.2
  exact
    Real.inverseChord_imCoordFormula_deriv_nonpos_of_mem_reducedArc
      hψ_mem hψ_ne

theorem Real.inverseChord_imCoordFormula_antitoneOn_neg :
    AntitoneOn
      (fun ψ : ℝ => Real.sin ψ / (2 * (1 - Real.cos ψ)))
      (Set.Ioo (-Real.pi) (0 : ℝ)) := by
  exact antitoneOn_of_deriv_nonpos
    (convex_Ioo (-Real.pi) (0 : ℝ))
    Real.inverseChord_imCoordFormula_continuousOn_neg
    Real.inverseChord_imCoordFormula_differentiableOn_neg
    Real.inverseChord_imCoordFormula_deriv_nonpos_neg

/-- On the positive reduced arc the inverse chord imaginary coordinate is
antitone. -/
theorem Complex.reducedArc_inverseGeometricDenominator_imCoord_antitoneOn_pos :
    AntitoneOn
      Complex.reducedArc_inverseGeometricDenominator_imCoord
      (Set.Ioc (0 : ℝ) Real.pi) := by
  intro x hx y hy hxy
  have hx_mem : x ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨lt_of_lt_of_le (neg_lt_zero.mpr Real.pi_pos) hx.1.le, hx.2⟩
  have hy_mem : y ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨lt_of_lt_of_le (neg_lt_zero.mpr Real.pi_pos) hy.1.le, hy.2⟩
  have hx_ne : x ≠ 0 :=
    ne_of_gt hx.1
  have hy_ne : y ≠ 0 :=
    ne_of_gt hy.1
  have hformula_x :
      Complex.reducedArc_inverseGeometricDenominator_imCoord x =
        Real.sin x / (2 * (1 - Real.cos x)) :=
    Complex.reducedArc_inverseGeometricDenominator_imCoord_eq hx_mem hx_ne
  have hformula_y :
      Complex.reducedArc_inverseGeometricDenominator_imCoord y =
        Real.sin y / (2 * (1 - Real.cos y)) :=
    Complex.reducedArc_inverseGeometricDenominator_imCoord_eq hy_mem hy_ne
  exact Eq.subst
    (motive := fun target : ℝ =>
      Complex.reducedArc_inverseGeometricDenominator_imCoord y ≤ target)
    hformula_x.symm
    (Eq.subst
      (motive := fun source : ℝ =>
        source ≤ Real.sin x / (2 * (1 - Real.cos x)))
      hformula_y.symm
      (Real.inverseChord_imCoordFormula_antitoneOn_pos hx hy hxy))

/-- On the negative reduced arc the inverse chord imaginary coordinate is
antitone. -/
theorem Complex.reducedArc_inverseGeometricDenominator_imCoord_antitoneOn_neg :
    AntitoneOn
      Complex.reducedArc_inverseGeometricDenominator_imCoord
      (Set.Ioo (-Real.pi) (0 : ℝ)) := by
  intro x hx y hy hxy
  have hx_mem : x ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨hx.1, le_of_lt (lt_trans hx.2 Real.pi_pos)⟩
  have hy_mem : y ∈ Set.Ioc (-Real.pi) Real.pi :=
    ⟨hy.1, le_of_lt (lt_trans hy.2 Real.pi_pos)⟩
  have hx_ne : x ≠ 0 :=
    ne_of_lt hx.2
  have hy_ne : y ≠ 0 :=
    ne_of_lt hy.2
  have hformula_x :
      Complex.reducedArc_inverseGeometricDenominator_imCoord x =
        Real.sin x / (2 * (1 - Real.cos x)) :=
    Complex.reducedArc_inverseGeometricDenominator_imCoord_eq hx_mem hx_ne
  have hformula_y :
      Complex.reducedArc_inverseGeometricDenominator_imCoord y =
        Real.sin y / (2 * (1 - Real.cos y)) :=
    Complex.reducedArc_inverseGeometricDenominator_imCoord_eq hy_mem hy_ne
  exact Eq.subst
    (motive := fun target : ℝ =>
      Complex.reducedArc_inverseGeometricDenominator_imCoord y ≤ target)
    hformula_x.symm
    (Eq.subst
      (motive := fun source : ℝ =>
        source ≤ Real.sin x / (2 * (1 - Real.cos x)))
      hformula_y.symm
      (Real.inverseChord_imCoordFormula_antitoneOn_neg hx hy hxy))

/-- An index in the open summation interval belongs to the monotonicity block. -/
theorem Nat.mem_Ico_of_mem_Ioo_right
    {a b m n : ℕ}
    (hn : n ∈ Finset.Ioo a m)
    (hm : m ∈ Finset.Icc a b) :
    n ∈ Finset.Ico a b := by
  have hn_bounds : a < n ∧ n < m :=
    Finset.mem_Ioo.mp hn
  have hm_bounds : a ≤ m ∧ m ≤ b :=
    Finset.mem_Icc.mp hm
  have han : a ≤ n :=
    le_of_lt hn_bounds.1
  have hnb : n < b :=
    lt_of_lt_of_le hn_bounds.2 hm_bounds.2
  exact Finset.mem_Ico.mpr ⟨han, hnb⟩

/-- The predecessor of an open summation index belongs to the monotonicity
block. -/
theorem Nat.pred_mem_Ico_of_mem_Ioo_right
    {a b m n : ℕ}
    (hn : n ∈ Finset.Ioo a m)
    (hm : m ∈ Finset.Icc a b) :
    n - 1 ∈ Finset.Ico a b := by
  have hn_bounds : a < n ∧ n < m :=
    Finset.mem_Ioo.mp hn
  have hm_bounds : a ≤ m ∧ m ≤ b :=
    Finset.mem_Icc.mp hm
  have ha_pred : a ≤ n - 1 :=
    Nat.le_pred_of_lt hn_bounds.1
  have hn_pos : 0 < n :=
    lt_of_le_of_lt (Nat.zero_le a) hn_bounds.1
  have hpred_lt_n : n - 1 < n :=
    Nat.pred_lt hn_pos
  have hpred_lt_b : n - 1 < b :=
    lt_of_lt_of_le (lt_trans hpred_lt_n hn_bounds.2) hm_bounds.2
  exact Finset.mem_Ico.mpr ⟨ha_pred, hpred_lt_b⟩

/-- Monotone real sequences have nonnegative adjacent increments on the open
summation interval. -/
theorem Real.monotoneOn_nat_Ioo_adjacent_sub_nonneg
    (y : ℕ → ℝ)
    {a b m n : ℕ}
    (hn : n ∈ Finset.Ioo a m)
    (hm : m ∈ Finset.Icc a b)
    (hy : MonotoneOn y (Finset.Ico a b : Set ℕ)) :
    0 ≤ y n - y (n - 1) := by
  have hn_mem : n ∈ Finset.Ico a b :=
    Nat.mem_Ico_of_mem_Ioo_right hn hm
  have hpred_mem : n - 1 ∈ Finset.Ico a b :=
    Nat.pred_mem_Ico_of_mem_Ioo_right hn hm
  have hpred_le : n - 1 ≤ n :=
    Nat.sub_le n 1
  have hmono : y (n - 1) ≤ y n :=
    hy hpred_mem hn_mem hpred_le
  exact sub_nonneg.mpr hmono

/-- Antitone real sequences have nonpositive adjacent increments on the open
summation interval. -/
theorem Real.antitoneOn_nat_Ioo_adjacent_sub_nonpos
    (y : ℕ → ℝ)
    {a b m n : ℕ}
    (hn : n ∈ Finset.Ioo a m)
    (hm : m ∈ Finset.Icc a b)
    (hy : AntitoneOn y (Finset.Ico a b : Set ℕ)) :
    y n - y (n - 1) ≤ 0 := by
  have hn_mem : n ∈ Finset.Ico a b :=
    Nat.mem_Ico_of_mem_Ioo_right hn hm
  have hpred_mem : n - 1 ∈ Finset.Ico a b :=
    Nat.pred_mem_Ico_of_mem_Ioo_right hn hm
  have hpred_le : n - 1 ≤ n :=
    Nat.sub_le n 1
  have hanti : y n ≤ y (n - 1) :=
    hy hpred_mem hn_mem hpred_le
  exact sub_nonpos.mpr hanti

/-- Norm of an adjacent increment for a monotone real sequence. -/
theorem Real.monotoneOn_nat_Ioo_adjacent_norm_eq_sub
    (y : ℕ → ℝ)
    {a b m n : ℕ}
    (hn : n ∈ Finset.Ioo a m)
    (hm : m ∈ Finset.Icc a b)
    (hy : MonotoneOn y (Finset.Ico a b : Set ℕ)) :
    ‖y n - y (n - 1)‖ = y n - y (n - 1) := by
  have hnonneg : 0 ≤ y n - y (n - 1) :=
    Real.monotoneOn_nat_Ioo_adjacent_sub_nonneg y hn hm hy
  calc
    ‖y n - y (n - 1)‖ = |y n - y (n - 1)| :=
      Real.norm_eq_abs (y n - y (n - 1))
    _ = y n - y (n - 1) :=
      abs_of_nonneg hnonneg

/-- Norm of an adjacent increment for an antitone real sequence. -/
theorem Real.antitoneOn_nat_Ioo_adjacent_norm_eq_sub_rev
    (y : ℕ → ℝ)
    {a b m n : ℕ}
    (hn : n ∈ Finset.Ioo a m)
    (hm : m ∈ Finset.Icc a b)
    (hy : AntitoneOn y (Finset.Ico a b : Set ℕ)) :
    ‖y n - y (n - 1)‖ = y (n - 1) - y n := by
  have hnonpos : y n - y (n - 1) ≤ 0 :=
    Real.antitoneOn_nat_Ioo_adjacent_sub_nonpos y hn hm hy
  calc
    ‖y n - y (n - 1)‖ = |y n - y (n - 1)| :=
      Real.norm_eq_abs (y n - y (n - 1))
    _ = -(y n - y (n - 1)) :=
      abs_of_nonpos hnonpos
    _ = y (n - 1) - y n :=
      neg_sub (y n) (y (n - 1))

/-- Adjacent reduced inverse-denominator differences are controlled exactly by
the adjacent imaginary-coordinate difference. -/
theorem Complex.reducedArc_inverseGeometricDenominator_adjacent_norm_eq_imCoord
    (ψ : ℕ → ℝ)
    {n : ℕ}
    (hn_mem : ψ n ∈ Set.Ioc (-Real.pi) Real.pi)
    (hpred_mem : ψ (n - 1) ∈ Set.Ioc (-Real.pi) Real.pi)
    (hn_ne : ψ n ≠ 0)
    (hpred_ne : ψ (n - 1) ≠ 0) :
    ‖Complex.reducedArc_inverseGeometricDenominator (ψ n) -
      Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖ =
    ‖Complex.reducedArc_inverseGeometricDenominator_imCoord (ψ n) -
      Complex.reducedArc_inverseGeometricDenominator_imCoord (ψ (n - 1))‖ := by
  exact
    Complex.reducedArc_inverseGeometricDenominator_sub_norm_eq_imCoord
      hn_mem hpred_mem hn_ne hpred_ne

/-- A one-sided reduced-arc membership hypothesis implies membership in the
full reduced arc. -/
theorem Real.mem_reducedArc_of_mem_oneSided_reducedArc
    {ψ L U : ℝ}
    (hside : L = (0 : ℝ) ∧ U = Real.pi ∨
      L = -Real.pi ∧ U = (0 : ℝ))
    (hψ : ψ ∈ Set.Ioc L U) :
    ψ ∈ Set.Ioc (-Real.pi) Real.pi := by
  match hside with
  | Or.inl hpos =>
      have hψ_pos : ψ ∈ Set.Ioc (0 : ℝ) Real.pi :=
        Eq.subst
          (motive := fun l : ℝ => ψ ∈ Set.Ioc l Real.pi)
          hpos.1
          (Eq.subst
            (motive := fun u : ℝ => ψ ∈ Set.Ioc L u)
            hpos.2
            hψ)
      exact
        ⟨lt_trans (neg_lt_zero.mpr Real.pi_pos) hψ_pos.1, hψ_pos.2⟩
  | Or.inr hneg =>
      have hψ_neg : ψ ∈ Set.Ioc (-Real.pi) (0 : ℝ) :=
        Eq.subst
          (motive := fun l : ℝ => ψ ∈ Set.Ioc l (0 : ℝ))
          hneg.1
          (Eq.subst
            (motive := fun u : ℝ => ψ ∈ Set.Ioc L u)
            hneg.2
            hψ)
      exact
        ⟨hψ_neg.1, le_of_lt (lt_trans hψ_neg.2 Real.pi_pos)⟩

/-- Positive lower bound for the norm excludes zero. -/
theorem Real.ne_zero_of_pos_le_norm
    {λ x : ℝ}
    (hλ_pos : 0 < λ)
    (hx : λ ≤ ‖x‖) :
    x ≠ 0 := by
  intro hx_zero
  have hnorm_zero : ‖x‖ = 0 :=
    congrArg norm hx_zero
  have hλ_le_zero : λ ≤ 0 :=
    Eq.subst
      (motive := fun r : ℝ => λ ≤ r)
      hnorm_zero
      hx
  exact (not_le_of_gt hλ_pos) hλ_le_zero

/-- One-sided separated reduced-arc data gives nonzero membership in the full
reduced arc at an index. -/
theorem Real.oneSided_reducedArc_mem_and_ne_of_sep
    (ψ : ℕ → ℝ)
    {a b n : ℕ}
    {λ L U : ℝ}
    (hλ_pos : 0 < λ)
    (hside : L = (0 : ℝ) ∧ U = Real.pi ∨
      L = -Real.pi ∧ U = (0 : ℝ))
    (hn : n ∈ Finset.Ico a b)
    (hψ_mem :
      ∀ k : ℕ,
        k ∈ Finset.Ico a b →
          ψ k ∈ Set.Ioc L U)
    (hψ_sep :
      ∀ k : ℕ,
        k ∈ Finset.Ico a b →
          λ ≤ ‖ψ k‖) :
    ψ n ∈ Set.Ioc (-Real.pi) Real.pi ∧ ψ n ≠ 0 := by
  have hmem_side : ψ n ∈ Set.Ioc L U :=
    hψ_mem n hn
  have hmem : ψ n ∈ Set.Ioc (-Real.pi) Real.pi :=
    Real.mem_reducedArc_of_mem_oneSided_reducedArc hside hmem_side
  have hne : ψ n ≠ 0 :=
    Real.ne_zero_of_pos_le_norm hλ_pos (hψ_sep n hn)
  exact ⟨hmem, hne⟩

/-- Membership in the positive one-sided reduced arc after substituting the
recorded side endpoints. -/
theorem Real.mem_Ioc_zero_pi_of_mem_pos_side
    {ψ L U : ℝ}
    (hpos : L = (0 : ℝ) ∧ U = Real.pi)
    (hψ : ψ ∈ Set.Ioc L U) :
    ψ ∈ Set.Ioc (0 : ℝ) Real.pi :=
  Eq.subst
    (motive := fun l : ℝ => ψ ∈ Set.Ioc l Real.pi)
    hpos.1
    (Eq.subst
      (motive := fun u : ℝ => ψ ∈ Set.Ioc L u)
      hpos.2
      hψ)

/-- Membership in the negative one-sided reduced arc after substituting the
recorded side endpoints. -/
theorem Real.mem_Ioc_neg_pi_zero_of_mem_neg_side
    {ψ L U : ℝ}
    (hneg : L = -Real.pi ∧ U = (0 : ℝ))
    (hψ : ψ ∈ Set.Ioc L U) :
    ψ ∈ Set.Ioc (-Real.pi) (0 : ℝ) :=
  Eq.subst
    (motive := fun l : ℝ => ψ ∈ Set.Ioc l (0 : ℝ))
    hneg.1
    (Eq.subst
      (motive := fun u : ℝ => ψ ∈ Set.Ioc L u)
      hneg.2
      hψ)

/-- Negative-side membership plus separation from zero gives strict membership
in the open negative side. -/
theorem Real.mem_Ioo_neg_pi_zero_of_mem_neg_side_sep
    {ψ L U λ : ℝ}
    (hλ_pos : 0 < λ)
    (hneg : L = -Real.pi ∧ U = (0 : ℝ))
    (hψ : ψ ∈ Set.Ioc L U)
    (hsep : λ ≤ ‖ψ‖) :
    ψ ∈ Set.Ioo (-Real.pi) (0 : ℝ) := by
  have hψ_neg : ψ ∈ Set.Ioc (-Real.pi) (0 : ℝ) :=
    Real.mem_Ioc_neg_pi_zero_of_mem_neg_side hneg hψ
  have hne : ψ ≠ 0 :=
    Real.ne_zero_of_pos_le_norm hλ_pos hsep
  have hlt_zero : ψ < 0 :=
    lt_of_le_of_ne hψ_neg.2 hne
  exact ⟨hψ_neg.1, hlt_zero⟩

/-- A point in the reduced arc separated from zero lies on exactly one side of
the singularity. -/
theorem Real.mem_neg_side_or_pos_side_of_mem_reducedArc_sep
    {ψ λ : ℝ}
    (hλ_pos : 0 < λ)
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_sep : λ ≤ ‖ψ‖) :
    ψ ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∨
      ψ ∈ Set.Ioc (0 : ℝ) Real.pi := by
  have hψ_ne : ψ ≠ 0 :=
    Real.ne_zero_of_pos_le_norm hλ_pos hψ_sep
  match lt_or_gt_of_ne hψ_ne with
  | Or.inl hψ_lt_zero =>
      exact Or.inl ⟨hψ_mem.1, hψ_lt_zero⟩
  | Or.inr hψ_pos =>
      exact Or.inr ⟨hψ_pos, hψ_mem.2⟩

/-- On a separated reduced arc, failure of negative-side membership forces
positive-side membership. -/
theorem Real.mem_pos_side_of_not_mem_neg_side_of_mem_reducedArc_sep
    {ψ λ : ℝ}
    (hλ_pos : 0 < λ)
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_sep : λ ≤ ‖ψ‖)
    (hψ_not_neg : ¬ ψ ∈ Set.Ioc (-Real.pi) (0 : ℝ)) :
    ψ ∈ Set.Ioc (0 : ℝ) Real.pi := by
  have hcases :
      ψ ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∨
        ψ ∈ Set.Ioc (0 : ℝ) Real.pi :=
    Real.mem_neg_side_or_pos_side_of_mem_reducedArc_sep
      hλ_pos hψ_mem hψ_sep
  match hcases with
  | Or.inl hneg =>
      have hneg_ioc : ψ ∈ Set.Ioc (-Real.pi) (0 : ℝ) :=
        ⟨hneg.1, hneg.2.le⟩
      exact False.elim (hψ_not_neg hneg_ioc)
  | Or.inr hpos =>
      exact hpos

/-- On a separated reduced arc, failure of positive-side membership forces
negative-side membership. -/
theorem Real.mem_neg_side_of_not_mem_pos_side_of_mem_reducedArc_sep
    {ψ λ : ℝ}
    (hλ_pos : 0 < λ)
    (hψ_mem : ψ ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_sep : λ ≤ ‖ψ‖)
    (hψ_not_pos : ¬ ψ ∈ Set.Ioc (0 : ℝ) Real.pi) :
    ψ ∈ Set.Ioc (-Real.pi) (0 : ℝ) := by
  have hcases :
      ψ ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∨
        ψ ∈ Set.Ioc (0 : ℝ) Real.pi :=
    Real.mem_neg_side_or_pos_side_of_mem_reducedArc_sep
      hλ_pos hψ_mem hψ_sep
  match hcases with
  | Or.inl hneg =>
      exact ⟨hneg.1, hneg.2.le⟩
  | Or.inr hpos =>
      exact False.elim (hψ_not_pos hpos)

/-- Sign-side dichotomy for a separated reduced-arc sequence at an index. -/
theorem Real.sequence_mem_neg_side_or_pos_side_of_mem_reducedArc_sep
    (ψ : ℕ → ℝ)
    {a b n : ℕ}
    {λ : ℝ}
    (hλ_pos : 0 < λ)
    (hn : n ∈ Finset.Ico a b)
    (hψ_mem :
      ∀ k : ℕ,
        k ∈ Finset.Ico a b →
          ψ k ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_sep :
      ∀ k : ℕ,
        k ∈ Finset.Ico a b →
          λ ≤ ‖ψ k‖) :
    ψ n ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∨
      ψ n ∈ Set.Ioc (0 : ℝ) Real.pi :=
  Real.mem_neg_side_or_pos_side_of_mem_reducedArc_sep
    hλ_pos (hψ_mem n hn) (hψ_sep n hn)

/-- Adjacent separated reduced-arc samples are classified by their signs. -/
theorem Real.adjacent_mem_side_cases_of_mem_Ioo_sep
    (ψ : ℕ → ℝ)
    {a b m n : ℕ}
    {λ : ℝ}
    (hλ_pos : 0 < λ)
    (hn : n ∈ Finset.Ioo a m)
    (hm : m ∈ Finset.Icc a b)
    (hψ_mem :
      ∀ k : ℕ,
        k ∈ Finset.Ico a b →
          ψ k ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_sep :
      ∀ k : ℕ,
        k ∈ Finset.Ico a b →
          λ ≤ ‖ψ k‖) :
    (ψ (n - 1) ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∧
        ψ n ∈ Set.Ioo (-Real.pi) (0 : ℝ)) ∨
      (ψ (n - 1) ∈ Set.Ioc (0 : ℝ) Real.pi ∧
        ψ n ∈ Set.Ioc (0 : ℝ) Real.pi) ∨
      (ψ (n - 1) ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∧
        ψ n ∈ Set.Ioc (0 : ℝ) Real.pi) ∨
      (ψ (n - 1) ∈ Set.Ioc (0 : ℝ) Real.pi ∧
        ψ n ∈ Set.Ioo (-Real.pi) (0 : ℝ)) := by
  have hn_mem : n ∈ Finset.Ico a b :=
    Nat.mem_Ico_of_mem_Ioo_right hn hm
  have hpred_mem : n - 1 ∈ Finset.Ico a b :=
    Nat.pred_mem_Ico_of_mem_Ioo_right hn hm
  have hn_side :
      ψ n ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∨
        ψ n ∈ Set.Ioc (0 : ℝ) Real.pi :=
    Real.sequence_mem_neg_side_or_pos_side_of_mem_reducedArc_sep
      ψ hλ_pos hn_mem hψ_mem hψ_sep
  have hpred_side :
      ψ (n - 1) ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∨
        ψ (n - 1) ∈ Set.Ioc (0 : ℝ) Real.pi :=
    Real.sequence_mem_neg_side_or_pos_side_of_mem_reducedArc_sep
      ψ hλ_pos hpred_mem hψ_mem hψ_sep
  match hpred_side with
  | Or.inl hpred_neg =>
      match hn_side with
      | Or.inl hn_neg =>
          exact Or.inl ⟨hpred_neg, hn_neg⟩
      | Or.inr hn_pos =>
          exact Or.inr (Or.inr (Or.inl ⟨hpred_neg, hn_pos⟩))
  | Or.inr hpred_pos =>
      match hn_side with
      | Or.inl hn_neg =>
          exact Or.inr (Or.inr (Or.inr ⟨hpred_pos, hn_neg⟩))
      | Or.inr hn_pos =>
          exact Or.inr (Or.inl ⟨hpred_pos, hn_pos⟩)

/-- A monotone sequence cannot move from the positive side to the negative side
across one adjacent step. -/
theorem Real.monotoneOn_forbids_adjacent_pos_to_neg
    (ψ : ℕ → ℝ)
    {a b m n : ℕ}
    (hn : n ∈ Finset.Ioo a m)
    (hm : m ∈ Finset.Icc a b)
    (hψ_mono : MonotoneOn ψ (Finset.Ico a b : Set ℕ))
    (hpred_pos : ψ (n - 1) ∈ Set.Ioc (0 : ℝ) Real.pi)
    (hn_neg : ψ n ∈ Set.Ioo (-Real.pi) (0 : ℝ)) :
    False := by
  have hn_mem : n ∈ Finset.Ico a b :=
    Nat.mem_Ico_of_mem_Ioo_right hn hm
  have hpred_mem : n - 1 ∈ Finset.Ico a b :=
    Nat.pred_mem_Ico_of_mem_Ioo_right hn hm
  have hpred_le_n : n - 1 ≤ n :=
    Nat.sub_le n 1
  have hmono_step : ψ (n - 1) ≤ ψ n :=
    hψ_mono hpred_mem hn_mem hpred_le_n
  have hzero_lt_n : 0 < ψ n :=
    lt_of_lt_of_le hpred_pos.1 hmono_step
  exact (not_lt_of_ge hn_neg.2.le) hzero_lt_n

/-- An antitone sequence cannot move from the negative side to the positive side
across one adjacent step. -/
theorem Real.antitoneOn_forbids_adjacent_neg_to_pos
    (ψ : ℕ → ℝ)
    {a b m n : ℕ}
    (hn : n ∈ Finset.Ioo a m)
    (hm : m ∈ Finset.Icc a b)
    (hψ_anti : AntitoneOn ψ (Finset.Ico a b : Set ℕ))
    (hpred_neg : ψ (n - 1) ∈ Set.Ioo (-Real.pi) (0 : ℝ))
    (hn_pos : ψ n ∈ Set.Ioc (0 : ℝ) Real.pi) :
    False := by
  have hn_mem : n ∈ Finset.Ico a b :=
    Nat.mem_Ico_of_mem_Ioo_right hn hm
  have hpred_mem : n - 1 ∈ Finset.Ico a b :=
    Nat.pred_mem_Ico_of_mem_Ioo_right hn hm
  have hpred_le_n : n - 1 ≤ n :=
    Nat.sub_le n 1
  have hanti_step : ψ n ≤ ψ (n - 1) :=
    hψ_anti hpred_mem hn_mem hpred_le_n
  have hzero_lt_pred : 0 < ψ (n - 1) :=
    lt_of_lt_of_le hn_pos.1 hanti_step
  exact (not_lt_of_ge hpred_neg.2.le) hzero_lt_pred

/-- Adjacent side classification for a monotone sequence: same-side or
negative-to-positive crossing. -/
theorem Real.monotoneOn_adjacent_side_cases_of_mem_Ioo_sep
    (ψ : ℕ → ℝ)
    {a b m n : ℕ}
    {λ : ℝ}
    (hλ_pos : 0 < λ)
    (hn : n ∈ Finset.Ioo a m)
    (hm : m ∈ Finset.Icc a b)
    (hψ_mem :
      ∀ k : ℕ,
        k ∈ Finset.Ico a b →
          ψ k ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_mono : MonotoneOn ψ (Finset.Ico a b : Set ℕ))
    (hψ_sep :
      ∀ k : ℕ,
        k ∈ Finset.Ico a b →
          λ ≤ ‖ψ k‖) :
    (ψ (n - 1) ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∧
        ψ n ∈ Set.Ioo (-Real.pi) (0 : ℝ)) ∨
      (ψ (n - 1) ∈ Set.Ioc (0 : ℝ) Real.pi ∧
        ψ n ∈ Set.Ioc (0 : ℝ) Real.pi) ∨
      (ψ (n - 1) ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∧
        ψ n ∈ Set.Ioc (0 : ℝ) Real.pi) := by
  have hcases :=
    Real.adjacent_mem_side_cases_of_mem_Ioo_sep
      ψ hλ_pos hn hm hψ_mem hψ_sep
  match hcases with
  | Or.inl hneg_neg =>
      exact Or.inl hneg_neg
  | Or.inr hrest =>
      match hrest with
      | Or.inl hpos_pos =>
          exact Or.inr (Or.inl hpos_pos)
      | Or.inr hcross =>
          match hcross with
          | Or.inl hneg_pos =>
              exact Or.inr (Or.inr hneg_pos)
          | Or.inr hpos_neg =>
              exact False.elim
                (Real.monotoneOn_forbids_adjacent_pos_to_neg
                  ψ hn hm hψ_mono hpos_neg.1 hpos_neg.2)

/-- Adjacent side classification for an antitone sequence: same-side or
positive-to-negative crossing. -/
theorem Real.antitoneOn_adjacent_side_cases_of_mem_Ioo_sep
    (ψ : ℕ → ℝ)
    {a b m n : ℕ}
    {λ : ℝ}
    (hλ_pos : 0 < λ)
    (hn : n ∈ Finset.Ioo a m)
    (hm : m ∈ Finset.Icc a b)
    (hψ_mem :
      ∀ k : ℕ,
        k ∈ Finset.Ico a b →
          ψ k ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_anti : AntitoneOn ψ (Finset.Ico a b : Set ℕ))
    (hψ_sep :
      ∀ k : ℕ,
        k ∈ Finset.Ico a b →
          λ ≤ ‖ψ k‖) :
    (ψ (n - 1) ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∧
        ψ n ∈ Set.Ioo (-Real.pi) (0 : ℝ)) ∨
      (ψ (n - 1) ∈ Set.Ioc (0 : ℝ) Real.pi ∧
        ψ n ∈ Set.Ioc (0 : ℝ) Real.pi) ∨
      (ψ (n - 1) ∈ Set.Ioc (0 : ℝ) Real.pi ∧
        ψ n ∈ Set.Ioo (-Real.pi) (0 : ℝ)) := by
  have hcases :=
    Real.adjacent_mem_side_cases_of_mem_Ioo_sep
      ψ hλ_pos hn hm hψ_mem hψ_sep
  match hcases with
  | Or.inl hneg_neg =>
      exact Or.inl hneg_neg
  | Or.inr hrest =>
      match hrest with
      | Or.inl hpos_pos =>
          exact Or.inr (Or.inl hpos_pos)
      | Or.inr hcross =>
          match hcross with
          | Or.inl hneg_pos =>
              exact False.elim
                (Real.antitoneOn_forbids_adjacent_neg_to_pos
                  ψ hn hm hψ_anti hneg_pos.1 hneg_pos.2)
          | Or.inr hpos_neg =>
              exact Or.inr (Or.inr hpos_neg)

/-- A monotone separated sequence has at most one negative-to-positive adjacent
crossing. -/
theorem Real.monotoneOn_forbids_two_adjacent_neg_to_pos_crossings
    (ψ : ℕ → ℝ)
    {a b m i j : ℕ}
    (hi : i ∈ Finset.Ioo a m)
    (hj : j ∈ Finset.Ioo a m)
    (hm : m ∈ Finset.Icc a b)
    (hij : i < j)
    (hψ_mono : MonotoneOn ψ (Finset.Ico a b : Set ℕ))
    (hi_cross :
      ψ (i - 1) ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∧
        ψ i ∈ Set.Ioc (0 : ℝ) Real.pi)
    (hj_cross :
      ψ (j - 1) ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∧
        ψ j ∈ Set.Ioc (0 : ℝ) Real.pi) :
    False := by
  have hi_mem : i ∈ Finset.Ico a b :=
    Nat.mem_Ico_of_mem_Ioo_right hi hm
  have hj_pred_mem : j - 1 ∈ Finset.Ico a b :=
    Nat.pred_mem_Ico_of_mem_Ioo_right hj hm
  have hi_le_jpred : i ≤ j - 1 :=
    Nat.le_pred_of_lt hij
  have hmono_step : ψ i ≤ ψ (j - 1) :=
    hψ_mono hi_mem hj_pred_mem hi_le_jpred
  have hzero_lt_jpred : 0 < ψ (j - 1) :=
    lt_of_lt_of_le hi_cross.2.1 hmono_step
  exact (not_lt_of_ge hj_cross.1.2.le) hzero_lt_jpred

/-- An antitone separated sequence has at most one positive-to-negative adjacent
crossing. -/
theorem Real.antitoneOn_forbids_two_adjacent_pos_to_neg_crossings
    (ψ : ℕ → ℝ)
    {a b m i j : ℕ}
    (hi : i ∈ Finset.Ioo a m)
    (hj : j ∈ Finset.Ioo a m)
    (hm : m ∈ Finset.Icc a b)
    (hij : i < j)
    (hψ_anti : AntitoneOn ψ (Finset.Ico a b : Set ℕ))
    (hi_cross :
      ψ (i - 1) ∈ Set.Ioc (0 : ℝ) Real.pi ∧
        ψ i ∈ Set.Ioo (-Real.pi) (0 : ℝ))
    (hj_cross :
      ψ (j - 1) ∈ Set.Ioc (0 : ℝ) Real.pi ∧
        ψ j ∈ Set.Ioo (-Real.pi) (0 : ℝ)) :
    False := by
  have hi_mem : i ∈ Finset.Ico a b :=
    Nat.mem_Ico_of_mem_Ioo_right hi hm
  have hj_pred_mem : j - 1 ∈ Finset.Ico a b :=
    Nat.pred_mem_Ico_of_mem_Ioo_right hj hm
  have hi_le_jpred : i ≤ j - 1 :=
    Nat.le_pred_of_lt hij
  have hanti_step : ψ (j - 1) ≤ ψ i :=
    hψ_anti hi_mem hj_pred_mem hi_le_jpred
  have hzero_lt_i : 0 < ψ i :=
    lt_of_lt_of_le hj_cross.1.1 hanti_step
  exact (not_lt_of_ge hi_cross.2.2.le) hzero_lt_i

/-- Negative-to-positive adjacent crossing predicate. -/
def Real.adjacentNegToPosCrossing
    (ψ : ℕ → ℝ)
    (n : ℕ) : Prop :=
  ψ (n - 1) ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∧
    ψ n ∈ Set.Ioc (0 : ℝ) Real.pi

/-- Positive-to-negative adjacent crossing predicate. -/
def Real.adjacentPosToNegCrossing
    (ψ : ℕ → ℝ)
    (n : ℕ) : Prop :=
  ψ (n - 1) ∈ Set.Ioc (0 : ℝ) Real.pi ∧
    ψ n ∈ Set.Ioo (-Real.pi) (0 : ℝ)

/-- The expanded form of `adjacentNegToPosCrossing`. -/
theorem Real.adjacentNegToPosCrossing_iff
    (ψ : ℕ → ℝ)
    (n : ℕ) :
    Real.adjacentNegToPosCrossing ψ n ↔
      ψ (n - 1) ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∧
        ψ n ∈ Set.Ioc (0 : ℝ) Real.pi :=
  Iff.rfl

/-- The expanded form of `adjacentPosToNegCrossing`. -/
theorem Real.adjacentPosToNegCrossing_iff
    (ψ : ℕ → ℝ)
    (n : ℕ) :
    Real.adjacentPosToNegCrossing ψ n ↔
      ψ (n - 1) ∈ Set.Ioc (0 : ℝ) Real.pi ∧
        ψ n ∈ Set.Ioo (-Real.pi) (0 : ℝ) :=
  Iff.rfl

/-- Monotone negative-to-positive crossings are unique on the summation
interval. -/
theorem Real.monotoneOn_adjacentNegToPosCrossing_subsingleton
    (ψ : ℕ → ℝ)
    {a b m : ℕ}
    (hm : m ∈ Finset.Icc a b)
    (hψ_mono : MonotoneOn ψ (Finset.Ico a b : Set ℕ)) :
    Set.Subsingleton
      {n : ℕ |
        n ∈ (Finset.Ioo a m : Set ℕ) ∧
          Real.adjacentNegToPosCrossing ψ n} := by
  intro i hi j hj
  have hi_mem : i ∈ Finset.Ioo a m :=
    hi.1
  have hj_mem : j ∈ Finset.Ioo a m :=
    hj.1
  have hi_cross :
      ψ (i - 1) ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∧
        ψ i ∈ Set.Ioc (0 : ℝ) Real.pi :=
    hi.2
  have hj_cross :
      ψ (j - 1) ∈ Set.Ioo (-Real.pi) (0 : ℝ) ∧
        ψ j ∈ Set.Ioc (0 : ℝ) Real.pi :=
    hj.2
  match lt_trichotomy i j with
  | Or.inl hij =>
      exact False.elim
        (Real.monotoneOn_forbids_two_adjacent_neg_to_pos_crossings
          ψ hi_mem hj_mem hm hij hψ_mono hi_cross hj_cross)
  | Or.inr hge =>
      match hge with
      | Or.inl hij =>
          exact hij
      | Or.inr hji =>
          exact Eq.symm
            (False.elim
              (Real.monotoneOn_forbids_two_adjacent_neg_to_pos_crossings
                ψ hj_mem hi_mem hm hji hψ_mono hj_cross hi_cross))

/-- Antitone positive-to-negative crossings are unique on the summation
interval. -/
theorem Real.antitoneOn_adjacentPosToNegCrossing_subsingleton
    (ψ : ℕ → ℝ)
    {a b m : ℕ}
    (hm : m ∈ Finset.Icc a b)
    (hψ_anti : AntitoneOn ψ (Finset.Ico a b : Set ℕ)) :
    Set.Subsingleton
      {n : ℕ |
        n ∈ (Finset.Ioo a m : Set ℕ) ∧
          Real.adjacentPosToNegCrossing ψ n} := by
  intro i hi j hj
  have hi_mem : i ∈ Finset.Ioo a m :=
    hi.1
  have hj_mem : j ∈ Finset.Ioo a m :=
    hj.1
  have hi_cross :
      ψ (i - 1) ∈ Set.Ioc (0 : ℝ) Real.pi ∧
        ψ i ∈ Set.Ioo (-Real.pi) (0 : ℝ) :=
    hi.2
  have hj_cross :
      ψ (j - 1) ∈ Set.Ioc (0 : ℝ) Real.pi ∧
        ψ j ∈ Set.Ioo (-Real.pi) (0 : ℝ) :=
    hj.2
  match lt_trichotomy i j with
  | Or.inl hij =>
      exact False.elim
        (Real.antitoneOn_forbids_two_adjacent_pos_to_neg_crossings
          ψ hi_mem hj_mem hm hij hψ_anti hi_cross hj_cross)
  | Or.inr hge =>
      match hge with
      | Or.inl hij =>
          exact hij
      | Or.inr hji =>
          exact Eq.symm
            (False.elim
              (Real.antitoneOn_forbids_two_adjacent_pos_to_neg_crossings
                ψ hj_mem hi_mem hm hji hψ_anti hj_cross hi_cross))

/-- A monotone separated reduced sequence is either entirely on one side on
`Ico a m`, or it has a first positive index giving a negative block followed by
a positive block. -/
theorem Real.monotoneOn_reducedArc_side_decomposition
    (ψ : ℕ → ℝ)
    {a b m : ℕ}
    {λ : ℝ}
    (hm : m ∈ Finset.Icc a b)
    (hλ_pos : 0 < λ)
    (hψ_mem :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ψ n ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_mono : MonotoneOn ψ (Finset.Ico a b : Set ℕ))
    (hψ_sep :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          λ ≤ ‖ψ n‖) :
    (∀ n : ℕ,
        n ∈ Finset.Ico a m →
          ψ n ∈ Set.Ioc (-Real.pi) (0 : ℝ)) ∨
      (∀ n : ℕ,
        n ∈ Finset.Ico a m →
          ψ n ∈ Set.Ioc (0 : ℝ) Real.pi) ∨
      ∃ c : ℕ,
        a < c ∧ c < m ∧
          (∀ n : ℕ,
            n ∈ Finset.Ico a c →
              ψ n ∈ Set.Ioc (-Real.pi) (0 : ℝ)) ∧
          (∀ n : ℕ,
            n ∈ Finset.Ico c m →
              ψ n ∈ Set.Ioc (0 : ℝ) Real.pi) := by
  classical
  let positives : Finset ℕ :=
    (Finset.Ico a m).filter
      (fun n : ℕ => ψ n ∈ Set.Ioc (0 : ℝ) Real.pi)
  have hm_bounds : a ≤ m ∧ m ≤ b :=
    Finset.mem_Icc.mp hm
  by_cases hpos_nonempty : positives.Nonempty
  · let c : ℕ := positives.min' hpos_nonempty
    have hc_filter : c ∈ positives :=
      Finset.min'_mem positives hpos_nonempty
    have hc_data :
        c ∈ Finset.Ico a m ∧
          ψ c ∈ Set.Ioc (0 : ℝ) Real.pi :=
      Finset.mem_filter.mp hc_filter
    have hc_bounds : a ≤ c ∧ c < m :=
      Finset.mem_Ico.mp hc_data.1
    by_cases hca : c = a
    · exact Or.inr (Or.inl
        (fun n hn =>
          let hn_bounds : a ≤ n ∧ n < m := Finset.mem_Ico.mp hn
          let hn_mem_original : n ∈ Finset.Ico a b :=
            Finset.mem_Ico.mpr
              ⟨hn_bounds.1, lt_of_lt_of_le hn_bounds.2 hm_bounds.2⟩
          let hc_mem_original : c ∈ Finset.Ico a b :=
            Finset.mem_Ico.mpr
              ⟨hc_bounds.1, lt_of_lt_of_le hc_bounds.2 hm_bounds.2⟩
          let hc_le_n : c ≤ n :=
            Eq.subst
              (motive := fun r : ℕ => r ≤ n)
              hca.symm
              hn_bounds.1
          let hmono_step : ψ c ≤ ψ n :=
            hψ_mono hc_mem_original hn_mem_original hc_le_n
          ⟨lt_of_lt_of_le hc_data.2.1 hmono_step,
            (hψ_mem n hn_mem_original).2⟩))
    · have hac : a < c :=
        lt_of_le_of_ne hc_bounds.1 (Ne.symm hca)
      exact Or.inr (Or.inr
        ⟨c, hac, hc_bounds.2,
          (fun n hn =>
            let hn_bounds : a ≤ n ∧ n < c := Finset.mem_Ico.mp hn
            let hn_mem_am : n ∈ Finset.Ico a m :=
              Finset.mem_Ico.mpr
                ⟨hn_bounds.1, lt_trans hn_bounds.2 hc_bounds.2⟩
            let hn_mem_original : n ∈ Finset.Ico a b :=
              Finset.mem_Ico.mpr
                ⟨hn_bounds.1,
                  lt_of_lt_of_le (lt_trans hn_bounds.2 hc_bounds.2)
                    hm_bounds.2⟩
            let hnot_pos :
                ¬ ψ n ∈ Set.Ioc (0 : ℝ) Real.pi :=
              fun hn_pos =>
                let hn_filter : n ∈ positives :=
                  Finset.mem_filter.mpr ⟨hn_mem_am, hn_pos⟩
                let hc_le_n : c ≤ n :=
                  Finset.min'_le positives n hn_filter
                (not_lt_of_ge hc_le_n) hn_bounds.2
            Real.mem_neg_side_of_not_mem_pos_side_of_mem_reducedArc_sep
              hλ_pos (hψ_mem n hn_mem_original)
              (hψ_sep n hn_mem_original) hnot_pos),
          (fun n hn =>
            let hn_bounds : c ≤ n ∧ n < m := Finset.mem_Ico.mp hn
            let hn_mem_original : n ∈ Finset.Ico a b :=
              Finset.mem_Ico.mpr
                ⟨le_trans hc_bounds.1 hn_bounds.1,
                  lt_of_lt_of_le hn_bounds.2 hm_bounds.2⟩
            let hc_mem_original : c ∈ Finset.Ico a b :=
              Finset.mem_Ico.mpr
                ⟨hc_bounds.1, lt_of_lt_of_le hc_bounds.2 hm_bounds.2⟩
            let hmono_step : ψ c ≤ ψ n :=
              hψ_mono hc_mem_original hn_mem_original hn_bounds.1
            ⟨lt_of_lt_of_le hc_data.2.1 hmono_step,
              (hψ_mem n hn_mem_original).2⟩)⟩)
  · exact Or.inl
      (fun n hn =>
        let hn_bounds : a ≤ n ∧ n < m := Finset.mem_Ico.mp hn
        let hn_mem_original : n ∈ Finset.Ico a b :=
          Finset.mem_Ico.mpr
            ⟨hn_bounds.1, lt_of_lt_of_le hn_bounds.2 hm_bounds.2⟩
        let hnot_pos :
            ¬ ψ n ∈ Set.Ioc (0 : ℝ) Real.pi :=
          fun hn_pos =>
            hpos_nonempty ⟨n, Finset.mem_filter.mpr ⟨hn, hn_pos⟩⟩
        Real.mem_neg_side_of_not_mem_pos_side_of_mem_reducedArc_sep
          hλ_pos (hψ_mem n hn_mem_original)
          (hψ_sep n hn_mem_original) hnot_pos)

/-- An antitone separated reduced sequence is either entirely on one side on
`Ico a m`, or it has a first negative index giving a positive block followed by
a negative block. -/
theorem Real.antitoneOn_reducedArc_side_decomposition
    (ψ : ℕ → ℝ)
    {a b m : ℕ}
    {λ : ℝ}
    (hm : m ∈ Finset.Icc a b)
    (hλ_pos : 0 < λ)
    (hψ_mem :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ψ n ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_anti : AntitoneOn ψ (Finset.Ico a b : Set ℕ))
    (hψ_sep :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          λ ≤ ‖ψ n‖) :
    (∀ n : ℕ,
        n ∈ Finset.Ico a m →
          ψ n ∈ Set.Ioc (0 : ℝ) Real.pi) ∨
      (∀ n : ℕ,
        n ∈ Finset.Ico a m →
          ψ n ∈ Set.Ioc (-Real.pi) (0 : ℝ)) ∨
      ∃ c : ℕ,
        a < c ∧ c < m ∧
          (∀ n : ℕ,
            n ∈ Finset.Ico a c →
              ψ n ∈ Set.Ioc (0 : ℝ) Real.pi) ∧
          (∀ n : ℕ,
            n ∈ Finset.Ico c m →
              ψ n ∈ Set.Ioc (-Real.pi) (0 : ℝ)) := by
  classical
  let negatives : Finset ℕ :=
    (Finset.Ico a m).filter
      (fun n : ℕ => ψ n ∈ Set.Ioc (-Real.pi) (0 : ℝ))
  have hm_bounds : a ≤ m ∧ m ≤ b :=
    Finset.mem_Icc.mp hm
  by_cases hneg_nonempty : negatives.Nonempty
  · let c : ℕ := negatives.min' hneg_nonempty
    have hc_filter : c ∈ negatives :=
      Finset.min'_mem negatives hneg_nonempty
    have hc_data :
        c ∈ Finset.Ico a m ∧
          ψ c ∈ Set.Ioc (-Real.pi) (0 : ℝ) :=
      Finset.mem_filter.mp hc_filter
    have hc_bounds : a ≤ c ∧ c < m :=
      Finset.mem_Ico.mp hc_data.1
    by_cases hca : c = a
    · exact Or.inr (Or.inl
        (fun n hn =>
          let hn_bounds : a ≤ n ∧ n < m := Finset.mem_Ico.mp hn
          let hn_mem_original : n ∈ Finset.Ico a b :=
            Finset.mem_Ico.mpr
              ⟨hn_bounds.1, lt_of_lt_of_le hn_bounds.2 hm_bounds.2⟩
          let hc_mem_original : c ∈ Finset.Ico a b :=
            Finset.mem_Ico.mpr
              ⟨hc_bounds.1, lt_of_lt_of_le hc_bounds.2 hm_bounds.2⟩
          let hc_le_n : c ≤ n :=
            Eq.subst
              (motive := fun r : ℕ => r ≤ n)
              hca.symm
              hn_bounds.1
          let hanti_step : ψ n ≤ ψ c :=
            hψ_anti hc_mem_original hn_mem_original hc_le_n
          ⟨(hψ_mem n hn_mem_original).1,
            le_trans hanti_step hc_data.2.2⟩))
    · have hac : a < c :=
        lt_of_le_of_ne hc_bounds.1 (Ne.symm hca)
      exact Or.inr (Or.inr
        ⟨c, hac, hc_bounds.2,
          (fun n hn =>
            let hn_bounds : a ≤ n ∧ n < c := Finset.mem_Ico.mp hn
            let hn_mem_am : n ∈ Finset.Ico a m :=
              Finset.mem_Ico.mpr
                ⟨hn_bounds.1, lt_trans hn_bounds.2 hc_bounds.2⟩
            let hn_mem_original : n ∈ Finset.Ico a b :=
              Finset.mem_Ico.mpr
                ⟨hn_bounds.1,
                  lt_of_lt_of_le (lt_trans hn_bounds.2 hc_bounds.2)
                    hm_bounds.2⟩
            let hnot_neg :
                ¬ ψ n ∈ Set.Ioc (-Real.pi) (0 : ℝ) :=
              fun hn_neg =>
                let hn_filter : n ∈ negatives :=
                  Finset.mem_filter.mpr ⟨hn_mem_am, hn_neg⟩
                let hc_le_n : c ≤ n :=
                  Finset.min'_le negatives n hn_filter
                (not_lt_of_ge hc_le_n) hn_bounds.2
            Real.mem_pos_side_of_not_mem_neg_side_of_mem_reducedArc_sep
              hλ_pos (hψ_mem n hn_mem_original)
              (hψ_sep n hn_mem_original) hnot_neg),
          (fun n hn =>
            let hn_bounds : c ≤ n ∧ n < m := Finset.mem_Ico.mp hn
            let hn_mem_original : n ∈ Finset.Ico a b :=
              Finset.mem_Ico.mpr
                ⟨le_trans hc_bounds.1 hn_bounds.1,
                  lt_of_lt_of_le hn_bounds.2 hm_bounds.2⟩
            let hc_mem_original : c ∈ Finset.Ico a b :=
              Finset.mem_Ico.mpr
                ⟨hc_bounds.1, lt_of_lt_of_le hc_bounds.2 hm_bounds.2⟩
            let hanti_step : ψ n ≤ ψ c :=
              hψ_anti hc_mem_original hn_mem_original hn_bounds.1
            ⟨(hψ_mem n hn_mem_original).1,
              le_trans hanti_step hc_data.2.2⟩)⟩)
  · exact Or.inl
      (fun n hn =>
        let hn_bounds : a ≤ n ∧ n < m := Finset.mem_Ico.mp hn
        let hn_mem_original : n ∈ Finset.Ico a b :=
          Finset.mem_Ico.mpr
            ⟨hn_bounds.1, lt_of_lt_of_le hn_bounds.2 hm_bounds.2⟩
        let hnot_neg :
            ¬ ψ n ∈ Set.Ioc (-Real.pi) (0 : ℝ) :=
          fun hn_neg =>
            hneg_nonempty ⟨n, Finset.mem_filter.mpr ⟨hn, hn_neg⟩⟩
        Real.mem_pos_side_of_not_mem_neg_side_of_mem_reducedArc_sep
          hλ_pos (hψ_mem n hn_mem_original)
          (hψ_sep n hn_mem_original) hnot_neg)

/-- The imaginary coordinate of a complex number is bounded by its norm. -/
theorem Complex.norm_im_le_norm
    (z : ℂ) :
    ‖z.im‖ ≤ ‖z‖ := by
  calc
    ‖z.im‖ = |z.im| :=
      Real.norm_eq_abs z.im
    _ ≤ Complex.abs z :=
      Complex.abs_im_le_abs z
    _ = ‖z‖ :=
      (Complex.norm_eq_abs z).symm

/-- The reduced inverse-denominator imaginary coordinate is bounded by the
complex norm. -/
theorem Complex.reducedArc_inverseGeometricDenominator_imCoord_norm_le_norm
    (ψ : ℝ) :
    ‖Complex.reducedArc_inverseGeometricDenominator_imCoord ψ‖ ≤
      ‖Complex.reducedArc_inverseGeometricDenominator ψ‖ := by
  exact Complex.norm_im_le_norm
    (Complex.reducedArc_inverseGeometricDenominator ψ)

/-- On a one-sided reduced arc, composing the inverse-chord imaginary coordinate
with a monotone-or-antitone sequence remains monotone-or-antitone. -/
theorem Complex.reducedArc_inverseGeometricDenominator_imCoord_mono_or_anti_on_oneSided
    (ψ : ℕ → ℝ)
    {a b : ℕ}
    {λ L U : ℝ}
    (hλ_pos : 0 < λ)
    (hside : L = (0 : ℝ) ∧ U = Real.pi ∨
      L = -Real.pi ∧ U = (0 : ℝ))
    (hψ_mem :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ψ n ∈ Set.Ioc L U)
    (hψ_mono :
      MonotoneOn (fun n : ℕ => ψ n) (Finset.Ico a b : Set ℕ) ∨
      AntitoneOn (fun n : ℕ => ψ n) (Finset.Ico a b : Set ℕ))
    (hψ_sep :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          λ ≤ ‖ψ n‖) :
    MonotoneOn
        (fun n : ℕ =>
          Complex.reducedArc_inverseGeometricDenominator_imCoord (ψ n))
        (Finset.Ico a b : Set ℕ) ∨
      AntitoneOn
        (fun n : ℕ =>
          Complex.reducedArc_inverseGeometricDenominator_imCoord (ψ n))
        (Finset.Ico a b : Set ℕ) := by
  match hside with
  | Or.inl hpos =>
      have hmem_pos :
          ∀ n : ℕ,
            n ∈ Finset.Ico a b →
              ψ n ∈ Set.Ioc (0 : ℝ) Real.pi := by
        intro n hn
        exact Real.mem_Ioc_zero_pi_of_mem_pos_side hpos (hψ_mem n hn)
      match hψ_mono with
      | Or.inl hmono =>
          exact Or.inr
            (fun i hi j hj hij =>
              Complex.reducedArc_inverseGeometricDenominator_imCoord_antitoneOn_pos
                (hmem_pos i hi) (hmem_pos j hj) (hmono hi hj hij))
      | Or.inr hanti =>
          exact Or.inl
            (fun i hi j hj hij =>
              Complex.reducedArc_inverseGeometricDenominator_imCoord_antitoneOn_pos
                (hmem_pos j hj) (hmem_pos i hi) (hanti hi hj hij))
  | Or.inr hneg =>
      have hmem_neg :
          ∀ n : ℕ,
            n ∈ Finset.Ico a b →
              ψ n ∈ Set.Ioo (-Real.pi) (0 : ℝ) := by
        intro n hn
        exact Real.mem_Ioo_neg_pi_zero_of_mem_neg_side_sep
          hλ_pos hneg (hψ_mem n hn) (hψ_sep n hn)
      match hψ_mono with
      | Or.inl hmono =>
          exact Or.inr
            (fun i hi j hj hij =>
              Complex.reducedArc_inverseGeometricDenominator_imCoord_antitoneOn_neg
                (hmem_neg i hi) (hmem_neg j hj) (hmono hi hj hij))
      | Or.inr hanti =>
          exact Or.inl
            (fun i hi j hj hij =>
              Complex.reducedArc_inverseGeometricDenominator_imCoord_antitoneOn_neg
                (hmem_neg j hj) (hmem_neg i hi) (hanti hi hj hij))

/-- Scalar constant fold used by the one-sided variation endpoint estimate. -/
theorem Real.two_mul_add_two_mul_eq_four_mul
    (x : ℝ) :
    2 * x + 2 * x = 4 * x := by
  have hnum : (2 : ℝ) + 2 = 4 :=
    rfl
  calc
    2 * x + 2 * x = ((2 : ℝ) + 2) * x :=
      (add_mul (2 : ℝ) 2 x).symm
    _ = 4 * x :=
      congrArg (fun r : ℝ => r * x) hnum

/-- Telescope for adjacent forward differences over an open natural interval. -/
theorem Real.sum_Ioo_adjacent_sub_eq_endpoint_sub
    (y : ℕ → ℝ)
    {a m : ℕ}
    (ham : a < m) :
    (∑ n ∈ Finset.Ioo a m, (y n - y (n - 1))) =
      y (m - 1) - y a := by
  have hIoo :
      Finset.Ioo a m = Finset.Ico (a + 1) m :=
    (Finset.Ico_succ_left (a := a) (b := m)).symm
  have hsucc_le : a + 1 ≤ m :=
    Nat.succ_le_of_lt ham
  have htel :
      (∑ n ∈ Finset.Ico (a + 1) m,
        ((fun k : ℕ => y (k - 1)) (n + 1) -
          (fun k : ℕ => y (k - 1)) n)) =
        (fun k : ℕ => y (k - 1)) m -
          (fun k : ℕ => y (k - 1)) (a + 1) :=
    Finset.sum_Ico_eq_sub (fun k : ℕ => y (k - 1)) hsucc_le
  have hleft :
      (∑ n ∈ Finset.Ico (a + 1) m,
        ((fun k : ℕ => y (k - 1)) (n + 1) -
          (fun k : ℕ => y (k - 1)) n)) =
        ∑ n ∈ Finset.Ico (a + 1) m, (y n - y (n - 1)) := by
    exact Finset.sum_congr rfl
      (fun n hn =>
        congrArg
          (fun r : ℝ => r - y (n - 1))
          (congrArg y
            (Eq.trans (Nat.add_succ_sub_one n 0) (add_zero n))))
  have hright :
      (fun k : ℕ => y (k - 1)) m -
          (fun k : ℕ => y (k - 1)) (a + 1) =
        y (m - 1) - y a := by
    exact congrArg
      (fun r : ℝ => y (m - 1) - r)
      (congrArg y
        (Eq.trans (Nat.add_succ_sub_one a 0) (add_zero a)))
  calc
    (∑ n ∈ Finset.Ioo a m, (y n - y (n - 1))) =
        ∑ n ∈ Finset.Ico (a + 1) m, (y n - y (n - 1)) := by
      exact congrArg
        (fun s : Finset ℕ =>
          ∑ n ∈ s, (y n - y (n - 1)))
        hIoo
    _ =
        (∑ n ∈ Finset.Ico (a + 1) m,
          ((fun k : ℕ => y (k - 1)) (n + 1) -
            (fun k : ℕ => y (k - 1)) n)) :=
      hleft.symm
    _ =
        (fun k : ℕ => y (k - 1)) m -
          (fun k : ℕ => y (k - 1)) (a + 1) :=
      htel
    _ = y (m - 1) - y a :=
      hright

/-- Telescope for adjacent backward differences over an open natural interval. -/
theorem Real.sum_Ioo_adjacent_sub_rev_eq_endpoint_sub
    (y : ℕ → ℝ)
    {a m : ℕ}
    (ham : a < m) :
    (∑ n ∈ Finset.Ioo a m, (y (n - 1) - y n)) =
      y a - y (m - 1) := by
  have hneg :
      (∑ n ∈ Finset.Ioo a m, (y (n - 1) - y n)) =
        -∑ n ∈ Finset.Ioo a m, (y n - y (n - 1)) := by
    calc
      (∑ n ∈ Finset.Ioo a m, (y (n - 1) - y n)) =
          ∑ n ∈ Finset.Ioo a m, -(y n - y (n - 1)) := by
        exact Finset.sum_congr rfl
          (fun n hn => (neg_sub (y n) (y (n - 1))).symm)
      _ = -∑ n ∈ Finset.Ioo a m, (y n - y (n - 1)) :=
        Finset.sum_neg_distrib
  have hforward :
      (∑ n ∈ Finset.Ioo a m, (y n - y (n - 1))) =
        y (m - 1) - y a :=
    Real.sum_Ioo_adjacent_sub_eq_endpoint_sub y ham
  calc
    (∑ n ∈ Finset.Ioo a m, (y (n - 1) - y n)) =
        -∑ n ∈ Finset.Ioo a m, (y n - y (n - 1)) :=
      hneg
    _ = -(y (m - 1) - y a) :=
      congrArg Neg.neg hforward
    _ = y a - y (m - 1) :=
      neg_sub (y (m - 1)) (y a)

/-- A real difference is bounded by the sum of endpoint norms. -/
theorem Real.sub_le_norm_add_norm
    (x y : ℝ) :
    x - y ≤ ‖x‖ + ‖y‖ := by
  have hx : x ≤ ‖x‖ :=
    Real.le_norm_self x
  have hy : -y ≤ ‖y‖ := by
    calc
      -y ≤ ‖-y‖ :=
        Real.le_norm_self (-y)
      _ = ‖y‖ :=
        norm_neg y
  have hsum : x + -y ≤ ‖x‖ + ‖y‖ :=
    add_le_add hx hy
  exact Eq.subst
    (motive := fun r : ℝ => r ≤ ‖x‖ + ‖y‖)
    (sub_eq_add_neg x y).symm
    hsum

/-- Monotone finite variation over an open natural interval telescopes to the
endpoint difference. -/
theorem Real.monotoneOn_nat_Ioo_totalVariation_eq_endpoint_sub
    (y : ℕ → ℝ)
    {a b m : ℕ}
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hy : MonotoneOn y (Finset.Ico a b : Set ℕ)) :
    (∑ n ∈ Finset.Ioo a m, ‖y n - y (n - 1)‖) =
      y (m - 1) - y a := by
  have hnorm :
      (∑ n ∈ Finset.Ioo a m, ‖y n - y (n - 1)‖) =
        ∑ n ∈ Finset.Ioo a m, (y n - y (n - 1)) := by
    exact Finset.sum_congr rfl
      (fun n hn =>
        Real.monotoneOn_nat_Ioo_adjacent_norm_eq_sub y hn hm hy)
  exact Eq.trans hnorm
    (Real.sum_Ioo_adjacent_sub_eq_endpoint_sub y ham)

/-- Antitone finite variation over an open natural interval telescopes to the
reverse endpoint difference. -/
theorem Real.antitoneOn_nat_Ioo_totalVariation_eq_endpoint_sub
    (y : ℕ → ℝ)
    {a b m : ℕ}
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hy : AntitoneOn y (Finset.Ico a b : Set ℕ)) :
    (∑ n ∈ Finset.Ioo a m, ‖y n - y (n - 1)‖) =
      y a - y (m - 1) := by
  have hnorm :
      (∑ n ∈ Finset.Ioo a m, ‖y n - y (n - 1)‖) =
        ∑ n ∈ Finset.Ioo a m, (y (n - 1) - y n) := by
    exact Finset.sum_congr rfl
      (fun n hn =>
        Real.antitoneOn_nat_Ioo_adjacent_norm_eq_sub_rev y hn hm hy)
  exact Eq.trans hnorm
    (Real.sum_Ioo_adjacent_sub_rev_eq_endpoint_sub y ham)

/-- Finite total variation of a monotone real sequence is controlled by endpoint
size. -/
theorem Real.monotoneOn_nat_Ioo_totalVariation_le_endpoint_norm
    (y : ℕ → ℝ)
    {a b m : ℕ}
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hy_mono :
      MonotoneOn y (Finset.Ico a b : Set ℕ) ∨
      AntitoneOn y (Finset.Ico a b : Set ℕ)) :
    (∑ n ∈ Finset.Ioo a m, ‖y n - y (n - 1)‖) ≤
      ‖y a‖ + ‖y (m - 1)‖ := by
  match hy_mono with
  | Or.inl hy =>
      have hsum :
          (∑ n ∈ Finset.Ioo a m, ‖y n - y (n - 1)‖) =
            y (m - 1) - y a :=
        Real.monotoneOn_nat_Ioo_totalVariation_eq_endpoint_sub y ham hm hy
      have hbound :
          y (m - 1) - y a ≤ ‖y (m - 1)‖ + ‖y a‖ :=
        Real.sub_le_norm_add_norm (y (m - 1)) (y a)
      have hcomm :
          ‖y (m - 1)‖ + ‖y a‖ = ‖y a‖ + ‖y (m - 1)‖ :=
        add_comm ‖y (m - 1)‖ ‖y a‖
      exact Eq.subst
        (motive := fun r : ℝ =>
          (∑ n ∈ Finset.Ioo a m, ‖y n - y (n - 1)‖) ≤ r)
        hcomm
        (Eq.subst
          (motive := fun r : ℝ =>
            r ≤ ‖y (m - 1)‖ + ‖y a‖)
          hsum.symm
          hbound)
  | Or.inr hy =>
      have hsum :
          (∑ n ∈ Finset.Ioo a m, ‖y n - y (n - 1)‖) =
            y a - y (m - 1) :=
        Real.antitoneOn_nat_Ioo_totalVariation_eq_endpoint_sub y ham hm hy
      have hbound :
          y a - y (m - 1) ≤ ‖y a‖ + ‖y (m - 1)‖ :=
        Real.sub_le_norm_add_norm (y a) (y (m - 1))
      exact Eq.subst
        (motive := fun r : ℝ =>
          r ≤ ‖y a‖ + ‖y (m - 1)‖)
        hsum.symm
        hbound

/-- One-sided inverse-chord variation after reducing to the vertical-line
imaginary coordinate. -/
theorem Complex.reducedArc_inverseGeometricDenominator_oneSided_variation_bound_from_imCoord
    (ψ : ℕ → ℝ)
    {a b m : ℕ}
    {λ : ℝ}
    {L U : ℝ}
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hλ_pos : 0 < λ)
    (hside : L = (0 : ℝ) ∧ U = Real.pi ∨
      L = -Real.pi ∧ U = (0 : ℝ))
    (hψ_mem :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ψ n ∈ Set.Ioc L U)
    (hψ_mono :
      MonotoneOn (fun n : ℕ => ψ n) (Finset.Ico a b : Set ℕ) ∨
      AntitoneOn (fun n : ℕ => ψ n) (Finset.Ico a b : Set ℕ))
    (hψ_sep :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          λ ≤ ‖ψ n‖)
    (hψ_den :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖Complex.reducedArc_inverseGeometricDenominator (ψ n)‖ ≤
            2 * λ⁻¹) :
    (∑ n ∈ Finset.Ioo a m,
      ‖Complex.reducedArc_inverseGeometricDenominator (ψ n) -
        Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖) ≤
        4 * λ⁻¹ := by
  let y : ℕ → ℝ :=
    fun n : ℕ =>
      Complex.reducedArc_inverseGeometricDenominator_imCoord (ψ n)
  have hymono :
      MonotoneOn y (Finset.Ico a b : Set ℕ) ∨
        AntitoneOn y (Finset.Ico a b : Set ℕ) :=
    Complex.reducedArc_inverseGeometricDenominator_imCoord_mono_or_anti_on_oneSided
      ψ hλ_pos hside hψ_mem hψ_mono hψ_sep
  have hcomplex_to_y :
      (∑ n ∈ Finset.Ioo a m,
        ‖Complex.reducedArc_inverseGeometricDenominator (ψ n) -
          Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖) =
        ∑ n ∈ Finset.Ioo a m, ‖y n - y (n - 1)‖ := by
    exact Finset.sum_congr rfl
      (fun n hn =>
        let hn_Ico : n ∈ Finset.Ico a b :=
          Nat.mem_Ico_of_mem_Ioo_right hn hm
        let hpred_Ico : n - 1 ∈ Finset.Ico a b :=
          Nat.pred_mem_Ico_of_mem_Ioo_right hn hm
        let hn_data :
            ψ n ∈ Set.Ioc (-Real.pi) Real.pi ∧ ψ n ≠ 0 :=
          Real.oneSided_reducedArc_mem_and_ne_of_sep
            ψ hλ_pos hside hn_Ico hψ_mem hψ_sep
        let hpred_data :
            ψ (n - 1) ∈ Set.Ioc (-Real.pi) Real.pi ∧
              ψ (n - 1) ≠ 0 :=
          Real.oneSided_reducedArc_mem_and_ne_of_sep
            ψ hλ_pos hside hpred_Ico hψ_mem hψ_sep
        Complex.reducedArc_inverseGeometricDenominator_adjacent_norm_eq_imCoord
          ψ hn_data.1 hpred_data.1 hn_data.2 hpred_data.2)
  have hreal_variation :
      (∑ n ∈ Finset.Ioo a m, ‖y n - y (n - 1)‖) ≤
        ‖y a‖ + ‖y (m - 1)‖ :=
    Real.monotoneOn_nat_Ioo_totalVariation_le_endpoint_norm
      y ham hm hymono
  have hm_bounds : a ≤ m ∧ m ≤ b :=
    Finset.mem_Icc.mp hm
  have ha_mem : a ∈ Finset.Ico a b :=
    Finset.mem_Ico.mpr
      ⟨le_rfl, lt_of_lt_of_le ham hm_bounds.2⟩
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
  have ha_y :
      ‖y a‖ ≤ 2 * λ⁻¹ := by
    exact le_trans
      (Complex.reducedArc_inverseGeometricDenominator_imCoord_norm_le_norm
        (ψ a))
      (hψ_den a ha_mem)
  have hm_y :
      ‖y (m - 1)‖ ≤ 2 * λ⁻¹ := by
    exact le_trans
      (Complex.reducedArc_inverseGeometricDenominator_imCoord_norm_le_norm
        (ψ (m - 1)))
      (hψ_den (m - 1) hm_pred_mem)
  have hendpoint :
      ‖y a‖ + ‖y (m - 1)‖ ≤
        2 * λ⁻¹ + 2 * λ⁻¹ :=
    add_le_add ha_y hm_y
  have hendpoint_four :
      ‖y a‖ + ‖y (m - 1)‖ ≤ 4 * λ⁻¹ :=
    Eq.subst
      (motive := fun r : ℝ =>
        ‖y a‖ + ‖y (m - 1)‖ ≤ r)
      (Real.two_mul_add_two_mul_eq_four_mul λ⁻¹)
      hendpoint
  have hy_bound :
      (∑ n ∈ Finset.Ioo a m, ‖y n - y (n - 1)‖) ≤
        4 * λ⁻¹ :=
    le_trans hreal_variation hendpoint_four
  exact Eq.subst
    (motive := fun r : ℝ => r ≤ 4 * λ⁻¹)
    hcomplex_to_y.symm
    hy_bound

/-- Variation bound for the reduced inverse denominator on one side of the
singularity at zero. -/
theorem Complex.reducedArc_inverseGeometricDenominator_oneSided_variation_bound
    (ψ : ℕ → ℝ)
    {a b m : ℕ}
    {λ : ℝ}
    {L U : ℝ}
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hλ_pos : 0 < λ)
    (hside : L = (0 : ℝ) ∧ U = Real.pi ∨
      L = -Real.pi ∧ U = (0 : ℝ))
    (hψ_mem :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ψ n ∈ Set.Ioc L U)
    (hψ_mono :
      MonotoneOn (fun n : ℕ => ψ n) (Finset.Ico a b : Set ℕ) ∨
      AntitoneOn (fun n : ℕ => ψ n) (Finset.Ico a b : Set ℕ))
    (hψ_sep :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          λ ≤ ‖ψ n‖)
    (hψ_den :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖Complex.reducedArc_inverseGeometricDenominator (ψ n)‖ ≤
            2 * λ⁻¹) :
    (∑ n ∈ Finset.Ioo a m,
      ‖Complex.reducedArc_inverseGeometricDenominator (ψ n) -
        Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖) ≤
        4 * λ⁻¹ := by
  exact
    Complex.reducedArc_inverseGeometricDenominator_oneSided_variation_bound_from_imCoord
      ψ ham hm hλ_pos hside hψ_mem hψ_mono hψ_sep hψ_den

/-- A single adjacent inverse-denominator jump is bounded by the two endpoint
denominator bounds. -/
theorem Complex.reducedArc_inverseGeometricDenominator_adjacent_norm_le_four_inv
    (ψ : ℕ → ℝ)
    {a b m n : ℕ}
    {λ : ℝ}
    (hn : n ∈ Finset.Ioo a m)
    (hm : m ∈ Finset.Icc a b)
    (hψ_den :
      ∀ k : ℕ,
        k ∈ Finset.Ico a b →
          ‖Complex.reducedArc_inverseGeometricDenominator (ψ k)‖ ≤
            2 * λ⁻¹) :
    ‖Complex.reducedArc_inverseGeometricDenominator (ψ n) -
      Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖ ≤
        4 * λ⁻¹ := by
  have hn_mem : n ∈ Finset.Ico a b :=
    Nat.mem_Ico_of_mem_Ioo_right hn hm
  have hpred_mem : n - 1 ∈ Finset.Ico a b :=
    Nat.pred_mem_Ico_of_mem_Ioo_right hn hm
  have hn_bound :
      ‖Complex.reducedArc_inverseGeometricDenominator (ψ n)‖ ≤
        2 * λ⁻¹ :=
    hψ_den n hn_mem
  have hpred_bound :
      ‖Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖ ≤
        2 * λ⁻¹ :=
    hψ_den (n - 1) hpred_mem
  have hjump :
      ‖Complex.reducedArc_inverseGeometricDenominator (ψ n) -
        Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖ ≤
        ‖Complex.reducedArc_inverseGeometricDenominator (ψ n)‖ +
          ‖Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖ :=
    norm_sub_le
      (Complex.reducedArc_inverseGeometricDenominator (ψ n))
      (Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1)))
  have hendpoint :
      ‖Complex.reducedArc_inverseGeometricDenominator (ψ n)‖ +
          ‖Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖ ≤
        2 * λ⁻¹ + 2 * λ⁻¹ :=
    add_le_add hn_bound hpred_bound
  have hfour :
      ‖Complex.reducedArc_inverseGeometricDenominator (ψ n)‖ +
          ‖Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖ ≤
        4 * λ⁻¹ :=
    Eq.subst
      (motive := fun r : ℝ =>
        ‖Complex.reducedArc_inverseGeometricDenominator (ψ n)‖ +
            ‖Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖ ≤ r)
      (Real.two_mul_add_two_mul_eq_four_mul λ⁻¹)
      hendpoint
  exact le_trans hjump hfour

/-- Splitting an open natural interval at an interior index separates the left
open interval, the crossing index, and the right open interval. -/
theorem Finset.sum_Ioo_split_at
    {α : Type*}
    [AddCommMonoid α]
    (f : ℕ → α)
    {a c m : ℕ}
    (hac : a < c)
    (hcm : c < m) :
    (∑ n ∈ Finset.Ioo a m, f n) =
      (∑ n ∈ Finset.Ioo a c, f n) + f c +
        ∑ n ∈ Finset.Ioo c m, f n := by
  have ha_succ_c : a + 1 ≤ c :=
    Nat.succ_le_of_lt hac
  have hc_le_m : c ≤ m :=
    le_of_lt hcm
  have hleft :
      Finset.Ioo a c = Finset.Ico (a + 1) c :=
    (Finset.Ico_succ_left (a := a) (b := c)).symm
  have hwhole :
      Finset.Ioo a m = Finset.Ico (a + 1) m :=
    (Finset.Ico_succ_left (a := a) (b := m)).symm
  have hright :
      Finset.Ioo c m = Finset.Ico (c + 1) m :=
    (Finset.Ico_succ_left (a := c) (b := m)).symm
  have hconsecutive :
      (∑ n ∈ Finset.Ico (a + 1) c, f n) +
          ∑ n ∈ Finset.Ico c m, f n =
        ∑ n ∈ Finset.Ico (a + 1) m, f n :=
    Finset.sum_Ico_consecutive f ha_succ_c hc_le_m
  have hpeel :
      (∑ n ∈ Finset.Ico c m, f n) =
        f c + ∑ n ∈ Finset.Ico (c + 1) m, f n :=
    Finset.sum_eq_sum_Ico_succ_bot hcm f
  calc
    (∑ n ∈ Finset.Ioo a m, f n) =
        ∑ n ∈ Finset.Ico (a + 1) m, f n :=
      congrArg (fun s : Finset ℕ => ∑ n ∈ s, f n) hwhole
    _ =
        (∑ n ∈ Finset.Ico (a + 1) c, f n) +
          ∑ n ∈ Finset.Ico c m, f n :=
      hconsecutive.symm
    _ =
        (∑ n ∈ Finset.Ico (a + 1) c, f n) +
          (f c + ∑ n ∈ Finset.Ico (c + 1) m, f n) :=
      congrArg
        (fun r : α =>
          (∑ n ∈ Finset.Ico (a + 1) c, f n) + r)
        hpeel
    _ =
        ((∑ n ∈ Finset.Ico (a + 1) c, f n) + f c) +
          ∑ n ∈ Finset.Ico (c + 1) m, f n :=
      (add_assoc
        (∑ n ∈ Finset.Ico (a + 1) c, f n)
        (f c)
        (∑ n ∈ Finset.Ico (c + 1) m, f n)).symm
    _ =
        (∑ n ∈ Finset.Ioo a c, f n) + f c +
          ∑ n ∈ Finset.Ioo c m, f n :=
      congrArg₂ Add.add
        (congrArg₂ Add.add
          (congrArg (fun s : Finset ℕ => ∑ n ∈ s, f n) hleft.symm)
          rfl)
        (congrArg (fun s : Finset ℕ => ∑ n ∈ s, f n) hright.symm)

/-- The public three-piece constant dominates a single one-sided constant. -/
theorem Real.four_mul_inv_le_four_mul_three_mul_inv
    {λ : ℝ}
    (hλ_pos : 0 < λ) :
    4 * λ⁻¹ ≤ 4 * (3 * λ⁻¹) := by
  have hλ_inv_nonneg : 0 ≤ λ⁻¹ :=
    inv_nonneg.mpr hλ_pos.le
  have hthree_nonneg : 0 ≤ (3 : ℝ) :=
    zero_le_three
  have hone_le_three : (1 : ℝ) ≤ 3 :=
    one_le_three
  have hinner :
      λ⁻¹ ≤ 3 * λ⁻¹ := by
    have hmul :
        1 * λ⁻¹ ≤ 3 * λ⁻¹ :=
      mul_le_mul_of_nonneg_right hone_le_three hλ_inv_nonneg
    exact Eq.subst
      (motive := fun r : ℝ => r ≤ 3 * λ⁻¹)
      (one_mul λ⁻¹)
      hmul
  exact mul_le_mul_of_nonneg_left hinner zero_le_four

/-- Three copies of the one-sided constant fold to the three-piece constant. -/
theorem Real.three_four_inv_eq_four_mul_three_mul_inv
    (λ : ℝ) :
    (4 * λ⁻¹ + 4 * λ⁻¹) + 4 * λ⁻¹ =
      4 * (3 * λ⁻¹) := by
  have htwo :
      4 * λ⁻¹ + 4 * λ⁻¹ = (4 + 4 : ℝ) * λ⁻¹ :=
    (add_mul (4 : ℝ) 4 λ⁻¹).symm
  have height :
      (4 + 4 : ℝ) = 8 :=
    rfl
  have htwelve :
      (8 : ℝ) + 4 = 12 :=
    rfl
  calc
    (4 * λ⁻¹ + 4 * λ⁻¹) + 4 * λ⁻¹ =
        ((4 + 4 : ℝ) * λ⁻¹) + 4 * λ⁻¹ :=
      congrArg (fun r : ℝ => r + 4 * λ⁻¹) htwo
    _ = (8 * λ⁻¹) + 4 * λ⁻¹ :=
      congrArg (fun r : ℝ => r * λ⁻¹ + 4 * λ⁻¹) height
    _ = ((8 : ℝ) + 4) * λ⁻¹ :=
      (add_mul (8 : ℝ) 4 λ⁻¹).symm
    _ = 12 * λ⁻¹ :=
      congrArg (fun r : ℝ => r * λ⁻¹) htwelve
    _ = (4 * 3) * λ⁻¹ :=
      congrArg (fun r : ℝ => r * λ⁻¹) (show (12 : ℝ) = 4 * 3 from rfl)
    _ = 4 * (3 * λ⁻¹) :=
      mul_assoc (4 : ℝ) 3 λ⁻¹

/-- The three-piece monotone sign-crossing bound: negative-side variation,
one crossing jump, and positive-side variation.

This is the discrete owner obligation behind the split theorem. -/
theorem Complex.reducedArc_inverseGeometricDenominator_three_piece_variation_bound
    (ψ : ℕ → ℝ)
    {a b m : ℕ}
    {λ : ℝ}
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hλ_pos : 0 < λ)
    (hψ_mem :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ψ n ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_mono :
      MonotoneOn (fun n : ℕ => ψ n) (Finset.Ico a b : Set ℕ) ∨
      AntitoneOn (fun n : ℕ => ψ n) (Finset.Ico a b : Set ℕ))
    (hψ_sep :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          λ ≤ ‖ψ n‖)
    (hψ_den :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖Complex.reducedArc_inverseGeometricDenominator (ψ n)‖ ≤
            2 * λ⁻¹) :
    (∑ n ∈ Finset.Ioo a m,
      ‖Complex.reducedArc_inverseGeometricDenominator (ψ n) -
        Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖) ≤
        4 * (3 * λ⁻¹) := by
  let jump : ℕ → ℝ :=
    fun n : ℕ =>
      ‖Complex.reducedArc_inverseGeometricDenominator (ψ n) -
        Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖
  have hm_bounds : a ≤ m ∧ m ≤ b :=
    Finset.mem_Icc.mp hm
  have hm_self : m ∈ Finset.Icc a m :=
    Finset.mem_Icc.mpr ⟨hm_bounds.1, le_rfl⟩
  have htarget_one :
      4 * λ⁻¹ ≤ 4 * (3 * λ⁻¹) :=
    Real.four_mul_inv_le_four_mul_three_mul_inv hλ_pos
  have htarget_three :
      (4 * λ⁻¹ + 4 * λ⁻¹) + 4 * λ⁻¹ ≤
        4 * (3 * λ⁻¹) :=
    Eq.le (Real.three_four_inv_eq_four_mul_three_mul_inv λ)
  match hψ_mono with
  | Or.inl hmono =>
      have hmono_am :
          MonotoneOn ψ (Finset.Ico a m : Set ℕ) := by
        intro i hi j hj hij
        have hi_bounds : a ≤ i ∧ i < m :=
          Finset.mem_Ico.mp hi
        have hj_bounds : a ≤ j ∧ j < m :=
          Finset.mem_Ico.mp hj
        exact hmono
          (Finset.mem_Ico.mpr
            ⟨hi_bounds.1, lt_of_lt_of_le hi_bounds.2 hm_bounds.2⟩)
          (Finset.mem_Ico.mpr
            ⟨hj_bounds.1, lt_of_lt_of_le hj_bounds.2 hm_bounds.2⟩)
          hij
      have hsep_am :
          ∀ n : ℕ,
            n ∈ Finset.Ico a m →
              λ ≤ ‖ψ n‖ := by
        intro n hn
        have hn_bounds : a ≤ n ∧ n < m :=
          Finset.mem_Ico.mp hn
        exact hψ_sep n
          (Finset.mem_Ico.mpr
            ⟨hn_bounds.1, lt_of_lt_of_le hn_bounds.2 hm_bounds.2⟩)
      have hden_am :
          ∀ n : ℕ,
            n ∈ Finset.Ico a m →
              ‖Complex.reducedArc_inverseGeometricDenominator (ψ n)‖ ≤
                2 * λ⁻¹ := by
        intro n hn
        have hn_bounds : a ≤ n ∧ n < m :=
          Finset.mem_Ico.mp hn
        exact hψ_den n
          (Finset.mem_Ico.mpr
            ⟨hn_bounds.1, lt_of_lt_of_le hn_bounds.2 hm_bounds.2⟩)
      have hdecomp :=
        Real.monotoneOn_reducedArc_side_decomposition
          ψ hm hλ_pos hψ_mem hmono hψ_sep
      match hdecomp with
      | Or.inl hall_neg =>
          exact le_trans
            (Complex.reducedArc_inverseGeometricDenominator_oneSided_variation_bound
              ψ ham hm_self hλ_pos (Or.inr ⟨rfl, rfl⟩)
              hall_neg (Or.inl hmono_am) hsep_am hden_am)
            htarget_one
      | Or.inr hrest =>
          match hrest with
          | Or.inl hall_pos =>
              exact le_trans
                (Complex.reducedArc_inverseGeometricDenominator_oneSided_variation_bound
                  ψ ham hm_self hλ_pos (Or.inl ⟨rfl, rfl⟩)
                  hall_pos (Or.inl hmono_am) hsep_am hden_am)
                htarget_one
          | Or.inr hcross =>
              match hcross with
              | ⟨c, hac, hcm, hleft_side, hright_side⟩ =>
                  have hc_mem_original : c ∈ Finset.Ico a b :=
                    Finset.mem_Ico.mpr
                      ⟨le_of_lt hac, lt_of_lt_of_le hcm hm_bounds.2⟩
                  have hc_Icc_left : c ∈ Finset.Icc a c :=
                    Finset.mem_Icc.mpr ⟨le_of_lt hac, le_rfl⟩
                  have hm_Icc_right : m ∈ Finset.Icc c m :=
                    Finset.mem_Icc.mpr ⟨le_of_lt hcm, le_rfl⟩
                  have hmono_left :
                      MonotoneOn ψ (Finset.Ico a c : Set ℕ) := by
                    intro i hi j hj hij
                    have hi_bounds : a ≤ i ∧ i < c :=
                      Finset.mem_Ico.mp hi
                    have hj_bounds : a ≤ j ∧ j < c :=
                      Finset.mem_Ico.mp hj
                    exact hmono
                      (Finset.mem_Ico.mpr
                        ⟨hi_bounds.1,
                          lt_of_lt_of_le (lt_trans hi_bounds.2 hcm)
                            hm_bounds.2⟩)
                      (Finset.mem_Ico.mpr
                        ⟨hj_bounds.1,
                          lt_of_lt_of_le (lt_trans hj_bounds.2 hcm)
                            hm_bounds.2⟩)
                      hij
                  have hmono_right :
                      MonotoneOn ψ (Finset.Ico c m : Set ℕ) := by
                    intro i hi j hj hij
                    have hi_bounds : c ≤ i ∧ i < m :=
                      Finset.mem_Ico.mp hi
                    have hj_bounds : c ≤ j ∧ j < m :=
                      Finset.mem_Ico.mp hj
                    exact hmono
                      (Finset.mem_Ico.mpr
                        ⟨le_trans (le_of_lt hac) hi_bounds.1,
                          lt_of_lt_of_le hi_bounds.2 hm_bounds.2⟩)
                      (Finset.mem_Ico.mpr
                        ⟨le_trans (le_of_lt hac) hj_bounds.1,
                          lt_of_lt_of_le hj_bounds.2 hm_bounds.2⟩)
                      hij
                  have hsep_left :
                      ∀ n : ℕ,
                        n ∈ Finset.Ico a c →
                          λ ≤ ‖ψ n‖ := by
                    intro n hn
                    have hn_bounds : a ≤ n ∧ n < c :=
                      Finset.mem_Ico.mp hn
                    exact hψ_sep n
                      (Finset.mem_Ico.mpr
                        ⟨hn_bounds.1,
                          lt_of_lt_of_le (lt_trans hn_bounds.2 hcm)
                            hm_bounds.2⟩)
                  have hsep_right :
                      ∀ n : ℕ,
                        n ∈ Finset.Ico c m →
                          λ ≤ ‖ψ n‖ := by
                    intro n hn
                    have hn_bounds : c ≤ n ∧ n < m :=
                      Finset.mem_Ico.mp hn
                    exact hψ_sep n
                      (Finset.mem_Ico.mpr
                        ⟨le_trans (le_of_lt hac) hn_bounds.1,
                          lt_of_lt_of_le hn_bounds.2 hm_bounds.2⟩)
                  have hden_left :
                      ∀ n : ℕ,
                        n ∈ Finset.Ico a c →
                          ‖Complex.reducedArc_inverseGeometricDenominator
                            (ψ n)‖ ≤ 2 * λ⁻¹ := by
                    intro n hn
                    have hn_bounds : a ≤ n ∧ n < c :=
                      Finset.mem_Ico.mp hn
                    exact hψ_den n
                      (Finset.mem_Ico.mpr
                        ⟨hn_bounds.1,
                          lt_of_lt_of_le (lt_trans hn_bounds.2 hcm)
                            hm_bounds.2⟩)
                  have hden_right :
                      ∀ n : ℕ,
                        n ∈ Finset.Ico c m →
                          ‖Complex.reducedArc_inverseGeometricDenominator
                            (ψ n)‖ ≤ 2 * λ⁻¹ := by
                    intro n hn
                    have hn_bounds : c ≤ n ∧ n < m :=
                      Finset.mem_Ico.mp hn
                    exact hψ_den n
                      (Finset.mem_Ico.mpr
                        ⟨le_trans (le_of_lt hac) hn_bounds.1,
                          lt_of_lt_of_le hn_bounds.2 hm_bounds.2⟩)
                  have hleft :
                      (∑ n ∈ Finset.Ioo a c, jump n) ≤ 4 * λ⁻¹ :=
                    Complex.reducedArc_inverseGeometricDenominator_oneSided_variation_bound
                      ψ hac hc_Icc_left hλ_pos (Or.inr ⟨rfl, rfl⟩)
                      hleft_side (Or.inl hmono_left) hsep_left hden_left
                  have hright :
                      (∑ n ∈ Finset.Ioo c m, jump n) ≤ 4 * λ⁻¹ :=
                    Complex.reducedArc_inverseGeometricDenominator_oneSided_variation_bound
                      ψ hcm hm_Icc_right hλ_pos (Or.inl ⟨rfl, rfl⟩)
                      hright_side (Or.inl hmono_right) hsep_right hden_right
                  have hc_Ioo : c ∈ Finset.Ioo a m :=
                    Finset.mem_Ioo.mpr ⟨hac, hcm⟩
                  have hjump :
                      jump c ≤ 4 * λ⁻¹ :=
                    Complex.reducedArc_inverseGeometricDenominator_adjacent_norm_le_four_inv
                      ψ hc_Ioo hm hψ_den
                  have hsplit :
                      (∑ n ∈ Finset.Ioo a m, jump n) =
                        (∑ n ∈ Finset.Ioo a c, jump n) + jump c +
                          ∑ n ∈ Finset.Ioo c m, jump n :=
                    Finset.sum_Ioo_split_at jump hac hcm
                  have hparts :
                      (∑ n ∈ Finset.Ioo a c, jump n) + jump c +
                          ∑ n ∈ Finset.Ioo c m, jump n ≤
                        (4 * λ⁻¹ + 4 * λ⁻¹) + 4 * λ⁻¹ :=
                    add_le_add (add_le_add hleft hjump) hright
                  exact Eq.subst
                    (motive := fun r : ℝ =>
                      r ≤ 4 * (3 * λ⁻¹))
                    hsplit.symm
                    (le_trans hparts htarget_three)
  | Or.inr hanti =>
      have hanti_am :
          AntitoneOn ψ (Finset.Ico a m : Set ℕ) := by
        intro i hi j hj hij
        have hi_bounds : a ≤ i ∧ i < m :=
          Finset.mem_Ico.mp hi
        have hj_bounds : a ≤ j ∧ j < m :=
          Finset.mem_Ico.mp hj
        exact hanti
          (Finset.mem_Ico.mpr
            ⟨hi_bounds.1, lt_of_lt_of_le hi_bounds.2 hm_bounds.2⟩)
          (Finset.mem_Ico.mpr
            ⟨hj_bounds.1, lt_of_lt_of_le hj_bounds.2 hm_bounds.2⟩)
          hij
      have hsep_am :
          ∀ n : ℕ,
            n ∈ Finset.Ico a m →
              λ ≤ ‖ψ n‖ := by
        intro n hn
        have hn_bounds : a ≤ n ∧ n < m :=
          Finset.mem_Ico.mp hn
        exact hψ_sep n
          (Finset.mem_Ico.mpr
            ⟨hn_bounds.1, lt_of_lt_of_le hn_bounds.2 hm_bounds.2⟩)
      have hden_am :
          ∀ n : ℕ,
            n ∈ Finset.Ico a m →
              ‖Complex.reducedArc_inverseGeometricDenominator (ψ n)‖ ≤
                2 * λ⁻¹ := by
        intro n hn
        have hn_bounds : a ≤ n ∧ n < m :=
          Finset.mem_Ico.mp hn
        exact hψ_den n
          (Finset.mem_Ico.mpr
            ⟨hn_bounds.1, lt_of_lt_of_le hn_bounds.2 hm_bounds.2⟩)
      have hdecomp :=
        Real.antitoneOn_reducedArc_side_decomposition
          ψ hm hλ_pos hψ_mem hanti hψ_sep
      match hdecomp with
      | Or.inl hall_pos =>
          exact le_trans
            (Complex.reducedArc_inverseGeometricDenominator_oneSided_variation_bound
              ψ ham hm_self hλ_pos (Or.inl ⟨rfl, rfl⟩)
              hall_pos (Or.inr hanti_am) hsep_am hden_am)
            htarget_one
      | Or.inr hrest =>
          match hrest with
          | Or.inl hall_neg =>
              exact le_trans
                (Complex.reducedArc_inverseGeometricDenominator_oneSided_variation_bound
                  ψ ham hm_self hλ_pos (Or.inr ⟨rfl, rfl⟩)
                  hall_neg (Or.inr hanti_am) hsep_am hden_am)
                htarget_one
          | Or.inr hcross =>
              match hcross with
              | ⟨c, hac, hcm, hleft_side, hright_side⟩ =>
                  have hc_Icc_left : c ∈ Finset.Icc a c :=
                    Finset.mem_Icc.mpr ⟨le_of_lt hac, le_rfl⟩
                  have hm_Icc_right : m ∈ Finset.Icc c m :=
                    Finset.mem_Icc.mpr ⟨le_of_lt hcm, le_rfl⟩
                  have hanti_left :
                      AntitoneOn ψ (Finset.Ico a c : Set ℕ) := by
                    intro i hi j hj hij
                    have hi_bounds : a ≤ i ∧ i < c :=
                      Finset.mem_Ico.mp hi
                    have hj_bounds : a ≤ j ∧ j < c :=
                      Finset.mem_Ico.mp hj
                    exact hanti
                      (Finset.mem_Ico.mpr
                        ⟨hi_bounds.1,
                          lt_of_lt_of_le (lt_trans hi_bounds.2 hcm)
                            hm_bounds.2⟩)
                      (Finset.mem_Ico.mpr
                        ⟨hj_bounds.1,
                          lt_of_lt_of_le (lt_trans hj_bounds.2 hcm)
                            hm_bounds.2⟩)
                      hij
                  have hanti_right :
                      AntitoneOn ψ (Finset.Ico c m : Set ℕ) := by
                    intro i hi j hj hij
                    have hi_bounds : c ≤ i ∧ i < m :=
                      Finset.mem_Ico.mp hi
                    have hj_bounds : c ≤ j ∧ j < m :=
                      Finset.mem_Ico.mp hj
                    exact hanti
                      (Finset.mem_Ico.mpr
                        ⟨le_trans (le_of_lt hac) hi_bounds.1,
                          lt_of_lt_of_le hi_bounds.2 hm_bounds.2⟩)
                      (Finset.mem_Ico.mpr
                        ⟨le_trans (le_of_lt hac) hj_bounds.1,
                          lt_of_lt_of_le hj_bounds.2 hm_bounds.2⟩)
                      hij
                  have hsep_left :
                      ∀ n : ℕ,
                        n ∈ Finset.Ico a c →
                          λ ≤ ‖ψ n‖ := by
                    intro n hn
                    have hn_bounds : a ≤ n ∧ n < c :=
                      Finset.mem_Ico.mp hn
                    exact hψ_sep n
                      (Finset.mem_Ico.mpr
                        ⟨hn_bounds.1,
                          lt_of_lt_of_le (lt_trans hn_bounds.2 hcm)
                            hm_bounds.2⟩)
                  have hsep_right :
                      ∀ n : ℕ,
                        n ∈ Finset.Ico c m →
                          λ ≤ ‖ψ n‖ := by
                    intro n hn
                    have hn_bounds : c ≤ n ∧ n < m :=
                      Finset.mem_Ico.mp hn
                    exact hψ_sep n
                      (Finset.mem_Ico.mpr
                        ⟨le_trans (le_of_lt hac) hn_bounds.1,
                          lt_of_lt_of_le hn_bounds.2 hm_bounds.2⟩)
                  have hden_left :
                      ∀ n : ℕ,
                        n ∈ Finset.Ico a c →
                          ‖Complex.reducedArc_inverseGeometricDenominator
                            (ψ n)‖ ≤ 2 * λ⁻¹ := by
                    intro n hn
                    have hn_bounds : a ≤ n ∧ n < c :=
                      Finset.mem_Ico.mp hn
                    exact hψ_den n
                      (Finset.mem_Ico.mpr
                        ⟨hn_bounds.1,
                          lt_of_lt_of_le (lt_trans hn_bounds.2 hcm)
                            hm_bounds.2⟩)
                  have hden_right :
                      ∀ n : ℕ,
                        n ∈ Finset.Ico c m →
                          ‖Complex.reducedArc_inverseGeometricDenominator
                            (ψ n)‖ ≤ 2 * λ⁻¹ := by
                    intro n hn
                    have hn_bounds : c ≤ n ∧ n < m :=
                      Finset.mem_Ico.mp hn
                    exact hψ_den n
                      (Finset.mem_Ico.mpr
                        ⟨le_trans (le_of_lt hac) hn_bounds.1,
                          lt_of_lt_of_le hn_bounds.2 hm_bounds.2⟩)
                  have hleft :
                      (∑ n ∈ Finset.Ioo a c, jump n) ≤ 4 * λ⁻¹ :=
                    Complex.reducedArc_inverseGeometricDenominator_oneSided_variation_bound
                      ψ hac hc_Icc_left hλ_pos (Or.inl ⟨rfl, rfl⟩)
                      hleft_side (Or.inr hanti_left) hsep_left hden_left
                  have hright :
                      (∑ n ∈ Finset.Ioo c m, jump n) ≤ 4 * λ⁻¹ :=
                    Complex.reducedArc_inverseGeometricDenominator_oneSided_variation_bound
                      ψ hcm hm_Icc_right hλ_pos (Or.inr ⟨rfl, rfl⟩)
                      hright_side (Or.inr hanti_right) hsep_right hden_right
                  have hc_Ioo : c ∈ Finset.Ioo a m :=
                    Finset.mem_Ioo.mpr ⟨hac, hcm⟩
                  have hjump :
                      jump c ≤ 4 * λ⁻¹ :=
                    Complex.reducedArc_inverseGeometricDenominator_adjacent_norm_le_four_inv
                      ψ hc_Ioo hm hψ_den
                  have hsplit :
                      (∑ n ∈ Finset.Ioo a m, jump n) =
                        (∑ n ∈ Finset.Ioo a c, jump n) + jump c +
                          ∑ n ∈ Finset.Ioo c m, jump n :=
                    Finset.sum_Ioo_split_at jump hac hcm
                  have hparts :
                      (∑ n ∈ Finset.Ioo a c, jump n) + jump c +
                          ∑ n ∈ Finset.Ioo c m, jump n ≤
                        (4 * λ⁻¹ + 4 * λ⁻¹) + 4 * λ⁻¹ :=
                    add_le_add (add_le_add hleft hjump) hright
                  exact Eq.subst
                    (motive := fun r : ℝ =>
                      r ≤ 4 * (3 * λ⁻¹))
                    hsplit.symm
                    (le_trans hparts htarget_three)

/-- The three-piece variation constant is bounded by the public `π`-constant. -/
theorem Real.four_mul_three_mul_inv_le_four_mul_pi_mul_inv
    {λ : ℝ}
    (hλ_pos : 0 < λ) :
    4 * (3 * λ⁻¹) ≤ 4 * Real.pi * λ⁻¹ := by
  have hλ_inv_nonneg : 0 ≤ λ⁻¹ :=
    inv_nonneg.mpr hλ_pos.le
  have hthree_le_pi : (3 : ℝ) ≤ Real.pi :=
    le_of_lt Real.pi_gt_three
  have hinner :
      3 * λ⁻¹ ≤ Real.pi * λ⁻¹ :=
    mul_le_mul_of_nonneg_right hthree_le_pi hλ_inv_nonneg
  have houter :
      4 * (3 * λ⁻¹) ≤ 4 * (Real.pi * λ⁻¹) :=
    mul_le_mul_of_nonneg_left hinner zero_lt_four.le
  have htarget :
      4 * (Real.pi * λ⁻¹) = 4 * Real.pi * λ⁻¹ :=
    (mul_assoc (4 : ℝ) Real.pi λ⁻¹).symm
  exact Eq.subst
    (motive := fun r : ℝ => 4 * (3 * λ⁻¹) ≤ r)
    htarget
    houter

/-- A monotone reduced sequence separated from zero splits into at most a
negative-side block, one crossing jump, and a positive-side block. -/
theorem Complex.reducedArc_inverseGeometricDenominator_split_variation_bound
    (ψ : ℕ → ℝ)
    {a b m : ℕ}
    {λ : ℝ}
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hλ_pos : 0 < λ)
    (hψ_mem :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ψ n ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_mono :
      MonotoneOn (fun n : ℕ => ψ n) (Finset.Ico a b : Set ℕ) ∨
      AntitoneOn (fun n : ℕ => ψ n) (Finset.Ico a b : Set ℕ))
    (hψ_sep :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          λ ≤ ‖ψ n‖)
    (hψ_den :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖Complex.reducedArc_inverseGeometricDenominator (ψ n)‖ ≤
            2 * λ⁻¹) :
    (∑ n ∈ Finset.Ioo a m,
      ‖Complex.reducedArc_inverseGeometricDenominator (ψ n) -
        Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖) ≤
        4 * Real.pi * λ⁻¹ := by
  exact le_trans
    (Complex.reducedArc_inverseGeometricDenominator_three_piece_variation_bound
      ψ ham hm hλ_pos hψ_mem hψ_mono hψ_sep hψ_den)
    (Real.four_mul_three_mul_inv_le_four_mul_pi_mul_inv hλ_pos)

/-- The analytic reduced-arc variation theorem for the inverse chord map.

This is the genuine no-winding core: a monotone finite sequence in the
fundamental interval, separated from `0`, has controlled total variation under
`ψ ↦ (1 - exp(iψ))⁻¹`. -/
theorem Complex.reducedArc_inverseGeometricDenominator_monotone_variation_bound
    (ψ : ℕ → ℝ)
    {a b m : ℕ}
    {λ : ℝ}
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hλ_pos : 0 < λ)
    (hψ_mem :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ψ n ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_mono :
      MonotoneOn (fun n : ℕ => ψ n) (Finset.Ico a b : Set ℕ) ∨
      AntitoneOn (fun n : ℕ => ψ n) (Finset.Ico a b : Set ℕ))
    (hψ_sep :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          λ ≤ ‖ψ n‖)
    (hψ_den :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖Complex.reducedArc_inverseGeometricDenominator (ψ n)‖ ≤
            2 * λ⁻¹) :
    (∑ n ∈ Finset.Ioo a m,
      ‖Complex.reducedArc_inverseGeometricDenominator (ψ n) -
        Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖) ≤
        4 * Real.pi * λ⁻¹ := by
  exact
    Complex.reducedArc_inverseGeometricDenominator_split_variation_bound
      ψ ham hm hλ_pos hψ_mem hψ_mono hψ_sep hψ_den

/-- Exact reduced-arc variation lemma for the inverse geometric denominator.

This is the genuine no-winding analytic core: a monotone finite sequence in the
fundamental interval, separated from `0`, has controlled total variation under
`ψ ↦ (1 - exp(iψ))⁻¹`. -/
theorem Complex.reducedArc_inverseGeometricDenominator_variation_bound
    (ψ : ℕ → ℝ)
    {a b m : ℕ}
    {λ : ℝ}
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hλ_pos : 0 < λ)
    (hψ_mem :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ψ n ∈ Set.Ioc (-Real.pi) Real.pi)
    (hψ_mono :
      MonotoneOn (fun n : ℕ => ψ n) (Finset.Ico a b : Set ℕ) ∨
      AntitoneOn (fun n : ℕ => ψ n) (Finset.Ico a b : Set ℕ))
    (hψ_sep :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          λ ≤ ‖ψ n‖)
    (hψ_den :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖(1 - Complex.exp (Complex.I * (ψ n : ℂ)))⁻¹‖ ≤
            2 * λ⁻¹) :
    (∑ n ∈ Finset.Ioo a m,
      ‖(1 - Complex.exp (Complex.I * (ψ n : ℂ)))⁻¹ -
        (1 - Complex.exp (Complex.I * (ψ (n - 1) : ℂ)))⁻¹‖) ≤
        4 * Real.pi * λ⁻¹ := by
  have hψ_den_reduced :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖Complex.reducedArc_inverseGeometricDenominator (ψ n)‖ ≤
            2 * λ⁻¹ := by
    intro n hn
    exact Eq.subst
      (motive := fun z : ℂ => ‖z‖ ≤ 2 * λ⁻¹)
      (Complex.reducedArc_inverseGeometricDenominator_eq (ψ n)).symm
      (hψ_den n hn)
  have hcore :
      (∑ n ∈ Finset.Ioo a m,
        ‖Complex.reducedArc_inverseGeometricDenominator (ψ n) -
          Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖) ≤
          4 * Real.pi * λ⁻¹ :=
    Complex.reducedArc_inverseGeometricDenominator_monotone_variation_bound
      ψ ham hm hλ_pos hψ_mem hψ_mono hψ_sep hψ_den_reduced
  have hsum :
      (∑ n ∈ Finset.Ioo a m,
        ‖Complex.reducedArc_inverseGeometricDenominator (ψ n) -
          Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1))‖) =
        ∑ n ∈ Finset.Ioo a m,
          ‖(1 - Complex.exp (Complex.I * (ψ n : ℂ)))⁻¹ -
            (1 - Complex.exp (Complex.I * (ψ (n - 1) : ℂ)))⁻¹‖ := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hn_eq :
        Complex.reducedArc_inverseGeometricDenominator (ψ n) =
          (1 - Complex.exp (Complex.I * (ψ n : ℂ)))⁻¹ :=
      Complex.reducedArc_inverseGeometricDenominator_eq (ψ n)
    have hpred_eq :
        Complex.reducedArc_inverseGeometricDenominator (ψ (n - 1)) =
          (1 - Complex.exp (Complex.I * (ψ (n - 1) : ℂ)))⁻¹ :=
      Complex.reducedArc_inverseGeometricDenominator_eq (ψ (n - 1))
    exact congrArg norm (congrArg₂ Sub.sub hn_eq hpred_eq)
  exact Eq.subst
    (motive := fun r : ℝ => r ≤ 4 * Real.pi * λ⁻¹)
    hsum
    hcore

/-- Reduced no-winding monotone separated increments control the total variation
of the inverse geometric denominators appearing in the finite Abel transform.

The reduced monotonicity hypothesis is essential: raw monotone increments can
wind through many periods and make this total variation grow with the number of
turns. -/
theorem Complex.realPhase_reducedMonotoneSeparated_inverseGeometricDenominator_variation_bound
    (φ : ℝ → ℝ)
    {a b m : ℕ}
    {λ : ℝ}
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hλ_pos : 0 < λ)
    (hred_mono : Complex.realPhase_reducedIntegerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b λ)
    (hden :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖Complex.realPhase_inverseGeometricDenominator φ n‖ ≤
            2 * λ⁻¹) :
    (∑ n ∈ Finset.Ioo a m,
      ‖Complex.realPhase_inverseGeometricDenominator φ n -
        Complex.realPhase_inverseGeometricDenominator φ (n - 1)‖) ≤
        4 * Real.pi * λ⁻¹ := by
  let ψ : ℕ → ℝ := Complex.realPhase_reducedIntegerIncrement φ
  have hψ_mem :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ψ n ∈ Set.Ioc (-Real.pi) Real.pi := by
    intro n hn
    unfold ψ Complex.realPhase_reducedIntegerIncrement
    convert
      toIocMod_mem_Ioc Real.two_pi_pos (-Real.pi)
        (Complex.realPhase_integerIncrement φ n) using 1
    ring
  have hψ_sep :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          λ ≤ ‖ψ n‖ := by
    intro n hn
    unfold ψ
    exact
      Complex.realPhase_reducedIntegerIncrement_norm_lower_bound
        φ hsep hn
  have hψ_den :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖(1 - Complex.exp (Complex.I * (ψ n : ℂ)))⁻¹‖ ≤
            2 * λ⁻¹ := by
    intro n hn
    have htransport :
        Complex.realPhase_inverseGeometricDenominator φ n =
          (1 - Complex.exp (Complex.I * (ψ n : ℂ)))⁻¹ := by
      unfold ψ
      exact Complex.realPhase_inverseGeometricDenominator_eq_reduced φ n
    exact Eq.subst
      (motive := fun z : ℂ => ‖z‖ ≤ 2 * λ⁻¹)
      htransport
      (hden n hn)
  have hcore :
      (∑ n ∈ Finset.Ioo a m,
        ‖(1 - Complex.exp (Complex.I * (ψ n : ℂ)))⁻¹ -
          (1 - Complex.exp (Complex.I * (ψ (n - 1) : ℂ)))⁻¹‖) ≤
          4 * Real.pi * λ⁻¹ :=
    Complex.reducedArc_inverseGeometricDenominator_variation_bound
      ψ ham hm hλ_pos hψ_mem hred_mono hψ_sep hψ_den
  have hterms :
      (∑ n ∈ Finset.Ioo a m,
        ‖Complex.realPhase_inverseGeometricDenominator φ n -
          Complex.realPhase_inverseGeometricDenominator φ (n - 1)‖) =
        ∑ n ∈ Finset.Ioo a m,
          ‖(1 - Complex.exp (Complex.I * (ψ n : ℂ)))⁻¹ -
            (1 - Complex.exp (Complex.I * (ψ (n - 1) : ℂ)))⁻¹‖ := by
    refine Finset.sum_congr rfl ?_
    intro n hn
    have hn :
        Complex.realPhase_inverseGeometricDenominator φ n =
          (1 - Complex.exp (Complex.I * (ψ n : ℂ)))⁻¹ := by
      unfold ψ
      exact Complex.realPhase_inverseGeometricDenominator_eq_reduced φ n
    have hpred :
        Complex.realPhase_inverseGeometricDenominator φ (n - 1) =
          (1 - Complex.exp (Complex.I * (ψ (n - 1) : ℂ)))⁻¹ := by
      unfold ψ
      exact Complex.realPhase_inverseGeometricDenominator_eq_reduced φ (n - 1)
    exact congrArg norm (congrArg₂ Sub.sub hn hpred)
  exact Eq.subst
    (motive := fun r : ℝ => r ≤ 4 * Real.pi * λ⁻¹)
    hterms.symm
    hcore

/-- Variation estimate for the explicit finite Abel variation term. -/
theorem Complex.realPhase_prefixAbelVariation_norm_bound
    (φ : ℝ → ℝ)
    {a b m : ℕ}
    {λ : ℝ}
    (ham : a < m)
    (hm : m ∈ Finset.Icc a b)
    (hλ_pos : 0 < λ)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hred_mono : Complex.realPhase_reducedIntegerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b λ)
    (hden :
      ∀ n : ℕ,
        n ∈ Finset.Ico a b →
          ‖Complex.realPhase_inverseGeometricDenominator φ n‖ ≤
            2 * λ⁻¹) :
    ‖Complex.realPhase_prefixAbelVariation φ a m‖ ≤
      4 * Real.pi * λ⁻¹ := by
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
          4 * Real.pi * λ⁻¹ :=
    Complex.realPhase_reducedMonotoneSeparated_inverseGeometricDenominator_variation_bound
      φ ham hm hλ_pos hred_mono hsep hden
  exact le_trans hsum_norm
    (Eq.subst
      (motive := fun r : ℝ => r ≤ 4 * Real.pi * λ⁻¹)
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
    (hred_mono : Complex.realPhase_reducedIntegerIncrementMonotoneOn φ a b)
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
      ‖variation‖ ≤ 4 * Real.pi * λ⁻¹ := by
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
        φ ham hm hλ_pos hinc_mono hred_mono hsep hden'

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
    (hred_mono : Complex.realPhase_reducedIntegerIncrementMonotoneOn φ a b)
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
      ‖variation‖ ≤ 4 * Real.pi * λ⁻¹ := by
  by_cases hma : m = a
  · exact Eq.subst
      (motive := fun r : ℕ =>
        ∃ boundary variation : ℂ,
          (∑ n ∈ Finset.Icc a r,
            Complex.exp (Complex.I * (φ n : ℂ))) =
              boundary + variation ∧
          ‖boundary‖ ≤ 4 * (λ⁻¹ + 1) ∧
          ‖variation‖ ≤ 4 * Real.pi * λ⁻¹)
      hma.symm
      (Complex.realPhase_monotoneIncrement_singleton_prefix_abel_terms_bounded
        φ a hλ_pos)
  · have hm_bounds : a ≤ m ∧ m ≤ b :=
      Finset.mem_Icc.mp hm
    have ham : a < m :=
      lt_of_le_of_ne hm_bounds.1 (Ne.symm hma)
    exact
      Complex.realPhase_monotoneIncrement_prefix_abel_terms_bounded_of_lt
        φ ha hab_lt ham hm hλ_pos hinc_mono hred_mono hsep hden

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
    (hred_mono : Complex.realPhase_reducedIntegerIncrementMonotoneOn φ a b)
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
        4 * (λ⁻¹ + 1) + 4 * Real.pi * λ⁻¹ := by
  rcases
    Complex.realPhase_monotoneIncrement_prefix_abel_terms_bounded
      φ ha hab_lt hm hλ_pos hinc_mono hred_mono hsep hden with
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
    (hred_mono : Complex.realPhase_reducedIntegerIncrementMonotoneOn φ a b)
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
        4 * (λ⁻¹ + 1) + 4 * Real.pi * λ⁻¹ := by
  have hb_mem : b ∈ Finset.Icc a b :=
    Finset.mem_Icc.mpr ⟨le_of_lt hab_lt, le_rfl⟩
  exact
    Complex.realPhase_monotoneIncrement_partialSummation_prefix_bound
      φ ha hab_lt hb_mem hλ_pos hinc_mono hred_mono hsep hden

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
    (hred_mono : Complex.realPhase_reducedIntegerIncrementMonotoneOn φ a b)
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
        4 * (λ⁻¹ + 1) + 4 * Real.pi * λ⁻¹ := by
  exact
    Complex.realPhase_monotoneIncrement_abel_transform_norm_bound
      φ ha hab_lt hλ_pos hinc_mono hred_mono hsep hden

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
    (hred_mono : Complex.realPhase_reducedIntegerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b λ) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        4 * (λ⁻¹ + 1) + 4 * Real.pi * λ⁻¹ := by
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
      φ ha hab_lt hλ_pos hinc_mono hred_mono hsep hden

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
    (hred_mono : Complex.realPhase_reducedIntegerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b λ) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        4 * (λ⁻¹ + 1) + 4 * Real.pi * λ⁻¹ := by
  rcases lt_or_eq_of_le hab with hab_lt | hab_eq
  · exact
      Complex.realPhase_monotoneSeparatedIncrement_dirichlet_bound_of_lt
        φ ha hab_lt hλ_pos hinc_mono hred_mono hsep
  · exact
      Eq.subst
        (motive := fun c : ℕ =>
          ‖∑ n ∈ Finset.Icc a c,
            Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
              4 * (λ⁻¹ + 1) + 4 * Real.pi * λ⁻¹)
        hab_eq
        (Complex.realPhase_singleton_integer_block_bound φ a hλ_pos)

/-- Finite monotone separated-increment exponential-sum primitive.

This is the public finite-difference Kusmin-Landau surface.  It is a thin
wrapper over the Dirichlet-test primitive with the boundary-safe constant
`4 * (λ⁻¹ + 1) + 4 * Real.pi * λ⁻¹`. -/
theorem Complex.realPhase_separatedIncrement_integer_block_bound
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {λ : ℝ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hλ_pos : 0 < λ)
    (hinc_mono : Complex.realPhase_integerIncrementMonotoneOn φ a b)
    (hred_mono : Complex.realPhase_reducedIntegerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b λ) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        4 * (λ⁻¹ + 1) + 4 * Real.pi * λ⁻¹ := by
  exact
    Complex.realPhase_monotoneSeparatedIncrement_dirichlet_bound
      φ ha hab hλ_pos hinc_mono hred_mono hsep

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
    (hred_mono : Complex.realPhase_reducedIntegerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b λ) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        4 * (λ⁻¹ + 1) + 4 * Real.pi * λ⁻¹ := by
  exact
    Complex.realPhase_separatedIncrement_integer_block_bound
      φ ha hab hλ_pos hinc_mono hred_mono hsep

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
    (hred_mono : Complex.realPhase_reducedIntegerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b λ) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        4 * (λ⁻¹ + 1) + 4 * Real.pi * λ⁻¹ := by
  exact
    Complex.realPhase_kusminLandau_integer_block_bound_of_separatedIncrement
      φ ha hab hλ_pos hderiv_antitone hderiv_lower hinc_mono hred_mono hsep

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
    (hred_mono : Complex.realPhase_reducedIntegerIncrementMonotoneOn φ a b)
    (hsep : Complex.realPhase_integerIncrementSeparatedOn φ a b λ) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        4 * (λ⁻¹ + 1) + 4 * Real.pi * λ⁻¹ := by
  have hosc :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
          4 * (λ⁻¹ + 1) + 4 * Real.pi * λ⁻¹ :=
    Complex.realPhase_kusminLandau_integer_block_bound
      φ ha hab hλ_pos hderiv_antitone hderiv_lower hinc_mono hred_mono hsep
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

/-- The corrected endpoint-plus-reduced-arc block constant is bounded by a
single numeral constant convenient for dyadic summation. -/
theorem Complex.logarithmicPhase_exact_block_constant_le_twenty
    {x : ℝ}
    (hx : 0 ≤ x) :
    4 * (x + 1) + 4 * Real.pi * x ≤ 20 * (x + 1) := by
  have hpi_x : Real.pi * x ≤ 4 * x :=
    mul_le_mul_of_nonneg_right Real.pi_le_four hx
  have hfour_pi_x :
      4 * Real.pi * x ≤ 4 * (4 * x) := by
    have hmul :
        4 * (Real.pi * x) ≤ 4 * (4 * x) :=
      mul_le_mul_of_nonneg_left hpi_x zero_le_four
    exact Eq.subst
      (motive := fun r : ℝ => r ≤ 4 * (4 * x))
      (mul_assoc (4 : ℝ) Real.pi x).symm
      hmul
  have hfour_four :
      4 * (4 * x) = 16 * x := by
    calc
      4 * (4 * x) = (4 * 4 : ℝ) * x :=
        (mul_assoc (4 : ℝ) 4 x).symm
      _ = 16 * x :=
        congrArg (fun r : ℝ => r * x)
          (show (4 * 4 : ℝ) = 16 from rfl)
  have hpi_bound :
      4 * Real.pi * x ≤ 16 * x :=
    Eq.subst
      (motive := fun r : ℝ => 4 * Real.pi * x ≤ r)
      hfour_four
      hfour_pi_x
  have hreduce :
      4 * (x + 1) + 4 * Real.pi * x ≤
        4 * (x + 1) + 16 * x :=
    add_le_add_left hpi_bound (4 * (x + 1))
  have hleft_expand :
      4 * (x + 1) + 16 * x =
        20 * x + 4 := by
    have hfour_expand :
        4 * (x + 1) = 4 * x + 4 := by
      calc
        4 * (x + 1) = 4 * x + 4 * 1 :=
          mul_add (4 : ℝ) x 1
        _ = 4 * x + 4 :=
          congrArg (fun r : ℝ => 4 * x + r)
            (mul_one (4 : ℝ))
    have hcomm :
        (4 * x + 4) + 16 * x =
          (4 * x + 16 * x) + 4 := by
      calc
        (4 * x + 4) + 16 * x =
            4 * x + (4 + 16 * x) :=
          add_assoc (4 * x) 4 (16 * x)
        _ = 4 * x + (16 * x + 4) :=
          congrArg (fun r : ℝ => 4 * x + r)
            (add_comm 4 (16 * x))
        _ = (4 * x + 16 * x) + 4 :=
          (add_assoc (4 * x) (16 * x) 4).symm
    have hfold :
        4 * x + 16 * x = 20 * x := by
      calc
        4 * x + 16 * x = (4 + 16 : ℝ) * x :=
          (add_mul (4 : ℝ) 16 x).symm
        _ = 20 * x :=
          congrArg (fun r : ℝ => r * x)
            (show (4 + 16 : ℝ) = 20 from rfl)
    calc
      4 * (x + 1) + 16 * x =
          (4 * x + 4) + 16 * x :=
        congrArg (fun r : ℝ => r + 16 * x) hfour_expand
      _ = (4 * x + 16 * x) + 4 :=
        hcomm
      _ = 20 * x + 4 :=
        congrArg (fun r : ℝ => r + 4) hfold
  have hright_expand :
      20 * (x + 1) = 20 * x + 20 := by
    calc
      20 * (x + 1) = 20 * x + 20 * 1 :=
        mul_add (20 : ℝ) x 1
      _ = 20 * x + 20 :=
        congrArg (fun r : ℝ => 20 * x + r)
          (mul_one (20 : ℝ))
  have hfour_le_twenty : (4 : ℝ) ≤ 20 := by
    have hsixteen_nonneg : 0 ≤ (16 : ℝ) :=
      zero_le_ofNat
    calc
      (4 : ℝ) ≤ 4 + 16 :=
        le_add_of_nonneg_right hsixteen_nonneg
      _ = 20 :=
        rfl
  have hcore :
      20 * x + 4 ≤ 20 * x + 20 :=
    add_le_add_left hfour_le_twenty (20 * x)
  exact le_trans hreduce
    (Eq.subst
      (motive := fun left : ℝ =>
        left ≤ 20 * (x + 1))
      hleft_expand.symm
      (Eq.subst
        (motive := fun right : ℝ =>
          20 * x + 4 ≤ right)
        hright_expand.symm
        hcore))

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
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b)
    (hsep :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b
        (‖t‖ / ((b + 1 : ℕ) : ℝ))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
        20 * (((b + 1 : ℕ) : ℝ) / ‖t‖ + 1) := by
  let λ : ℝ := ‖t‖ / ((b + 1 : ℕ) : ℝ)
  have hλ_pos : 0 < λ :=
    Complex.logarithmicPhase_block_lowerParameter_pos t ht b
  have hfirst :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
          4 * (λ⁻¹ + 1) + 4 * Real.pi * λ⁻¹ :=
    Complex.realPhase_firstDerivative_integer_block_bound
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      ha hab hλ_pos
      hderiv_antitone
      hderiv_lower
      hinc_mono
      hred_mono
      hsep
  have hλ_inv :
      λ⁻¹ = ((b + 1 : ℕ) : ℝ) / ‖t‖ :=
    Complex.logarithmicPhase_block_lowerParameter_inv_eq t ht b
  have hexact :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
          4 * (((b + 1 : ℕ) : ℝ) / ‖t‖ + 1) +
            4 * Real.pi * (((b + 1 : ℕ) : ℝ) / ‖t‖) :=
    Eq.subst
    (motive := fun scale : ℝ =>
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
          4 * (scale + 1) + 4 * Real.pi * scale)
    hλ_inv
    hfirst
  have hscale_nonneg :
      0 ≤ ((b + 1 : ℕ) : ℝ) / ‖t‖ := by
    have ht_pos : 0 < ‖t‖ :=
      lt_of_lt_of_le zero_lt_one ht
    exact div_nonneg (Nat.cast_nonneg (b + 1)) ht_pos.le
  exact le_trans hexact
    (Complex.logarithmicPhase_exact_block_constant_le_twenty hscale_nonneg)

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
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b)
    (hsep :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b
        (‖t‖ / ((b + 1 : ℕ) : ℝ))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.boundaryLineOnePointRealParam_logarithmicPhaseFunction t n‖ ≤
        20 * (((b + 1 : ℕ) : ℝ) / ‖t‖ + 1) := by
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
          20 * (((b + 1 : ℕ) : ℝ) / ‖t‖ + 1) :=
    Complex.logarithmicPhaseRealPhase_firstDerivative_integer_block_bound
      t ht ha hab
      (Complex.logarithmicPhaseRealPhase_deriv_norm_antitoneOn_integer_block t ha hab)
      (fun x hx =>
        Complex.logarithmicPhaseRealPhase_deriv_norm_block_lower_bound t ha hab hx)
      hinc_mono
      hred_mono
      hsep
  exact Eq.subst
    (motive := fun S : ℂ =>
      ‖S‖ ≤ 20 * (((b + 1 : ℕ) : ℝ) / ‖t‖ + 1))
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
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b)
    (hsep :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) a b
        (‖t‖ / ((b + 1 : ℕ) : ℝ))) :
    ‖∑ n ∈ Finset.Icc a b,
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        20 * (((b + 1 : ℕ) : ℝ) / ‖t‖ + 1) := by
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
          20 * (((b + 1 : ℕ) : ℝ) / ‖t‖ + 1) :=
    Complex.logarithmicPhase_firstDerivative_integer_block_bound
      t ht ha hab
      (Complex.logarithmicPhase_deriv_norm_antitoneOn_integer_block t ha hab)
      (fun x hx =>
        Complex.logarithmicPhase_deriv_norm_block_lower_bound t ha hab hx)
      hinc_mono
      hred_mono
      hsep
  exact Eq.subst
    (motive := fun S : ℂ =>
      ‖S‖ ≤ 20 * (((b + 1 : ℕ) : ℝ) / ‖t‖ + 1))
    hsample.symm
    hblock

/-- The one-block estimate is already bounded by the dyadic-cover expression
used by the global theorem. -/
theorem Complex.logarithmicPhase_single_block_le_dyadic_cover_expression
    (t : ℝ)
    (N : ℕ) :
    20 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + 1) ≤
      20 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1) := by
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
  exact mul_le_mul_of_nonneg_left hinside (Nat.cast_nonneg 20)

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
                  20 * (((b + 1 : ℕ) : ℝ) / ‖t‖ + 1)) :
    ∀ t : ℝ,
      1 ≤ ‖t‖ →
        ∀ N : ℕ,
          ‖∑ n ∈ Finset.Icc 1 N,
            ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
              20 *
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
        0 ≤ 20 *
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
      exact mul_nonneg (Nat.cast_nonneg 20) hinside_nonneg
    exact Eq.subst
      (motive := fun S : ℂ =>
        ‖S‖ ≤
          20 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1))
      hsum_zero.symm
      htarget_nonneg
  · have hN_pos : 1 ≤ N :=
      Nat.succ_le_of_lt (Nat.pos_of_ne_zero hN)
    have hsingle :
        ‖∑ n ∈ Finset.Icc 1 N,
          ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
            20 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + 1) :=
      hblock t ht (by decide : 1 ≤ 1) hN_pos
    have hcover :
        20 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + 1) ≤
          20 * (((N + 1 : ℕ) : ℝ) / ‖t‖ + Nat.log2 (N + 1) + 1) :=
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
          norm_num [Real.log_one]
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
                Complex.realPhase_reducedIntegerIncrementMonotoneOn
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
          t ht ha hab hfd.1 hfd.2.1 hfd.2.2)
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
                Complex.realPhase_reducedIntegerIncrementMonotoneOn
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
                Complex.realPhase_reducedIntegerIncrementMonotoneOn
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
                Complex.realPhase_reducedIntegerIncrementMonotoneOn
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
              Complex.realPhase_reducedIntegerIncrementMonotoneOn
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
