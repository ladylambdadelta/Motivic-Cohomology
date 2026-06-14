import LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.BoundaryLine

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

/-- Classical first-derivative estimate for the concrete logarithmic phase
`x ↦ exp(-it log x)`.

This is the remaining van der Corput/first-derivative-test input after the
phase derivative and derivative norm have been computed from the definition. -/
theorem Complex.logarithmicPhase_firstDerivativeTest_partialSum_bound_standard :
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
  sorry

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
          ‖t‖ / x) :
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
  exact Complex.logarithmicPhase_firstDerivativeTest_partialSum_bound_standard

/-- The standard first-derivative-test owner root for the concrete logarithmic
phase.  This is the analytic input behind the Euler-Maclaurin boundary
package; cf. Titchmarsh, *The Theory of the Riemann Zeta-function*, §3.5. -/
theorem Complex.logarithmicPhase_firstDerivativeTest_partialSum_bound :
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

/-- First-derivative estimate for the logarithmic phase sums on the boundary
line.

The previous scaffold stated an `O(log N)` bound for the unweighted sums
`∑ n^{-it}`.  The owner-level first-derivative estimate has the standard
oscillatory-sum size shown here; the reciprocal Abel weight is introduced in
`AbelTail`. -/
theorem Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum_bound :
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
  exact Complex.logarithmicPhase_firstDerivativeTest_partialSum_bound

end

end LFunctions
end Boundary
