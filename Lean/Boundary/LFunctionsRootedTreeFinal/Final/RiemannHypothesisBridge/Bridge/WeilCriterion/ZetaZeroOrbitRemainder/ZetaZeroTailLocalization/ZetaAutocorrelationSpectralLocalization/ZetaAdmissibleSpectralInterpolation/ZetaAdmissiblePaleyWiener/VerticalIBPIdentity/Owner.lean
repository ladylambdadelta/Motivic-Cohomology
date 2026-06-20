import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.VerticalDerivativeSource.Owner

/-!
# Paley-Wiener vertical integration-by-parts identity

This file owns the first vertical-line integration-by-parts identity, its
frequency solving algebra, and the one-step high-frequency norm comparison. It
is copy-first extracted from the current Paley-Wiener owner file and is not
imported by that parent yet, so declaration names intentionally match the
existing owner surface.
-/

open scoped Real
open MeasureTheory

namespace Boundary
namespace LFunctions

open ZetaAdmissibleFunction

/-- The compact-support boundary term for the horizontal twist vanishes at any lower and
upper cutoffs chosen strictly outside the certified support interval. -/
theorem zetaPaleyWienerVerticalLineIBP_boundaryTerm_eq_zero_of_strict_bounds
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (x y lower upper : ℝ) (hlower : lower < I.lower) (hupper : I.upper < upper) :
    zetaPaleyWienerHorizontalTwist f x upper *
        zetaPaleyWienerVerticalOscillation y upper -
      zetaPaleyWienerHorizontalTwist f x lower *
        zetaPaleyWienerVerticalOscillation y lower =
      0 := by
  have hupper_zero :
      zetaPaleyWienerHorizontalTwist f x upper = 0 :=
    zetaPaleyWienerHorizontalTwist_eq_zero_of_supportInterval_lt
      f I x upper hupper
  have hlower_zero :
      zetaPaleyWienerHorizontalTwist f x lower = 0 :=
    zetaPaleyWienerHorizontalTwist_eq_zero_of_lt_supportInterval
      f I x lower hlower
  calc
    zetaPaleyWienerHorizontalTwist f x upper *
          zetaPaleyWienerVerticalOscillation y upper -
        zetaPaleyWienerHorizontalTwist f x lower *
          zetaPaleyWienerVerticalOscillation y lower
        = 0 * zetaPaleyWienerVerticalOscillation y upper -
            zetaPaleyWienerHorizontalTwist f x lower *
              zetaPaleyWienerVerticalOscillation y lower := by
          exact congrArg
            (fun v : ℂ =>
              v * zetaPaleyWienerVerticalOscillation y upper -
                zetaPaleyWienerHorizontalTwist f x lower *
                  zetaPaleyWienerVerticalOscillation y lower)
            hupper_zero
    _ = 0 - zetaPaleyWienerHorizontalTwist f x lower *
            zetaPaleyWienerVerticalOscillation y lower := by
          exact congrArg
            (fun v : ℂ =>
              v - zetaPaleyWienerHorizontalTwist f x lower *
                zetaPaleyWienerVerticalOscillation y lower)
            (zero_mul (zetaPaleyWienerVerticalOscillation y upper))
    _ = 0 - 0 * zetaPaleyWienerVerticalOscillation y lower := by
          exact congrArg
            (fun v : ℂ => 0 - v * zetaPaleyWienerVerticalOscillation y lower)
            hlower_zero
    _ = 0 - 0 := by
          exact congrArg
            (fun v : ℂ => 0 - v)
            (zero_mul (zetaPaleyWienerVerticalOscillation y lower))
    _ = 0 := sub_zero (0 : ℂ)

/-- The vertical-line integration-by-parts identity before solving for the kernel
integral. -/
theorem zetaPaleyWienerVerticalLineKernel_integral_mul_frequency_eq_neg_derivativeIntegral
    (f : ZetaAdmissibleFunction) (_I : ZetaPaleyWienerSupportInterval f)
    (x y : ℝ) :
    (Complex.I * (y : ℂ)) *
        (∫ t : ℝ, zetaPaleyWienerVerticalLineKernel f x y t) =
      -zetaPaleyWienerVerticalLineIBPDerivativeIntegral f x y := by
  let A : ℂ := Complex.I * (y : ℂ)
  let H : ℝ → ℂ := fun t => zetaPaleyWienerHorizontalTwist f x t
  let V : ℝ → ℂ := fun t => zetaPaleyWienerVerticalOscillation y t
  let D : ℝ → ℂ := fun t => zetaPaleyWienerVerticalLineIBPDerivative f x t
  have hH :
      ∀ t : ℝ, HasDerivAt H (D t) t := by
    intro t
    exact hasDerivAt_zetaPaleyWienerHorizontalTwist f x t
  have hV :
      ∀ t : ℝ, HasDerivAt V (A * V t) t := by
    intro t
    exact hasDerivAt_zetaPaleyWienerVerticalOscillation y t
  have hHV :
      Integrable (fun t : ℝ => H t * V t) := by
    exact zetaPaleyWienerVerticalLineKernel_integrable f x y
  have hHDV :
      Integrable (fun t : ℝ => H t * (A * V t)) := by
    have hcontinuous :
        Continuous (fun t : ℝ => H t * (A * V t)) := by
      exact (zetaPaleyWienerHorizontalTwist_continuous f x).mul
        (continuous_const.mul
          (Complex.continuous_exp.comp
            ((continuous_const.mul continuous_const).mul Complex.continuous_ofReal)))
    have hsupport :
        HasCompactSupport (fun t : ℝ => H t * (A * V t)) := by
      exact (zetaPaleyWienerHorizontalTwist_hasCompactSupport f x).mul_right
    exact hcontinuous.integrable_of_hasCompactSupport hsupport
  have hDV :
      Integrable (fun t : ℝ => D t * V t) := by
    exact zetaPaleyWienerVerticalLineIBPDerivative_integrable f x y
  have hibp :
      (∫ t : ℝ, H t * (A * V t)) =
        -∫ t : ℝ, D t * V t :=
    MeasureTheory.integral_mul_deriv_eq_deriv_mul_of_integrable
      hH hV hHDV hDV hHV
  have hleft_integrand :
      (fun t : ℝ => H t * (A * V t)) =
        fun t : ℝ => A * (H t * V t) := by
    funext t
    calc
      H t * (A * V t) = (H t * A) * V t := by
        exact (mul_assoc (H t) A (V t)).symm
      _ = (A * H t) * V t := by
        exact congrArg (fun v : ℂ => v * V t) (mul_comm (H t) A)
      _ = A * (H t * V t) := by
        exact mul_assoc A (H t) (V t)
  have hleft :
      (∫ t : ℝ, H t * (A * V t)) =
        A * (∫ t : ℝ, zetaPaleyWienerVerticalLineKernel f x y t) := by
    calc
      (∫ t : ℝ, H t * (A * V t))
          = ∫ t : ℝ, A * (H t * V t) := by
            exact congrArg
              (fun q : ℝ → ℂ => ∫ t : ℝ, q t)
              hleft_integrand
      _ = A * (∫ t : ℝ, H t * V t) := by
            exact integral_smul A (fun t : ℝ => H t * V t)
      _ = A * (∫ t : ℝ, zetaPaleyWienerVerticalLineKernel f x y t) := by
            exact congrArg
              (fun v : ℂ => A * v)
              (complex_integral_congr_of_pointwise_eq
                (fun t : ℝ => H t * V t)
                (fun t : ℝ => zetaPaleyWienerVerticalLineKernel f x y t)
                (fun t : ℝ => rfl))
  have hright :
      (∫ t : ℝ, D t * V t) =
        zetaPaleyWienerVerticalLineIBPDerivativeIntegral f x y := by
    exact complex_integral_congr_of_pointwise_eq
      (fun t : ℝ => D t * V t)
      (fun t : ℝ =>
        zetaPaleyWienerVerticalLineIBPDerivative f x t *
          zetaPaleyWienerVerticalOscillation y t)
      (fun t : ℝ => rfl)
  exact Eq.subst
    (motive := fun v : ℂ =>
      v = -zetaPaleyWienerVerticalLineIBPDerivativeIntegral f x y)
    hleft
    (Eq.subst
      (motive := fun v : ℂ =>
        (∫ t : ℝ, H t * (A * V t)) = -v)
      hright
      hibp)

/-- The negated integration-by-parts identity in derivative-integral-first form. -/
theorem zetaPaleyWienerVerticalLineIBPDerivativeIntegral_eq_neg_frequency_mul_kernelIntegral
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (x y : ℝ) :
    zetaPaleyWienerVerticalLineIBPDerivativeIntegral f x y =
      -(Complex.I * (y : ℂ)) *
        (∫ t : ℝ, zetaPaleyWienerVerticalLineKernel f x y t) := by
  have h :
      (Complex.I * (y : ℂ)) *
          (∫ t : ℝ, zetaPaleyWienerVerticalLineKernel f x y t) =
        -zetaPaleyWienerVerticalLineIBPDerivativeIntegral f x y :=
    zetaPaleyWienerVerticalLineKernel_integral_mul_frequency_eq_neg_derivativeIntegral
      f I x y
  exact Eq.trans
    (Eq.trans
      (neg_neg (zetaPaleyWienerVerticalLineIBPDerivativeIntegral f x y)).symm
      (congrArg Neg.neg h.symm))
    (neg_mul (Complex.I * (y : ℂ))
      (∫ t : ℝ, zetaPaleyWienerVerticalLineKernel f x y t)).symm

/-- The frequency multiplier times the displayed inverse factor is `-1`. -/
theorem zetaPaleyWiener_frequency_mul_I_inverse_eq_neg_one
    (y : ℝ) (hy : (y : ℂ) ≠ 0) :
    (Complex.I * (y : ℂ)) * (Complex.I * (y : ℂ)⁻¹) = -1 := by
  calc
    (Complex.I * (y : ℂ)) * (Complex.I * (y : ℂ)⁻¹)
        = (Complex.I * Complex.I) * ((y : ℂ) * (y : ℂ)⁻¹) := by
          exact mul_mul_mul_comm Complex.I (y : ℂ) Complex.I ((y : ℂ)⁻¹)
    _ = (-1 : ℂ) * ((y : ℂ) * (y : ℂ)⁻¹) := by
          exact congrArg
            (fun v : ℂ => v * ((y : ℂ) * (y : ℂ)⁻¹))
            Complex.I_mul_I
    _ = (-1 : ℂ) * 1 := by
          exact congrArg
            (fun v : ℂ => (-1 : ℂ) * v)
            (mul_inv_cancel₀ hy)
    _ = -1 := mul_one (-1 : ℂ)

/-- Multiplying the proposed solved form by the vertical frequency recovers the negated
derivative integral. -/
theorem zetaPaleyWiener_frequency_mul_solvedIntegral
    (y : ℝ) (hy : (y : ℂ) ≠ 0) (D : ℂ) :
    (Complex.I * (y : ℂ)) * (Complex.I * (y : ℂ)⁻¹ * D) =
      -D := by
  calc
    (Complex.I * (y : ℂ)) * (Complex.I * (y : ℂ)⁻¹ * D)
        = ((Complex.I * (y : ℂ)) * (Complex.I * (y : ℂ)⁻¹)) * D := by
          exact (mul_assoc (Complex.I * (y : ℂ)) (Complex.I * (y : ℂ)⁻¹) D).symm
    _ = (-1 : ℂ) * D := by
          exact congrArg
            (fun v : ℂ => v * D)
            (zetaPaleyWiener_frequency_mul_I_inverse_eq_neg_one y hy)
    _ = -D := neg_one_mul D

/-- Solving the vertical-line integration-by-parts identity for the original kernel
integral introduces the factor `I * y⁻¹`. -/
theorem zetaPaleyWienerVerticalLineKernel_integral_solve_frequency
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (x y : ℝ) (hy : (y : ℂ) ≠ 0) :
    (∫ t : ℝ, zetaPaleyWienerVerticalLineKernel f x y t) =
      Complex.I * (y : ℂ)⁻¹ *
        zetaPaleyWienerVerticalLineIBPDerivativeIntegral f x y := by
  let K : ℂ := ∫ t : ℝ, zetaPaleyWienerVerticalLineKernel f x y t
  let D : ℂ := zetaPaleyWienerVerticalLineIBPDerivativeIntegral f x y
  let A : ℂ := Complex.I * (y : ℂ)
  have hA : A ≠ 0 :=
    mul_ne_zero Complex.I_ne_zero hy
  have hibp :
      A * K = -D :=
    zetaPaleyWienerVerticalLineKernel_integral_mul_frequency_eq_neg_derivativeIntegral
      f I x y
  have hcandidate :
      A * (Complex.I * (y : ℂ)⁻¹ * D) = -D :=
    zetaPaleyWiener_frequency_mul_solvedIntegral y hy D
  exact mul_left_cancel₀ hA (hibp.trans hcandidate.symm)

/-- One vertical-line integration-by-parts identity before taking norms.

The oscillatory factor is `exp (I * y * t)`, so differentiating it contributes
`I * y`; the inverse factor is therefore `I * y⁻¹`, not just `y⁻¹`. -/
theorem zetaPaleyWienerVerticalLineKernel_integral_eq_I_mul_inverse_mul_derivativeIntegral
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (x y : ℝ) (hy : (y : ℂ) ≠ 0) :
    (∫ t : ℝ, zetaPaleyWienerVerticalLineKernel f x y t) =
      Complex.I * (y : ℂ)⁻¹ *
        zetaPaleyWienerVerticalLineIBPDerivativeIntegral f x y := by
  exact zetaPaleyWienerVerticalLineKernel_integral_solve_frequency
    f I x y hy

/-- The complex unit `I` has norm one. -/
theorem complex_norm_I_eq_one :
    ‖Complex.I‖ = (1 : ℝ) := by
  exact Eq.trans (complex_norm_eq_abs Complex.I) Complex.abs_I

/-- Multiplication by `I` does not change the norm. -/
theorem norm_I_mul_eq_norm
    (w : ℂ) :
    ‖Complex.I * w‖ = ‖w‖ := by
  have hmul : ‖Complex.I * w‖ = ‖Complex.I‖ * ‖w‖ :=
    norm_mul Complex.I w
  exact Eq.trans hmul
    (Eq.trans
      (congrArg (fun v : ℝ => v * ‖w‖) complex_norm_I_eq_one)
      (one_mul ‖w‖))

/-- The `I * y⁻¹` norm is the same as the `y⁻¹` norm. -/
theorem norm_I_mul_inverse_eq_norm_inverse
    (y : ℝ) :
    ‖Complex.I * (y : ℂ)⁻¹‖ = ‖(y : ℂ)⁻¹‖ := by
  exact norm_I_mul_eq_norm ((y : ℂ)⁻¹)

/-- Vertical-line integration by parts after substituting the spectral parameter `z`. -/
theorem zetaLaplaceTransform_eq_I_mul_inverse_mul_verticalLineIBPDerivativeIntegral
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (z : ℂ) (hzhigh : 1 ≤ ‖z.im‖) :
    Boundary.zetaLaplaceTransform f.toZetaTestFunction' z =
      Complex.I * (z.im : ℂ)⁻¹ *
        zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im := by
  have htransform :
      Boundary.zetaLaplaceTransform f.toZetaTestFunction' z =
        ∫ t : ℝ, zetaPaleyWienerVerticalLineKernel f z.re z.im t :=
    zetaLaplaceTransform_eq_verticalLineKernelIntegral f z
  have hfreq :
      (z.im : ℂ) ≠ 0 :=
    zetaPaleyWienerVerticalFrequency_ne_zero_of_high hzhigh
  have hibp :
      (∫ t : ℝ, zetaPaleyWienerVerticalLineKernel f z.re z.im t) =
        Complex.I * (z.im : ℂ)⁻¹ *
          zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im :=
    zetaPaleyWienerVerticalLineKernel_integral_eq_I_mul_inverse_mul_derivativeIntegral
      f I z.re z.im hfreq
  exact htransform.trans hibp

/-- The harmless `I` factor in the vertical-line integration-by-parts identity does not
change the norm comparison. -/
theorem norm_I_mul_inverse_mul_verticalLineIBPDerivativeIntegral_le
    (y : ℝ) (D : ℂ) :
    ‖Complex.I * (y : ℂ)⁻¹ * D‖ ≤ ‖(y : ℂ)⁻¹‖ * ‖D‖ := by
  have hmul :
      ‖Complex.I * (y : ℂ)⁻¹ * D‖ =
        ‖Complex.I * (y : ℂ)⁻¹‖ * ‖D‖ :=
    norm_mul (Complex.I * (y : ℂ)⁻¹) D
  have hleft :
      ‖Complex.I * (y : ℂ)⁻¹‖ = ‖(y : ℂ)⁻¹‖ :=
    norm_I_mul_inverse_eq_norm_inverse y
  exact le_of_eq
    (Eq.trans hmul
      (congrArg (fun v : ℝ => v * ‖D‖) hleft))

/-- Vertical-line integration by parts as a norm identity.

After absorbing the horizontal factor into the source on `re z = x`, integration by
parts on the vertical oscillation gives one inverse vertical-frequency factor. -/
theorem zetaLaplaceTransform_supportInterval_verticalLineIBP_normIdentity
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (z : ℂ)
    (_hzstrip : zetaPaleyWienerInVerticalStrip a b z)
    (hzhigh : 1 ≤ ‖z.im‖) :
    ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ =
      ‖Complex.I * (z.im : ℂ)⁻¹ *
        zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im‖ := by
  have hidentity :
      Boundary.zetaLaplaceTransform f.toZetaTestFunction' z =
        Complex.I * (z.im : ℂ)⁻¹ *
          zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im :=
    zetaLaplaceTransform_eq_I_mul_inverse_mul_verticalLineIBPDerivativeIntegral
      f I z hzhigh
  exact congrArg (fun v : ℂ => ‖v‖) hidentity

/-- One vertical-line integration-by-parts norm comparison.

On the line `re z = x`, the horizontal exponential is part of the source and the remaining
oscillation is `exp (I * y * t)`.  Boundary terms vanish from the fixed compact support
interval, giving one inverse vertical-frequency factor. -/
theorem zetaLaplaceTransform_supportInterval_verticalLineIBP_normComparison
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (a b : ℝ) (z : ℂ)
    (hzstrip : zetaPaleyWienerInVerticalStrip a b z)
    (hzhigh : 1 ≤ ‖z.im‖) :
    ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ ≤
      ‖(z.im : ℂ)⁻¹‖ *
        ‖zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im‖ := by
  have hidentity :
      ‖Boundary.zetaLaplaceTransform f.toZetaTestFunction' z‖ =
        ‖Complex.I * (z.im : ℂ)⁻¹ *
          zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im‖ :=
    zetaLaplaceTransform_supportInterval_verticalLineIBP_normIdentity
      f I a b z hzstrip hzhigh
  have hnorm :
      ‖Complex.I * (z.im : ℂ)⁻¹ *
          zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im‖ ≤
        ‖(z.im : ℂ)⁻¹‖ *
          ‖zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im‖ :=
    norm_I_mul_inverse_mul_verticalLineIBPDerivativeIntegral_le
      z.im
      (zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im)
  exact Eq.subst
    (motive := fun v : ℝ =>
      v ≤ ‖(z.im : ℂ)⁻¹‖ *
          ‖zetaPaleyWienerVerticalLineIBPDerivativeIntegral f z.re z.im‖)
    hidentity.symm
    hnorm

/-- The derivative source used after horizontal twisting is supported in the same compact
support interval. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_eq_zero_off_supportInterval
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (x t : ℝ) (ht_lower : t < I.lower) :
    zetaPaleyWienerVerticalLineIBPDerivative f x t = 0 := by
  have hsource_not :
      t ∉ tsupport f.toZetaTestFunction := by
    intro ht
    exact (not_lt_of_ge (I.lower_mem t ht)) ht_lower
  exact zetaPaleyWienerHorizontalTwistDerivative_eq_zero_of_not_mem_source
    f x t hsource_not

/-- The derivative source used after horizontal twisting vanishes above the support
interval. -/
theorem zetaPaleyWienerHorizontalTwistDerivative_eq_zero_of_supportInterval_lt
    (f : ZetaAdmissibleFunction) (I : ZetaPaleyWienerSupportInterval f)
    (x t : ℝ) (ht_upper : I.upper < t) :
    zetaPaleyWienerVerticalLineIBPDerivative f x t = 0 := by
  have hsource_not :
      t ∉ tsupport f.toZetaTestFunction := by
    intro ht
    exact (not_lt_of_ge (I.upper_mem t ht)) ht_upper
  exact zetaPaleyWienerHorizontalTwistDerivative_eq_zero_of_not_mem_source
    f x t hsource_not

end LFunctions
end Boundary
