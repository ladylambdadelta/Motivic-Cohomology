import Mathlib.MeasureTheory.Integral.Periodic
import Mathlib.MeasureTheory.Measure.Restrict
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.LogSineIntegral.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.ZeroMultiplicityCore.Owner

/-!
# Log-sine and unit-circle boundary kernel

This owner layer was split from `LogSineCircleKernel.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

noncomputable def realSinePowerIntegral
    (s : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..Real.pi, (Real.sin u) ^ s

/-- The half-interval sine-power integral on `[0, π/2]`. -/
noncomputable def realSinePowerHalfIntegral
    (s : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..(Real.pi / 2), (Real.sin u) ^ s

/-- The Gamma-ratio appearing in the classical sine-power integral.

For `-1 < s`, it is equal to `∫₀^π sin(u)^s du`. -/
noncomputable def realSinePowerGammaRatio
    (s : ℝ) : ℝ :=
  Real.sqrt Real.pi *
    Real.Gamma ((s + 1) / 2) /
      Real.Gamma (s / 2 + 1)

/-- The real Euler-Beta integral attached to the sine-power exponent.

Mathlib's owner Beta integral is complex-valued; for the real positive
parameters used here, the real part is the classical real Beta integral. -/
noncomputable def realSinePowerEulerBetaIntegral
    (s : ℝ) : ℝ :=
  (Complex.betaIntegral (((s + 1) / 2 : ℝ) : ℂ) ((1 / 2 : ℝ) : ℂ)).re

/-- Real logarithmic derivative of the Gamma function on its regular locus.

This is the classical digamma function `ψ(x) = Γ'(x) / Γ(x)`, expressed using
`deriv` so it can consume mathlib's differentiability theorem for `Real.Gamma`.
-/
noncomputable def realGammaLogDeriv
    (x : ℝ) : ℝ :=
  deriv Real.Gamma x / Real.Gamma x

/-- Elementary scalar cancellation for the half-interval normalization. -/
theorem real_two_mul_one_half_mul
    (x : ℝ) :
    2 * ((1 / 2 : ℝ) * x) = x := by
  have htwo_half : (2 : ℝ) * (1 / 2 : ℝ) = 1 := by
    calc
      (2 : ℝ) * (1 / 2 : ℝ) = (2 : ℝ) * (2 : ℝ)⁻¹ := by
        exact congrArg (fun y : ℝ => (2 : ℝ) * y) (one_div (2 : ℝ))
      _ = 1 := by
        exact mul_inv_cancel₀ two_ne_zero
  calc
    2 * ((1 / 2 : ℝ) * x) = (2 * (1 / 2 : ℝ)) * x := by
      exact (mul_assoc (2 : ℝ) (1 / 2 : ℝ) x).symm
    _ = 1 * x := by
      exact congrArg (fun y : ℝ => y * x) htwo_half
    _ = x := by
      exact one_mul x

/-- Strict lower bound for the left Euler-Beta parameter in the sine-power integral. -/
theorem realSinePowerEulerBeta_leftParameter_pos
    {s : ℝ}
    (hs : -1 < s) :
    0 < (s + 1) / 2 := by
  have hshift : (-1 : ℝ) + 1 < s + 1 :=
    add_lt_add_right hs 1
  have hsum : 0 < s + 1 := by
    have hzero : (-1 : ℝ) + 1 = 0 :=
      neg_add_cancel 1
    exact
      Eq.subst
        (motive := fun x : ℝ => x < s + 1)
        hzero
        hshift
  exact div_pos hsum zero_lt_two

/-- Strict lower bound for the right Euler-Beta parameter in the sine-power integral. -/
theorem realSinePowerEulerBeta_rightParameter_pos :
    0 < (1 / 2 : ℝ) :=
  one_half_pos

/-- Symmetry of the sine-power integral about `π/2`.

For `-1 < s`, the endpoint singularities are integrable and the substitution
`u ↦ π - u` identifies the two halves of `[0,π]`. -/
theorem realSinePowerIntegral_eq_two_mul_halfIntegral
    (s : ℝ)
    (hs : -1 < s) :
    realSinePowerIntegral s =
      2 * realSinePowerHalfIntegral s := by
  exact _root_.LFunctions.Real.sinePowerIntegral_eq_two_mul_halfIntegral s hs

/-- Euler-Beta substitution for the half sine-power integral.

The substitution `t = sin² u` on `[0,π/2]` gives
`∫₀^{π/2} sin(u)^s du = 1/2 * B((s+1)/2, 1/2)`. -/
theorem realSinePowerHalfIntegral_eq_half_eulerBetaIntegral
    (s : ℝ)
    (hs : -1 < s) :
    realSinePowerHalfIntegral s =
      (1 / 2 : ℝ) * realSinePowerEulerBetaIntegral s := by
  exact _root_.LFunctions.Real.sinePowerHalfIntegral_eq_half_eulerBetaIntegral s hs

/-- The sine-power integral is the corresponding Euler-Beta integral. -/
theorem realSinePowerIntegral_eq_eulerBetaIntegral
    (s : ℝ)
    (hs : -1 < s) :
    realSinePowerIntegral s =
      realSinePowerEulerBetaIntegral s := by
  have hsplit :
      realSinePowerIntegral s =
        2 * realSinePowerHalfIntegral s :=
    realSinePowerIntegral_eq_two_mul_halfIntegral s hs
  have hhalf :
      realSinePowerHalfIntegral s =
        (1 / 2 : ℝ) * realSinePowerEulerBetaIntegral s :=
    realSinePowerHalfIntegral_eq_half_eulerBetaIntegral s hs
  calc
    realSinePowerIntegral s =
        2 * realSinePowerHalfIntegral s := hsplit
    _ = 2 * ((1 / 2 : ℝ) * realSinePowerEulerBetaIntegral s) := by
      exact congrArg (fun x : ℝ => 2 * x) hhalf
    _ = realSinePowerEulerBetaIntegral s := by
      exact real_two_mul_one_half_mul (realSinePowerEulerBetaIntegral s)

/-- Beta/Gamma comparison for the sine-power Euler-Beta integral.

This is the specialization of
`Complex.Gamma_mul_Gamma_eq_betaIntegral` to the positive real parameters
`(s+1)/2` and `1/2`, followed by `Γ(1/2)=sqrt π` and the identity
`(s+1)/2 + 1/2 = s/2 + 1`. -/
theorem realSinePowerEulerBetaIntegral_eq_gammaRatio
    (s : ℝ)
    (hs : -1 < s) :
    realSinePowerEulerBetaIntegral s =
      realSinePowerGammaRatio s := by
  exact _root_.LFunctions.Real.sinePowerEulerBetaIntegral_eq_gammaRatio s hs

/-- Beta/Gamma evaluation of the sine-power integral.

This is the standard formula
`∫₀^π sin(u)^s du =
sqrt(π) Γ((s+1)/2) / Γ(s/2+1)`, valid for `-1 < s`.
Classically it follows by symmetry, the substitution `t = sin² u` on
`[0,π/2]`, and Euler's Beta integral. -/
theorem real_integral_sin_rpow_zero_pi_eq_gammaRatio
    (s : ℝ)
    (hs : -1 < s) :
    realSinePowerIntegral s =
      realSinePowerGammaRatio s := by
  exact
    Eq.trans
      (realSinePowerIntegral_eq_eulerBetaIntegral s hs)
      (realSinePowerEulerBetaIntegral_eq_gammaRatio s hs)

/-- Near exponent `0`, the sine-power integral is represented by the
Beta/Gamma ratio. -/
theorem realSinePowerIntegral_eventuallyEq_gammaRatio_at_zero :
    (fun s : ℝ => realSinePowerIntegral s) =ᶠ[𝓝 (0 : ℝ)]
      (fun s : ℝ => realSinePowerGammaRatio s) := by
  have hnear :
      ∀ᶠ s in 𝓝 (0 : ℝ), -1 < s :=
    Ioi_mem_nhds (show -1 < (0 : ℝ) by exact neg_lt_zero.mpr one_pos)
  exact
    hnear.mono
      (fun s hs =>
        real_integral_sin_rpow_zero_pi_eq_gammaRatio s hs)

/-- Differentiating the sine-power integral at exponent `0` gives the
log-sine integral.

This is the standard differentiation-under-the-integral step:
`d/ds sin(u)^s |_{s=0} = log(sin u)`, with endpoint domination supplied by
the logarithmic endpoint models. -/
theorem realSinePowerIntegral_hasDerivAt_zero :
    HasDerivAt
      realSinePowerIntegral
      (∫ u in (0 : ℝ)..Real.pi, Real.log (Real.sin u))
      0 := by
  exact _root_.LFunctions.Real.sinePowerIntegral_hasDerivAt_zero

/-- Legendre duplication in logarithmic-derivative form at `1/2`.

This is the exact Gamma-function constant needed for the log-sine integral:
`ψ(1) - ψ(1/2) = 2 log 2`.  It follows by differentiating
`Γ(x) Γ(x+1/2) = Γ(2x) 2^(1-2x) sqrt π` at `x = 1/2` and cancelling
nonzero Gamma values. -/
theorem realGammaLogDeriv_one_sub_half_eq_two_log_two :
    realGammaLogDeriv 1 - realGammaLogDeriv (1 / 2) =
      2 * Real.log 2 := by
  exact _root_.LFunctions.Real.gammaLogDeriv_one_sub_half_eq_two_log_two

/-- Reversed Legendre log-derivative difference at the half-point.

This is the sign-normalized form used by the sine-power Gamma-ratio
derivative. -/
theorem realGammaLogDeriv_half_sub_one_eq_neg_two_log_two :
    realGammaLogDeriv (1 / 2) - realGammaLogDeriv 1 =
      -(2 * Real.log 2) := by
  calc
    realGammaLogDeriv (1 / 2) - realGammaLogDeriv 1 =
        -(realGammaLogDeriv 1 - realGammaLogDeriv (1 / 2)) := by
      exact (neg_sub (realGammaLogDeriv 1) (realGammaLogDeriv (1 / 2))).symm
    _ = -(2 * Real.log 2) := by
      exact congrArg Neg.neg realGammaLogDeriv_one_sub_half_eq_two_log_two

/-- The Gamma-ratio derivative value after inserting Legendre duplication.

This is the scalar algebra separating the classical Gamma input from the
ordinary derivative transport. -/
theorem realSinePowerGammaRatio_logDeriv_derivativeValue_eq_neg_pi_log_two :
    Real.pi *
        ((realGammaLogDeriv (1 / 2) - realGammaLogDeriv 1) / 2) =
      -Real.pi * Real.log 2 := by
  calc
    Real.pi *
        ((realGammaLogDeriv (1 / 2) - realGammaLogDeriv 1) / 2) =
        Real.pi * (-(2 * Real.log 2) / 2) := by
      exact congrArg
        (fun x : ℝ => Real.pi * (x / 2))
        realGammaLogDeriv_half_sub_one_eq_neg_two_log_two
    _ = Real.pi * (-(Real.log 2)) := by
      have hcancel :
          (2 * Real.log 2) / 2 = Real.log 2 :=
        mul_div_cancel_left₀ (Real.log 2) two_ne_zero
      have hneg_div :
          -(2 * Real.log 2) / 2 = -((2 * Real.log 2) / 2) :=
        neg_div 2 (2 * Real.log 2)
      have hneg_cancel :
          -(2 * Real.log 2) / 2 = -Real.log 2 :=
        hneg_div.trans (congrArg Neg.neg hcancel)
      exact congrArg
        (fun x : ℝ => Real.pi * x)
        hneg_cancel
    _ = -(Real.pi * Real.log 2) := by
      exact (neg_mul_eq_mul_neg Real.pi (Real.log 2)).symm
    _ = -Real.pi * Real.log 2 := by
      exact neg_mul_eq_neg_mul Real.pi (Real.log 2)

/-- Derivative of the sine-power Gamma-ratio in terms of Gamma logarithmic
derivatives.

For `R(s) = sqrt(π) Γ((s+1)/2) / Γ(s/2+1)`, the logarithmic derivative is
`R'(0)/R(0) = (ψ(1/2)-ψ(1))/2`; since `R(0)=π`, the derivative is
`π * (ψ(1/2)-ψ(1)) / 2`. -/
theorem realSinePowerGammaRatio_hasDerivAt_zero_from_logDeriv :
    HasDerivAt
      realSinePowerGammaRatio
      (Real.pi *
        ((realGammaLogDeriv (1 / 2) - realGammaLogDeriv 1) / 2))
      0 := by
  exact _root_.LFunctions.Real.sinePowerGammaRatio_hasDerivAt_zero_from_logDeriv

/-- Derivative at zero of the Gamma-ratio for the sine-power integral.

Using the Legendre duplication formula in logarithmic derivative form at
`s = 0`, the derivative of
`sqrt(π) Γ((s+1)/2) / Γ(s/2+1)` is `-π log 2`. -/
theorem realSinePowerGammaRatio_hasDerivAt_zero :
    HasDerivAt
      realSinePowerGammaRatio
      (-Real.pi * Real.log 2)
      0 := by
  have hder :
      HasDerivAt
        realSinePowerGammaRatio
        (Real.pi *
          ((realGammaLogDeriv (1 / 2) - realGammaLogDeriv 1) / 2))
        0 :=
    realSinePowerGammaRatio_hasDerivAt_zero_from_logDeriv
  exact
    Eq.subst
      (motive := fun d : ℝ => HasDerivAt realSinePowerGammaRatio d 0)
      realSinePowerGammaRatio_logDeriv_derivativeValue_eq_neg_pi_log_two
      hder

/-- Identification of the derivative of the sine-power integral with the
derivative of its Gamma-ratio model at exponent `0`. -/
theorem realSinePowerIntegral_logDerivative_eq_gammaRatio_derivative :
    (∫ u in (0 : ℝ)..Real.pi, Real.log (Real.sin u)) =
      -Real.pi * Real.log 2 := by
  have hsin :
      HasDerivAt
        realSinePowerIntegral
        (∫ u in (0 : ℝ)..Real.pi, Real.log (Real.sin u))
        0 :=
    realSinePowerIntegral_hasDerivAt_zero
  have hgamma :
      HasDerivAt
        realSinePowerGammaRatio
        (-Real.pi * Real.log 2)
        0 :=
    realSinePowerGammaRatio_hasDerivAt_zero
  have heq :
      (fun s : ℝ => realSinePowerIntegral s) =ᶠ[𝓝 (0 : ℝ)]
        (fun s : ℝ => realSinePowerGammaRatio s) :=
    realSinePowerIntegral_eventuallyEq_gammaRatio_at_zero
  have hsin_as_gamma :
      HasDerivAt
        realSinePowerGammaRatio
        (∫ u in (0 : ℝ)..Real.pi, Real.log (Real.sin u))
        0 :=
    hsin.congr_of_eventuallyEq heq.symm
  exact
    HasDerivAt.unique hsin_as_gamma hgamma

/-- The classical sine-log integral on `[0, π]`.

This is the deepest real-variable integral behind the boundary-zero Jensen
kernel: `∫₀^π log(sin u) du = -π log 2`. -/
theorem real_integral_log_sin_zero_pi :
    (∫ u in (0 : ℝ)..Real.pi, Real.log (Real.sin u)) =
      -Real.pi * Real.log 2 := by
  exact realSinePowerIntegral_logDerivative_eq_gammaRatio_derivative


end
end LFunctions
end Boundary
