import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.LogSineIntegral.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.ZeroMultiplicityCore.Owner

/-!
# Log-sine and unit-circle boundary kernel

This file is a sequential owner sublayer split from the Jensen formula owner.
Declaration order is preserved so downstream import behavior remains routed
through `EntireJensenFormula.Owner`.
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
        exact mul_inv_cancel₀ (2 : ℝ) two_ne_zero
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
      exact sub_eq_neg_sub (realGammaLogDeriv (1 / 2)) (realGammaLogDeriv 1)
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
      exact congrArg
        (fun x : ℝ => Real.pi * x)
        (neg_mul_div_two_cancel (Real.log 2))
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
    hsin.congr_of_eventuallyEq heq
  exact
    HasDerivAt.unique hsin_as_gamma hgamma

/-- The classical sine-log integral on `[0, π]`.

This is the deepest real-variable integral behind the boundary-zero Jensen
kernel: `∫₀^π log(sin u) du = -π log 2`. -/
theorem real_integral_log_sin_zero_pi :
    (∫ u in (0 : ℝ)..Real.pi, Real.log (Real.sin u)) =
      -Real.pi * Real.log 2 := by
  exact realSinePowerIntegral_logDerivative_eq_gammaRatio_derivative

/-- Elementary real algebra used in the unit-circle chord norm-square
calculation. -/
theorem real_one_sub_cos_sq_add_neg_sin_sq_eq_two_mul_one_sub_cos
    (θ : ℝ) :
    (1 - Real.cos θ) ^ 2 + (-Real.sin θ) ^ 2 =
      2 * (1 - Real.cos θ) := by
  let c : ℝ := Real.cos θ
  let s : ℝ := Real.sin θ
  have hs_sq : s ^ 2 = 1 - c ^ 2 := by
    exact Real.sin_sq θ
  have hneg_sq : (-s) ^ 2 = s ^ 2 :=
    neg_sq s
  have hsub_sq : (1 - c) ^ 2 = 1 ^ 2 - 2 * 1 * c + c ^ 2 :=
    sub_sq 1 c
  have hone_sq : (1 : ℝ) ^ 2 = 1 :=
    one_pow 2
  have htwo_one_mul : 2 * (1 : ℝ) * c = 2 * c := by
    exact congrArg (fun x : ℝ => x * c) (mul_one 2)
  have hleft_expand :
      (1 - c) ^ 2 + (-s) ^ 2 =
        (1 - 2 * c + c ^ 2) + s ^ 2 := by
    calc
      (1 - c) ^ 2 + (-s) ^ 2 =
          (1 ^ 2 - 2 * 1 * c + c ^ 2) + (-s) ^ 2 := by
        exact congrArg (fun x : ℝ => x + (-s) ^ 2) hsub_sq
      _ = (1 - 2 * 1 * c + c ^ 2) + (-s) ^ 2 := by
        exact congrArg (fun x : ℝ => (x - 2 * 1 * c + c ^ 2) + (-s) ^ 2) hone_sq
      _ = (1 - 2 * c + c ^ 2) + (-s) ^ 2 := by
        exact congrArg (fun x : ℝ => (1 - x + c ^ 2) + (-s) ^ 2) htwo_one_mul
      _ = (1 - 2 * c + c ^ 2) + s ^ 2 := by
        exact congrArg (fun x : ℝ => (1 - 2 * c + c ^ 2) + x) hneg_sq
  have hgroup :
      (1 - 2 * c + c ^ 2) + s ^ 2 =
        1 - 2 * c + (c ^ 2 + s ^ 2) := by
    calc
      (1 - 2 * c + c ^ 2) + s ^ 2 =
          ((1 - 2 * c) + c ^ 2) + s ^ 2 := by
        exact rfl
      _ = (1 - 2 * c) + (c ^ 2 + s ^ 2) := by
        exact add_assoc (1 - 2 * c) (c ^ 2) (s ^ 2)
      _ = 1 - 2 * c + (c ^ 2 + s ^ 2) := by
        exact rfl
  have hcos_sin : c ^ 2 + s ^ 2 = 1 := by
    exact Eq.trans (add_comm (c ^ 2) (s ^ 2)) (Real.sin_sq_add_cos_sq θ)
  have hcollapse :
      1 - 2 * c + (c ^ 2 + s ^ 2) = 1 - 2 * c + 1 := by
    exact congrArg (fun x : ℝ => 1 - 2 * c + x) hcos_sin
  have hfinal :
      1 - 2 * c + 1 = 2 * (1 - c) := by
    calc
      1 - 2 * c + 1 = (1 + 1) - 2 * c := by
        exact (sub_add_eq_add_sub 1 (2 * c) 1).symm
      _ = 2 - 2 * c := by
        exact congrArg (fun x : ℝ => x - 2 * c) (one_add_one_eq_two)
      _ = 2 * 1 - 2 * c := by
        exact congrArg (fun x : ℝ => x - 2 * c) (Eq.symm (mul_one 2))
      _ = 2 * (1 - c) := by
        exact (mul_sub 2 1 c).symm
  calc
    (1 - Real.cos θ) ^ 2 + (-Real.sin θ) ^ 2 =
        (1 - c) ^ 2 + (-s) ^ 2 := by
      exact rfl
    _ = (1 - 2 * c + c ^ 2) + s ^ 2 := by
      exact hleft_expand
    _ = 1 - 2 * c + (c ^ 2 + s ^ 2) := by
      exact hgroup
    _ = 1 - 2 * c + 1 := by
      exact hcollapse
    _ = 2 * (1 - c) := by
      exact hfinal
    _ = 2 * (1 - Real.cos θ) := by
      exact rfl

/-- Elementary real algebra used in the half-angle chord identity. -/
theorem real_two_abs_sin_half_sq_eq_two_mul_one_sub_cos
    (θ : ℝ) :
    (2 * |Real.sin (θ / 2)|) ^ 2 =
      2 * (1 - Real.cos θ) := by
  let u : ℝ := θ / 2
  have habs_sq : |Real.sin u| ^ 2 = (Real.sin u) ^ 2 :=
    sq_abs (Real.sin u)
  have hmul_sq :
      (2 * |Real.sin u|) ^ 2 = 2 ^ 2 * |Real.sin u| ^ 2 :=
    mul_pow 2 |Real.sin u| 2
  have htwo_sq : (2 : ℝ) ^ 2 = 4 :=
    rfl
  have hsin_half :
      (Real.sin u) ^ 2 = 1 / 2 - Real.cos (2 * u) / 2 :=
    Real.sin_sq_eq_half_sub u
  have htheta : 2 * u = θ := by
    calc
      2 * u = 2 * (θ / 2) := by
        exact rfl
      _ = θ := by
        exact mul_div_cancel_left₀ θ two_ne_zero
  have hcos_theta :
      Real.cos (2 * u) = Real.cos θ :=
    congrArg Real.cos htheta
  have hfour_mul :
      4 * (1 / 2 - Real.cos θ / 2) =
        2 * (1 - Real.cos θ) := by
    calc
      4 * (1 / 2 - Real.cos θ / 2) =
          4 * ((1 - Real.cos θ) / 2) := by
        exact congrArg (fun x : ℝ => 4 * x) (Eq.symm (sub_div 1 (Real.cos θ) 2))
      _ = (4 / 2) * (1 - Real.cos θ) := by
        exact (div_mul_eq_mul_div 4 (1 - Real.cos θ) 2).symm
      _ = 2 * (1 - Real.cos θ) := by
        exact congrArg (fun x : ℝ => x * (1 - Real.cos θ))
          (mul_div_cancel_left₀ (2 : ℝ) two_ne_zero)
  calc
    (2 * |Real.sin (θ / 2)|) ^ 2 =
        (2 * |Real.sin u|) ^ 2 := by
      exact rfl
    _ = 2 ^ 2 * |Real.sin u| ^ 2 := by
      exact hmul_sq
    _ = 4 * |Real.sin u| ^ 2 := by
      exact congrArg (fun x : ℝ => x * |Real.sin u| ^ 2) htwo_sq
    _ = 4 * (Real.sin u) ^ 2 := by
      exact congrArg (fun x : ℝ => 4 * x) habs_sq
    _ = 4 * (1 / 2 - Real.cos (2 * u) / 2) := by
      exact congrArg (fun x : ℝ => 4 * x) hsin_half
    _ = 4 * (1 / 2 - Real.cos θ / 2) := by
      exact congrArg (fun x : ℝ => 4 * (1 / 2 - x / 2)) hcos_theta
    _ = 2 * (1 - Real.cos θ) := by
      exact hfour_mul

/-- Complex norm-square chord calculation on the unit circle. -/
theorem unitCircleLogKernel_normSq_eq_two_mul_one_sub_cos
    (θ : ℝ) :
    Complex.normSq (1 - Complex.exp (θ * Complex.I)) =
      2 * (1 - Real.cos θ) := by
  calc
    Complex.normSq (1 - Complex.exp (θ * Complex.I)) =
        Complex.normSq (1 - (Real.cos θ + Real.sin θ * Complex.I)) := by
      exact congrArg (fun z : ℂ => Complex.normSq (1 - z)) (Complex.exp_mul_I θ)
    _ = (1 - Real.cos θ) ^ 2 + (-Real.sin θ) ^ 2 := by
      exact
        (show
          Complex.normSq (1 - (Real.cos θ + Real.sin θ * Complex.I)) =
            (1 - Real.cos θ) ^ 2 + (-Real.sin θ) ^ 2 from
          rfl)
    _ = 2 * (1 - Real.cos θ) := by
      exact real_one_sub_cos_sq_add_neg_sin_sq_eq_two_mul_one_sub_cos θ

/-- Half-angle square identity for the unit-circle chord length. -/
theorem unitCircleLogKernel_two_abs_sin_half_sq_eq_two_mul_one_sub_cos
    (θ : ℝ) :
    (2 * |Real.sin (θ / 2)|) ^ 2 =
      2 * (1 - Real.cos θ) := by
  exact real_two_abs_sin_half_sq_eq_two_mul_one_sub_cos θ

/-- Squared chord length for the unit-circle logarithmic kernel.

This is the coordinate norm-square calculation:
`|1 - e^{iθ}|² = (2 |sin(θ/2)|)²`. -/
theorem unitCircleLogKernel_norm_sq_eq_two_abs_sin_half_sq
    (θ : ℝ) :
    ‖1 - Complex.exp (θ * Complex.I)‖ ^ 2 =
      (2 * |Real.sin (θ / 2)|) ^ 2 := by
  let z : ℂ := 1 - Complex.exp (θ * Complex.I)
  calc
    ‖1 - Complex.exp (θ * Complex.I)‖ ^ 2 =
        Complex.abs z ^ 2 := by
      exact congrArg (fun x : ℝ => x ^ 2) (Complex.norm_eq_abs z)
    _ = Complex.normSq z := by
      exact Complex.sq_abs z
    _ = 2 * (1 - Real.cos θ) := by
      exact unitCircleLogKernel_normSq_eq_two_mul_one_sub_cos θ
    _ = (2 * |Real.sin (θ / 2)|) ^ 2 := by
      exact (unitCircleLogKernel_two_abs_sin_half_sq_eq_two_mul_one_sub_cos θ).symm

/-- Unit-circle kernel norm as the sine half-angle expression. -/
theorem unitCircleLogKernel_norm_eq_two_abs_sin_half
    (θ : ℝ) :
    ‖1 - Complex.exp (θ * Complex.I)‖ =
      2 * |Real.sin (θ / 2)| := by
  have hleft_nonneg :
      0 ≤ ‖1 - Complex.exp (θ * Complex.I)‖ :=
    norm_nonneg (1 - Complex.exp (θ * Complex.I))
  have htwo_nonneg : (0 : ℝ) ≤ 2 :=
    zero_le_two
  have hright_nonneg :
      0 ≤ 2 * |Real.sin (θ / 2)| :=
    mul_nonneg htwo_nonneg (abs_nonneg (Real.sin (θ / 2)))
  exact
    (sq_eq_sq₀ hleft_nonneg hright_nonneg).1
      (unitCircleLogKernel_norm_sq_eq_two_abs_sin_half_sq θ)

/-- Pointwise logarithmic split of the unit-circle kernel away from the
finite endpoint singularities. -/
theorem unitCircleLogKernel_log_eq_const_plus_halfSineLog_of_sin_ne_zero
    (θ : ℝ)
    (hθ : Real.sin (θ / 2) ≠ 0) :
    Real.log ‖1 - Complex.exp (θ * Complex.I)‖ =
      Real.log 2 + Real.log |Real.sin (θ / 2)| := by
  have hnorm :
      ‖1 - Complex.exp (θ * Complex.I)‖ =
        2 * |Real.sin (θ / 2)| :=
    unitCircleLogKernel_norm_eq_two_abs_sin_half θ
  have htwo : (2 : ℝ) ≠ 0 :=
    two_ne_zero
  have habs : |Real.sin (θ / 2)| ≠ 0 :=
    abs_ne_zero.mpr hθ
  calc
    Real.log ‖1 - Complex.exp (θ * Complex.I)‖ =
        Real.log (2 * |Real.sin (θ / 2)|) := by
      exact congrArg Real.log hnorm
    _ = Real.log 2 + Real.log |Real.sin (θ / 2)| := by
      exact Real.log_mul htwo habs

/-- The endpoint singularity set of the half-angle unit-circle kernel is null
on the fundamental Jensen interval. -/
theorem unitCircleLogKernel_halfSine_zero_ae_ne :
    ∀ᵐ θ ∂MeasureTheory.volume.restrict (Ι (0 : ℝ) (2 * Real.pi)),
      Real.sin (θ / 2) ≠ 0 := by
  have hne_endpoint :
      ∀ᵐ θ ∂MeasureTheory.volume.restrict (Ι (0 : ℝ) (2 * Real.pi)),
        θ ≠ 2 * Real.pi :=
    MeasureTheory.ae_restrict_of_ae
      ((Set.countable_singleton (2 * Real.pi)).ae_not_mem MeasureTheory.volume)
  have hinterval :
      ∀ᵐ θ ∂MeasureTheory.volume.restrict (Ι (0 : ℝ) (2 * Real.pi)),
        θ ∈ Ι (0 : ℝ) (2 * Real.pi) :=
    MeasureTheory.ae_restrict_mem measurableSet_uIoc
  exact
    (hne_endpoint.and hinterval).mono
      (fun θ hθ =>
        have hθ_ne_endpoint : θ ≠ 2 * Real.pi := hθ.1
        have hθ_interval : θ ∈ Ι (0 : ℝ) (2 * Real.pi) := hθ.2
        have hθ_cases :
            0 < θ ∧ θ ≤ 2 * Real.pi ∨ 2 * Real.pi < θ ∧ θ ≤ 0 :=
          Set.mem_uIoc.1 hθ_interval
        match hθ_cases with
        | Or.inl hmain =>
            have hθ_lt_endpoint : θ < 2 * Real.pi :=
              lt_of_le_of_ne hmain.2 (Ne.symm hθ_ne_endpoint)
            have hhalf_pos : 0 < θ / 2 :=
              div_pos hmain.1 zero_lt_two
            have hhalf_lt_pi : θ / 2 < Real.pi := by
              have hθ_lt_pi_mul_two : θ < Real.pi * 2 :=
                lt_of_lt_of_eq hθ_lt_endpoint (mul_comm 2 Real.pi)
              exact (div_lt_iff₀ zero_lt_two).2 hθ_lt_pi_mul_two
            (Real.sin_pos_of_pos_of_lt_pi hhalf_pos hhalf_lt_pi).ne'
        | Or.inr hrev =>
            have hendpoint_le_zero : 2 * Real.pi ≤ 0 :=
              hrev.1.le.trans hrev.2
            have hendpoint_pos : 0 < 2 * Real.pi :=
              mul_pos zero_lt_two Real.pi_pos
            False.elim ((not_lt_of_ge hendpoint_le_zero) hendpoint_pos))

/-- Restricted-a.e. logarithmic split of the unit-circle kernel on the
fundamental interval.

The exceptional set is the finite set of endpoint singularities where
`sin (θ/2) = 0`. -/
theorem unitCircleLogKernel_log_eq_const_plus_halfSineLog_ae :
    (fun θ : ℝ => Real.log ‖1 - Complex.exp (θ * Complex.I)‖) =ᵐ[
        MeasureTheory.volume.restrict (Ι (0 : ℝ) (2 * Real.pi))]
      (fun θ : ℝ => Real.log 2 + Real.log |Real.sin (θ / 2)|) := by
  exact
    unitCircleLogKernel_halfSine_zero_ae_ne.mono
      (fun θ hθ =>
        unitCircleLogKernel_log_eq_const_plus_halfSineLog_of_sin_ne_zero θ hθ)

/-- Integral split after the pointwise half-angle norm identity. -/
theorem unitCircleLogKernel_integral_eq_const_plus_halfSineLog :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      Real.log ‖1 - Complex.exp (θ * Complex.I)‖) =
      ∫ θ in (0 : ℝ)..(2 * Real.pi),
        Real.log 2 + Real.log |Real.sin (θ / 2)| := by
  exact
    intervalIntegral.integral_congr_ae
      unitCircleLogKernel_log_eq_const_plus_halfSineLog_ae

/-- Half-angle linear substitution before removing the absolute value. -/
theorem unitCircleLogKernel_halfSineLog_integral_eq_twice_absSineLog :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      Real.log |Real.sin (θ / 2)|) =
      2 * (∫ u in (0 : ℝ)..Real.pi, Real.log |Real.sin u|) := by
  let f : ℝ → ℝ := fun u : ℝ => Real.log |Real.sin u|
  calc
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      Real.log |Real.sin (θ / 2)|) =
        ∫ θ in (0 : ℝ)..(2 * Real.pi), f (θ / 2) := by
      rfl
    _ = 2 * (∫ u in (0 : ℝ) / 2..(2 * Real.pi) / 2, f u) := by
      exact intervalIntegral.integral_comp_div (f := f) (a := (0 : ℝ))
        (b := 2 * Real.pi) (c := 2) two_ne_zero
    _ = 2 * (∫ u in (0 : ℝ)..Real.pi, Real.log |Real.sin u|) := by
      have h0 : (0 : ℝ) / 2 = 0 := by
        exact zero_div 2
      have hpi : (2 * Real.pi) / 2 = Real.pi := by
        calc
          (2 * Real.pi) / 2 = (Real.pi * 2) / 2 := by
            exact congrArg (fun x : ℝ => x / 2) (mul_comm 2 Real.pi)
          _ = Real.pi * (2 / 2 : ℝ) := by
            exact mul_div_assoc Real.pi 2 2
          _ = Real.pi * 1 := by
            exact congrArg (fun x : ℝ => Real.pi * x) (div_self two_ne_zero)
          _ = Real.pi := by
            exact mul_one Real.pi
      have hinterval :
          (∫ u in (0 : ℝ) / 2..(2 * Real.pi) / 2, f u) =
            ∫ u in (0 : ℝ)..Real.pi, f u := by
        congr 1
      calc
        2 * (∫ u in (0 : ℝ) / 2..(2 * Real.pi) / 2, f u)
            = 2 * (∫ u in (0 : ℝ)..Real.pi, f u) := by
              exact congrArg (fun t : ℝ => 2 * t) hinterval
        _ = 2 * (∫ u in (0 : ℝ)..Real.pi, Real.log |Real.sin u|) := by
              rfl

/-- The sine is a.e. positive on the open Jensen sine interval. -/
theorem real_sin_pos_ae_zero_pi :
    ∀ᵐ u ∂MeasureTheory.volume.restrict (Ι (0 : ℝ) Real.pi),
      0 < Real.sin u := by
  have hne_pi :
      ∀ᵐ u ∂MeasureTheory.volume.restrict (Ι (0 : ℝ) Real.pi),
        u ≠ Real.pi :=
    MeasureTheory.ae_restrict_of_ae
      ((Set.countable_singleton Real.pi).ae_not_mem MeasureTheory.volume)
  have hinterval :
      ∀ᵐ u ∂MeasureTheory.volume.restrict (Ι (0 : ℝ) Real.pi),
        u ∈ Ι (0 : ℝ) Real.pi :=
    MeasureTheory.ae_restrict_mem measurableSet_uIoc
  exact
    (hne_pi.and hinterval).mono
      (fun u hu =>
        have hu_ne_pi : u ≠ Real.pi := hu.1
        have hu_interval : u ∈ Ι (0 : ℝ) Real.pi := hu.2
        have hu_cases :
            0 < u ∧ u ≤ Real.pi ∨ Real.pi < u ∧ u ≤ 0 :=
          Set.mem_uIoc.1 hu_interval
        match hu_cases with
        | Or.inl hmain =>
            Real.sin_pos_of_pos_of_lt_pi
              hmain.1
              (lt_of_le_of_ne hmain.2 (Ne.symm hu_ne_pi))
        | Or.inr hrev =>
            have hpi_le_zero : Real.pi ≤ 0 :=
              hrev.1.le.trans hrev.2
            False.elim ((not_lt_of_ge hpi_le_zero) Real.pi_pos))

/-- A.e. removal of the absolute value in the sine-log integral on `[0,π]`. -/
theorem real_log_abs_sin_ae_eq_log_sin_zero_pi :
    (fun u : ℝ => Real.log |Real.sin u|) =ᵐ[
        MeasureTheory.volume.restrict (Ι (0 : ℝ) Real.pi)]
      (fun u : ℝ => Real.log (Real.sin u)) := by
  exact
    real_sin_pos_ae_zero_pi.mono
      (fun u hu =>
        congrArg Real.log (abs_of_pos hu))

/-- On `[0,π]`, replacing `log |sin u|` by `log (sin u)` changes only the
finite endpoint singularities. -/
theorem real_integral_log_abs_sin_zero_pi_eq_log_sin :
    (∫ u in (0 : ℝ)..Real.pi, Real.log |Real.sin u|) =
      ∫ u in (0 : ℝ)..Real.pi, Real.log (Real.sin u) := by
  exact
    intervalIntegral.integral_congr_ae
      real_log_abs_sin_ae_eq_log_sin_zero_pi

/-- Away from the endpoint zeros, the logarithmic sine kernel is continuous on
the Jensen sine interval. -/
theorem real_log_abs_sin_continuousOn_Icc_compl_endpoints :
    ContinuousOn
      (fun u : ℝ => Real.log |Real.sin u|)
      ({u : ℝ | u ∈ Set.Icc (0 : ℝ) Real.pi ∧
        u ∉ ({0, Real.pi} : Set ℝ)}) := by
  have hsin_ne :
      ∀ u : ℝ,
        u ∈ {u : ℝ | u ∈ Set.Icc (0 : ℝ) Real.pi ∧
          u ∉ ({0, Real.pi} : Set ℝ)} →
          |Real.sin u| ≠ 0 := by
    intro u hu
    have huIcc : u ∈ Set.Icc (0 : ℝ) Real.pi :=
      hu.1
    have hu_not_end : u ∉ ({0, Real.pi} : Set ℝ) :=
      hu.2
    have hu0_ne : u ≠ 0 := by
      intro hu0
      exact hu_not_end (Or.inl hu0)
    have hupi_ne : u ≠ Real.pi := by
      intro hupi
      exact hu_not_end (Or.inr hupi)
    have h0_lt_u : 0 < u :=
      lt_of_le_of_ne huIcc.1 (Ne.symm hu0_ne)
    have hu_lt_pi : u < Real.pi :=
      lt_of_le_of_ne huIcc.2 hupi_ne
    have hsin_pos : 0 < Real.sin u :=
      Real.sin_pos_of_pos_of_lt_pi h0_lt_u hu_lt_pi
    exact abs_ne_zero.mpr hsin_pos.ne'
  have habs_cont :
      ContinuousOn
        (fun u : ℝ => |Real.sin u|)
        ({u : ℝ | u ∈ Set.Icc (0 : ℝ) Real.pi ∧
          u ∉ ({0, Real.pi} : Set ℝ)}) :=
    (Real.continuous_sin.continuousOn).abs
  exact
    ContinuousOn.log habs_cont hsin_ne

/-- The sine quotient filled by value `1` at the origin is continuous at `0`.

This is the derivative-slope form of `sin θ / θ → 1`. -/
theorem real_filled_sin_div_self_continuousAt_zero :
    ContinuousAt
      (Function.update (fun x : ℝ => Real.sin x / x) 0 1)
      0 := by
  have hslope :
      ContinuousAt
        (Function.update
          (fun x : ℝ => (Real.sin x - Real.sin 0) / (x - 0))
          0
          (Real.cos 0))
        0 :=
    (Real.hasDerivAt_sin 0).continuousAt_div
  have hfun :
      Function.update
          (fun x : ℝ => (Real.sin x - Real.sin 0) / (x - 0))
          0
          (Real.cos 0) =
        Function.update (fun x : ℝ => Real.sin x / x) 0 1 := by
    funext x
    match Classical.decEq ℝ x 0 with
    | isTrue hx =>
        exact
          Eq.trans
            (congrFun
              (Function.update_eq_self
                (fun x : ℝ => (Real.sin x - Real.sin 0) / (x - 0))
                0
                (Real.cos 0))
              x)
            (Eq.subst
              (motive := fun y : ℝ =>
                Real.cos 0 =
                  Function.update (fun x : ℝ => Real.sin x / x) 0 1 y)
              hx.symm
              Real.cos_zero)
    | isFalse hx =>
        have hleft :
          Function.update
              (fun x : ℝ => (Real.sin x - Real.sin 0) / (x - 0))
              0
              (Real.cos 0) x =
            (Real.sin x - Real.sin 0) / (x - 0) :=
        Function.update_of_ne hx (Real.cos 0)
          (fun x : ℝ => (Real.sin x - Real.sin 0) / (x - 0))
        have hright :
          Function.update (fun x : ℝ => Real.sin x / x) 0 1 x =
            Real.sin x / x :=
          Function.update_of_ne hx 1 (fun x : ℝ => Real.sin x / x)
        calc
          Function.update
              (fun x : ℝ => (Real.sin x - Real.sin 0) / (x - 0))
              0
              (Real.cos 0) x =
              (Real.sin x - Real.sin 0) / (x - 0) := hleft
          _ = Real.sin x / x := by
            exact congrArg₂ HDiv.hDiv
              (sub_eq_self.2 Real.sin_zero)
              (sub_zero x)
          _ = Function.update (fun x : ℝ => Real.sin x / x) 0 1 x := hright.symm
  exact
    Eq.subst
      (motive := fun f : ℝ → ℝ => ContinuousAt f 0)
      hfun
      hslope

/-- A continuous real-valued function that is nonzero at `c` has locally
interval-integrable logarithmic absolute value near `c`. -/
theorem real_log_abs_local_intervalIntegrable_of_continuous_nonzero
    (f : ℝ → ℝ)
    (c : ℝ)
    (hf : Continuous f)
    (hfc : f c ≠ 0) :
    ∃ u v : ℝ,
      u < c ∧ c < v ∧
      IntervalIntegrable
        (fun x : ℝ => Real.log |f x|)
        MeasureTheory.volume
        u
        v := by
  have hne_event :
      ∀ᶠ x in 𝓝 c, f x ≠ 0 :=
    hf.continuousAt.eventually_ne hfc
  obtain ⟨ε, hε_pos, hball⟩ :=
    Metric.mem_nhds_iff.1 hne_event
  let δ : ℝ := ε / 2
  let u : ℝ := c - δ
  let v : ℝ := c + δ
  have hδ_pos : 0 < δ :=
    half_pos hε_pos
  have hδ_nonneg : 0 ≤ δ :=
    hδ_pos.le
  have hδ_lt : δ < ε :=
    half_lt_self hε_pos
  have hu_lt_c : u < c := by
    exact sub_lt_self c hδ_pos
  have hc_lt_v : c < v := by
    exact lt_add_of_pos_right c hδ_pos
  have huv_le : u ≤ v :=
    hu_lt_c.le.trans hc_lt_v.le
  have huIcc_eq_closed :
      Set.uIcc u v = Metric.closedBall c δ := by
    calc
      Set.uIcc u v = Set.Icc u v := by
        exact Set.uIcc_of_le huv_le
      _ = Set.Icc (c - δ) (c + δ) := by
        exact rfl
      _ = Metric.closedBall c δ := by
        exact (Real.closedBall_eq_Icc (x := c) (r := δ)).symm
  have hcont_abs :
      ContinuousOn
        (fun x : ℝ => |f x|)
        (Set.uIcc u v) :=
    hf.continuousOn.abs
  have hnonzero_abs :
      ∀ x : ℝ, x ∈ Set.uIcc u v → |f x| ≠ 0 := by
    intro x hx
    have hx_closed : x ∈ Metric.closedBall c δ :=
      huIcc_eq_closed ▸ hx
    have hx_ball : x ∈ Metric.ball c ε :=
      Metric.closedBall_subset_ball hδ_lt hx_closed
    exact abs_ne_zero.mpr (hball hx_ball)
  exact
    ⟨u, v, hu_lt_c, hc_lt_v,
      (ContinuousOn.log hcont_abs hnonzero_abs).intervalIntegrable⟩

/-- The sine quotient filled by value `1` at the origin is continuous. -/
theorem real_filled_sin_div_self_continuous :
    Continuous
      (Function.update (fun x : ℝ => Real.sin x / x) 0 1) := by
  exact
    continuous_iff_continuousAt.2
      (fun x : ℝ =>
        match Classical.decEq ℝ x 0 with
        | isTrue hx =>
            Eq.subst
              (motive := fun y : ℝ =>
                ContinuousAt
                  (Function.update (fun x : ℝ => Real.sin x / x) 0 1)
                  y)
              hx.symm
              real_filled_sin_div_self_continuousAt_zero
        | isFalse hx =>
            (continuousAt_update_of_ne hx).2
              (Real.continuous_sin.continuousAt.div continuousAt_id hx))

/-- The filled sine-ratio logarithm is locally interval-integrable near `0`.

The filled ratio is continuous at `0` by applying
`HasDerivAt.continuousAt_div` to `Real.hasDerivAt_sin 0`; the value at `0` is
`1`, so the logarithm is locally continuous and hence locally
interval-integrable. -/
theorem real_log_abs_filled_sin_div_self_local_intervalIntegrable_zero :
    ∃ u v : ℝ,
      u < (0 : ℝ) ∧ (0 : ℝ) < v ∧
      IntervalIntegrable
        (fun θ : ℝ =>
          Real.log |Function.update (fun x : ℝ => Real.sin x / x) 0 1 θ|)
        MeasureTheory.volume
        u
        v := by
  have hvalue :
      Function.update (fun x : ℝ => Real.sin x / x) 0 1 0 = 1 :=
    Function.update_same 0 1 (fun x : ℝ => Real.sin x / x)
  have hnonzero :
      Function.update (fun x : ℝ => Real.sin x / x) 0 1 0 ≠ 0 := by
    exact hvalue ▸ one_ne_zero
  exact
    real_log_abs_local_intervalIntegrable_of_continuous_nonzero
      (Function.update (fun x : ℝ => Real.sin x / x) 0 1)
      0
      real_filled_sin_div_self_continuous
      hnonzero

/-- The derivative-slope quotient for `sin` filled at `π` is continuous. -/
theorem real_filled_sin_sub_pi_div_sub_pi_continuous :
    Continuous
      (Function.update
        (fun x : ℝ => (Real.sin x - Real.sin Real.pi) / (x - Real.pi))
        Real.pi
        (Real.cos Real.pi)) := by
  have hcont_at_pi :
      ContinuousAt
        (Function.update
          (fun x : ℝ => (Real.sin x - Real.sin Real.pi) / (x - Real.pi))
          Real.pi
          (Real.cos Real.pi))
        Real.pi :=
    (Real.hasDerivAt_sin Real.pi).continuousAt_div
  exact
    continuous_iff_continuousAt.2
      (fun x : ℝ =>
        match Classical.decEq ℝ x Real.pi with
        | isTrue hx =>
            Eq.subst
              (motive := fun y : ℝ =>
                ContinuousAt
                  (Function.update
                    (fun x : ℝ =>
                      (Real.sin x - Real.sin Real.pi) / (x - Real.pi))
                    Real.pi
                    (Real.cos Real.pi))
                  y)
              hx.symm
              hcont_at_pi
        | isFalse hx =>
            (continuousAt_update_of_ne hx).2
              ((Real.continuous_sin.continuousAt.sub continuousAt_const).div
                (continuousAt_id.sub continuousAt_const)
                (sub_ne_zero.mpr hx)))

/-- The filled derivative-slope logarithm for `sin` is locally
interval-integrable near `π`. -/
theorem real_log_abs_filled_sin_sub_pi_div_sub_pi_local_intervalIntegrable_pi :
    ∃ u v : ℝ,
      u < Real.pi ∧ Real.pi < v ∧
      IntervalIntegrable
        (fun θ : ℝ =>
          Real.log |
            Function.update
              (fun x : ℝ =>
                (Real.sin x - Real.sin Real.pi) / (x - Real.pi))
              Real.pi
              (Real.cos Real.pi)
              θ|)
        MeasureTheory.volume
        u
        v := by
  have hvalue :
      Function.update
          (fun x : ℝ => (Real.sin x - Real.sin Real.pi) / (x - Real.pi))
          Real.pi
          (Real.cos Real.pi)
          Real.pi =
        Real.cos Real.pi :=
    Function.update_same Real.pi (Real.cos Real.pi)
      (fun x : ℝ => (Real.sin x - Real.sin Real.pi) / (x - Real.pi))
  have hcos_nonzero : Real.cos Real.pi ≠ 0 := by
    exact Real.cos_pi ▸ neg_ne_zero.mpr one_ne_zero
  have hnonzero :
      Function.update
          (fun x : ℝ => (Real.sin x - Real.sin Real.pi) / (x - Real.pi))
          Real.pi
          (Real.cos Real.pi)
          Real.pi ≠ 0 := by
    exact hvalue ▸ hcos_nonzero
  exact
    real_log_abs_local_intervalIntegrable_of_continuous_nonzero
      (Function.update
        (fun x : ℝ => (Real.sin x - Real.sin Real.pi) / (x - Real.pi))
        Real.pi
        (Real.cos Real.pi))
      Real.pi
      real_filled_sin_sub_pi_div_sub_pi_continuous
      hnonzero

/-- Local logarithmic model for `log |sin u|` at `0`.

The remainder is `log |sin u / u|`, extended at `0`; its continuity follows
from the standard sine-ratio limit. -/
theorem real_log_abs_sin_localModel_zero :
    ∃ n : ℕ, ∃ g : ℝ → ℝ,
      (∃ u v : ℝ,
        u < (0 : ℝ) ∧ (0 : ℝ) < v ∧
        IntervalIntegrable g MeasureTheory.volume u v) ∧
      ∀ᶠ θ in 𝓝[≠] (0 : ℝ),
        Real.log |Real.sin θ| =
          (n : ℝ) * Real.log |θ - 0| + g θ := by
  let g : ℝ → ℝ :=
    fun θ : ℝ =>
      Real.log |Function.update (fun x : ℝ => Real.sin x / x) 0 1 θ|
  have hlocal :
      ∃ u v : ℝ,
        u < (0 : ℝ) ∧ (0 : ℝ) < v ∧
        IntervalIntegrable g MeasureTheory.volume u v :=
    real_log_abs_filled_sin_div_self_local_intervalIntegrable_zero
  have hevent :
      ∀ᶠ θ in 𝓝[≠] (0 : ℝ),
        Real.log |Real.sin θ| =
          (1 : ℝ) * Real.log |θ - 0| + g θ := by
    have hsmall :
        ∀ᶠ θ in 𝓝[≠] (0 : ℝ), θ ∈ Set.Ioo (-Real.pi) Real.pi :=
      mem_of_superset
        (nhdsWithin_le_nhds (s := {0}ᶜ)
          (Ioo_mem_nhds (neg_lt_zero.mpr Real.pi_pos) Real.pi_pos))
        (fun θ hθ => hθ)
    have hself :
        ∀ᶠ θ in 𝓝[≠] (0 : ℝ), θ ∈ ({0} : Set ℝ)ᶜ :=
      self_mem_nhdsWithin
    exact
      (hself.and hsmall).mono
        (fun θ hθ =>
          have hθ_ne : θ ≠ 0 := hθ.1
          have hθ_small : θ ∈ Set.Ioo (-Real.pi) Real.pi := hθ.2
          have hsin_ne : Real.sin θ ≠ 0 := by
            have hzero_iff : Real.sin θ = 0 ↔ θ = 0 :=
              Real.sin_eq_zero_iff_of_lt_of_lt hθ_small.1 hθ_small.2
            intro hsin_zero
            exact hθ_ne (hzero_iff.1 hsin_zero)
          have hupdate :
              Function.update (fun x : ℝ => Real.sin x / x) 0 1 θ =
                Real.sin θ / θ := by
            exact Function.update_of_ne hθ_ne 1 (fun x : ℝ => Real.sin x / x)
          have hsin_factor :
              Real.sin θ = θ * (Real.sin θ / θ) := by
            exact (mul_div_cancel₀ (Real.sin θ) hθ_ne).symm
          have habs_factor :
              |Real.sin θ| = |θ| * |Real.sin θ / θ| := by
            calc
              |Real.sin θ| = |θ * (Real.sin θ / θ)| := by
                exact congrArg abs hsin_factor
              _ = |θ| * |Real.sin θ / θ| := by
                exact abs_mul θ (Real.sin θ / θ)
          have hθ_abs_ne : |θ| ≠ 0 :=
            abs_ne_zero.mpr hθ_ne
          have hratio_ne : |Real.sin θ / θ| ≠ 0 := by
            exact abs_ne_zero.mpr (div_ne_zero hsin_ne hθ_ne)
          calc
            Real.log |Real.sin θ| =
                Real.log (|θ| * |Real.sin θ / θ|) := by
              exact congrArg Real.log habs_factor
            _ = Real.log |θ| + Real.log |Real.sin θ / θ| := by
              exact Real.log_mul hθ_abs_ne hratio_ne
            _ = (1 : ℝ) * Real.log |θ - 0| + g θ := by
              have htheta_sub : |θ - 0| = |θ| :=
                congrArg abs (sub_zero θ)
              have hgθ : g θ = Real.log |Real.sin θ / θ| := by
                exact congrArg (fun x : ℝ => Real.log |x|) hupdate
              calc
                Real.log |θ| + Real.log |Real.sin θ / θ| =
                    Real.log |θ - 0| + Real.log |Real.sin θ / θ| := by
                  exact congrArg
                    (fun x : ℝ => Real.log x + Real.log |Real.sin θ / θ|)
                    htheta_sub.symm
                _ = (1 : ℝ) * Real.log |θ - 0| +
                    Real.log |Real.sin θ / θ| := by
                  exact congrArg
                    (fun x : ℝ => x + Real.log |Real.sin θ / θ|)
                    (Eq.symm (one_mul (Real.log |θ - 0|)))
                _ = (1 : ℝ) * Real.log |θ - 0| + g θ := by
                  exact congrArg
                    (fun x : ℝ => (1 : ℝ) * Real.log |θ - 0| + x)
                    hgθ.symm)
  exact ⟨1, g, hlocal, hevent⟩

/-- Local logarithmic model for `log |sin u|` at `π`.

This is transported from the model at `0` using
`sin u = sin (π - u)` and `|π - u| = |u - π|`. -/
theorem real_log_abs_sin_localModel_pi :
    ∃ n : ℕ, ∃ g : ℝ → ℝ,
      (∃ u v : ℝ,
        u < Real.pi ∧ Real.pi < v ∧
        IntervalIntegrable g MeasureTheory.volume u v) ∧
      ∀ᶠ θ in 𝓝[≠] Real.pi,
        Real.log |Real.sin θ| =
          (n : ℝ) * Real.log |θ - Real.pi| + g θ := by
  let g : ℝ → ℝ :=
    fun θ : ℝ =>
      Real.log |
        Function.update
          (fun x : ℝ =>
            (Real.sin x - Real.sin Real.pi) / (x - Real.pi))
          Real.pi
          (Real.cos Real.pi)
          θ|
  have hlocal :
      ∃ u v : ℝ,
        u < Real.pi ∧ Real.pi < v ∧
        IntervalIntegrable g MeasureTheory.volume u v :=
    real_log_abs_filled_sin_sub_pi_div_sub_pi_local_intervalIntegrable_pi
  have hevent :
      ∀ᶠ θ in 𝓝[≠] Real.pi,
        Real.log |Real.sin θ| =
          (1 : ℝ) * Real.log |θ - Real.pi| + g θ := by
    have hsmall :
        ∀ᶠ θ in 𝓝[≠] Real.pi, θ ∈ Set.Ioo 0 (2 * Real.pi) :=
      mem_of_superset
        (nhdsWithin_le_nhds (s := {Real.pi}ᶜ)
          (Ioo_mem_nhds Real.pi_pos
            (lt_of_eq_of_lt
              (Eq.symm (one_mul Real.pi))
              (mul_lt_mul_of_pos_right one_lt_two Real.pi_pos))))
        (fun θ hθ => hθ)
    have hself :
        ∀ᶠ θ in 𝓝[≠] Real.pi, θ ∈ ({Real.pi} : Set ℝ)ᶜ :=
      self_mem_nhdsWithin
    exact
      (hself.and hsmall).mono
        (fun θ hθ =>
          have hθ_ne : θ ≠ Real.pi := hθ.1
          have hθ_small : θ ∈ Set.Ioo 0 (2 * Real.pi) := hθ.2
          have hsin_ne : Real.sin θ ≠ 0 := by
            have hsub_small : θ - Real.pi ∈ Set.Ioo (-Real.pi) Real.pi := by
              constructor
              · exact neg_lt_sub_iff_lt_add.2
                  (lt_of_lt_of_eq hθ_small.1 (zero_add Real.pi).symm)
              · exact sub_lt_iff_lt_add.2
                  (lt_of_lt_of_eq hθ_small.2 (Eq.symm (two_mul Real.pi)))
            have hsub_ne : θ - Real.pi ≠ 0 :=
              sub_ne_zero.mpr hθ_ne
            have hzero_iff :
                Real.sin (θ - Real.pi) = 0 ↔ θ - Real.pi = 0 :=
              Real.sin_eq_zero_iff_of_lt_of_lt hsub_small.1 hsub_small.2
            intro hsin_zero
            have hsin_sub_zero : Real.sin (θ - Real.pi) = 0 := by
              exact Eq.trans (Real.sin_sub_pi θ) (neg_eq_zero.mpr hsin_zero)
            exact hsub_ne (hzero_iff.1 hsin_sub_zero)
          have hupdate :
              Function.update
                  (fun x : ℝ => (Real.sin x - Real.sin Real.pi) /
                    (x - Real.pi))
                  Real.pi
                  (Real.cos Real.pi)
                  θ =
                (Real.sin θ - Real.sin Real.pi) / (θ - Real.pi) := by
            exact
              Function.update_of_ne hθ_ne (Real.cos Real.pi)
                (fun x : ℝ =>
                  (Real.sin x - Real.sin Real.pi) / (x - Real.pi))
          have hsin_factor :
              Real.sin θ = (θ - Real.pi) *
                ((Real.sin θ - Real.sin Real.pi) / (θ - Real.pi)) := by
            calc
              Real.sin θ = Real.sin θ - Real.sin Real.pi := by
                exact (sub_eq_self.2 Real.sin_pi).symm
              _ = (θ - Real.pi) *
                  ((Real.sin θ - Real.sin Real.pi) / (θ - Real.pi)) := by
                exact (mul_div_cancel₀ (Real.sin θ - Real.sin Real.pi)
                  (sub_ne_zero.mpr hθ_ne)).symm
          have habs_factor :
              |Real.sin θ| =
                |θ - Real.pi| *
                  |(Real.sin θ - Real.sin Real.pi) / (θ - Real.pi)| := by
            calc
              |Real.sin θ| =
                  |(θ - Real.pi) *
                    ((Real.sin θ - Real.sin Real.pi) / (θ - Real.pi))| := by
                exact congrArg abs hsin_factor
              _ = |θ - Real.pi| *
                  |(Real.sin θ - Real.sin Real.pi) / (θ - Real.pi)| := by
                exact abs_mul (θ - Real.pi)
                  ((Real.sin θ - Real.sin Real.pi) / (θ - Real.pi))
          have hθ_abs_ne : |θ - Real.pi| ≠ 0 :=
            abs_ne_zero.mpr (sub_ne_zero.mpr hθ_ne)
          have hratio_ne :
              |(Real.sin θ - Real.sin Real.pi) / (θ - Real.pi)| ≠ 0 := by
            have hnum_ne : Real.sin θ - Real.sin Real.pi ≠ 0 := by
              intro hdiff_zero
              have hsin_eq_pi : Real.sin θ = Real.sin Real.pi :=
                sub_eq_zero.1 hdiff_zero
              exact hsin_ne (Eq.trans hsin_eq_pi Real.sin_pi)
            exact abs_ne_zero.mpr (div_ne_zero hnum_ne (sub_ne_zero.mpr hθ_ne))
          calc
            Real.log |Real.sin θ| =
                Real.log
                  (|θ - Real.pi| *
                    |(Real.sin θ - Real.sin Real.pi) / (θ - Real.pi)|) := by
              exact congrArg Real.log habs_factor
            _ = Real.log |θ - Real.pi| +
                Real.log |(Real.sin θ - Real.sin Real.pi) /
                  (θ - Real.pi)| := by
              exact Real.log_mul hθ_abs_ne hratio_ne
            _ = (1 : ℝ) * Real.log |θ - Real.pi| + g θ := by
              have hgθ :
                  g θ =
                    Real.log
                      |(Real.sin θ - Real.sin Real.pi) /
                        (θ - Real.pi)| := by
                exact congrArg (fun x : ℝ => Real.log |x|) hupdate
              calc
                Real.log |θ - Real.pi| +
                    Real.log |(Real.sin θ - Real.sin Real.pi) /
                      (θ - Real.pi)| =
                    (1 : ℝ) * Real.log |θ - Real.pi| +
                      Real.log |(Real.sin θ - Real.sin Real.pi) /
                        (θ - Real.pi)| := by
                  exact congrArg
                    (fun x : ℝ =>
                      x + Real.log
                        |(Real.sin θ - Real.sin Real.pi) / (θ - Real.pi)|)
                    (Eq.symm (one_mul (Real.log |θ - Real.pi|)))
                _ = (1 : ℝ) * Real.log |θ - Real.pi| + g θ := by
                  exact congrArg
                    (fun x : ℝ => (1 : ℝ) * Real.log |θ - Real.pi| + x)
                    hgθ.symm)
  exact ⟨1, g, hlocal, hevent⟩

/-- Endpoint local logarithmic models for the finite singular set
`{0, π}` of `log |sin|` on `[0,π]`. -/
theorem real_log_abs_sin_endpoint_localModel
    (θ₀ : ℝ)
    (hθ₀ : θ₀ ∈ ({0, Real.pi} : Set ℝ)) :
    ∃ n : ℕ, ∃ g : ℝ → ℝ,
      (∃ u v : ℝ,
        u < θ₀ ∧ θ₀ < v ∧
        IntervalIntegrable g MeasureTheory.volume u v) ∧
      ∀ᶠ θ in 𝓝[≠] θ₀,
        Real.log |Real.sin θ| =
          (n : ℝ) * Real.log |θ - θ₀| + g θ := by
  have hcases : θ₀ = 0 ∨ θ₀ = Real.pi :=
    Set.mem_insert_iff.1 hθ₀
  match hcases with
  | Or.inl hzero =>
      exact
        Eq.subst
          (motive := fun x : ℝ =>
            ∃ n : ℕ, ∃ g : ℝ → ℝ,
              (∃ u v : ℝ,
                u < x ∧ x < v ∧
                IntervalIntegrable g MeasureTheory.volume u v) ∧
              ∀ᶠ θ in 𝓝[≠] x,
                Real.log |Real.sin θ| =
                  (n : ℝ) * Real.log |θ - x| + g θ)
          hzero.symm
          real_log_abs_sin_localModel_zero
  | Or.inr hpi =>
      exact
        Eq.subst
          (motive := fun x : ℝ =>
            ∃ n : ℕ, ∃ g : ℝ → ℝ,
              (∃ u v : ℝ,
                u < x ∧ x < v ∧
                IntervalIntegrable g MeasureTheory.volume u v) ∧
              ∀ᶠ θ in 𝓝[≠] x,
                Real.log |Real.sin θ| =
                  (n : ℝ) * Real.log |θ - x| + g θ)
          hpi.symm
          real_log_abs_sin_localModel_pi

/-- Standard interval-integrability of the logarithmic sine kernel on
`[0,π]`.

This is the integrability companion to the classical log-sine integral
`real_integral_log_sin_zero_pi`. -/
theorem real_log_abs_sin_intervalIntegrable_zero_pi :
    IntervalIntegrable
      (fun u : ℝ => Real.log |Real.sin u|)
      MeasureTheory.volume
      0
      Real.pi := by
  exact
    intervalIntegrable_of_finite_log_singularities_on_compact
      (fun u : ℝ => Real.log |Real.sin u|)
      0
      Real.pi
      ({0, Real.pi} : Set ℝ)
      (le_of_lt Real.pi_pos)
      ((Set.finite_singleton Real.pi).insert 0)
      real_log_abs_sin_endpoint_localModel
      real_log_abs_sin_continuousOn_Icc_compl_endpoints

/-- Half-angle interval substitution for the sine-log kernel. -/
theorem unitCircleLogKernel_halfSineLog_integral_eq_twice_sineLog :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      Real.log |Real.sin (θ / 2)|) =
      2 * (∫ u in (0 : ℝ)..Real.pi, Real.log (Real.sin u)) := by
  calc
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      Real.log |Real.sin (θ / 2)|) =
        2 * (∫ u in (0 : ℝ)..Real.pi, Real.log |Real.sin u|) :=
      unitCircleLogKernel_halfSineLog_integral_eq_twice_absSineLog
    _ =
        2 * (∫ u in (0 : ℝ)..Real.pi, Real.log (Real.sin u)) := by
      exact congrArg (fun x : ℝ => 2 * x)
        real_integral_log_abs_sin_zero_pi_eq_log_sin

/-- Constant part of the unit-circle kernel integral. -/
theorem unitCircleLogKernel_const_integral_eq :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.log 2) =
      2 * Real.pi * Real.log 2 := by
  calc
    (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.log 2) =
        ((2 * Real.pi) - 0) • Real.log 2 := by
      exact intervalIntegral.integral_const (Real.log 2)
    _ = (2 * Real.pi) • Real.log 2 := by
      exact congrArg (fun x : ℝ => x • Real.log 2)
        (sub_zero (2 * Real.pi))
    _ = 2 * Real.pi * Real.log 2 := by
      rfl

/-- Interval-integrability of the half-angle sine logarithm on the
fundamental Jensen interval.

The only singularities are the endpoint logarithmic singularities of
`sin (θ/2)` at `0` and `2π`; this is the exact integrability input needed for
additivity of the kernel integral split. -/
theorem unitCircleLogKernel_halfSineLog_intervalIntegrable :
    IntervalIntegrable
      (fun θ : ℝ => Real.log |Real.sin (θ / 2)|)
      MeasureTheory.volume
      0
      (2 * Real.pi) := by
  have hbase :
      IntervalIntegrable
        (fun u : ℝ => Real.log |Real.sin u|)
        MeasureTheory.volume
        0
        Real.pi :=
    real_log_abs_sin_intervalIntegrable_zero_pi
  have hscaled :
      IntervalIntegrable
        (fun θ : ℝ => Real.log |Real.sin (θ * (1 / 2))|)
        MeasureTheory.volume
        ((0 : ℝ) / (1 / 2))
        (Real.pi / (1 / 2)) :=
    hbase.comp_mul_right (1 / 2)
  have hendpoints :
      ((0 : ℝ) / (1 / 2)) = 0 ∧ Real.pi / (1 / 2) = 2 * Real.pi := by
    constructor
    · exact zero_div (1 / 2)
    · have hhalf_ne : (1 / 2 : ℝ) ≠ 0 :=
        one_div_ne_zero two_ne_zero
      have hmul :
          (2 * Real.pi) * (1 / 2 : ℝ) = Real.pi := by
        calc
          (2 * Real.pi) * (1 / 2 : ℝ) = (2 * Real.pi) / 2 := by
            exact mul_one_div (2 * Real.pi) 2
          _ = Real.pi := by
            exact mul_div_cancel_left₀ Real.pi two_ne_zero
      exact ((eq_div_iff_mul_eq hhalf_ne).2 hmul).symm
  have harg :
      (fun θ : ℝ => Real.log |Real.sin (θ * (1 / 2))|) =
        (fun θ : ℝ => Real.log |Real.sin (θ / 2)|) := by
    funext θ
    exact congrArg (fun x : ℝ => Real.log |Real.sin x|) (mul_one_div θ 2)
  exact
    Eq.subst
      (motive := fun a : ℝ =>
        IntervalIntegrable
          (fun θ : ℝ => Real.log |Real.sin (θ / 2)|)
          MeasureTheory.volume
          a
          (2 * Real.pi))
      hendpoints.1
      (Eq.subst
        (motive := fun b : ℝ =>
          IntervalIntegrable
            (fun θ : ℝ => Real.log |Real.sin (θ / 2)|)
            MeasureTheory.volume
            ((0 : ℝ) / (1 / 2))
            b)
        hendpoints.2
        (Eq.subst
          (motive := fun f : ℝ → ℝ =>
            IntervalIntegrable f MeasureTheory.volume
              ((0 : ℝ) / (1 / 2))
              (Real.pi / (1 / 2)))
          harg
          hscaled))

/-- Additivity for the constant plus half-angle sine-log kernel split. -/
theorem unitCircleLogKernel_integral_add_const_halfSineLog :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
        Real.log 2 + Real.log |Real.sin (θ / 2)|) =
      (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.log 2) +
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log |Real.sin (θ / 2)|) := by
  exact
    intervalIntegral.integral_add
      intervalIntegrable_const
      unitCircleLogKernel_halfSineLog_intervalIntegrable

/-- Integral form of the unit-circle kernel after the sine half-angle
substitution. -/
theorem unitCircleLogKernel_integral_eq_sineLogIntegral :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      Real.log ‖1 - Complex.exp (θ * Complex.I)‖) =
      2 * Real.pi * Real.log 2 +
        2 * (∫ u in (0 : ℝ)..Real.pi, Real.log (Real.sin u)) := by
  have hsplit :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        Real.log ‖1 - Complex.exp (θ * Complex.I)‖) =
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log 2 + Real.log |Real.sin (θ / 2)| :=
    unitCircleLogKernel_integral_eq_const_plus_halfSineLog
  have hsum :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log 2 + Real.log |Real.sin (θ / 2)|) =
        (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.log 2) +
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log |Real.sin (θ / 2)|) := by
    exact unitCircleLogKernel_integral_add_const_halfSineLog
  have hconst :
      (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.log 2) =
        2 * Real.pi * Real.log 2 :=
    unitCircleLogKernel_const_integral_eq
  have hhalf :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        Real.log |Real.sin (θ / 2)|) =
        2 * (∫ u in (0 : ℝ)..Real.pi, Real.log (Real.sin u)) :=
    unitCircleLogKernel_halfSineLog_integral_eq_twice_sineLog
  calc
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      Real.log ‖1 - Complex.exp (θ * Complex.I)‖) =
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log 2 + Real.log |Real.sin (θ / 2)| := hsplit
    _ =
        (∫ θ in (0 : ℝ)..(2 * Real.pi), Real.log 2) +
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log |Real.sin (θ / 2)|) := hsum
    _ =
        2 * Real.pi * Real.log 2 +
          (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log |Real.sin (θ / 2)|) := by
      exact congrArg
        (fun x : ℝ =>
          x +
            (∫ θ in (0 : ℝ)..(2 * Real.pi),
              Real.log |Real.sin (θ / 2)|))
        hconst
    _ =
        2 * Real.pi * Real.log 2 +
          2 * (∫ u in (0 : ℝ)..Real.pi, Real.log (Real.sin u)) := by
      exact congrArg
        (fun x : ℝ => 2 * Real.pi * Real.log 2 + x)
        hhalf

/-- Arithmetic endpoint of the unit-circle kernel reduction. -/
theorem unitCircleLogKernel_integral_eq_zero_from_sineLogIntegral :
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
      Real.log ‖1 - Complex.exp (θ * Complex.I)‖) =
      0 := by
  let S : ℝ := ∫ u in (0 : ℝ)..Real.pi, Real.log (Real.sin u)
  let A : ℝ := 2 * Real.pi * Real.log 2
  have hkernel :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        Real.log ‖1 - Complex.exp (θ * Complex.I)‖) =
        A + 2 * S :=
    unitCircleLogKernel_integral_eq_sineLogIntegral
  have hsine :
      S = -Real.pi * Real.log 2 :=
    real_integral_log_sin_zero_pi
  have htwice_sine :
      2 * S = -A := by
    calc
      2 * S = 2 * (-Real.pi * Real.log 2) := by
        exact congrArg (fun x : ℝ => 2 * x) hsine
      _ = (2 * -Real.pi) * Real.log 2 := by
        exact (mul_assoc 2 (-Real.pi) (Real.log 2)).symm
      _ = (-(2 * Real.pi)) * Real.log 2 := by
        exact congrArg (fun x : ℝ => x * Real.log 2)
          (mul_neg 2 Real.pi)
      _ = -(2 * Real.pi * Real.log 2) := by
        exact neg_mul (2 * Real.pi) (Real.log 2)
      _ = -A := by
        rfl
  calc
    (∫ θ in (0 : ℝ)..(2 * Real.pi),
        Real.log ‖1 - Complex.exp (θ * Complex.I)‖) =
        A + 2 * S := hkernel
    _ = A + -A := by
      exact congrArg (fun x : ℝ => A + x) htwice_sine
    _ = 0 := by
      exact add_right_neg A

/-- Reduction of the unshifted unit-circle logarithmic kernel to the
classical sine-log integral. -/
theorem unitCircleLogKernel_mean_zero_from_sineLogIntegral :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖1 - Complex.exp (θ * Complex.I)‖) =
      0 := by
  have hzero :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
        Real.log ‖1 - Complex.exp (θ * Complex.I)‖) =
        0 :=
    unitCircleLogKernel_integral_eq_zero_from_sineLogIntegral
  calc
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖1 - Complex.exp (θ * Complex.I)‖) =
        (2 * Real.pi)⁻¹ * 0 := by
      exact congrArg (fun x : ℝ => (2 * Real.pi)⁻¹ * x) hzero
    _ = 0 := by
      exact mul_zero (2 * Real.pi)⁻¹

/-- Unshifted unit-circle logarithmic kernel mean.

This is the deepest classical Jensen kernel integral used for boundary zeros:
`average log |1 - exp(iθ)| = 0`. -/
theorem unitCircleLogKernel_mean_zero :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖1 - Complex.exp (θ * Complex.I)‖) =
      0 := by
  exact unitCircleLogKernel_mean_zero_from_sineLogIntegral

/-- Translation invariance of the unit-circle logarithmic kernel mean.

This is the endpoint-aware periodicity theorem for the logarithmic kernel with
its finite singular set.  It transports the unshifted Jensen kernel mean to the
kernel centered at angle `α`. -/
theorem unitCircleLogKernel_translated_mean_zero
    (α : ℝ) :
    (2 * Real.pi)⁻¹ *
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖1 - Complex.exp ((θ - α) * Complex.I)‖) =
      0 := by
  let k : ℝ → ℝ :=
    fun θ => Real.log ‖1 - Complex.exp (θ * Complex.I)‖
  have hk_periodic : Function.Periodic k (2 * Real.pi) := by
    exact Complex.exp_mul_I_periodic.comp
      (fun z : ℂ => Real.log ‖1 - z‖)
  have hshift :
      (∫ θ in (0 : ℝ)..(2 * Real.pi), k (θ - α)) =
        ∫ θ in ((0 : ℝ) + -α)..((2 * Real.pi) + -α), k θ := by
    exact intervalIntegral.integral_comp_add_right k (-α)
  have hendpoints :
      (∫ θ in ((0 : ℝ) + -α)..((2 * Real.pi) + -α), k θ) =
        ∫ θ in (-α)..((-α) + (2 * Real.pi)), k θ := by
    exact congrArg₂
      (fun a b : ℝ => ∫ θ in a..b, k θ)
      (zero_add (-α))
      (add_comm (2 * Real.pi) (-α))
  have hperiod :
      (∫ θ in (-α)..((-α) + (2 * Real.pi)), k θ) =
        ∫ θ in (0 : ℝ)..((0 : ℝ) + (2 * Real.pi)), k θ :=
    hk_periodic.intervalIntegral_add_eq (-α) 0
  have hunshift :
      (∫ θ in (0 : ℝ)..((0 : ℝ) + (2 * Real.pi)), k θ) =
        ∫ θ in (0 : ℝ)..(2 * Real.pi), k θ := by
    exact congrArg
      (fun b : ℝ => ∫ θ in (0 : ℝ)..b, k θ)
      (zero_add (2 * Real.pi))
  have hintegral :
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖1 - Complex.exp ((θ - α) * Complex.I)‖) =
        ∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖1 - Complex.exp (θ * Complex.I)‖ := by
    calc
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖1 - Complex.exp ((θ - α) * Complex.I)‖) =
          (∫ θ in (0 : ℝ)..(2 * Real.pi), k (θ - α)) := by
        rfl
      _ = ∫ θ in ((0 : ℝ) + -α)..((2 * Real.pi) + -α), k θ :=
        hshift
      _ = ∫ θ in (-α)..((-α) + (2 * Real.pi)), k θ :=
        hendpoints
      _ = ∫ θ in (0 : ℝ)..((0 : ℝ) + (2 * Real.pi)), k θ :=
        hperiod
      _ = ∫ θ in (0 : ℝ)..(2 * Real.pi), k θ :=
        hunshift
      _ =
          ∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log ‖1 - Complex.exp (θ * Complex.I)‖ := by
        rfl
  exact Eq.trans
    (congrArg (fun x : ℝ => (2 * Real.pi)⁻¹ * x) hintegral)
    unitCircleLogKernel_mean_zero

/-- Unit-circle boundary-zero logarithmic mean.

This is the exact classical singular integral used for boundary zeros:
`average log |1 - exp(i(t - α))| = 0`.  The logarithmic singularity at
`t = α` is integrable and is interpreted by the finite-exception boundary
integrability machinery in this file. -/

end
end LFunctions
end Boundary
