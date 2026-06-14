import Mathlib.Analysis.SpecialFunctions.Gamma.Beta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# The classical log-sine integral

This file owns the classical analysis package behind
`∫₀^π log (sin u) du = -π log 2`.

The intended proof chain is:

* split the sine-power integral into two half-intervals;
* use the Euler-Beta substitution on `[0, π/2]`;
* compare the Euler-Beta integral with Gamma quotients;
* differentiate at exponent `0`;
* use Legendre duplication in logarithmic-derivative form.
-/

namespace LFunctions

noncomputable section

/-- The sine-power integral on `[0,π]`. -/
noncomputable def Real.sinePowerIntegral
    (s : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..Real.pi, (Real.sin u) ^ s

/-- The half-interval sine-power integral on `[0,π/2]`. -/
noncomputable def Real.sinePowerHalfIntegral
    (s : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..(Real.pi / 2), (Real.sin u) ^ s

/-- The real Euler-Beta integral associated to the sine-power exponent. -/
noncomputable def Real.sinePowerEulerBetaIntegral
    (s : ℝ) : ℝ :=
  (Complex.betaIntegral (((s + 1) / 2 : ℝ) : ℂ) ((1 / 2 : ℝ) : ℂ)).re

/-- The Gamma-ratio associated to the sine-power integral. -/
noncomputable def Real.sinePowerGammaRatio
    (s : ℝ) : ℝ :=
  Real.sqrt Real.pi *
    Real.Gamma ((s + 1) / 2) /
      Real.Gamma (s / 2 + 1)

/-- Real logarithmic derivative of Gamma on its regular locus. -/
noncomputable def Real.gammaLogDeriv
    (x : ℝ) : ℝ :=
  deriv Real.Gamma x / Real.Gamma x

/-- Elementary scalar cancellation for the half-interval normalization. -/
theorem Real.two_mul_one_half_mul
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
theorem Real.sinePowerEulerBeta_leftParameter_pos
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
theorem Real.sinePowerEulerBeta_rightParameter_pos :
    0 < (1 / 2 : ℝ) :=
  one_half_pos

/-- Reflection symmetry splits the sine-power integral into twice the
half-interval integral. -/
theorem Real.sinePowerIntegral_eq_two_mul_halfIntegral
    (s : ℝ)
    (hs : -1 < s) :
    Real.sinePowerIntegral s =
      2 * Real.sinePowerHalfIntegral s := by
  sorry

/-- Euler-Beta substitution for the half sine-power integral. -/
theorem Real.sinePowerHalfIntegral_eq_half_eulerBetaIntegral
    (s : ℝ)
    (hs : -1 < s) :
    Real.sinePowerHalfIntegral s =
      (1 / 2 : ℝ) * Real.sinePowerEulerBetaIntegral s := by
  sorry

/-- The sine-power integral is the Euler-Beta integral. -/
theorem Real.sinePowerIntegral_eq_eulerBetaIntegral
    (s : ℝ)
    (hs : -1 < s) :
    Real.sinePowerIntegral s =
      Real.sinePowerEulerBetaIntegral s := by
  have hsplit :
      Real.sinePowerIntegral s =
        2 * Real.sinePowerHalfIntegral s :=
    Real.sinePowerIntegral_eq_two_mul_halfIntegral s hs
  have hbeta :
      Real.sinePowerHalfIntegral s =
        (1 / 2 : ℝ) * Real.sinePowerEulerBetaIntegral s :=
    Real.sinePowerHalfIntegral_eq_half_eulerBetaIntegral s hs
  calc
    Real.sinePowerIntegral s =
        2 * Real.sinePowerHalfIntegral s := hsplit
    _ = 2 * ((1 / 2 : ℝ) * Real.sinePowerEulerBetaIntegral s) := by
      exact congrArg (fun x : ℝ => 2 * x) hbeta
    _ = Real.sinePowerEulerBetaIntegral s := by
      exact Real.two_mul_one_half_mul (Real.sinePowerEulerBetaIntegral s)

/-- Beta/Gamma comparison for the sine-power Euler-Beta integral. -/
theorem Real.sinePowerEulerBetaIntegral_eq_gammaRatio
    (s : ℝ)
    (hs : -1 < s) :
    Real.sinePowerEulerBetaIntegral s =
      Real.sinePowerGammaRatio s := by
  sorry

/-- Beta/Gamma evaluation of the sine-power integral. -/
theorem Real.sinePowerIntegral_eq_gammaRatio
    (s : ℝ)
    (hs : -1 < s) :
    Real.sinePowerIntegral s =
      Real.sinePowerGammaRatio s := by
  exact
    Eq.trans
      (Real.sinePowerIntegral_eq_eulerBetaIntegral s hs)
      (Real.sinePowerEulerBetaIntegral_eq_gammaRatio s hs)

/-- Differentiating the sine-power integral at exponent `0`. -/
theorem Real.sinePowerIntegral_hasDerivAt_zero :
    HasDerivAt
      Real.sinePowerIntegral
      (∫ u in (0 : ℝ)..Real.pi, Real.log (Real.sin u))
      0 := by
  sorry

/-- Legendre duplication in logarithmic-derivative form at `1/2`. -/
theorem Real.gammaLogDeriv_one_sub_half_eq_two_log_two :
    Real.gammaLogDeriv 1 - Real.gammaLogDeriv (1 / 2) =
      2 * Real.log 2 := by
  sorry

/-- Reversed Legendre log-derivative difference at the half-point. -/
theorem Real.gammaLogDeriv_half_sub_one_eq_neg_two_log_two :
    Real.gammaLogDeriv (1 / 2) - Real.gammaLogDeriv 1 =
      -(2 * Real.log 2) := by
  calc
    Real.gammaLogDeriv (1 / 2) - Real.gammaLogDeriv 1 =
        -(Real.gammaLogDeriv 1 - Real.gammaLogDeriv (1 / 2)) := by
      exact sub_eq_neg_sub (Real.gammaLogDeriv (1 / 2)) (Real.gammaLogDeriv 1)
    _ = -(2 * Real.log 2) := by
      exact congrArg Neg.neg Real.gammaLogDeriv_one_sub_half_eq_two_log_two

/-- The Gamma-ratio derivative value after inserting Legendre duplication. -/
theorem Real.sinePowerGammaRatio_logDeriv_derivativeValue_eq_neg_pi_log_two :
    Real.pi *
        ((Real.gammaLogDeriv (1 / 2) - Real.gammaLogDeriv 1) / 2) =
      -Real.pi * Real.log 2 := by
  calc
    Real.pi *
        ((Real.gammaLogDeriv (1 / 2) - Real.gammaLogDeriv 1) / 2) =
        Real.pi * (-(2 * Real.log 2) / 2) := by
      exact congrArg
        (fun x : ℝ => Real.pi * (x / 2))
        Real.gammaLogDeriv_half_sub_one_eq_neg_two_log_two
    _ = Real.pi * (-(Real.log 2)) := by
      exact congrArg
        (fun x : ℝ => Real.pi * x)
        (neg_mul_div_two_cancel (Real.log 2))
    _ = -Real.pi * Real.log 2 := by
      exact neg_mul_eq_neg_mul Real.pi (Real.log 2)

/-- Derivative of the sine-power Gamma-ratio in logarithmic-derivative form. -/
theorem Real.sinePowerGammaRatio_hasDerivAt_zero_from_logDeriv :
    HasDerivAt
      Real.sinePowerGammaRatio
      (Real.pi *
        ((Real.gammaLogDeriv (1 / 2) - Real.gammaLogDeriv 1) / 2))
      0 := by
  sorry

/-- Derivative of the Gamma-ratio representation at exponent `0`. -/
theorem Real.sinePowerGammaRatio_hasDerivAt_zero :
    HasDerivAt
      Real.sinePowerGammaRatio
      (-Real.pi * Real.log 2)
      0 := by
  have hder :
      HasDerivAt
        Real.sinePowerGammaRatio
        (Real.pi *
          ((Real.gammaLogDeriv (1 / 2) - Real.gammaLogDeriv 1) / 2))
        0 :=
    Real.sinePowerGammaRatio_hasDerivAt_zero_from_logDeriv
  exact
    Eq.subst
      (motive := fun d : ℝ => HasDerivAt Real.sinePowerGammaRatio d 0)
      Real.sinePowerGammaRatio_logDeriv_derivativeValue_eq_neg_pi_log_two
      hder

/-- The classical log-sine integral on `[0,π]`. -/
theorem Real.integral_log_sin_zero_pi :
    ∫ u in (0 : ℝ)..Real.pi, Real.log (Real.sin u) =
      -Real.pi * Real.log 2 := by
  sorry

end

end LFunctions
