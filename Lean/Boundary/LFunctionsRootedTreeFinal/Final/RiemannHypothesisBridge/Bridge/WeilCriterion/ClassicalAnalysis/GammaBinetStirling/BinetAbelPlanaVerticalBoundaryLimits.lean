import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaPrincipalValueResidueTheorem

/-!
# Vertical boundary limits for the finite-height Abel-Plana contour

This file owns the cotangent vertical denominator normalizations, vertical
principal-value remainder limits, and reconstruction of the named Abel-Plana
boundary faces.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Vertical-axis cotangent exponential denominator normalization.

The upper-half-plane cotangent remainder on `I*t` is the usual Abel-Plana
kernel denominator `(exp (2πt) - 1)⁻¹`. -/
theorem Complex.finiteAbelPlanaCotangentKernel_upper_vertical_expDenominator
    (t : ℝ)
    (ht : 0 < t) :
    Complex.finiteAbelPlanaCotangentKernel (Complex.I * (t : ℂ)) +
        (Real.pi : ℂ) * Complex.I =
      -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) := by
  have hupper :
      Complex.finiteAbelPlanaCotangentKernel ((t : ℂ) * Complex.I) +
          (Real.pi : ℂ) * Complex.I =
        -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentUpperQ 0 t /
            (1 - Complex.finiteAbelPlanaCotangentUpperQ 0 t)) :=
    Complex.finiteAbelPlanaCotangentKernel_upper_vertical_exp_formula t ht
  have hden :
      -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentUpperQ 0 t /
        (1 - Complex.finiteAbelPlanaCotangentUpperQ 0 t)) =
        -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) := by
    have harg :
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
            ((0 : ℂ) + (t : ℂ) * Complex.I)) =
          -(((2 : ℝ) * Real.pi * t : ℝ) : ℂ) := by
      ring
    dsimp [Complex.finiteAbelPlanaCotangentUpperQ]
    rw [harg, Complex.exp_neg]
    field_simp [Complex.exp_ne_zero (((2 : ℝ) * Real.pi * t : ℝ) : ℂ)]
    ring
  exact Eq.trans hupper hden

/-- Integer-shifted vertical-axis cotangent exponential denominator
normalization at the right Abel-Plana endpoint. -/
theorem Complex.finiteAbelPlanaCotangentKernel_upper_integerShift_expDenominator
    (M : ℕ)
    (t : ℝ)
    (ht : 0 < t) :
    Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (t : ℂ)) +
        (Real.pi : ℂ) * Complex.I =
      -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) := by
  have hupper :
      Complex.finiteAbelPlanaCotangentKernel (((M : ℝ) : ℂ) + (t : ℂ) * Complex.I) +
          (Real.pi : ℂ) * Complex.I =
        -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentUpperQ (M : ℝ) t /
            (1 - Complex.finiteAbelPlanaCotangentUpperQ (M : ℝ) t)) :=
    Complex.finiteAbelPlanaCotangentKernel_upper_exp_formula (M : ℝ) t ht
  have hperiod :
      Complex.exp (((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) = 1 := by
    exact
      Complex.exp_eq_one_iff.mpr
        ⟨(M : ℤ), by ring⟩
  have hden :
      -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentUpperQ (M : ℝ) t /
        (1 - Complex.finiteAbelPlanaCotangentUpperQ (M : ℝ) t)) =
        -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) := by
    have harg :
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
            (((M : ℝ) : ℂ) + (t : ℂ) * Complex.I)) =
          (((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) -
            (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) := by
      norm_num
      ring
    dsimp [Complex.finiteAbelPlanaCotangentUpperQ]
    rw [harg, Complex.exp_sub, hperiod, one_div, Complex.exp_neg]
    field_simp [Complex.exp_ne_zero (((2 : ℝ) * Real.pi * t : ℝ) : ℂ)]
    ring
  have hpath :
      (((M : ℝ) : ℂ) + (t : ℂ) * Complex.I) =
        (M : ℂ) + Complex.I * (t : ℂ) := by
    norm_num
    ring
  exact Eq.trans (by simpa [hpath] using hupper) hden

/-- Vertical-axis lower-half cotangent exponential denominator normalization.

The lower-half-plane cotangent remainder on `-I*t` has the same Abel-Plana
kernel denominator as the upper half-plane remainder. -/
theorem Complex.finiteAbelPlanaCotangentKernel_lower_vertical_expDenominator
    (t : ℝ)
    (ht : 0 < t) :
    Complex.finiteAbelPlanaCotangentKernel (-(Complex.I * (t : ℂ))) -
        (Real.pi : ℂ) * Complex.I =
      (2 : ℂ) * (Real.pi : ℂ) * Complex.I /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) := by
  have hlower :
      Complex.finiteAbelPlanaCotangentKernel (-((t : ℂ) * Complex.I)) -
          (Real.pi : ℂ) * Complex.I =
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentLowerQ 0 t /
            (1 - Complex.finiteAbelPlanaCotangentLowerQ 0 t)) :=
    Complex.finiteAbelPlanaCotangentKernel_lower_vertical_exp_formula t ht
  have hden :
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentLowerQ 0 t /
            (1 - Complex.finiteAbelPlanaCotangentLowerQ 0 t)) =
        (2 : ℂ) * (Real.pi : ℂ) * Complex.I /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) := by
    have harg :
        (-((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
            ((0 : ℂ) - (t : ℂ) * Complex.I))) =
          -(((2 : ℝ) * Real.pi * t : ℝ) : ℂ) := by
      ring
    dsimp [Complex.finiteAbelPlanaCotangentLowerQ]
    rw [harg, Complex.exp_neg]
    field_simp [Complex.exp_ne_zero (((2 : ℝ) * Real.pi * t : ℝ) : ℂ)]
    ring
  have hpath :
      (-((t : ℂ) * Complex.I)) = -(Complex.I * (t : ℂ)) := by
    ring
  exact Eq.trans (by simpa [hpath] using hlower) hden

/-- Integer-shifted lower-half cotangent exponential denominator
normalization at the right Abel-Plana endpoint. -/
theorem Complex.finiteAbelPlanaCotangentKernel_lower_integerShift_expDenominator
    (M : ℕ)
    (t : ℝ)
    (ht : 0 < t) :
    Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) - Complex.I * (t : ℂ)) -
        (Real.pi : ℂ) * Complex.I =
      (2 : ℂ) * (Real.pi : ℂ) * Complex.I /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) := by
  have hlower :
      Complex.finiteAbelPlanaCotangentKernel (((M : ℝ) : ℂ) - (t : ℂ) * Complex.I) -
          (Real.pi : ℂ) * Complex.I =
        ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentLowerQ (M : ℝ) t /
            (1 - Complex.finiteAbelPlanaCotangentLowerQ (M : ℝ) t)) :=
    Complex.finiteAbelPlanaCotangentKernel_lower_exp_formula (M : ℝ) t ht
  have hperiod :
      Complex.exp (-(((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I))) = 1 := by
    have hbase :
        Complex.exp (((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) = 1 := by
      exact
        Complex.exp_eq_one_iff.mpr
          ⟨(M : ℤ), by ring⟩
    rw [Complex.exp_neg, hbase]
    norm_num
  have hden :
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentLowerQ (M : ℝ) t /
            (1 - Complex.finiteAbelPlanaCotangentLowerQ (M : ℝ) t)) =
        (2 : ℂ) * (Real.pi : ℂ) * Complex.I /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) := by
    have harg :
        (-((2 : ℂ) * (Real.pi : ℂ) * Complex.I *
            (((M : ℝ) : ℂ) - (t : ℂ) * Complex.I))) =
          -(((M : ℤ) : ℂ) * ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)) -
            (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) := by
      norm_num
      ring
    dsimp [Complex.finiteAbelPlanaCotangentLowerQ]
    rw [harg, Complex.exp_sub, hperiod, one_div, Complex.exp_neg]
    field_simp [Complex.exp_ne_zero (((2 : ℝ) * Real.pi * t : ℝ) : ℂ)]
    ring
  have hpath :
      (((M : ℝ) : ℂ) - (t : ℂ) * Complex.I) =
        (M : ℂ) - Complex.I * (t : ℂ) := by
    norm_num
    ring
  exact Eq.trans (by simpa [hpath] using hlower) hden

/-- Negative-half change of variables for the left vertical exponential
remainder.

This is the `y = -t` substitution on the lower half-line piece of the PV
left vertical remainder. -/
theorem Complex.finiteAbelPlana_log_leftVerticalRemainderPV_negativeHalf_changeVariables
    (w : ℂ)
    (T ε : ℝ)
    (hε : 0 < ε)
    (hεT : ε < T) :
    (-Complex.I) *
        (∫ y : ℝ in (-T)..(-ε),
          Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (y : ℂ)) -
              (Real.pi : ℂ) * Complex.I)) =
      (-Complex.I) *
        (∫ t : ℝ in ε..T,
          Complex.finiteAbelPlanaLogSummand w (-(Complex.I * (t : ℂ))) *
            (Complex.finiteAbelPlanaCotangentKernel (-(Complex.I * (t : ℂ))) -
              (Real.pi : ℂ) * Complex.I)) := by
  let F : ℝ → ℂ :=
    fun y =>
      Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
        (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (y : ℂ)) -
          (Real.pi : ℂ) * Complex.I)
  have hsub :
      (∫ t : ℝ in ε..T, F (-t)) =
        ∫ y : ℝ in (-T)..(-ε), F y :=
    intervalIntegral.integral_comp_neg (f := F) (a := ε) (b := T)
  have hpoint :
      ∀ t : ℝ,
        F (-t) =
          Complex.finiteAbelPlanaLogSummand w (-(Complex.I * (t : ℂ))) *
            (Complex.finiteAbelPlanaCotangentKernel (-(Complex.I * (t : ℂ))) -
              (Real.pi : ℂ) * Complex.I) := by
    intro t
    dsimp [F]
    ring_nf
  have hintegral :
      (∫ y : ℝ in (-T)..(-ε), F y) =
        ∫ t : ℝ in ε..T,
          Complex.finiteAbelPlanaLogSummand w (-(Complex.I * (t : ℂ))) *
            (Complex.finiteAbelPlanaCotangentKernel (-(Complex.I * (t : ℂ))) -
              (Real.pi : ℂ) * Complex.I) := by
    exact Eq.trans hsub.symm (intervalIntegral.integral_congr hpoint)
  exact congrArg (fun z : ℂ => (-Complex.I) * z) hintegral

/-- Positive-half cotangent exponential formula for the left vertical
exponential remainder. -/
theorem Complex.finiteAbelPlana_log_leftVerticalRemainderPV_positiveHalf_expFormula
    (w : ℂ)
    (t : ℝ)
    (ht : 0 < t) :
    (-Complex.I) *
        (Complex.finiteAbelPlanaLogSummand w (Complex.I * (t : ℂ)) *
          (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (t : ℂ)) +
            (Real.pi : ℂ) * Complex.I)) =
      (-Complex.I) *
        (Complex.finiteAbelPlanaLogSummand w (Complex.I * (t : ℂ)) *
          (-((2 : ℂ) * (Real.pi : ℂ) * Complex.I) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))) := by
  have hkernel :
      Complex.finiteAbelPlanaCotangentKernel (Complex.I * (t : ℂ)) +
          (Real.pi : ℂ) * Complex.I =
        -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) :=
    Complex.finiteAbelPlanaCotangentKernel_upper_vertical_expDenominator t ht
  exact
    congrArg
      (fun z : ℂ =>
        (-Complex.I) *
          (Complex.finiteAbelPlanaLogSummand w (Complex.I * (t : ℂ)) * z))
      hkernel

/-- Pointwise normalized left vertical exponential-remainder jump.

After residue normalization by `(2πi)⁻¹`, the lower and upper half-plane
cotangent remainders assemble into the lower Abel-Plana logarithmic jump
integrand. -/
theorem Complex.finiteAbelPlana_log_leftVerticalRemainderPV_pointwise_normalizedJump
    (w : ℂ)
    (t : ℝ)
    (ht : 0 < t) :
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
      (((-Complex.I) *
          (Complex.finiteAbelPlanaLogSummand w (-(Complex.I * (t : ℂ))) *
            (Complex.finiteAbelPlanaCotangentKernel (-(Complex.I * (t : ℂ))) -
              (Real.pi : ℂ) * Complex.I))) +
        ((-Complex.I) *
          (Complex.finiteAbelPlanaLogSummand w (Complex.I * (t : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel (Complex.I * (t : ℂ)) +
              (Real.pi : ℂ) * Complex.I)))) =
      -Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t := by
  have hlower :
      Complex.finiteAbelPlanaCotangentKernel (-(Complex.I * (t : ℂ))) -
          (Real.pi : ℂ) * Complex.I =
        (2 : ℂ) * (Real.pi : ℂ) * Complex.I /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) :=
    Complex.finiteAbelPlanaCotangentKernel_lower_vertical_expDenominator t ht
  have hupper :
      Complex.finiteAbelPlanaCotangentKernel (Complex.I * (t : ℂ)) +
          (Real.pi : ℂ) * Complex.I =
        -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) :=
    Complex.finiteAbelPlanaCotangentKernel_upper_vertical_expDenominator t ht
  have hden_ne :
      Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1 ≠ 0 := by
    have hpos : 0 < (2 : ℝ) * Real.pi * t := by
      exact mul_pos (mul_pos (by norm_num) Real.pi_pos) ht
    have hne : Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) ≠ 1 := by
      intro h
      have hre : Real.exp ((2 : ℝ) * Real.pi * t) = 1 := by
        simpa [Complex.exp_ofReal_re] using congrArg Complex.re h
      have hlog := Real.exp_eq_one_iff.mp hre
      linarith
    exact sub_ne_zero.mpr hne
  have htwo_pi_I_ne : ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  dsimp [Complex.finiteAbelPlanaLogSummand,
    Complex.finiteAbelPlanaLogLowerVerticalIntegrand]
  rw [hlower, hupper]
  field_simp [hden_ne, htwo_pi_I_ne]
  ring

/-- The two left vertical exponential pieces identify with the named lower
logarithmic-jump integrand on `(ε,T]`. -/
theorem Complex.finiteAbelPlana_log_leftVerticalRemainderPV_cutoffIntegrand_identification
    (w : ℂ)
    (T ε : ℝ)
    (hε : 0 < ε)
    (hεT : ε < T) :
    Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePVNormalized w T ε =
      -Complex.finiteAbelPlanaLogLowerVerticalIntegralFromTo w ε T := by
  dsimp [Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePVNormalized,
    Complex.finiteAbelPlanaLogLowerVerticalIntegralFromTo]
  exact
    setIntegral_congr_fun measurableSet_Ioc
      (fun t ht =>
        Complex.finiteAbelPlana_log_leftVerticalRemainderPV_pointwise_normalizedJump
          w t (lt_of_lt_of_le hε ht.1))

/-- Negative-half change of variables for the right endpoint vertical
exponential remainder.

This is the `y = -t` substitution on the lower half-line piece at
`M = N + 1`. -/
theorem Complex.finiteAbelPlana_log_rightVerticalRemainderPV_negativeHalf_changeVariables
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ)
    (hε : 0 < ε)
    (hεT : ε < T) :
    let M : ℕ := N + 1
    Complex.I *
        (∫ y : ℝ in (-T)..(-ε),
          Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (y : ℂ)) -
              (Real.pi : ℂ) * Complex.I)) =
      Complex.I *
        (∫ t : ℝ in ε..T,
          Complex.finiteAbelPlanaLogSummand w ((M : ℂ) - Complex.I * (t : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) - Complex.I * (t : ℂ)) -
              (Real.pi : ℂ) * Complex.I)) := by
  let M : ℕ := N + 1
  let F : ℝ → ℂ :=
    fun y =>
      Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (y : ℂ)) *
        (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (y : ℂ)) -
          (Real.pi : ℂ) * Complex.I)
  have hsub :
      (∫ t : ℝ in ε..T, F (-t)) =
        ∫ y : ℝ in (-T)..(-ε), F y :=
    intervalIntegral.integral_comp_neg (f := F) (a := ε) (b := T)
  have hpoint :
      ∀ t : ℝ,
        F (-t) =
          Complex.finiteAbelPlanaLogSummand w ((M : ℂ) - Complex.I * (t : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) - Complex.I * (t : ℂ)) -
              (Real.pi : ℂ) * Complex.I) := by
    intro t
    dsimp [F]
    ring_nf
  have hintegral :
      (∫ y : ℝ in (-T)..(-ε), F y) =
        ∫ t : ℝ in ε..T,
          Complex.finiteAbelPlanaLogSummand w ((M : ℂ) - Complex.I * (t : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) - Complex.I * (t : ℂ)) -
              (Real.pi : ℂ) * Complex.I) := by
    exact Eq.trans hsub.symm (intervalIntegral.integral_congr hpoint)
  exact congrArg (fun z : ℂ => Complex.I * z) hintegral

/-- Positive-half cotangent exponential formula for the right endpoint
vertical exponential remainder. -/
theorem Complex.finiteAbelPlana_log_rightVerticalRemainderPV_positiveHalf_expFormula
    (N : ℕ)
    (w : ℂ)
    (t : ℝ)
    (ht : 0 < t) :
    let M : ℕ := N + 1
    Complex.I *
        (Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (t : ℂ)) *
          (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (t : ℂ)) +
            (Real.pi : ℂ) * Complex.I)) =
      Complex.I *
        (Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (t : ℂ)) *
          (-((2 : ℂ) * (Real.pi : ℂ) * Complex.I) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))) := by
  let M : ℕ := N + 1
  have hkernel :
      Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (t : ℂ)) +
          (Real.pi : ℂ) * Complex.I =
        -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) := by
    exact
      Complex.finiteAbelPlanaCotangentKernel_upper_integerShift_expDenominator
        M t ht
  exact
    congrArg
      (fun z : ℂ =>
        Complex.I *
          (Complex.finiteAbelPlanaLogSummand w
            ((M : ℂ) + Complex.I * (t : ℂ)) * z))
      hkernel

/-- Pointwise normalized right endpoint vertical exponential-remainder jump.

This is the endpoint-shifted analogue of
`finiteAbelPlana_log_leftVerticalRemainderPV_pointwise_normalizedJump`. -/
theorem Complex.finiteAbelPlana_log_rightVerticalRemainderPV_pointwise_normalizedJump
    (N : ℕ)
    (w : ℂ)
    (t : ℝ)
    (ht : 0 < t) :
    let M : ℕ := N + 1
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
      ((Complex.I *
          (Complex.finiteAbelPlanaLogSummand w ((M : ℂ) - Complex.I * (t : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) - Complex.I * (t : ℂ)) -
              (Real.pi : ℂ) * Complex.I))) +
        (Complex.I *
          (Complex.finiteAbelPlanaLogSummand w ((M : ℂ) + Complex.I * (t : ℂ)) *
            (Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (t : ℂ)) +
              (Real.pi : ℂ) * Complex.I)))) =
      -Complex.finiteAbelPlanaLogUpperVerticalIntegrand N w t := by
  let M : ℕ := N + 1
  have hlower :
      Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) - Complex.I * (t : ℂ)) -
          (Real.pi : ℂ) * Complex.I =
        (2 : ℂ) * (Real.pi : ℂ) * Complex.I /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) :=
    Complex.finiteAbelPlanaCotangentKernel_lower_integerShift_expDenominator
      M t ht
  have hupper :
      Complex.finiteAbelPlanaCotangentKernel ((M : ℂ) + Complex.I * (t : ℂ)) +
          (Real.pi : ℂ) * Complex.I =
        -((2 : ℂ) * (Real.pi : ℂ) * Complex.I) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) :=
    Complex.finiteAbelPlanaCotangentKernel_upper_integerShift_expDenominator
      M t ht
  have hden_ne :
      Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1 ≠ 0 := by
    have hpos : 0 < (2 : ℝ) * Real.pi * t := by
      exact mul_pos (mul_pos (by norm_num) Real.pi_pos) ht
    have hne : Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) ≠ 1 := by
      intro h
      have hre : Real.exp ((2 : ℝ) * Real.pi * t) = 1 := by
        simpa [Complex.exp_ofReal_re] using congrArg Complex.re h
      have hlog := Real.exp_eq_one_iff.mp hre
      linarith
    exact sub_ne_zero.mpr hne
  have htwo_pi_I_ne : ((2 : ℂ) * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (ofReal_ne_zero.mpr Real.pi_ne_zero)) I_ne_zero
  dsimp [Complex.finiteAbelPlanaLogSummand,
    Complex.finiteAbelPlanaLogUpperVerticalIntegrand,
    Complex.binetAbelPlanaFiniteUpperLogJump]
  rw [hlower, hupper]
  field_simp [hden_ne, htwo_pi_I_ne]
  ring

/-- The two right endpoint vertical exponential pieces identify with the named
upper logarithmic-jump integrand on `(ε,T]`. -/
theorem Complex.finiteAbelPlana_log_rightVerticalRemainderPV_cutoffIntegrand_identification
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ)
    (hε : 0 < ε)
    (hεT : ε < T) :
    Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePVNormalized N w T ε =
      -Complex.finiteAbelPlanaLogUpperVerticalIntegralFromTo N w ε T := by
  dsimp [Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePVNormalized,
    Complex.finiteAbelPlanaLogUpperVerticalIntegralFromTo]
  exact
    setIntegral_congr_fun measurableSet_Ioc
      (fun t ht =>
        Complex.finiteAbelPlana_log_rightVerticalRemainderPV_pointwise_normalizedJump
          N w t (lt_of_lt_of_le hε ht.1))

/-- Left exponential-remainder PV side equals the cutoff lower vertical
logarithmic-jump integral. -/
theorem Complex.finiteAbelPlana_log_leftVerticalRemainderPV_eq_cutoffLowerVertical
    (w : ℂ)
    (T ε : ℝ)
    (hε : 0 < ε)
    (hεT : ε < T) :
    Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePVNormalized w T ε =
      -Complex.finiteAbelPlanaLogLowerVerticalIntegralFromTo w ε T := by
  exact
    Complex.finiteAbelPlana_log_leftVerticalRemainderPV_cutoffIntegrand_identification
      w T ε hε hεT

/-- Right exponential-remainder PV side equals the cutoff upper vertical
endpoint logarithmic-jump integral. -/
theorem Complex.finiteAbelPlana_log_rightVerticalRemainderPV_eq_cutoffUpperVertical
    (N : ℕ)
    (w : ℂ)
    (T ε : ℝ)
    (hε : 0 < ε)
    (hεT : ε < T) :
    Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePVNormalized N w T ε =
      -Complex.finiteAbelPlanaLogUpperVerticalIntegralFromTo N w ε T := by
  exact
    Complex.finiteAbelPlana_log_rightVerticalRemainderPV_cutoffIntegrand_identification
      N w T ε hε hεT

/-- Cutoff lower vertical integrals converge to the finite window as the lower
cutoff tends to zero from the right. -/
theorem Complex.finiteAbelPlana_log_lowerVerticalIntegralFromTo_tendsto_upTo
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    (hT : 0 < T) :
    Tendsto
      (fun ε : ℝ =>
        Complex.finiteAbelPlanaLogLowerVerticalIntegralFromTo w ε T)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) := by
  have hIoi :
      IntegrableOn
        (fun t : ℝ => Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)
        (Set.Ioi (0 : ℝ)) :=
    Complex.finiteAbelPlana_log_lowerVerticalIntegrand_integrableOn_Ioi hw
  have hIoc :
      IntegrableOn
        (fun t : ℝ => Complex.finiteAbelPlanaLogLowerVerticalIntegrand w t)
        (Set.Ioc (0 : ℝ) T) :=
    hIoi.mono_set (fun t ht => ht.1)
  exact
    Complex.tendsto_integral_Ioc_lower_cutoff_real_of_integrableOn_Ioc
      hIoc hT

/-- Cutoff upper vertical integrals converge to the finite window as the lower
cutoff tends to zero from the right. -/
theorem Complex.finiteAbelPlana_log_upperVerticalIntegralFromTo_tendsto_upTo
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    (hT : 0 < T) :
    Tendsto
      (fun ε : ℝ =>
        Complex.finiteAbelPlanaLogUpperVerticalIntegralFromTo N w ε T)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T)) := by
  have hIoi :
      IntegrableOn
        (fun t : ℝ => Complex.finiteAbelPlanaLogUpperVerticalIntegrand N w t)
        (Set.Ioi (0 : ℝ)) :=
    Complex.finiteAbelPlana_log_upperVerticalIntegrand_integrableOn_Ioi
      hw N
  have hIoc :
      IntegrableOn
        (fun t : ℝ => Complex.finiteAbelPlanaLogUpperVerticalIntegrand N w t)
        (Set.Ioc (0 : ℝ) T) :=
    hIoi.mono_set (fun t ht => ht.1)
  exact
    Complex.tendsto_integral_Ioc_lower_cutoff_real_of_integrableOn_Ioc
      hIoc hT

/-- PV left constant vertical side converges to the ordinary left constant
vertical side as the symmetric indentation radius tends to zero.

This is the local primitive-continuity input for the constant cotangent kernel:
the only missing mass is the slit `(-ε,ε)` around the endpoint indentation, and
its interval integral tends to zero. -/
theorem Complex.finiteAbelPlana_log_leftConstantSidePV_tendsto_constantSide
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    (hT : 0 < T) :
    Tendsto
      (fun ε : ℝ =>
        Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSidePV w T ε)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) := by
  let g₋ : ℝ → ℂ := fun y : ℝ =>
    Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
      ((Real.pi : ℂ) * Complex.I)
  let g₊ : ℝ → ℂ := fun y : ℝ =>
    Complex.finiteAbelPlanaLogSummand w (Complex.I * (y : ℂ)) *
      (-(Real.pi : ℂ) * Complex.I)
  have harg_neg :
      Tendsto (fun ε : ℝ => -ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    (continuousAt_id.neg).tendsto.comp nhdsWithin_le_nhds
  have hneg_primitive :
      Continuous (fun b : ℝ => ∫ y : ℝ in (-T)..b, g₋ y) :=
    intervalIntegral.continuous_primitive
      (fun a b =>
        Complex.intervalIntegrable_finiteAbelPlana_log_leftConstantVerticalIntegrand
          hw a b ((Real.pi : ℂ) * Complex.I))
      (-T)
  have hneg :
      Tendsto
        (fun ε : ℝ => ∫ y : ℝ in (-T)..(-ε), g₋ y)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫ y : ℝ in (-T)..(0 : ℝ), g₋ y)) :=
    hneg_primitive.continuousAt.tendsto.comp harg_neg
  have hpos_primitive :
      Continuous (fun a : ℝ => ∫ y : ℝ in T..a, g₊ y) :=
    intervalIntegral.continuous_primitive
      (fun a b =>
        Complex.intervalIntegrable_finiteAbelPlana_log_leftConstantVerticalIntegrand
          hw a b (-(Real.pi : ℂ) * Complex.I))
      T
  have hpos_to_T :
      Tendsto
        (fun ε : ℝ => ∫ y : ℝ in T..ε, g₊ y)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫ y : ℝ in T..(0 : ℝ), g₊ y)) :=
    hpos_primitive.continuousAt.tendsto.comp nhdsWithin_le_nhds
  have hpos :
      Tendsto
        (fun ε : ℝ => ∫ y : ℝ in ε..T, g₊ y)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫ y : ℝ in (0 : ℝ)..T, g₊ y)) := by
    have hnegated :
        Tendsto
          (fun ε : ℝ => -∫ y : ℝ in T..ε, g₊ y)
          (𝓝[>] (0 : ℝ))
          (𝓝 (-(∫ y : ℝ in T..(0 : ℝ), g₊ y))) :=
      hpos_to_T.neg
    have htarget :
        -(∫ y : ℝ in T..(0 : ℝ), g₊ y) =
          ∫ y : ℝ in (0 : ℝ)..T, g₊ y := by
      exact (intervalIntegral.integral_symm T (0 : ℝ) g₊).symm
    have heq :
        (fun ε : ℝ => ∫ y : ℝ in ε..T, g₊ y) =
          fun ε : ℝ => -∫ y : ℝ in T..ε, g₊ y := by
      funext ε
      exact (intervalIntegral.integral_symm T ε g₊).symm
    exact htarget ▸ (heq ▸ hnegated)
  have hsum :
      Tendsto
        (fun ε : ℝ =>
          (∫ y : ℝ in (-T)..(-ε), g₋ y) +
            ∫ y : ℝ in ε..T, g₊ y)
        (𝓝[>] (0 : ℝ))
        (𝓝
          ((∫ y : ℝ in (-T)..(0 : ℝ), g₋ y) +
            ∫ y : ℝ in (0 : ℝ)..T, g₊ y)) :=
    hneg.add hpos
  simpa [Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSidePV,
    Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide, g₋, g₊] using hsum

/-- PV right constant vertical side converges to the ordinary right constant
vertical side as the symmetric indentation radius tends to zero.

This is the endpoint-`N+1` analogue of
`finiteAbelPlana_log_leftConstantSidePV_tendsto_constantSide`. -/
theorem Complex.finiteAbelPlana_log_rightConstantSidePV_tendsto_constantSide
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    (hT : 0 < T) :
    Tendsto
      (fun ε : ℝ =>
        Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSidePV N w T ε)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) := by
  let g₋ : ℝ → ℂ := fun y : ℝ =>
    Complex.finiteAbelPlanaLogSummand w
        (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)) *
      ((Real.pi : ℂ) * Complex.I)
  let g₊ : ℝ → ℂ := fun y : ℝ =>
    Complex.finiteAbelPlanaLogSummand w
        (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)) *
      (-(Real.pi : ℂ) * Complex.I)
  have harg_neg :
      Tendsto (fun ε : ℝ => -ε) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
    (continuousAt_id.neg).tendsto.comp nhdsWithin_le_nhds
  have hneg_primitive :
      Continuous (fun b : ℝ => ∫ y : ℝ in (-T)..b, g₋ y) :=
    intervalIntegral.continuous_primitive
      (fun a b =>
        Complex.intervalIntegrable_finiteAbelPlana_log_rightConstantVerticalIntegrand
          N hw a b ((Real.pi : ℂ) * Complex.I))
      (-T)
  have hneg :
      Tendsto
        (fun ε : ℝ => ∫ y : ℝ in (-T)..(-ε), g₋ y)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫ y : ℝ in (-T)..(0 : ℝ), g₋ y)) :=
    hneg_primitive.continuousAt.tendsto.comp harg_neg
  have hpos_primitive :
      Continuous (fun a : ℝ => ∫ y : ℝ in T..a, g₊ y) :=
    intervalIntegral.continuous_primitive
      (fun a b =>
        Complex.intervalIntegrable_finiteAbelPlana_log_rightConstantVerticalIntegrand
          N hw a b (-(Real.pi : ℂ) * Complex.I))
      T
  have hpos_to_T :
      Tendsto
        (fun ε : ℝ => ∫ y : ℝ in T..ε, g₊ y)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫ y : ℝ in T..(0 : ℝ), g₊ y)) :=
    hpos_primitive.continuousAt.tendsto.comp nhdsWithin_le_nhds
  have hpos :
      Tendsto
        (fun ε : ℝ => ∫ y : ℝ in ε..T, g₊ y)
        (𝓝[>] (0 : ℝ))
        (𝓝 (∫ y : ℝ in (0 : ℝ)..T, g₊ y)) := by
    have hnegated :
        Tendsto
          (fun ε : ℝ => -∫ y : ℝ in T..ε, g₊ y)
          (𝓝[>] (0 : ℝ))
          (𝓝 (-(∫ y : ℝ in T..(0 : ℝ), g₊ y))) :=
      hpos_to_T.neg
    have htarget :
        -(∫ y : ℝ in T..(0 : ℝ), g₊ y) =
          ∫ y : ℝ in (0 : ℝ)..T, g₊ y := by
      exact (intervalIntegral.integral_symm T (0 : ℝ) g₊).symm
    have heq :
        (fun ε : ℝ => ∫ y : ℝ in ε..T, g₊ y) =
          fun ε : ℝ => -∫ y : ℝ in T..ε, g₊ y := by
      funext ε
      exact (intervalIntegral.integral_symm T ε g₊).symm
    exact htarget ▸ (heq ▸ hnegated)
  have hsum :
      Tendsto
        (fun ε : ℝ =>
          (∫ y : ℝ in (-T)..(-ε), g₋ y) +
            ∫ y : ℝ in ε..T, g₊ y)
        (𝓝[>] (0 : ℝ))
        (𝓝
          ((∫ y : ℝ in (-T)..(0 : ℝ), g₋ y) +
            ∫ y : ℝ in (0 : ℝ)..T, g₊ y)) :=
    hneg.add hpos
  simpa [Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSidePV,
    Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide, g₋, g₊] using hsum

/-- PV left constant-kernel primitive convergence. -/
theorem Complex.finiteAbelPlana_log_leftConstantKernelPV_tendsto_realEndpoint
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    (hT : 0 < T) :
    Tendsto
      (fun ε : ℝ =>
        -Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
          Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSidePV w T ε)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w)) := by
  have hside :
      Tendsto
        (fun ε : ℝ =>
          Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSidePV w T ε)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) :=
    Complex.finiteAbelPlana_log_leftConstantSidePV_tendsto_constantSide
      hw T hT
  have hscaled :
      Tendsto
        (fun ε : ℝ =>
          -Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
            Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSidePV w T ε)
        (𝓝[>] (0 : ℝ))
        (𝓝
          (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
            Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T)) :=
    (tendsto_const_nhds.sub ((tendsto_const_nhds.mul hside)))
  have htarget :
      -Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
          Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSide w T =
        Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w :=
    Complex.finiteAbelPlana_log_leftConstantKernelPrimitiveAssembly
      N w T hT
  exact htarget ▸ hscaled

/-- PV right constant-kernel primitive convergence. -/
theorem Complex.finiteAbelPlana_log_rightConstantKernelPV_tendsto_zero
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    (hT : 0 < T) :
    Tendsto
      (fun ε : ℝ =>
        Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
          Complex.I *
            Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSidePV N w T ε)
      (𝓝[>] (0 : ℝ))
      (𝓝 (0 : ℂ)) := by
  have hside :
      Tendsto
        (fun ε : ℝ =>
          Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSidePV N w T ε)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) :=
    Complex.finiteAbelPlana_log_rightConstantSidePV_tendsto_constantSide
      N hw T hT
  have hscaled :
      Tendsto
        (fun ε : ℝ =>
          Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
            Complex.I *
              Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSidePV N w T ε)
        (𝓝[>] (0 : ℝ))
        (𝓝
          (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
            Complex.I *
              Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T)) :=
    (tendsto_const_nhds.add (tendsto_const_nhds.mul hside))
  have htarget :
      Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
          Complex.I *
            Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSide N w T =
        0 :=
    Complex.finiteAbelPlana_log_rightConstantKernelPrimitiveAssembly
      N w T hT
  exact htarget ▸ hscaled

/-- PV left exponential-remainder convergence. -/
theorem Complex.finiteAbelPlana_log_leftVerticalRemainderPV_tendsto_lowerVertical
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    (hT : 0 < T) :
    Tendsto
      (fun ε : ℝ =>
        Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePVNormalized w T ε)
      (𝓝[>] (0 : ℝ))
      (𝓝 (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) := by
  have hevent :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePVNormalized w T ε =
          -Complex.finiteAbelPlanaLogLowerVerticalIntegralFromTo w ε T := by
    filter_upwards [Ioo_mem_nhdsWithin_Ioi ⟨by linarith, hT⟩] with ε hε
    exact
      Complex.finiteAbelPlana_log_leftVerticalRemainderPV_eq_cutoffLowerVertical
        w T ε hε.1 hε.2
  have hlim :
      Tendsto
        (fun ε : ℝ =>
          -Complex.finiteAbelPlanaLogLowerVerticalIntegralFromTo w ε T)
        (𝓝[>] (0 : ℝ))
        (𝓝 (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) :=
    (Complex.finiteAbelPlana_log_lowerVerticalIntegralFromTo_tendsto_upTo
      hw T hT).neg
  exact hlim.congr' hevent.symm

/-- PV right exponential-remainder convergence. -/
theorem Complex.finiteAbelPlana_log_rightVerticalRemainderPV_tendsto_upperVertical
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    (hT : 0 < T) :
    Tendsto
      (fun ε : ℝ =>
        Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePVNormalized N w T ε)
      (𝓝[>] (0 : ℝ))
      (𝓝 (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T)) := by
  have hevent :
      ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ),
        Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePVNormalized N w T ε =
          -Complex.finiteAbelPlanaLogUpperVerticalIntegralFromTo N w ε T := by
    filter_upwards [Ioo_mem_nhdsWithin_Ioi ⟨by linarith, hT⟩] with ε hε
    exact
      Complex.finiteAbelPlana_log_rightVerticalRemainderPV_eq_cutoffUpperVertical
        N w T ε hε.1 hε.2
  have hlim :
      Tendsto
        (fun ε : ℝ =>
          -Complex.finiteAbelPlanaLogUpperVerticalIntegralFromTo N w ε T)
        (𝓝[>] (0 : ℝ))
        (𝓝 (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T)) :=
    (Complex.finiteAbelPlana_log_upperVerticalIntegralFromTo_tendsto_upTo
      N hw T hT).neg
  exact hlim.congr' hevent.symm

/-- Principal-value left endpoint boundary-face convergence. -/
theorem Complex.finiteAbelPlana_log_leftBoundaryFacePV_tendsto_lowerNamedBoundaryFace
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    (hT : 0 < T) :
    Tendsto
      (fun ε : ℝ =>
        Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized N w T ε)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogLowerNamedBoundaryFace N w T)) := by
  have hconst :
      Tendsto
        (fun ε : ℝ =>
          -Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
            Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSidePV w T ε)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w)) :=
    Complex.finiteAbelPlana_log_leftConstantKernelPV_tendsto_realEndpoint
      N hw T hT
  have hrem :
      Tendsto
        (fun ε : ℝ =>
          Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePVNormalized w T ε)
        (𝓝[>] (0 : ℝ))
        (𝓝 (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T)) :=
    Complex.finiteAbelPlana_log_leftVerticalRemainderPV_tendsto_lowerVertical
      hw T hT
  have hsum := hconst.add hrem
  have hpoint :
      (fun ε : ℝ =>
        Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized N w T ε) =
      (fun ε : ℝ =>
        (-Complex.finiteAbelPlanaLogUpperHorizontalCotangentConstantSide N w T -
          Complex.I * Complex.finiteAbelPlanaLogLeftVerticalCotangentConstantSidePV w T ε) +
          Complex.finiteAbelPlanaLogLeftVerticalCotangentRemainderSidePVNormalized w T ε) := by
    funext ε
    dsimp [Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized]
    ring
  have htarget :
      Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression N w +
          (-Complex.finiteAbelPlanaLogLowerVerticalIntegralUpTo w T) =
        Complex.finiteAbelPlanaLogLowerNamedBoundaryFace N w T := by
    dsimp [Complex.finiteAbelPlanaLogLowerNamedBoundaryFace,
      Complex.finiteAbelPlanaLogFiniteHeightRealEndpointSideExpression]
    ring
  exact hpoint ▸ htarget ▸ hsum

/-- Principal-value right endpoint boundary-face convergence. -/
theorem Complex.finiteAbelPlana_log_rightBoundaryFacePV_tendsto_upperNamedBoundaryFace
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    (hT : 0 < T) :
    Tendsto
      (fun ε : ℝ =>
        Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized N w T ε)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogUpperNamedBoundaryFace N w T)) := by
  have hconst :
      Tendsto
        (fun ε : ℝ =>
          Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
            Complex.I *
              Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSidePV N w T ε)
        (𝓝[>] (0 : ℝ))
        (𝓝 (0 : ℂ)) :=
    Complex.finiteAbelPlana_log_rightConstantKernelPV_tendsto_zero
      N hw T hT
  have hrem :
      Tendsto
        (fun ε : ℝ =>
          Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePVNormalized N w T ε)
        (𝓝[>] (0 : ℝ))
        (𝓝 (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T)) :=
    Complex.finiteAbelPlana_log_rightVerticalRemainderPV_tendsto_upperVertical
      N hw T hT
  have hsum := hconst.add hrem
  have hpoint :
      (fun ε : ℝ =>
        Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized N w T ε) =
      (fun ε : ℝ =>
        (Complex.finiteAbelPlanaLogLowerHorizontalCotangentConstantSide N w T +
          Complex.I *
            Complex.finiteAbelPlanaLogRightVerticalCotangentConstantSidePV N w T ε) +
          Complex.finiteAbelPlanaLogRightVerticalCotangentRemainderSidePVNormalized N w T ε) := by
    funext ε
    dsimp [Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized]
    ring
  have htarget :
      (0 : ℂ) + (-Complex.finiteAbelPlanaLogUpperVerticalIntegralUpTo N w T) =
        Complex.finiteAbelPlanaLogUpperNamedBoundaryFace N w T := by
    dsimp [Complex.finiteAbelPlanaLogUpperNamedBoundaryFace]
    ring
  exact hpoint ▸ htarget ▸ hsum

/-- Principal-value boundary-face reconstruction. -/
theorem Complex.finiteAbelPlana_log_boundaryFacesPV_tendsto_namedBoundary
    (N : ℕ)
    {w : ℂ}
    (hw : 0 < w.re)
    (T : ℝ)
    (hT : 0 < T) :
    Tendsto
      (fun ε : ℝ =>
        Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized N w T ε +
          Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized N w T ε)
      (𝓝[>] (0 : ℝ))
      (𝓝 (Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T)) := by
  have hleft :
      Tendsto
        (fun ε : ℝ =>
          Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized N w T ε)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogLowerNamedBoundaryFace N w T)) :=
    Complex.finiteAbelPlana_log_leftBoundaryFacePV_tendsto_lowerNamedBoundaryFace
      N hw T hT
  have hright :
      Tendsto
        (fun ε : ℝ =>
          Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized N w T ε)
        (𝓝[>] (0 : ℝ))
        (𝓝 (Complex.finiteAbelPlanaLogUpperNamedBoundaryFace N w T)) :=
    Complex.finiteAbelPlana_log_rightBoundaryFacePV_tendsto_upperNamedBoundaryFace
      N hw T hT
  have hsum :
      Tendsto
        (fun ε : ℝ =>
          Complex.finiteAbelPlanaLogLeftBoundaryFacePVNormalized N w T ε +
            Complex.finiteAbelPlanaLogRightBoundaryFacePVNormalized N w T ε)
        (𝓝[>] (0 : ℝ))
        (𝓝
          (Complex.finiteAbelPlanaLogLowerNamedBoundaryFace N w T +
            Complex.finiteAbelPlanaLogUpperNamedBoundaryFace N w T)) :=
    hleft.add hright
  exact
    (Complex.finiteAbelPlana_log_namedBoundaryFaces_sum_eq_namedBoundary
      N w T) ▸ hsum

/-- Abel-Plana boundary-face reconstruction.

This is the true vertical/constant-side normalization: the two oriented raw
faces reconstruct the real endpoint contribution and the two named vertical
logarithmic-jump integrals. -/
theorem Complex.finiteAbelPlana_log_boundaryFaces_reconstruct_namedBoundary
    (N : ℕ)
    (w : ℂ)
    (T : ℝ)
    (hT : 0 < T) :
    Complex.finiteAbelPlanaLogLeftBoundaryFace N w T +
        Complex.finiteAbelPlanaLogRightBoundaryFace N w T =
      Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T := by
  have hleft :
      Complex.finiteAbelPlanaLogLeftBoundaryFace N w T =
        Complex.finiteAbelPlanaLogLowerNamedBoundaryFace N w T :=
    Complex.finiteAbelPlana_log_leftBoundaryFace_eq_lowerNamedBoundaryFace
      N w T hT
  have hright :
      Complex.finiteAbelPlanaLogRightBoundaryFace N w T =
        Complex.finiteAbelPlanaLogUpperNamedBoundaryFace N w T :=
    Complex.finiteAbelPlana_log_rightBoundaryFace_eq_upperNamedBoundaryFace
      N w T hT
  calc
    Complex.finiteAbelPlanaLogLeftBoundaryFace N w T +
        Complex.finiteAbelPlanaLogRightBoundaryFace N w T =
      Complex.finiteAbelPlanaLogLowerNamedBoundaryFace N w T +
        Complex.finiteAbelPlanaLogUpperNamedBoundaryFace N w T := by
      exact congrArg₂ HAdd.hAdd hleft hright
    _ = Complex.finiteAbelPlanaLogNamedBoundaryFaceSum N w T :=
      Complex.finiteAbelPlana_log_namedBoundaryFaces_sum_eq_namedBoundary
        N w T

end

end LFunctions
end Boundary
