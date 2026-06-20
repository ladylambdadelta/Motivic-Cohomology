import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaZeroTail.ZetaZeroMultiplicitySummability.ZetaZeroMultiplicityCounting.ZetaCompletedZeroJensen.ZetaEntireJensen.EntireJensenFormula.LogSineCircleKernel.LocalSine.Owner

/-!
# Log-sine and unit-circle boundary kernel

This owner layer was split from `LogSineCircleKernel.Owner` without changing public declaration names.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology


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
    (∫ _ in (0 : ℝ)..(2 * Real.pi), Real.log 2) =
      2 * Real.pi * Real.log 2 := by
  calc
    (∫ _ in (0 : ℝ)..(2 * Real.pi), Real.log 2) =
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
        (fun θ : ℝ => Real.log |Real.sin (θ / 2)|) :=
    funext
      (fun θ : ℝ =>
        congrArg (fun x : ℝ => Real.log |Real.sin x|) (mul_one_div θ 2))
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
      (∫ _ in (0 : ℝ)..(2 * Real.pi), Real.log 2) +
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
      exact add_neg_cancel A

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
    exact
      fun θ =>
        have harg :
            ((θ + 2 * Real.pi : ℝ) : ℂ) =
              (θ : ℂ) + 2 * (Real.pi : ℂ) := by
          calc
            ((θ + 2 * Real.pi : ℝ) : ℂ) =
                (θ : ℂ) + ((2 * Real.pi : ℝ) : ℂ) := by
              exact Complex.ofReal_add θ (2 * Real.pi)
            _ = (θ : ℂ) + 2 * (Real.pi : ℂ) := by
              exact congrArg
                (fun x : ℂ => (θ : ℂ) + x)
                (Complex.ofReal_mul 2 Real.pi)
        calc
          k (θ + 2 * Real.pi) =
              Real.log
                ‖1 - Complex.exp (((θ : ℂ) + 2 * (Real.pi : ℂ)) * Complex.I)‖ := by
            exact congrArg
              (fun x : ℂ => Real.log ‖1 - Complex.exp (x * Complex.I)‖)
              harg
          _ = k θ := by
            exact congrArg
              (fun z : ℂ => Real.log ‖1 - z‖)
              (Complex.exp_mul_I_periodic (θ : ℂ))
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
    Function.Periodic.intervalIntegral_add_eq hk_periodic (-α) 0
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
    have hshift_integrand :
        (∫ θ in (0 : ℝ)..(2 * Real.pi),
            Real.log ‖1 - Complex.exp ((θ - α) * Complex.I)‖) =
          ∫ θ in (0 : ℝ)..(2 * Real.pi), k (θ - α) := by
      exact
        intervalIntegral.integral_congr_ae
          (Filter.Eventually.of_forall
            (fun θ _ =>
              calc
                Real.log ‖1 - Complex.exp ((θ - α) * Complex.I)‖ =
                    Real.log
                      ‖1 - Complex.exp ((((θ - α : ℝ) : ℂ) * Complex.I))‖ := by
                  exact congrArg
                    (fun x : ℂ => Real.log ‖1 - Complex.exp (x * Complex.I)‖)
                    (Complex.ofReal_sub θ α).symm
                _ = k (θ - α) := by
                  exact rfl))
    calc
      (∫ θ in (0 : ℝ)..(2 * Real.pi),
          Real.log ‖1 - Complex.exp ((θ - α) * Complex.I)‖) =
          (∫ θ in (0 : ℝ)..(2 * Real.pi), k (θ - α)) := by
        exact hshift_integrand
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


end
end LFunctions
end Boundary
