import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.LocalMajorant

/-!
# Parameter derivative majorants for fixed-cutoff Euler-Maclaurin kernels

This file owns the pointwise parameter derivative of the fixed Bernoulli kernel
and the logarithmic majorants used for dominated differentiation.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
open MeasureTheory
local notation "π" => Real.pi

/-- Scalar algebra for the parameter derivative kernel. -/
theorem complex_parameterDerivative_kernel_value_algebra
    (B P L : ℂ) :
    B * (P * L * (-(1 : ℂ))) = -L * (B * P) := by
  calc
    B * (P * L * (-(1 : ℂ))) = B * ((P * L) * (-(1 : ℂ))) := rfl
    _ = B * (P * (L * (-(1 : ℂ)))) := by
      exact congrArg (fun t : ℂ => B * t) (mul_assoc P L (-(1 : ℂ)))
    _ = (B * P) * (L * (-(1 : ℂ))) := by
      exact (mul_assoc B P (L * (-(1 : ℂ)))).symm
    _ = (L * (-(1 : ℂ))) * (B * P) := by
      exact mul_comm (B * P) (L * (-(1 : ℂ)))
    _ = -L * (B * P) := by
      exact congrArg (fun t : ℂ => t * (B * P)) (mul_neg_one L)

/-- Exponent arithmetic for the logarithmic tail comparison. -/
theorem real_half_add_neg_delta_add_one_eq_neg_half_add_one
    (δ : ℝ) :
    δ / 2 + (-(δ + 1)) = -(δ / 2 + 1) := by
  have hδ_halves : δ = δ / 2 + δ / 2 :=
    (add_halves δ).symm
  calc
    δ / 2 + (-(δ + 1)) = δ / 2 + (-δ + -1) := by
      exact congrArg (fun t : ℝ => δ / 2 + t) (neg_add δ 1)
    _ = (δ / 2 + -δ) + -1 := by
      exact (add_assoc (δ / 2) (-δ) (-1)).symm
    _ = (δ / 2 + -(δ / 2 + δ / 2)) + -1 := by
      exact congrArg (fun t : ℝ => (δ / 2 + -t) + -1) hδ_halves
    _ = (δ / 2 + (-(δ / 2) + -(δ / 2))) + -1 := by
      exact congrArg
        (fun t : ℝ => (δ / 2 + t) + -1)
        (neg_add (δ / 2) (δ / 2))
    _ = ((δ / 2 + -(δ / 2)) + -(δ / 2)) + -1 := by
      exact congrArg (fun t : ℝ => t + -1)
        (add_assoc (δ / 2) (-(δ / 2)) (-(δ / 2))).symm
    _ = (0 + -(δ / 2)) + -1 := by
      exact congrArg
        (fun t : ℝ => (t + -(δ / 2)) + -1)
        (add_neg_cancel (δ / 2))
    _ = -(δ / 2) + -1 := by
      exact congrArg (fun t : ℝ => t + -1) (zero_add (-(δ / 2)))
    _ = -(δ / 2 + 1) := by
      exact (neg_add (δ / 2) 1).symm

/-- Reciprocal of the half-parameter used in logarithmic tail estimates. -/
theorem real_inv_half_eq_two_div
    (δ : ℝ) :
    (δ / 2)⁻¹ = 2 / δ := by
  exact inv_div δ 2

/-- Parameter derivative of the fixed-cutoff Bernoulli kernel.

For fixed positive `x`, differentiating
`z ↦ B₁({x}) x^(-(z+1))` in the complex parameter contributes the scalar
factor `-Log x`.  This is the pointwise derivative kernel needed before
applying dominated differentiation to the fixed lower-limit improper integral. -/
noncomputable def eulerMaclaurinBernoulliKernel_parameterDerivative
    (x z : ℂ) : ℂ :=
  -Complex.log x *
    (((eulerMaclaurinFirstPeriodicBernoulli x.re : ℝ) : ℂ) *
      (x ^ (-(z + 1))))

/-- Real-tail form of the parameter derivative kernel. -/
noncomputable def eulerMaclaurinBernoulliKernel_realTailParameterDerivative
    (x : ℝ)
    (z : ℂ) : ℂ :=
  -Complex.log ((x : ℝ) : ℂ) *
    (((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      ((((x : ℝ) : ℂ) ^ (-(z + 1)))))

/-- The fixed-parameter derivative kernel is a.e.-strongly measurable on a
positive cutoff tail. -/
theorem eulerMaclaurinBernoulliKernel_parameterDerivative_aestronglyMeasurable
    (N : ℕ)
    (hN : 0 < N)
    (z : ℂ) :
    AEStronglyMeasurable
      (fun x : ℝ =>
        eulerMaclaurinBernoulliKernel_realTailParameterDerivative x z)
      (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))) := by
  let K : ℝ → ℂ := fun x : ℝ =>
    ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
      (((x : ℝ) : ℂ) ^ (-(z + 1)))
  have hlog_real :
      AEStronglyMeasurable
        (fun x : ℝ => -((Real.log x : ℝ) : ℂ))
        (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))) := by
    have hcont :
        ContinuousOn
          (fun x : ℝ => -((Real.log x : ℝ) : ℂ))
          (Set.Ioi (((N : ℕ) : ℝ))) := by
      intro x hx
      have hx_pos : 0 < x :=
        lt_trans (Nat.cast_pos.mpr hN) hx
      exact
        ((Complex.continuous_ofReal.continuousAt.comp
            (Real.continuousAt_log (ne_of_gt hx_pos))).neg).continuousWithinAt
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hkernel :
      AEStronglyMeasurable K
        (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))) := by
    exact
      eulerMaclaurinBernoulliKernel_aestronglyMeasurable N hN z
  have hreal :
      AEStronglyMeasurable
        (fun x : ℝ => -((Real.log x : ℝ) : ℂ) * K x)
        (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))) :=
    hlog_real.mul hkernel
  have hae :
      (fun x : ℝ =>
        -((Real.log x : ℝ) : ℂ) * K x) =ᵐ[
          volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))]
        (fun x : ℝ =>
          eulerMaclaurinBernoulliKernel_realTailParameterDerivative x z) := by
    exact ae_restrict_of_forall_mem measurableSet_Ioi
      (fun x hx_tail => by
        have hx_pos : 0 < x :=
          lt_trans (Nat.cast_pos.mpr hN) hx_tail
        have hlog :
            ((Real.log x : ℝ) : ℂ) =
              Complex.log ((x : ℝ) : ℂ) :=
          Complex.ofReal_log hx_pos.le
        have hmem :
            -((Real.log x : ℝ) : ℂ) * K x =
              eulerMaclaurinBernoulliKernel_realTailParameterDerivative x z := by
          calc
            -((Real.log x : ℝ) : ℂ) * K x =
                -Complex.log ((x : ℝ) : ℂ) * K x := by
              exact congrArg (fun t : ℂ => -t * K x) hlog
            _ = -Complex.log ((x : ℝ) : ℂ) *
                (((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                  (((x : ℝ) : ℂ) ^ (-(z + 1)))) := rfl
            _ = eulerMaclaurinBernoulliKernel_realTailParameterDerivative x z := rfl
        exact hmem
      )
  exact hreal.congr hae

/-- Pointwise complex derivative of the fixed-tail Bernoulli kernel in the
parameter.

This is the owner-level chain-rule input for dominated differentiation.  The
remaining work inside this theorem is only the explicit `cpow` derivative
calculation on the positive real ray; no global analytic assumption is hidden
in a wrapper. -/
theorem eulerMaclaurinBernoulliKernel_hasDerivAt_parameter
    (x : ℝ)
    (hx : 0 < x)
    (z : ℂ) :
    HasDerivAt
      (fun w : ℂ =>
        ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
          (((x : ℝ) : ℂ) ^ (-(w + 1))))
      (eulerMaclaurinBernoulliKernel_realTailParameterDerivative x z)
      z := by
  let B : ℂ := ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
  let a : ℂ := ((x : ℝ) : ℂ)
  have ha_ne : a ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt hx)
  have hexp :
      HasDerivAt
        (fun w : ℂ => -(w + 1))
        (-(1 : ℂ))
        z := by
    exact ((hasDerivAt_id z).add_const (1 : ℂ)).neg
  have hpow :
      HasDerivAt
        (fun w : ℂ => a ^ (-(w + 1)))
        (a ^ (-(z + 1)) * Complex.log a * (-(1 : ℂ)))
        z :=
    hexp.const_cpow (Or.inl ha_ne)
  have hmul :
      HasDerivAt
        (fun w : ℂ => B * (a ^ (-(w + 1))))
        (B * (a ^ (-(z + 1)) * Complex.log a * (-(1 : ℂ))))
        z :=
    hpow.const_mul B
  have hvalue :
      B * (a ^ (-(z + 1)) * Complex.log a * (-(1 : ℂ))) =
        eulerMaclaurinBernoulliKernel_realTailParameterDerivative x z := by
    calc
      B * (a ^ (-(z + 1)) * Complex.log a * (-(1 : ℂ))) =
          -Complex.log a * (B * a ^ (-(z + 1))) := by
        exact complex_parameterDerivative_kernel_value_algebra
          B (a ^ (-(z + 1))) (Complex.log a)
      _ = eulerMaclaurinBernoulliKernel_realTailParameterDerivative x z := rfl
  exact (hmul.congr_deriv hvalue).congr_of_eventuallyEq
    (Filter.Eventually.of_forall
      (fun _w : ℂ => rfl))

/-- Logarithmic power tail dominating the parameter derivative kernel on a
local parameter ball. -/
noncomputable def eulerMaclaurinBernoulliKernel_derivativeMajorant
    (δ : ℝ) : ℝ → ℝ :=
  fun x : ℝ => Real.log x * x ^ (-(δ + 1))

/-- Pointwise logarithmic-power domination on the positive ray.

This is the elementary comparison `log x ≤ x^η / η`, with `η = δ / 2`,
multiplied by the positive factor `x^-(δ+1)`. -/
theorem eulerMaclaurin_log_rpow_neg_delta_add_one_le_rpow_tail
    {x δ : ℝ}
    (hx : 0 < x)
    (hx_one : 1 ≤ x)
    (hδ : 0 < δ) :
    ‖Real.log x * x ^ (-(δ + 1))‖ ≤
      (2 / δ) * x ^ (-(δ / 2 + 1)) := by
  let η : ℝ := δ / 2
  have hη_pos : 0 < η := by
    exact div_pos hδ two_pos
  have hx_nonneg : 0 ≤ x := le_of_lt hx
  have hpow_nonneg : 0 ≤ x ^ (-(δ + 1)) :=
    Real.rpow_nonneg hx_nonneg (-(δ + 1))
  have hlog_le : Real.log x ≤ x ^ η / η :=
    Real.log_le_rpow_div hx_nonneg hη_pos
  have hmul_le :
      Real.log x * x ^ (-(δ + 1)) ≤
        (x ^ η / η) * x ^ (-(δ + 1)) :=
    mul_le_mul_of_nonneg_right hlog_le hpow_nonneg
  have htarget_eq :
      (x ^ η / η) * x ^ (-(δ + 1)) =
        (2 / δ) * x ^ (-(δ / 2 + 1)) := by
    have hpow :
        x ^ η * x ^ (-(δ + 1)) =
          x ^ (-(δ / 2 + 1)) := by
      calc
        x ^ η * x ^ (-(δ + 1)) =
            x ^ (η + (-(δ + 1))) := by
          exact (Real.rpow_add hx η (-(δ + 1))).symm
        _ = x ^ (-(δ / 2 + 1)) := by
          have hexp : η + (-(δ + 1)) = -(δ / 2 + 1) := by
            calc
              η + (-(δ + 1)) = δ / 2 + (-(δ + 1)) := by
                rfl
              _ = -(δ / 2 + 1) := by
                exact real_half_add_neg_delta_add_one_eq_neg_half_add_one δ
          exact congrArg (fun e : ℝ => x ^ e) hexp
    calc
      (x ^ η / η) * x ^ (-(δ + 1)) =
          (η⁻¹) * (x ^ η * x ^ (-(δ + 1))) := by
        calc
          (x ^ η / η) * x ^ (-(δ + 1)) =
              (x ^ η * η⁻¹) * x ^ (-(δ + 1)) := by
            exact congrArg (fun t : ℝ => t * x ^ (-(δ + 1)))
              (div_eq_mul_inv (x ^ η) η)
          _ = η⁻¹ * (x ^ η * x ^ (-(δ + 1))) := by
            calc
              (x ^ η * η⁻¹) * x ^ (-(δ + 1)) =
                  η⁻¹ * x ^ η * x ^ (-(δ + 1)) := by
                exact congrArg (fun t : ℝ => t * x ^ (-(δ + 1)))
                  (mul_comm (x ^ η) η⁻¹)
              _ = η⁻¹ * (x ^ η * x ^ (-(δ + 1))) := by
                exact mul_assoc η⁻¹ (x ^ η) (x ^ (-(δ + 1)))
      _ = η⁻¹ * x ^ (-(δ / 2 + 1)) := by
        exact congrArg (fun t : ℝ => η⁻¹ * t) hpow
      _ = (2 / δ) * x ^ (-(δ / 2 + 1)) := by
        have hη_inv : η⁻¹ = 2 / δ := by
          exact real_inv_half_eq_two_div δ
        exact congrArg (fun t : ℝ => t * x ^ (-(δ / 2 + 1))) hη_inv
  have hlog_nonneg : 0 ≤ Real.log x :=
    Real.log_nonneg hx_one
  have hleft_nonneg :
      0 ≤ Real.log x * x ^ (-(δ + 1)) :=
    mul_nonneg hlog_nonneg hpow_nonneg
  calc
    ‖Real.log x * x ^ (-(δ + 1))‖ =
        |Real.log x * x ^ (-(δ + 1))| := by
      exact Real.norm_eq_abs (Real.log x * x ^ (-(δ + 1)))
    _ = Real.log x * x ^ (-(δ + 1)) := by
      exact abs_of_nonneg hleft_nonneg
    _ ≤ (x ^ η / η) * x ^ (-(δ + 1)) :=
      hmul_le
    _ = (2 / δ) * x ^ (-(δ / 2 + 1)) :=
      htarget_eq

/-- The logarithmic power tail is integrable on every positive cutoff tail.

Classically this follows from the comparison
`log x ≤ x^(δ/2)` for large `x`, reducing the tail to
`x^(-(1+δ/2))`, plus local integrability on the compact initial segment. -/
theorem eulerMaclaurin_integrableOn_Ioi_log_rpow_neg_delta_add_one
    (N : ℕ)
    (hN : 0 < N)
  (δ : ℝ)
  (hδ : 0 < δ) :
  IntegrableOn
    (eulerMaclaurinBernoulliKernel_derivativeMajorant δ)
    (Set.Ioi (((N : ℕ) : ℝ))) := by
  have hN_pos_real : 0 < (((N : ℕ) : ℝ)) := by
    exact Nat.cast_pos.mpr hN
  let b : ℝ → ℝ := fun x : ℝ => (2 / δ) * x ^ (-(δ / 2 + 1))
  have hb_integrable :
      IntegrableOn b (Set.Ioi (((N : ℕ) : ℝ))) := by
    have hexp_lt : -(δ / 2 + 1) < -(1 : ℝ) := by
      have hδ_half_pos : 0 < δ / 2 := div_pos hδ two_pos
      exact neg_lt_neg (lt_add_of_pos_left 1 hδ_half_pos)
    exact
      (integrableOn_Ioi_rpow_of_lt hexp_lt hN_pos_real).const_mul (2 / δ)
  have hmeas :
      AEStronglyMeasurable
        (eulerMaclaurinBernoulliKernel_derivativeMajorant δ)
        (volume.restrict (Set.Ioi (((N : ℕ) : ℝ)))) := by
    have hcont :
        ContinuousOn
          (eulerMaclaurinBernoulliKernel_derivativeMajorant δ)
          (Set.Ioi (((N : ℕ) : ℝ))) := by
      have hlog :
          ContinuousOn Real.log (Set.Ioi (((N : ℕ) : ℝ))) := by
        intro x hx
        have hx_pos : 0 < x := lt_trans hN_pos_real hx
        exact (Real.continuousAt_log (ne_of_gt hx_pos)).continuousWithinAt
      have hrpow :
          ContinuousOn
            (fun x : ℝ => x ^ (-(δ + 1)))
            (Set.Ioi (((N : ℕ) : ℝ))) := by
        exact continuousOn_id.rpow_const
          (fun x hx => Or.inl (ne_of_gt (lt_trans hN_pos_real hx)))
      exact hlog.mul hrpow
    exact hcont.aestronglyMeasurable measurableSet_Ioi
  have hbound :
      ∀ᵐ x ∂volume.restrict (Set.Ioi (((N : ℕ) : ℝ))),
        ‖eulerMaclaurinBernoulliKernel_derivativeMajorant δ x‖ ≤ b x := by
    exact ae_restrict_of_forall_mem measurableSet_Ioi
      (fun x hx => by
        have hx_pos : 0 < x := lt_trans hN_pos_real hx
        have hx_one : 1 ≤ x :=
          eulerMaclaurin_one_le_of_mem_Ioi_nat_cast N hN hx
        exact eulerMaclaurin_log_rpow_neg_delta_add_one_le_rpow_tail
          hx_pos hx_one hδ)
  exact Integrable.mono' hb_integrable hmeas hbound

/-- On a parameter ball with `δ ≤ re z`, the fixed-cutoff Bernoulli parameter
derivative kernel is dominated on the tail by the logarithmic power majorant. -/
theorem eulerMaclaurinBernoulliKernel_parameterDerivative_ae_le_log_rpow_majorant_of_ball_re_lower
    (N : ℕ)
    (hN : 0 < N)
    (z₀ : ℂ)
    (r δ : ℝ)
    (_hδ : 0 < δ)
    (hre_lower : ∀ z : ℂ, z ∈ Metric.ball z₀ r → δ ≤ z.re) :
    ∀ᵐ x ∂volume.restrict (Set.Ioi (((N : ℕ) : ℝ))),
      ∀ z : ℂ, z ∈ Metric.ball z₀ r →
        ‖eulerMaclaurinBernoulliKernel_realTailParameterDerivative x z‖ ≤
          eulerMaclaurinBernoulliKernel_derivativeMajorant δ x := by
  exact ae_restrict_of_forall_mem measurableSet_Ioi
    (fun x hx_tail z hz_ball => by
      have hx_one : 1 ≤ x :=
        eulerMaclaurin_one_le_of_mem_Ioi_nat_cast N hN hx_tail
      have hx_pos : 0 < x :=
        lt_of_lt_of_le zero_lt_one hx_one
      have hδz : δ ≤ z.re :=
        hre_lower z hz_ball
      have hB :
          ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ ≤ 1 :=
        eulerMaclaurinFirstPeriodicBernoulli_norm_cast_le_one_local x
      have hcpow :
          ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ ≤ x ^ (-(δ + 1)) :=
        eulerMaclaurin_norm_real_cpow_le_rpow_of_re_lower
          hx_pos hx_one z hδz
      have hlog_norm :
          ‖-Complex.log ((x : ℝ) : ℂ)‖ = Real.log x := by
        have hlog_ofReal :
            Complex.log ((x : ℝ) : ℂ) = (Real.log x : ℂ) :=
          (Complex.ofReal_log hx_pos.le).symm
        calc
          ‖-Complex.log ((x : ℝ) : ℂ)‖ =
              ‖Complex.log ((x : ℝ) : ℂ)‖ := by
            exact norm_neg (Complex.log ((x : ℝ) : ℂ))
          _ = ‖(Real.log x : ℂ)‖ := by
            exact congrArg norm hlog_ofReal
          _ = |Real.log x| := by
            exact RCLike.norm_ofReal (Real.log x)
          _ = Real.log x := by
            exact abs_of_nonneg (Real.log_nonneg hx_one)
      have hkernel_norm :
          ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((x : ℝ) : ℂ) ^ (-(z + 1)))‖ ≤
            x ^ (-(δ + 1)) := by
        have hcpow_nonneg :
            0 ≤ ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ :=
          norm_nonneg (((x : ℝ) : ℂ) ^ (-(z + 1)))
        have htarget_nonneg :
            0 ≤ x ^ (-(δ + 1)) :=
          Real.rpow_nonneg (le_of_lt hx_pos) (-(δ + 1))
        calc
          ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((x : ℝ) : ℂ) ^ (-(z + 1)))‖ =
              ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)‖ *
                ‖((x : ℝ) : ℂ) ^ (-(z + 1))‖ := by
            exact norm_mul
              ((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ)
              (((x : ℝ) : ℂ) ^ (-(z + 1)))
          _ ≤ 1 * (x ^ (-(δ + 1))) :=
            mul_le_mul hB hcpow hcpow_nonneg zero_le_one
          _ = x ^ (-(δ + 1)) := by
            exact one_mul (x ^ (-(δ + 1)))
      have hlog_nonneg : 0 ≤ Real.log x :=
        Real.log_nonneg hx_one
      calc
        ‖eulerMaclaurinBernoulliKernel_realTailParameterDerivative x z‖ =
            ‖-Complex.log ((x : ℝ) : ℂ)‖ *
            ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((x : ℝ) : ℂ) ^ (-(z + 1)))‖ := by
          exact norm_mul
            (-Complex.log ((x : ℝ) : ℂ))
            (((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
              (((x : ℝ) : ℂ) ^ (-(z + 1))))
        _ = Real.log x *
              ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                (((x : ℝ) : ℂ) ^ (-(z + 1)))‖ := by
          exact congrArg
            (fun t : ℝ =>
              t *
                ‖((eulerMaclaurinFirstPeriodicBernoulli x : ℝ) : ℂ) *
                  (((x : ℝ) : ℂ) ^ (-(z + 1)))‖)
            hlog_norm
        _ ≤ Real.log x * x ^ (-(δ + 1)) :=
          mul_le_mul_of_nonneg_left hkernel_norm hlog_nonneg
        _ = eulerMaclaurinBernoulliKernel_derivativeMajorant δ x := by
          rfl)

/-- Local integrable majorant for the parameter derivative of the fixed-cutoff
Bernoulli kernel on compact parameter neighborhoods inside the punctured
strip. -/
theorem eulerMaclaurinBernoulliKernel_parameterDerivative_local_integrable_majorant_on_puncturedStrip
    (N : ℕ)
    (hN : 0 < N)
    (z₀ : ℂ)
    (hz₀ : z₀ ∈ ({z : ℂ | 0 < z.re ∧ z.re < 2 ∧ z ≠ 1})) :
    ∃ r : ℝ, 0 < r ∧
      ∃ g : ℝ → ℝ, IntegrableOn g (Set.Ioi (((N : ℕ) : ℝ))) ∧
        ∀ᵐ x ∂volume.restrict (Set.Ioi (((N : ℕ) : ℝ))),
          ∀ z : ℂ, z ∈ Metric.ball z₀ r →
            ‖eulerMaclaurinBernoulliKernel_realTailParameterDerivative x z‖ ≤
              g x := by
  have hz₀_pos : 0 < z₀.re :=
    hz₀.1
  exact
    match eulerMaclaurin_ball_realPart_lowerBound_of_pos_re z₀ hz₀_pos with
    | ⟨r, δ, hr_pos, hδ_pos, hre_lower⟩ =>
        let g : ℝ → ℝ := eulerMaclaurinBernoulliKernel_derivativeMajorant δ
        have hg_integrable :
            IntegrableOn g (Set.Ioi (((N : ℕ) : ℝ))) :=
          eulerMaclaurin_integrableOn_Ioi_log_rpow_neg_delta_add_one
            N hN δ hδ_pos
        have hmajorant :
            ∀ᵐ x ∂volume.restrict (Set.Ioi (((N : ℕ) : ℝ))),
              ∀ z : ℂ, z ∈ Metric.ball z₀ r →
                ‖eulerMaclaurinBernoulliKernel_realTailParameterDerivative x z‖ ≤
                  g x :=
          eulerMaclaurinBernoulliKernel_parameterDerivative_ae_le_log_rpow_majorant_of_ball_re_lower
            N hN z₀ r δ hδ_pos hre_lower
        ⟨r, hr_pos, g, hg_integrable, hmajorant⟩

end

end LFunctions
end Boundary
