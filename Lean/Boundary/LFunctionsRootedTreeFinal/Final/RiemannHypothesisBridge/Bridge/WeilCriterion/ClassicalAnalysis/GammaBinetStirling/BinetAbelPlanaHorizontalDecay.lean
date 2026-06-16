import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSideAssembly

/-!
# Horizontal-edge decay for the finite-height Abel-Plana contour

This file owns the horizontal edge majorants, their decay, and the contour-error
identification with the vanishing horizontal edge contribution.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- The bottom horizontal edge is bounded by the standard finite-strip
cotangent exponential majorant. -/
theorem Complex.norm_finiteAbelPlanaLogBottomHorizontalEdge_le_majorant
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ‖Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T‖ ≤
        Complex.finiteAbelPlanaLogHorizontalEdgeMajorant N w T := by
  filter_upwards
    [Complex.norm_finiteAbelPlanaLogBottomHorizontalIntegrand_le_majorant
      hw N] with T hpoint
  have hnorm :
      ‖∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
          Complex.finiteAbelPlanaLogSummand w
            ((x : ℂ) - (T : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentKernel
              ((x : ℂ) - (T : ℂ) * Complex.I) -
            (Real.pi : ℂ) * Complex.I)‖ ≤
        Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant N w T *
          |((N + 1 : ℕ) : ℝ) - (0 : ℝ)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun x hx => hpoint x hx)
  simpa [Complex.finiteAbelPlanaLogBottomHorizontalEdge,
    Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant,
    Complex.finiteAbelPlanaLogHorizontalEdgeMajorant,
    mul_assoc, mul_left_comm, mul_comm] using hnorm

/-- The top horizontal edge is bounded by the standard finite-strip cotangent
exponential majorant. -/
theorem Complex.norm_finiteAbelPlanaLogTopHorizontalEdge_le_majorant
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    ∀ᶠ T : ℝ in atTop,
      ‖Complex.finiteAbelPlanaLogTopHorizontalEdge N w T‖ ≤
        Complex.finiteAbelPlanaLogHorizontalEdgeMajorant N w T := by
  filter_upwards
    [Complex.norm_finiteAbelPlanaLogTopHorizontalIntegrand_le_majorant
      hw N] with T hpoint
  have hnorm :
      ‖∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
          Complex.finiteAbelPlanaLogSummand w
            ((x : ℂ) + (T : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentKernel
              ((x : ℂ) + (T : ℂ) * Complex.I) +
            (Real.pi : ℂ) * Complex.I)‖ ≤
        Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant N w T *
          |((N + 1 : ℕ) : ℝ) - (0 : ℝ)| :=
    intervalIntegral.norm_integral_le_of_norm_le_const
      (fun x hx => hpoint x hx)
  simpa [Complex.finiteAbelPlanaLogTopHorizontalEdge,
    Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant,
    Complex.finiteAbelPlanaLogHorizontalEdgeMajorant,
    mul_assoc, mul_left_comm, mul_comm] using hnorm

/-- The logarithmic factor in the finite-strip horizontal-edge majorant is
eventually nonnegative and bounded by a quadratic polynomial. -/
theorem Real.eventually_finiteAbelPlanaLogHorizontalEdge_log_nonneg_le_sq
    (c : ℝ) :
    ∀ᶠ T : ℝ in atTop,
      0 ≤ Real.log (1 + c + |T|) + Real.pi + 1 ∧
        Real.log (1 + c + |T|) + Real.pi + 1 ≤ T ^ 2 := by
  filter_upwards [eventually_ge_atTop (max (4 + Real.pi : ℝ) (|c| + 1))] with T hT
  have hT_large : (4 + Real.pi : ℝ) ≤ T :=
    le_trans (le_max_left (4 + Real.pi : ℝ) (|c| + 1)) hT
  have hT_abs : |c| + 1 ≤ T :=
    le_trans (le_max_right (4 + Real.pi : ℝ) (|c| + 1)) hT
  have hT_three : (3 : ℝ) ≤ T := by
    have hpi_nonneg : (0 : ℝ) ≤ Real.pi := le_of_lt Real.pi_pos
    linarith
  have hT_nonneg : 0 ≤ T :=
    le_trans (by norm_num : (0 : ℝ) ≤ 3) hT_three
  have hT_abs_value : |T| = T :=
    abs_of_nonneg hT_nonneg
  have hc_le_abs : c ≤ |c| :=
    le_abs_self c
  have harg_ge_one : 1 ≤ 1 + c + |T| := by
    rw [hT_abs_value]
    nlinarith [hT_abs, hc_le_abs]
  have harg_nonneg : 0 ≤ 1 + c + |T| :=
    le_trans zero_le_one harg_ge_one
  have hlog_nonneg : 0 ≤ Real.log (1 + c + |T|) :=
    Real.log_nonneg harg_ge_one
  have hnonneg : 0 ≤ Real.log (1 + c + |T|) + Real.pi + 1 := by
    linarith [hlog_nonneg, le_of_lt Real.pi_pos]
  have harg_le_two_mul_T : 1 + c + |T| ≤ 2 * T := by
    rw [hT_abs_value]
    nlinarith [hT_abs, hc_le_abs]
  have hlog_le_arg : Real.log (1 + c + |T|) ≤ 1 + c + |T| :=
    Real.log_le_self harg_nonneg
  have hlog_add_le_two_mul_add :
      Real.log (1 + c + |T|) + Real.pi + 1 ≤ 2 * T + Real.pi + 1 := by
    linarith
  have htwo_mul_add_le_sq : 2 * T + Real.pi + 1 ≤ T ^ 2 := by
    nlinarith [hT_large]
  exact ⟨hnonneg, le_trans hlog_add_le_two_mul_add htwo_mul_add_le_sq⟩

/-- A real asymptotic helper for the finite-strip horizontal-edge majorant:
the logarithmic factor has polynomial growth, hence the exponential term
dominates it at infinity. -/
theorem Real.tendsto_finiteAbelPlanaLogHorizontalEdge_log_exp_zero
    (c : ℝ) :
    Tendsto
      (fun T : ℝ =>
        (Real.log (1 + c + |T|) + Real.pi + 1) *
          Real.exp (-(2 * Real.pi * |T|)))
      atTop
      (𝓝 (0 : ℝ)) := by
  have hpoly_exp :
      Tendsto
        (fun T : ℝ =>
          (T ^ 2 : ℝ) *
            Real.exp (-(2 * Real.pi * T)))
        atTop
        (𝓝 (0 : ℝ)) := by
    have hpow :
        Tendsto
          (fun T : ℝ =>
            T ^ (2 : ℕ) *
              Real.exp (-(2 * Real.pi * T)))
          atTop
          (𝓝 (0 : ℝ)) := by
      simpa [Real.rpow_natCast] using
        (Real.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
          (2 : ℝ) (2 * Real.pi)
          (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos))
    simpa using hpow
  have hlog_bounds :
      ∀ᶠ T : ℝ in atTop,
        0 ≤ Real.log (1 + c + |T|) + Real.pi + 1 ∧
          Real.log (1 + c + |T|) + Real.pi + 1 ≤ T ^ 2 :=
    Real.eventually_finiteAbelPlanaLogHorizontalEdge_log_nonneg_le_sq c
  have hnonneg :
      ∀ᶠ T : ℝ in atTop,
        0 ≤
          (Real.log (1 + c + |T|) + Real.pi + 1) *
            Real.exp (-(2 * Real.pi * |T|)) := by
    filter_upwards [hlog_bounds] with T hT
    exact mul_nonneg hT.1 (Real.exp_nonneg _)
  have hupper :
      ∀ᶠ T : ℝ in atTop,
        (Real.log (1 + c + |T|) + Real.pi + 1) *
            Real.exp (-(2 * Real.pi * |T|)) ≤
          T ^ 2 * Real.exp (-(2 * Real.pi * T)) := by
    filter_upwards [hlog_bounds, eventually_ge_atTop (0 : ℝ)] with T hlog hT
    have habs : |T| = T := abs_of_nonneg hT
    have hexp_nonneg :
        0 ≤ Real.exp (-(2 * Real.pi * T)) :=
      Real.exp_nonneg _
    calc
      (Real.log (1 + c + |T|) + Real.pi + 1) *
          Real.exp (-(2 * Real.pi * |T|)) =
          (Real.log (1 + c + |T|) + Real.pi + 1) *
            Real.exp (-(2 * Real.pi * T)) := by
        rw [habs]
      _ ≤ T ^ 2 * Real.exp (-(2 * Real.pi * T)) := by
        exact mul_le_mul_of_nonneg_right hlog.2 hexp_nonneg
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hpoly_exp hnonneg hupper

/-- The finite-strip horizontal-edge majorant tends to zero. -/
theorem Complex.finiteAbelPlanaLogHorizontalEdgeMajorant_tendsto_zero
    (N : ℕ)
    (w : ℂ) :
    Tendsto
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogHorizontalEdgeMajorant N w T)
      atTop
      (𝓝 (0 : ℝ)) := by
  have hdecay :
      Tendsto
        (fun T : ℝ =>
          (Real.log (1 + (‖w‖ + (N + 1 : ℝ)) + |T|) + Real.pi + 1) *
            Real.exp (-(2 * Real.pi * |T|)))
        atTop
        (𝓝 (0 : ℝ)) :=
    Real.tendsto_finiteAbelPlanaLogHorizontalEdge_log_exp_zero
      (‖w‖ + (N + 1 : ℝ))
  simpa [Complex.finiteAbelPlanaLogHorizontalEdgeMajorant, add_assoc,
    add_left_comm, add_comm, mul_assoc] using
    hdecay.const_mul ((4 * (Real.pi + 1)) * (N + 1 : ℝ))

theorem Complex.finiteAbelPlana_log_bottomHorizontalEdge_tendsto_zero
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    Tendsto
      (fun T : ℝ => Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T)
      atTop
      (𝓝 (0 : ℂ)) := by
  have hbound :
      ∀ᶠ T : ℝ in atTop,
        ‖Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T‖ ≤
          Complex.finiteAbelPlanaLogHorizontalEdgeMajorant N w T :=
    Complex.norm_finiteAbelPlanaLogBottomHorizontalEdge_le_majorant hw N
  have hmajorant :
      Tendsto
        (fun T : ℝ =>
          Complex.finiteAbelPlanaLogHorizontalEdgeMajorant N w T)
        atTop
        (𝓝 (0 : ℝ)) :=
    Complex.finiteAbelPlanaLogHorizontalEdgeMajorant_tendsto_zero N w
  exact tendsto_of_norm_tendsto_zero
    (squeeze_zero_norm' hbound hmajorant)

/-- The top horizontal edge vanishes as the rectangle height tends to
infinity. -/
theorem Complex.finiteAbelPlana_log_topHorizontalEdge_tendsto_zero
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    Tendsto
      (fun T : ℝ => Complex.finiteAbelPlanaLogTopHorizontalEdge N w T)
      atTop
      (𝓝 (0 : ℂ)) := by
  have hbound :
      ∀ᶠ T : ℝ in atTop,
        ‖Complex.finiteAbelPlanaLogTopHorizontalEdge N w T‖ ≤
          Complex.finiteAbelPlanaLogHorizontalEdgeMajorant N w T :=
    Complex.norm_finiteAbelPlanaLogTopHorizontalEdge_le_majorant hw N
  have hmajorant :
      Tendsto
        (fun T : ℝ =>
          Complex.finiteAbelPlanaLogHorizontalEdgeMajorant N w T)
        atTop
        (𝓝 (0 : ℝ)) :=
    Complex.finiteAbelPlanaLogHorizontalEdgeMajorant_tendsto_zero N w
  exact tendsto_of_norm_tendsto_zero
    (squeeze_zero_norm' hbound hmajorant)

/-- Horizontal edges vanish as the rectangle height tends to infinity. -/
theorem Complex.finiteAbelPlana_log_horizontalEdgeError_tendsto_zero_decay
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    Tendsto
      (fun T : ℝ => Complex.finiteAbelPlanaLogHorizontalEdgeError N w T)
      atTop
      (𝓝 (0 : ℂ)) := by
  have hbottom :
      Tendsto
        (fun T : ℝ => Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T)
        atTop
        (𝓝 (0 : ℂ)) :=
    Complex.finiteAbelPlana_log_bottomHorizontalEdge_tendsto_zero hw N
  have htop :
      Tendsto
        (fun T : ℝ => Complex.finiteAbelPlanaLogTopHorizontalEdge N w T)
        atTop
        (𝓝 (0 : ℂ)) :=
    Complex.finiteAbelPlana_log_topHorizontalEdge_tendsto_zero hw N
  dsimp [Complex.finiteAbelPlanaLogHorizontalEdgeError]
  exact hbottom.sub htop

/-- Finite-height horizontal-edge accounting and decay package. -/
theorem Complex.finiteAbelPlana_log_horizontalEdgeAccountingAndDecay_owner
    {w : ℂ}
    (hw : 0 < w.re) :
    ∀ N : ℕ,
      (∀ T : ℝ,
        0 < T →
        Complex.finiteAbelPlanaLogFiniteHeightContourError N w T =
          -Complex.finiteAbelPlanaLogHorizontalEdgeError N w T) ∧
      Tendsto
        (fun T : ℝ => Complex.finiteAbelPlanaLogHorizontalEdgeError N w T)
        atTop
        (𝓝 (0 : ℂ)) := by
  intro N
  exact
    ⟨Complex.finiteAbelPlana_log_finiteHeightContourError_eq_neg_horizontalEdgeError_residueAccounting
        hw N,
      Complex.finiteAbelPlana_log_horizontalEdgeError_tendsto_zero_decay
        hw N⟩

/-- Owner-side form of
`finiteAbelPlana_log_finiteHeightContourError_eq_neg_horizontalEdgeError`. -/
theorem Complex.finiteAbelPlana_log_finiteHeightContourError_eq_neg_horizontalEdgeError_owner
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ)
    (T : ℝ)
    (hT : 0 < T) :
    Complex.finiteAbelPlanaLogFiniteHeightContourError N w T =
      -Complex.finiteAbelPlanaLogHorizontalEdgeError N w T := by
  exact
    (Complex.finiteAbelPlana_log_horizontalEdgeAccountingAndDecay_owner
      hw N).1 T hT

/-- Owner-side form of
`finiteAbelPlana_log_horizontalEdgeError_tendsto_zero`. -/
theorem Complex.finiteAbelPlana_log_horizontalEdgeError_tendsto_zero_owner
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    Tendsto
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogHorizontalEdgeError N w T)
      atTop
      (𝓝 (0 : ℂ)) := by
  exact
    (Complex.finiteAbelPlana_log_horizontalEdgeAccountingAndDecay_owner
      hw N).2

/-- Owner-side form of
`finiteAbelPlana_log_finiteHeightContourError_tendsto_zero`. -/
theorem Complex.finiteAbelPlana_log_finiteHeightContourError_tendsto_zero_owner
    {w : ℂ}
    (hw : 0 < w.re)
    (N : ℕ) :
    Tendsto
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogFiniteHeightContourError N w T)
      atTop
      (𝓝 (0 : ℂ)) := by
  have hidentify :
      ∀ᶠ T : ℝ in atTop,
        Complex.finiteAbelPlanaLogFiniteHeightContourError N w T =
          -Complex.finiteAbelPlanaLogHorizontalEdgeError N w T := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with T hT
    exact
      Complex.finiteAbelPlana_log_finiteHeightContourError_eq_neg_horizontalEdgeError_owner
        hw N T hT
  have hdecay :
      Tendsto
        (fun T : ℝ =>
          -Complex.finiteAbelPlanaLogHorizontalEdgeError N w T)
        atTop
        (𝓝 (0 : ℂ)) :=
    (Complex.finiteAbelPlana_log_horizontalEdgeError_tendsto_zero_owner
      hw N).neg
  exact hdecay.congr' hidentify.symm

end

end LFunctions
end Boundary
