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

/-- Unfolding of the bottom horizontal edge. -/
theorem Complex.finiteAbelPlana_log_bottomHorizontalEdge_unfold
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T =
      ∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
        Complex.finiteAbelPlanaLogSummand w
          ((x : ℂ) - (T : ℂ) * Complex.I) *
        (Complex.finiteAbelPlanaCotangentKernel
            ((x : ℂ) - (T : ℂ) * Complex.I) -
          (Real.pi : ℂ) * Complex.I) := by
  rfl

/-- Unfolding of the top horizontal edge. -/
theorem Complex.finiteAbelPlana_log_topHorizontalEdge_unfold
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogTopHorizontalEdge N w T =
      ∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
        Complex.finiteAbelPlanaLogSummand w
          ((x : ℂ) + (T : ℂ) * Complex.I) *
        (Complex.finiteAbelPlanaCotangentKernel
            ((x : ℂ) + (T : ℂ) * Complex.I) +
          (Real.pi : ℂ) * Complex.I) := by
  rfl

/-- Unfolding of the horizontal edge error. -/
theorem Complex.finiteAbelPlana_log_horizontalEdgeError_unfold
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogHorizontalEdgeError N w T =
      Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T -
        Complex.finiteAbelPlanaLogTopHorizontalEdge N w T := by
  rfl

/-- Unfolding of the horizontal pointwise majorant. -/
theorem Complex.finiteAbelPlana_log_horizontalPointwiseMajorant_unfold
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant N w T =
      (4 * (Real.pi + 1)) *
        (Real.log (1 + ‖w‖ + (N + 1 : ℝ) + |T|) + Real.pi + 1) *
          Real.exp (-(2 * Real.pi * |T|)) := by
  rfl

/-- Unfolding of the horizontal edge majorant. -/
theorem Complex.finiteAbelPlana_log_horizontalEdgeMajorant_unfold
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogHorizontalEdgeMajorant N w T =
      (4 * (Real.pi + 1)) * (N + 1 : ℝ) *
        (Real.log (1 + ‖w‖ + (N + 1 : ℝ) + |T|) + Real.pi + 1) *
          Real.exp (-(2 * Real.pi * |T|)) := by
  rfl

/-- Multiplying the pointwise horizontal majorant by the interval length gives
the integrated horizontal edge majorant. -/
theorem Complex.finiteAbelPlana_log_horizontalPointwiseMajorant_mul_intervalLength
    (N : ℕ)
    (w : ℂ)
    (T : ℝ) :
    Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant N w T *
        |((N + 1 : ℕ) : ℝ) - (0 : ℝ)| =
      Complex.finiteAbelPlanaLogHorizontalEdgeMajorant N w T := by
  have hpoint :
      Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant N w T =
        (4 * (Real.pi + 1)) *
          (Real.log (1 + ‖w‖ + (N + 1 : ℝ) + |T|) + Real.pi + 1) *
            Real.exp (-(2 * Real.pi * |T|)) :=
    Complex.finiteAbelPlana_log_horizontalPointwiseMajorant_unfold N w T
  have hlength :
      |((N + 1 : ℕ) : ℝ) - (0 : ℝ)| = (N + 1 : ℝ) :=
    Real.horizontal_interval_length_abs N
  have hmajorant :
      Complex.finiteAbelPlanaLogHorizontalEdgeMajorant N w T =
        (4 * (Real.pi + 1)) * (N + 1 : ℝ) *
          (Real.log (1 + ‖w‖ + (N + 1 : ℝ) + |T|) + Real.pi + 1) *
            Real.exp (-(2 * Real.pi * |T|)) :=
    Complex.finiteAbelPlana_log_horizontalEdgeMajorant_unfold N w T
  calc
    Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant N w T *
        |((N + 1 : ℕ) : ℝ) - (0 : ℝ)| =
        ((4 * (Real.pi + 1)) *
          (Real.log (1 + ‖w‖ + (N + 1 : ℝ) + |T|) + Real.pi + 1) *
            Real.exp (-(2 * Real.pi * |T|))) *
          (N + 1 : ℝ) := by
      exact congrArg₂ HMul.hMul hpoint hlength
    _ =
        (4 * (Real.pi + 1)) * (N + 1 : ℝ) *
          (Real.log (1 + ‖w‖ + (N + 1 : ℝ) + |T|) + Real.pi + 1) *
            Real.exp (-(2 * Real.pi * |T|)) := by
      exact Real.horizontal_edge_majorant_assoc
        (4 * (Real.pi + 1))
        (N + 1 : ℝ)
        (Real.log (1 + ‖w‖ + (N + 1 : ℝ) + |T|) + Real.pi + 1)
        (Real.exp (-(2 * Real.pi * |T|)))
    _ = Complex.finiteAbelPlanaLogHorizontalEdgeMajorant N w T :=
      hmajorant.symm

/-- The real number `3` is nonnegative, in the Binet horizontal-decay
normalization. -/
theorem Real.binetHorizontal_zero_le_three : (0 : ℝ) ≤ 3 := by
  exact Nat.cast_nonneg 3

/-- The real number `2` is positive, in the Binet horizontal-decay
normalization. -/
theorem Real.binetHorizontal_two_pos : (0 : ℝ) < 2 := by
  exact Nat.cast_pos.mpr (Nat.succ_pos 1)

/-- The real number `1` is bounded by `4`, in the Binet horizontal-decay
normalization. -/
theorem Real.binetHorizontal_one_le_four : (1 : ℝ) ≤ 4 := by
  exact (Nat.cast_le.mpr (Nat.succ_le_succ (Nat.zero_le 3)) :
    ((1 : ℕ) : ℝ) ≤ ((4 : ℕ) : ℝ))

/-- The real number `3` is bounded by `4`, in the Binet horizontal-decay
normalization. -/
theorem Real.binetHorizontal_three_le_four : (3 : ℝ) ≤ 4 := by
  exact (Nat.cast_le.mpr
    (Nat.succ_le_succ
      (Nat.succ_le_succ
        (Nat.succ_le_succ (Nat.zero_le 0)))) :
    ((3 : ℕ) : ℝ) ≤ ((4 : ℕ) : ℝ))

/-- The basic absolute-value inequality `0 ≤ c + |c|`. -/
theorem Real.binetHorizontal_self_add_abs_nonneg (c : ℝ) :
    0 ≤ c + |c| := by
  have hneg : -c ≤ |c| :=
    neg_le_abs c
  calc
    0 = -c + c := by
      exact (neg_add_cancel c).symm
    _ ≤ |c| + c := by
      exact add_le_add_right hneg c
    _ = c + |c| := by
      exact add_comm |c| c

/-- If `|c| + 1 ≤ T`, then the shifted horizontal log argument is at least
`1` once `|T| = T`. -/
theorem Real.binetHorizontal_one_le_log_argument_of_abs_bound
    {c T : ℝ}
    (hT_abs : |c| + 1 ≤ T)
    (hT_abs_value : |T| = T) :
    1 ≤ 1 + c + |T| := by
  have hnonneg_c_T : 0 ≤ c + T := by
    calc
      0 ≤ c + |c| := Real.binetHorizontal_self_add_abs_nonneg c
      _ ≤ c + (|c| + 1) := by
        exact add_le_add_left (le_add_of_nonneg_right zero_le_one) c
      _ ≤ c + T := by
        exact add_le_add_left hT_abs c
      _ = T + c := by
        exact add_comm c T
      _ = c + T := by
        exact add_comm T c
  calc
    1 = 1 + 0 := by
      exact (add_zero 1).symm
    _ ≤ 1 + (c + T) := by
      exact add_le_add_left hnonneg_c_T 1
    _ = 1 + c + T := by
      exact (add_assoc 1 c T).symm
    _ = 1 + c + |T| := by
      exact congrArg (fun z : ℝ => 1 + c + z) hT_abs_value.symm

/-- If `|c| + 1 ≤ T`, then the shifted horizontal log argument is bounded by
`2*T` once `|T| = T`. -/
theorem Real.binetHorizontal_log_argument_le_two_mul
    {c T : ℝ}
    (hT_abs : |c| + 1 ≤ T)
    (hT_abs_value : |T| = T) :
    1 + c + |T| ≤ 2 * T := by
  have hc_one_le_T : c + 1 ≤ T := by
    calc
      c + 1 ≤ |c| + 1 := by
        exact add_le_add_right (le_abs_self c) 1
      _ ≤ T := hT_abs
  calc
    1 + c + |T| = (c + 1) + T := by
      calc
        1 + c + |T| = 1 + c + T := by
          exact congrArg (fun z : ℝ => 1 + c + z) hT_abs_value
        _ = (1 + c) + T := by
          rfl
        _ = (c + 1) + T := by
          exact congrArg (fun z : ℝ => z + T) (add_comm 1 c)
    _ ≤ T + T := by
      exact add_le_add_right hc_one_le_T T
    _ = 2 * T := by
      exact (two_mul T).symm

/-- The shifted logarithmic factor is nonnegative once the logarithm itself is
nonnegative. -/
theorem Real.binetHorizontal_log_factor_nonneg
    {c T : ℝ}
    (hlog_nonneg : 0 ≤ Real.log (1 + c + |T|)) :
    0 ≤ Real.log (1 + c + |T|) + Real.pi + 1 := by
  have hpi_nonneg : 0 ≤ Real.pi :=
    le_of_lt Real.pi_pos
  exact add_nonneg (add_nonneg hlog_nonneg hpi_nonneg) zero_le_one

/-- The logarithmic factor is bounded by `2*T + π + 1` once the log argument is
bounded by `2*T`. -/
theorem Real.binetHorizontal_log_factor_le_two_mul_add
    {c T : ℝ}
    (hlog_le_arg : Real.log (1 + c + |T|) ≤ 1 + c + |T|)
    (harg_le_two_mul_T : 1 + c + |T| ≤ 2 * T) :
    Real.log (1 + c + |T|) + Real.pi + 1 ≤
      2 * T + Real.pi + 1 := by
  have hlog_le_two_mul :
      Real.log (1 + c + |T|) ≤ 2 * T :=
    le_trans hlog_le_arg harg_le_two_mul_T
  exact add_le_add_right (add_le_add_right hlog_le_two_mul Real.pi) 1

/-- For the chosen horizontal-decay cutoff, the linear remainder is dominated
by the quadratic term. -/
theorem Real.binetHorizontal_two_mul_add_le_sq_of_large
    {T : ℝ}
    (hT_large : (4 + Real.pi : ℝ) ≤ T) :
    2 * T + Real.pi + 1 ≤ T ^ 2 := by
  have hpi_nonneg : 0 ≤ Real.pi :=
    le_of_lt Real.pi_pos
  have hthree_le_T : (3 : ℝ) ≤ T := by
    calc
      (3 : ℝ) ≤ 4 := Real.binetHorizontal_three_le_four
      _ ≤ 4 + Real.pi := by
        exact le_add_of_nonneg_right hpi_nonneg
      _ ≤ T := hT_large
  have hT_nonneg : 0 ≤ T :=
    le_trans Real.binetHorizontal_zero_le_three hthree_le_T
  have hpi_one_le_T : Real.pi + 1 ≤ T := by
    calc
      Real.pi + 1 ≤ Real.pi + 4 := by
        exact add_le_add_left Real.binetHorizontal_one_le_four Real.pi
      _ = 4 + Real.pi := by
        exact add_comm Real.pi 4
      _ ≤ T := hT_large
  have hlinear_le_three_mul : 2 * T + Real.pi + 1 ≤ 3 * T := by
    calc
      2 * T + Real.pi + 1 = 2 * T + (Real.pi + 1) := by
        exact add_assoc (2 * T) Real.pi 1
      _ ≤ 2 * T + T := by
        exact add_le_add_left hpi_one_le_T (2 * T)
      _ = (2 + 1) * T := by
        exact (add_mul 2 1 T).symm
      _ = 3 * T := by
        rfl
  have hthree_mul_le_sq : 3 * T ≤ T ^ 2 := by
    calc
      3 * T ≤ T * T := by
        exact mul_le_mul_of_nonneg_right hthree_le_T hT_nonneg
      _ = T ^ 2 := by
        exact (pow_two T).symm
  exact le_trans hlinear_le_three_mul hthree_mul_le_sq

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
  have hsource :
      ‖Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T‖ =
        ‖∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
          Complex.finiteAbelPlanaLogSummand w
            ((x : ℂ) - (T : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentKernel
              ((x : ℂ) - (T : ℂ) * Complex.I) -
            (Real.pi : ℂ) * Complex.I)‖ :=
    congrArg norm
      (Complex.finiteAbelPlana_log_bottomHorizontalEdge_unfold N w T)
  have htarget :
      Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant N w T *
          |((N + 1 : ℕ) : ℝ) - (0 : ℝ)| =
        Complex.finiteAbelPlanaLogHorizontalEdgeMajorant N w T :=
    Complex.finiteAbelPlana_log_horizontalPointwiseMajorant_mul_intervalLength
      N w T
  exact hsource.symm ▸ htarget ▸ hnorm

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
  have hsource :
      ‖Complex.finiteAbelPlanaLogTopHorizontalEdge N w T‖ =
        ‖∫ x : ℝ in (0 : ℝ)..((N + 1 : ℕ) : ℝ),
          Complex.finiteAbelPlanaLogSummand w
            ((x : ℂ) + (T : ℂ) * Complex.I) *
          (Complex.finiteAbelPlanaCotangentKernel
              ((x : ℂ) + (T : ℂ) * Complex.I) +
            (Real.pi : ℂ) * Complex.I)‖ :=
    congrArg norm
      (Complex.finiteAbelPlana_log_topHorizontalEdge_unfold N w T)
  have htarget :
      Complex.finiteAbelPlanaLogHorizontalPointwiseMajorant N w T *
          |((N + 1 : ℕ) : ℝ) - (0 : ℝ)| =
        Complex.finiteAbelPlanaLogHorizontalEdgeMajorant N w T :=
    Complex.finiteAbelPlana_log_horizontalPointwiseMajorant_mul_intervalLength
      N w T
  exact hsource.symm ▸ htarget ▸ hnorm

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
    calc
      (3 : ℝ) ≤ 4 := Real.binetHorizontal_three_le_four
      _ ≤ 4 + Real.pi := by
        exact le_add_of_nonneg_right hpi_nonneg
      _ ≤ T := hT_large
  have hT_nonneg : 0 ≤ T :=
    le_trans Real.binetHorizontal_zero_le_three hT_three
  have hT_abs_value : |T| = T :=
    abs_of_nonneg hT_nonneg
  have hc_le_abs : c ≤ |c| :=
    le_abs_self c
  have harg_ge_one : 1 ≤ 1 + c + |T| := by
    exact Real.binetHorizontal_one_le_log_argument_of_abs_bound
      hT_abs hT_abs_value
  have harg_nonneg : 0 ≤ 1 + c + |T| :=
    le_trans zero_le_one harg_ge_one
  have hlog_nonneg : 0 ≤ Real.log (1 + c + |T|) :=
    Real.log_nonneg harg_ge_one
  have hnonneg : 0 ≤ Real.log (1 + c + |T|) + Real.pi + 1 := by
    exact Real.binetHorizontal_log_factor_nonneg hlog_nonneg
  have harg_le_two_mul_T : 1 + c + |T| ≤ 2 * T := by
    exact Real.binetHorizontal_log_argument_le_two_mul
      hT_abs hT_abs_value
  have hlog_le_arg : Real.log (1 + c + |T|) ≤ 1 + c + |T| :=
    Real.log_le_self harg_nonneg
  have hlog_add_le_two_mul_add :
      Real.log (1 + c + |T|) + Real.pi + 1 ≤ 2 * T + Real.pi + 1 := by
    exact Real.binetHorizontal_log_factor_le_two_mul_add
      hlog_le_arg harg_le_two_mul_T
  have htwo_mul_add_le_sq : 2 * T + Real.pi + 1 ≤ T ^ 2 := by
    exact Real.binetHorizontal_two_mul_add_le_sq_of_large hT_large
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
      have hrpow :
          Tendsto
            (fun T : ℝ =>
              T ^ (2 : ℝ) *
                Real.exp (-(2 * Real.pi * T)))
            atTop
            (𝓝 (0 : ℝ)) :=
        Real.tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
          (2 : ℝ) (2 * Real.pi)
          (mul_pos Real.binetHorizontal_two_pos Real.pi_pos)
      have heq :
          ∀ᶠ T : ℝ in atTop,
            T ^ (2 : ℕ) *
                Real.exp (-(2 * Real.pi * T)) =
              T ^ (2 : ℝ) *
                Real.exp (-(2 * Real.pi * T)) := by
        filter_upwards [eventually_ge_atTop (0 : ℝ)] with T hT
        exact congrArg
          (fun x : ℝ => x * Real.exp (-(2 * Real.pi * T)))
          (Real.rpow_natCast T 2).symm
      exact hrpow.congr' heq.symm
    exact hpow
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
        exact congrArg
          (fun y : ℝ =>
            (Real.log (1 + c + |T|) + Real.pi + 1) *
              Real.exp (-(2 * Real.pi * y)))
          habs
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
  have hscaled :
      Tendsto
        (fun T : ℝ =>
          ((4 * (Real.pi + 1)) * (N + 1 : ℝ)) *
            ((Real.log (1 + (‖w‖ + (N + 1 : ℝ)) + |T|) + Real.pi + 1) *
              Real.exp (-(2 * Real.pi * |T|))))
        atTop
        (𝓝 (0 : ℝ)) :=
    hdecay.const_mul ((4 * (Real.pi + 1)) * (N + 1 : ℝ))
  have hsource :
      (fun T : ℝ =>
        ((4 * (Real.pi + 1)) * (N + 1 : ℝ)) *
          ((Real.log (1 + (‖w‖ + (N + 1 : ℝ)) + |T|) + Real.pi + 1) *
            Real.exp (-(2 * Real.pi * |T|)))) =
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogHorizontalEdgeMajorant N w T) := by
    funext T
    have harg :
        1 + (‖w‖ + (N + 1 : ℝ)) + |T| =
          1 + ‖w‖ + (N + 1 : ℝ) + |T| :=
      (add_assoc 1 ‖w‖ (N + 1 : ℝ)).symm ▸ rfl
    calc
      ((4 * (Real.pi + 1)) * (N + 1 : ℝ)) *
          ((Real.log (1 + (‖w‖ + (N + 1 : ℝ)) + |T|) + Real.pi + 1) *
            Real.exp (-(2 * Real.pi * |T|))) =
          (4 * (Real.pi + 1)) * (N + 1 : ℝ) *
            (Real.log (1 + ‖w‖ + (N + 1 : ℝ) + |T|) + Real.pi + 1) *
              Real.exp (-(2 * Real.pi * |T|)) := by
        exact congrArg
          (fun y : ℝ =>
            ((4 * (Real.pi + 1)) * (N + 1 : ℝ)) *
              ((Real.log y + Real.pi + 1) *
                Real.exp (-(2 * Real.pi * |T|))))
          harg
      _ = Complex.finiteAbelPlanaLogHorizontalEdgeMajorant N w T :=
        (Complex.finiteAbelPlana_log_horizontalEdgeMajorant_unfold N w T).symm
  exact hsource ▸ hscaled

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
  have hsource :
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogBottomHorizontalEdge N w T -
          Complex.finiteAbelPlanaLogTopHorizontalEdge N w T) =
      (fun T : ℝ =>
        Complex.finiteAbelPlanaLogHorizontalEdgeError N w T) := by
    funext T
    exact (Complex.finiteAbelPlana_log_horizontalEdgeError_unfold N w T).symm
  exact hsource ▸ hbottom.sub htop

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
