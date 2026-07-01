import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.VerticalRecurrence.Angular.Defect
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.VerticalRecurrence.FactorBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Vertical recurrence: shifted radius and real-part factors

This subowner contains radius-power and real-part exponential comparisons.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- On a deterministically shifted vertical strip, the radius is comparable to
`1 + |y|`.

This is the base geometric input for the radius-power comparison; the remaining
power step only has to transport this through `rpow` with bounded exponent. -/
theorem Complex.shiftedVertical_radius_base_comparable
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          let w : ℂ :=
            Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y;
          ‖w‖ ≤ C * (1 + ‖y‖) ∧
          c * (1 + ‖y‖) ≤ ‖w‖ := by
  match
      Complex.gammaRecurrenceProduct_factor_upper_on_verticalStrip
        (A + Complex.verticalStripTransportShift A)
        (B + Complex.verticalStripTransportShift A)
        1 with
  | ⟨C, hC_pos, hupper⟩ =>
  have hc_pos : 0 < (1 / 2 : ℝ) :=
    one_div_pos.mpr two_pos
  exact ⟨1, C, 1 / 2, zero_lt_one, hC_pos, hc_pos, by
  intro x y hxA hxB hy
  let w : ℂ :=
    Complex.fixedRealPartVerticalPoint
      (x + Complex.verticalStripTransportShift A) y
  have hxA_shift :
      A + Complex.verticalStripTransportShift A ≤
        x + Complex.verticalStripTransportShift A :=
    add_le_add_right hxA (Complex.verticalStripTransportShift A)
  have hxB_shift :
      x + Complex.verticalStripTransportShift A ≤
        B + Complex.verticalStripTransportShift A :=
    add_le_add_right hxB (Complex.verticalStripTransportShift A)
  have hzero_lt_one_nat : (0 : ℕ) < 1 :=
    Nat.zero_lt_one
  have hupper_w :
      ‖Complex.fixedRealPartVerticalPoint
          (x + Complex.verticalStripTransportShift A) y + ((0 : ℕ) : ℂ)‖ ≤
        C * (1 + ‖y‖) :=
    hupper (x + Complex.verticalStripTransportShift A) y
      hxA_shift hxB_shift 0 hzero_lt_one_nat
  have hzero_add :
      Complex.fixedRealPartVerticalPoint
          (x + Complex.verticalStripTransportShift A) y + (0 : ℂ) =
        w :=
    add_zero w
  have hupper_final :
      ‖w‖ ≤ C * (1 + ‖y‖) :=
    calc
      ‖w‖ =
          ‖Complex.fixedRealPartVerticalPoint
            (x + Complex.verticalStripTransportShift A) y + (0 : ℂ)‖ :=
        congrArg norm hzero_add.symm
      _ =
          ‖Complex.fixedRealPartVerticalPoint
            (x + Complex.verticalStripTransportShift A) y + ((0 : ℕ) : ℂ)‖ := by
        exact congrArg norm
          (congrArg
            (fun t : ℂ =>
              Complex.fixedRealPartVerticalPoint
                (x + Complex.verticalStripTransportShift A) y + t)
            (Nat.cast_zero.symm))
      _ ≤ C * (1 + ‖y‖) := hupper_w
  have hlower_final :
      (1 / 2 : ℝ) * (1 + ‖y‖) ≤ ‖w‖ := by
    have hlower_raw :
        (1 / 2 : ℝ) * (1 + ‖y‖) ≤
          ‖Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y + ((0 : ℕ) : ℂ)‖ :=
      Complex.gammaRecurrenceProduct_factor_largeHeight_lower 0 hy
    calc
      (1 / 2 : ℝ) * (1 + ‖y‖) ≤
          ‖Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y + ((0 : ℕ) : ℂ)‖ :=
        hlower_raw
      _ =
          ‖Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y + (0 : ℂ)‖ := by
        exact congrArg norm
          (congrArg
            (fun t : ℂ =>
              Complex.fixedRealPartVerticalPoint
                (x + Complex.verticalStripTransportShift A) y + t)
            Nat.cast_zero)
      _ = ‖w‖ := congrArg norm hzero_add
  exact ⟨hupper_final, hlower_final⟩⟩

/-- Real bounded-exponent transport for radius powers.

If `R` is uniformly comparable to the height scale `Y`, and the exponent `e`
stays in a fixed bounded interval, then `R^e` is uniformly comparable to
`Y^e`.  This is the purely real step needed after the shifted-strip radius
comparison has removed all complex geometry. -/
theorem real_rpow_comparable_of_base_comparable_and_bounded_exponent
    (C c L U : ℝ)
    (_hC_pos : 0 < C)
    (hc_pos : 0 < c) :
    ∃ K : ℝ, ∃ k : ℝ,
      0 < K ∧
      0 < k ∧
      ∀ R Y e : ℝ,
        0 < Y →
        c * Y ≤ R →
        R ≤ C * Y →
        L ≤ e →
        e ≤ U →
          R ^ e ≤ K * Y ^ e ∧
          k * Y ^ e ≤ R ^ e := by
  let E : ℝ := max |L| |U|
  let M : ℝ := |Real.log c| + |Real.log C|
  let K : ℝ := Real.exp (E * M)
  let k : ℝ := Real.exp (-(E * M))
  have hE_nonneg : 0 ≤ E :=
    le_trans (abs_nonneg L) (le_max_left |L| |U|)
  have hM_nonneg : 0 ≤ M :=
    add_nonneg (abs_nonneg (Real.log c)) (abs_nonneg (Real.log C))
  have hEM_nonneg : 0 ≤ E * M :=
    mul_nonneg hE_nonneg hM_nonneg
  have hK_pos : 0 < K :=
    Real.exp_pos (E * M)
  have hk_pos : 0 < k :=
    Real.exp_pos (-(E * M))
  exact ⟨K, k, hK_pos, hk_pos, by
  intro R Y e hY_pos hlow hhigh hL hU
  let q : ℝ := R / Y
  have hY_nonneg : 0 ≤ Y :=
    le_of_lt hY_pos
  have hY_ne : Y ≠ 0 :=
    ne_of_gt hY_pos
  have hq_lower : c ≤ q := by
    calc
      c = (c * Y) / Y := by
        exact (mul_div_cancel_right₀ c hY_ne).symm
      _ ≤ R / Y :=
        div_le_div_of_nonneg_right hlow hY_nonneg
  have hq_upper : q ≤ C := by
    calc
      q = R / Y := rfl
      _ ≤ (C * Y) / Y :=
        div_le_div_of_nonneg_right hhigh hY_nonneg
      _ = C := by
        exact mul_div_cancel_right₀ C hY_ne
  have hq_pos : 0 < q :=
    lt_of_lt_of_le hc_pos hq_lower
  have hq_nonneg : 0 ≤ q :=
    le_of_lt hq_pos
  have hR_eq : R = q * Y := by
    calc
      R = (R / Y) * Y := by
        exact (div_mul_cancel₀ R hY_ne).symm
      _ = q * Y := rfl
  have he_abs : |e| ≤ E :=
    real_abs_le_max_abs_of_mem_Icc hL hU
  have hlog_abs : |Real.log q| ≤ M := by
    have hlog_le_C : Real.log q ≤ Real.log C :=
      Real.log_le_log hq_pos hq_upper
    have hlog_c_le : Real.log c ≤ Real.log q :=
      Real.log_le_log hc_pos hq_lower
    have hupper : Real.log q ≤ M := by
      calc
        Real.log q ≤ Real.log C := hlog_le_C
        _ ≤ |Real.log C| := le_abs_self (Real.log C)
        _ ≤ |Real.log c| + |Real.log C| :=
          le_add_of_nonneg_left (abs_nonneg (Real.log c))
    have hlower : -M ≤ Real.log q := by
      have hneg_log_q_le : -Real.log q ≤ |Real.log c| := by
        calc
          -Real.log q ≤ -Real.log c := neg_le_neg hlog_c_le
          _ ≤ |Real.log c| := neg_le_abs (Real.log c)
      have hneg_log_q_le_M : -Real.log q ≤ M := by
        calc
          -Real.log q ≤ |Real.log c| := hneg_log_q_le
          _ ≤ |Real.log c| + |Real.log C| :=
            le_add_of_nonneg_right (abs_nonneg (Real.log C))
      exact neg_le.mp hneg_log_q_le_M
    exact abs_le.mpr ⟨hlower, hupper⟩
  have hmul_abs :
      |e * Real.log q| ≤ E * M := by
    calc
      |e * Real.log q| = |e| * |Real.log q| :=
        abs_mul e (Real.log q)
      _ ≤ E * M :=
        mul_le_mul he_abs hlog_abs (abs_nonneg (Real.log q)) hE_nonneg
  have hupper_exp_arg : e * Real.log q ≤ E * M :=
    le_trans (le_abs_self (e * Real.log q)) hmul_abs
  have hlower_exp_arg : -(E * M) ≤ e * Real.log q := by
    have hneg_abs : -|e * Real.log q| ≤ e * Real.log q :=
      neg_abs_le (e * Real.log q)
    have hneg_bound : -(E * M) ≤ -|e * Real.log q| :=
      neg_le_neg hmul_abs
    exact le_trans hneg_bound hneg_abs
  have hq_pow_upper : q ^ e ≤ K := by
    have hq_pow_eq : q ^ e = Real.exp (Real.log q * e) :=
      Real.rpow_def_of_pos hq_pos e
    have hcomm : Real.log q * e = e * Real.log q :=
      mul_comm (Real.log q) e
    calc
      q ^ e = Real.exp (Real.log q * e) := hq_pow_eq
      _ = Real.exp (e * Real.log q) := congrArg Real.exp hcomm
      _ ≤ K := Real.exp_le_exp.mpr hupper_exp_arg
  have hq_pow_lower : k ≤ q ^ e := by
    have hq_pow_eq : q ^ e = Real.exp (Real.log q * e) :=
      Real.rpow_def_of_pos hq_pos e
    have hcomm : Real.log q * e = e * Real.log q :=
      mul_comm (Real.log q) e
    calc
      k ≤ Real.exp (e * Real.log q) := Real.exp_le_exp.mpr hlower_exp_arg
      _ = Real.exp (Real.log q * e) := (congrArg Real.exp hcomm).symm
      _ = q ^ e := hq_pow_eq.symm
  have hY_pow_nonneg : 0 ≤ Y ^ e :=
    Real.rpow_nonneg hY_nonneg e
  have hR_pow_eq : R ^ e = q ^ e * Y ^ e := by
    calc
      R ^ e = (q * Y) ^ e := by
        exact congrArg (fun t : ℝ => t ^ e) hR_eq
      _ = q ^ e * Y ^ e :=
        Real.mul_rpow hq_nonneg hY_nonneg
  constructor
  · calc
      R ^ e = q ^ e * Y ^ e := hR_pow_eq
      _ ≤ K * Y ^ e :=
        mul_le_mul_of_nonneg_right hq_pow_upper hY_pow_nonneg
  · calc
      k * Y ^ e ≤ q ^ e * Y ^ e :=
        mul_le_mul_of_nonneg_right hq_pow_lower hY_pow_nonneg
      _ = R ^ e := hR_pow_eq.symm⟩

/-- Bounded-exponent radius-power comparison for shifted vertical strips.

On a bounded shifted strip, `‖x + N + i y‖` is comparable to `1 + |y|`, while
the exponent `x + N - 1/2` ranges over a fixed compact real interval.  The
standard logarithmic/rpow comparison therefore gives uniform two-sided
constants for the radius power. -/
theorem Complex.shiftedVertical_radiusPower_comparable_boundedExponent
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          let w : ℂ :=
            Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y;
          ‖w‖ ^ (w.re - 1 / 2) ≤
            C * (1 + ‖y‖) ^ (x + Complex.verticalStripTransportShift A - 1 / 2) ∧
          c * (1 + ‖y‖) ^ (x + Complex.verticalStripTransportShift A - 1 / 2) ≤
            ‖w‖ ^ (w.re - 1 / 2) := by
  match Complex.shiftedVertical_radius_base_comparable A B with
  | ⟨Hbase, Cbase, cbase, hHbase_pos, hCbase_pos, hcbase_pos, hbase⟩ =>
  let L : ℝ := A + Complex.verticalStripTransportShift A - 1 / 2
  let U : ℝ := B + Complex.verticalStripTransportShift A - 1 / 2
  match
      real_rpow_comparable_of_base_comparable_and_bounded_exponent
        Cbase cbase L U hCbase_pos hcbase_pos with
  | ⟨K, k, hK_pos, hk_pos, hrpow⟩ =>
  exact ⟨Hbase, K, k, hHbase_pos, hK_pos, hk_pos, by
  intro x y hxA hxB hy
  let w : ℂ :=
    Complex.fixedRealPartVerticalPoint
      (x + Complex.verticalStripTransportShift A) y
  let Y : ℝ := 1 + ‖y‖
  let e : ℝ := x + Complex.verticalStripTransportShift A - 1 / 2
  have hbase_xy := hbase x y hxA hxB hy
  have hY_pos : 0 < Y :=
    add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg y)
  have hw_re :
      w.re = x + Complex.verticalStripTransportShift A :=
    Complex.fixedRealPartVerticalPoint_re
      (x + Complex.verticalStripTransportShift A) y
  have heq :
      w.re - 1 / 2 = e := by
    exact congrArg (fun t : ℝ => t - 1 / 2) hw_re
  have hL : L ≤ e :=
    add_le_add_right
      (add_le_add_right hxA (Complex.verticalStripTransportShift A))
      (-(1 / 2 : ℝ))
  have hU : e ≤ U :=
    add_le_add_right
      (add_le_add_right hxB (Complex.verticalStripTransportShift A))
      (-(1 / 2 : ℝ))
  have hr :
      ‖w‖ ^ e ≤ K * Y ^ e ∧
        k * Y ^ e ≤ ‖w‖ ^ e :=
    hrpow ‖w‖ Y e hY_pos hbase_xy.2 hbase_xy.1 hL hU
  exact
    ⟨by
      calc
        ‖w‖ ^ (w.re - 1 / 2) = ‖w‖ ^ e :=
          congrArg (fun t : ℝ => ‖w‖ ^ t) heq
        _ ≤ K * Y ^ e := hr.1,
      by
      calc
        k * Y ^ e ≤ ‖w‖ ^ e := hr.2
        _ = ‖w‖ ^ (w.re - 1 / 2) :=
          (congrArg (fun t : ℝ => ‖w‖ ^ t) heq).symm⟩⟩

/-- In a fixed shifted vertical strip, the radial polynomial factor in the
principal-power denominator is comparable to the standard height polynomial. -/
theorem Complex.shiftedVertical_radiusPower_comparable
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          let w : ℂ :=
            Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y;
          ‖w‖ ^ (w.re - 1 / 2) ≤
            C * (1 + ‖y‖) ^ (x + Complex.verticalStripTransportShift A - 1 / 2) ∧
          c * (1 + ‖y‖) ^ (x + Complex.verticalStripTransportShift A - 1 / 2) ≤
            ‖w‖ ^ (w.re - 1 / 2) := by
  exact
    Complex.shiftedVertical_radiusPower_comparable_boundedExponent
      A B

/-- On a fixed shifted vertical strip, the real-part exponential factor
`exp (-Re w)` is bounded above and below by positive constants. -/
theorem Complex.shiftedVertical_realPartExp_bounded
    (A B : ℝ) :
    ∃ C : ℝ, ∃ c : ℝ,
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
          let w : ℂ :=
            Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y;
          Real.exp (-w.re) ≤ C ∧
          c ≤ Real.exp (-w.re) := by
  let N : ℝ := Complex.verticalStripTransportShift A
  let C : ℝ := max (Real.exp (-(A + N))) (Real.exp (-(B + N)))
  let c : ℝ := min (Real.exp (-(A + N))) (Real.exp (-(B + N)))
  have hEA_pos : 0 < Real.exp (-(A + N)) :=
    Real.exp_pos (-(A + N))
  have hEB_pos : 0 < Real.exp (-(B + N)) :=
    Real.exp_pos (-(B + N))
  have hC_pos : 0 < C :=
    lt_of_lt_of_le hEA_pos (le_max_left (Real.exp (-(A + N))) (Real.exp (-(B + N))))
  have hc_pos : 0 < c :=
    lt_min hEA_pos hEB_pos
  exact ⟨C, c, hC_pos, hc_pos, by
  intro x y hxA hxB
  let w : ℂ :=
    Complex.fixedRealPartVerticalPoint
      (x + Complex.verticalStripTransportShift A) y
  have hw_re :
      w.re = x + N := by
    exact Complex.fixedRealPartVerticalPoint_re
      (x + Complex.verticalStripTransportShift A) y
  have hleft : A + N ≤ x + N :=
    add_le_add_right hxA N
  have hright : x + N ≤ B + N :=
    add_le_add_right hxB N
  have hneg_upper : -(B + N) ≤ -(x + N) :=
    neg_le_neg hright
  have hneg_lower : -(x + N) ≤ -(A + N) :=
    neg_le_neg hleft
  have hexp_upper_A :
      Real.exp (-(x + N)) ≤ Real.exp (-(A + N)) :=
    Real.exp_le_exp.mpr hneg_lower
  have hexp_upper :
      Real.exp (-(x + N)) ≤ C :=
    le_trans hexp_upper_A
      (le_max_left (Real.exp (-(A + N))) (Real.exp (-(B + N))))
  have hexp_lower_B :
      Real.exp (-(B + N)) ≤ Real.exp (-(x + N)) :=
    Real.exp_le_exp.mpr hneg_upper
  have hexp_lower :
      c ≤ Real.exp (-(x + N)) :=
    le_trans
      (min_le_right (Real.exp (-(A + N))) (Real.exp (-(B + N))))
      hexp_lower_B
  exact
    ⟨by
      calc
        Real.exp (-w.re) = Real.exp (-(x + N)) :=
          congrArg (fun t : ℝ => Real.exp (-t)) hw_re
        _ ≤ C := hexp_upper,
      by
      calc
        c ≤ Real.exp (-(x + N)) := hexp_lower
        _ = Real.exp (-w.re) :=
          (congrArg (fun t : ℝ => Real.exp (-t)) hw_re).symm⟩⟩

/-- Real algebra behind the reciprocal denominator after the exponential and
principal-power norm formulas have been substituted. -/
theorem real_stirlingDenominator_reciprocal_shape
    (R x θ y : ℝ)
    (hR_pos : 0 < R) :
    1 / (Real.exp x *
        (R ^ (1 / 2 - x) / Real.exp (θ * (-y)))) =
      Real.exp (-(θ * y)) * R ^ (x - 1 / 2) * Real.exp (-x) := by
  let E : ℝ := Real.exp x
  let Q : ℝ := R ^ (1 / 2 - x)
  let F : ℝ := Real.exp (θ * (-y))
  have hQ_pos : 0 < Q :=
    Real.rpow_pos_of_pos hR_pos (1 / 2 - x)
  have hF_pos : 0 < F :=
    Real.exp_pos (θ * (-y))
  have hE_pos : 0 < E :=
    Real.exp_pos x
  have htheta : θ * (-y) = -(θ * y) := by
    exact mul_neg θ y
  have hF_eq : F = Real.exp (-(θ * y)) := by
    exact congrArg Real.exp htheta
  have hQ_inv :
      Q⁻¹ = R ^ (x - 1 / 2) := by
    have hexp : x - 1 / 2 = -(1 / 2 - x) := by
      calc
        x - 1 / 2 = x + -(1 / 2) := sub_eq_add_neg x (1 / 2)
        _ = -(1 / 2) + x := add_comm x (-(1 / 2))
        _ = -(1 / 2) + -(-x) := by
          exact congrArg (fun t : ℝ => -(1 / 2) + t) (neg_neg x).symm
        _ = -(1 / 2 + -x) := by
          exact (neg_add (1 / 2) (-x)).symm
        _ = -(1 / 2 - x) := by
          exact congrArg Neg.neg (sub_eq_add_neg (1 / 2) x).symm
    have hneg :
        R ^ (-(1 / 2 - x)) = Q⁻¹ :=
      Real.rpow_neg (le_of_lt hR_pos) (1 / 2 - x)
    exact Eq.trans hneg.symm (congrArg (fun t : ℝ => R ^ t) hexp).symm
  have hE_inv : E⁻¹ = Real.exp (-x) := by
    exact (Real.exp_neg x).symm
  calc
    1 / (Real.exp x * (R ^ (1 / 2 - x) / Real.exp (θ * (-y)))) =
        1 / (E * (Q / F)) := rfl
    _ = (E * (Q / F))⁻¹ := by
      exact one_div (E * (Q / F))
    _ = (Q / F)⁻¹ * E⁻¹ := by
      exact mul_inv_rev E (Q / F)
    _ = (F * Q⁻¹) * E⁻¹ := by
      have hdiv_inv : (Q / F)⁻¹ = F * Q⁻¹ := by
        calc
          (Q / F)⁻¹ = F / Q := inv_div Q F
          _ = F * Q⁻¹ := div_eq_mul_inv F Q
      exact congrArg (fun t : ℝ => t * E⁻¹) hdiv_inv
    _ = F * Q⁻¹ * E⁻¹ := by
      rfl
    _ = Real.exp (-(θ * y)) * R ^ (x - 1 / 2) * Real.exp (-x) := by
      exact congrArg₂ HMul.hMul
        (congrArg₂ HMul.hMul hF_eq hQ_inv)
        hE_inv


end
end LFunctions
end Boundary
