import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-!
# Arctangent bounds for the Binet kernel

This file owns the small-argument principal-arctangent norm estimates used by
the Binet kernel.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Principal arctangent series terms are bounded by a geometric majorant on the
closed disk `‖z‖ ≤ 1 / 2`. -/
theorem Complex.arctan_series_term_norm_le_geometric
    {z : ℂ}
    (hz : ‖z‖ ≤ (1 / 2 : ℝ)) :
    ∀ n : ℕ,
      ‖(-1 : ℂ) ^ n * z ^ (2 * n + 1) / (2 * n + 1 : ℂ)‖ ≤
        ‖z‖ * ((1 / 2 : ℝ) ^ n) := by
  intro n
  have hz_nonneg : 0 ≤ ‖z‖ :=
    norm_nonneg z
  have hsq_le_half : ‖z‖ ^ 2 ≤ (1 / 2 : ℝ) := by
    have hsq_le_quarter : ‖z‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
      sq_le_sq' hz_nonneg hz
    have hquarter_le_half : (1 / 2 : ℝ) ^ 2 ≤ (1 / 2 : ℝ) := by
      norm_num
    exact le_trans hsq_le_quarter hquarter_le_half
  have hpow_bound :
      ‖z‖ ^ (2 * n + 1) ≤ ‖z‖ * ((1 / 2 : ℝ) ^ n) := by
    calc
      ‖z‖ ^ (2 * n + 1) = ‖z‖ * (‖z‖ ^ 2) ^ n := by
        ring
      _ ≤ ‖z‖ * ((1 / 2 : ℝ) ^ n) := by
        exact
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (sq_nonneg ‖z‖) hsq_le_half n)
            hz_nonneg
  have hden_ge_one : (1 : ℝ) ≤ ‖((2 * n + 1 : ℕ) : ℂ)‖ := by
    norm_num
  have hden_pos : 0 < ‖((2 * n + 1 : ℕ) : ℂ)‖ :=
    lt_of_lt_of_le zero_lt_one hden_ge_one
  have hdiv_le :
      ‖z‖ ^ (2 * n + 1) / ‖((2 * n + 1 : ℕ) : ℂ)‖ ≤
        ‖z‖ ^ (2 * n + 1) := by
    exact
      div_le_of_le_mul₀
        (norm_nonneg _)
        hden_pos
        (by
          calc
            ‖z‖ ^ (2 * n + 1) ≤ ‖z‖ ^ (2 * n + 1) * 1 := by
              rw [mul_one]
            _ ≤ ‖z‖ ^ (2 * n + 1) * ‖((2 * n + 1 : ℕ) : ℂ)‖ :=
              mul_le_mul_of_nonneg_left hden_ge_one
                (pow_nonneg hz_nonneg (2 * n + 1)))
  calc
    ‖(-1 : ℂ) ^ n * z ^ (2 * n + 1) / (2 * n + 1 : ℂ)‖ =
        ‖z‖ ^ (2 * n + 1) / ‖((2 * n + 1 : ℕ) : ℂ)‖ := by
      simp [norm_div, norm_mul, norm_pow]
    _ ≤ ‖z‖ ^ (2 * n + 1) := hdiv_le
    _ ≤ ‖z‖ * ((1 / 2 : ℝ) ^ n) := hpow_bound

/-- The geometric majorant for the arctangent series sums to `2 * ‖z‖`. -/
theorem Complex.arctan_geometric_majorant_hasSum
    (z : ℂ) :
    HasSum (fun n : ℕ => ‖z‖ * ((1 / 2 : ℝ) ^ n)) (2 * ‖z‖) := by
  have hgeom :
      HasSum (fun n : ℕ => ((1 / 2 : ℝ) ^ n)) ((1 - (1 / 2 : ℝ))⁻¹) :=
    hasSum_geometric_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
  have hmul :
      HasSum (fun n : ℕ => ‖z‖ * ((1 / 2 : ℝ) ^ n))
        (‖z‖ * (1 - (1 / 2 : ℝ))⁻¹) :=
    hgeom.mul_left ‖z‖
  have hsum_eq :
      ‖z‖ * (1 - (1 / 2 : ℝ))⁻¹ = 2 * ‖z‖ := by
    ring
  exact hsum_eq ▸ hmul

/-- Principal arctangent is bounded by twice the argument norm on the closed
disk `‖z‖ ≤ 1 / 2`, proved from the arctangent power series. -/
theorem Complex.norm_arctan_le_two_norm_of_norm_le_half_from_series
    {z : ℂ}
    (hz : ‖z‖ ≤ (1 / 2 : ℝ)) :
    ‖Complex.arctan z‖ ≤ 2 * ‖z‖ := by
  have hz_lt_one : ‖z‖ < (1 : ℝ) :=
    lt_of_le_of_lt hz (by norm_num : (1 / 2 : ℝ) < 1)
  have hseries :
      HasSum
        (fun n : ℕ =>
          (-1 : ℂ) ^ n * z ^ (2 * n + 1) / (2 * n + 1 : ℂ))
        (Complex.arctan z) :=
    Complex.hasSum_arctan hz_lt_one
  have hmajorant :
      HasSum (fun n : ℕ => ‖z‖ * ((1 / 2 : ℝ) ^ n)) (2 * ‖z‖) :=
    Complex.arctan_geometric_majorant_hasSum z
  exact
    hseries.norm_le_of_bounded hmajorant
      (Complex.arctan_series_term_norm_le_geometric hz)

/-- Principal arctangent is bounded by twice the argument norm on the closed
disk `‖z‖ ≤ 1 / 2`. -/
theorem Complex.norm_arctan_le_two_norm_of_norm_le_half
    {z : ℂ}
    (hz : ‖z‖ ≤ (1 / 2 : ℝ)) :
    ‖Complex.arctan z‖ ≤ 2 * ‖z‖ := by
  exact
    Complex.norm_arctan_le_two_norm_of_norm_le_half_from_series hz

/-- Arithmetic used to turn a bounded fixed-tail arctangent estimate into a
linear estimate. -/
theorem Real.arctan_fixed_tail_two_mul_div_mul_half_eq
    {B r : ℝ}
    (hr : r ≠ 0) :
    (2 * B / r) * (r / 2) = B := by
  field_simp [hr]

/-- Upper bound for a quotient from an upper numerator bound and a lower
denominator bound. -/
theorem Real.arctan_fixed_tail_div_le_div_of_le_of_le
    {a A d n : ℝ}
    (ha_pos : 0 < a)
    (hn_nonneg : 0 ≤ n)
    (hnA : n ≤ A)
    (had : a ≤ d) :
    n / d ≤ A / a := by
  have hd_pos : 0 < d := lt_of_lt_of_le ha_pos had
  have hA_nonneg : 0 ≤ A := le_trans hn_nonneg hnA
  rw [div_le_div_iff₀ hd_pos ha_pos]
  exact
    le_trans
      (mul_le_mul_of_nonneg_right hnA (le_of_lt ha_pos))
      (mul_le_mul_of_nonneg_left had hA_nonneg)

/-- Lower bound for a quotient from a lower numerator bound and an upper
denominator bound. -/
theorem Real.arctan_fixed_tail_div_le_div_of_le_of_le'
    {a A d n : ℝ}
    (ha_pos : 0 < a)
    (hA_pos : 0 < A)
    (hd_pos : 0 < d)
    (had : d ≤ A)
    (han : a ≤ n) :
    a / A ≤ n / d := by
  rw [div_le_div_iff₀ hA_pos hd_pos]
  exact
    le_trans
      (mul_le_mul_of_nonneg_left had (le_of_lt ha_pos))
      (mul_le_mul_of_nonneg_right han (le_of_lt hA_pos))

/-- The real number `3` is positive. -/
theorem Real.arctan_fixed_tail_zero_lt_three : (0 : ℝ) < 3 :=
  Nat.cast_pos.mpr (Nat.succ_pos 2)

/-- Multiplying by `1 / 3` cancels a leading factor `3`. -/
theorem Real.arctan_fixed_tail_one_div_three_mul_three_mul
    (x : ℝ) :
    (1 / 3 : ℝ) * (3 * x) = x := by
  calc
    (1 / 3 : ℝ) * (3 * x)
        = ((1 / 3 : ℝ) * 3) * x :=
            mul_assoc (1 / 3 : ℝ) 3 x
    _ = 1 * x := by
            exact congrArg (fun y : ℝ => y * x)
              (one_div_mul_cancel
                (ne_of_gt Real.arctan_fixed_tail_zero_lt_three))
    _ = x :=
            one_mul x

/-- Algebraic normalization of the first arctangent branch denominator. -/
theorem Complex.arctan_fixed_tail_one_sub_real_div_mul_I_eq
    (w : ℂ)
    (t : ℝ) :
    1 - ((t : ℂ) / w) * Complex.I =
      (w - (t : ℂ) * Complex.I) / w := by
  by_cases hw : w = 0
  · subst w
    simp
  · field_simp [hw]
    ring

/-- Algebraic normalization of the second arctangent branch denominator. -/
theorem Complex.arctan_fixed_tail_one_add_real_div_mul_I_eq
    (w : ℂ)
    (t : ℝ) :
    1 + ((t : ℂ) / w) * Complex.I =
      (w + (t : ℂ) * Complex.I) / w := by
  by_cases hw : w = 0
  · subst w
    simp
  · field_simp [hw]
    ring

/-- The first normalized branch denominator is bounded below by the real part
of the fixed open-half-plane point. -/
theorem Complex.arctan_fixed_tail_one_sub_real_div_mul_I_norm_lower
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (t : ℝ) :
    w.re / ‖w‖ ≤ ‖1 - ((t : ℂ) / w) * Complex.I‖ := by
  have hw_ne_zero : w ≠ 0 := by
    intro hw_zero
    rw [hw_zero] at hw_re_pos
    exact (lt_irrefl (0 : ℝ)) hw_re_pos
  have hw_norm_pos : 0 < ‖w‖ :=
    norm_pos_iff.mpr hw_ne_zero
  have hre_nonneg : 0 ≤ (w - (t : ℂ) * Complex.I).re := by
    simpa using le_of_lt hw_re_pos
  have hre_abs_eq :
      |(w - (t : ℂ) * Complex.I).re| = w.re := by
    simp [Complex.sub_re, Complex.mul_re, hre_nonneg]
  have hre_le_norm :
      w.re ≤ ‖w - (t : ℂ) * Complex.I‖ := by
    calc
      w.re = |(w - (t : ℂ) * Complex.I).re| := hre_abs_eq.symm
      _ ≤ ‖w - (t : ℂ) * Complex.I‖ := by
        simpa [Complex.normSq, norm_eq_abs] using
          Complex.abs_re_le_abs (w - (t : ℂ) * Complex.I)
  calc
    w.re / ‖w‖ ≤ ‖w - (t : ℂ) * Complex.I‖ / ‖w‖ :=
      div_le_div_of_nonneg_right hre_le_norm (le_of_lt hw_norm_pos)
    _ = ‖(w - (t : ℂ) * Complex.I) / w‖ := by
      rw [norm_div]
    _ = ‖1 - ((t : ℂ) / w) * Complex.I‖ := by
      rw [Complex.arctan_fixed_tail_one_sub_real_div_mul_I_eq]

/-- The second normalized branch denominator is bounded below by the real part
of the fixed open-half-plane point. -/
theorem Complex.arctan_fixed_tail_one_add_real_div_mul_I_norm_lower
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (t : ℝ) :
    w.re / ‖w‖ ≤ ‖1 + ((t : ℂ) / w) * Complex.I‖ := by
  have hw_ne_zero : w ≠ 0 := by
    intro hw_zero
    rw [hw_zero] at hw_re_pos
    exact (lt_irrefl (0 : ℝ)) hw_re_pos
  have hw_norm_pos : 0 < ‖w‖ :=
    norm_pos_iff.mpr hw_ne_zero
  have hre_nonneg : 0 ≤ (w + (t : ℂ) * Complex.I).re := by
    simpa using le_of_lt hw_re_pos
  have hre_abs_eq :
      |(w + (t : ℂ) * Complex.I).re| = w.re := by
    simp [Complex.add_re, Complex.mul_re, hre_nonneg]
  have hre_le_norm :
      w.re ≤ ‖w + (t : ℂ) * Complex.I‖ := by
    calc
      w.re = |(w + (t : ℂ) * Complex.I).re| := hre_abs_eq.symm
      _ ≤ ‖w + (t : ℂ) * Complex.I‖ := by
        simpa [Complex.normSq, norm_eq_abs] using
          Complex.abs_re_le_abs (w + (t : ℂ) * Complex.I)
  calc
    w.re / ‖w‖ ≤ ‖w + (t : ℂ) * Complex.I‖ / ‖w‖ :=
      div_le_div_of_nonneg_right hre_le_norm (le_of_lt hw_norm_pos)
    _ = ‖(w + (t : ℂ) * Complex.I) / w‖ := by
      rw [norm_div]
    _ = ‖1 + ((t : ℂ) / w) * Complex.I‖ := by
      rw [Complex.arctan_fixed_tail_one_add_real_div_mul_I_eq]

/-- The principal logarithm is bounded by the absolute logarithm of the norm
plus the universal argument bound. -/
theorem Complex.arctan_fixed_tail_log_norm_le_abs_log_norm_add_pi
    (z : ℂ) :
    ‖Complex.log z‖ ≤ |Real.log ‖z‖| + Real.pi := by
  calc
    ‖Complex.log z‖ = Complex.abs (Complex.log z) := norm_eq_abs _
    _ ≤ |(Complex.log z).re| + |(Complex.log z).im| :=
      Complex.abs_le_abs_re_add_abs_im (Complex.log z)
    _ = |Real.log ‖z‖| + |Complex.arg z| := by
      rw [Complex.log_re, Complex.log_im, norm_eq_abs]
    _ ≤ |Real.log ‖z‖| + Real.pi :=
      add_le_add_left (Complex.abs_arg_le_pi z) _

/-- A positive two-sided bound for a real argument gives a finite bound for
the absolute value of its logarithm. -/
theorem Real.arctan_fixed_tail_abs_log_le_max_abs_log_of_bounds
    {m M x : ℝ}
    (hm_pos : 0 < m)
    (hmM : m ≤ M)
    (hmx : m ≤ x)
    (hxM : x ≤ M) :
    |Real.log x| ≤
      max |Real.log m| |Real.log M| := by
  have hx_pos : 0 < x := lt_of_lt_of_le hm_pos hmx
  have hM_pos : 0 < M := lt_of_lt_of_le hm_pos hmM
  have hlog_lower : Real.log m ≤ Real.log x :=
    Real.log_le_log hm_pos hmx
  have hlog_upper : Real.log x ≤ Real.log M :=
    Real.log_le_log hx_pos hxM
  have hleft :
      -(max |Real.log m| |Real.log M|) ≤ Real.log x := by
    have hneg_abs_m : -|Real.log m| ≤ Real.log m :=
      neg_abs_le (Real.log m)
    have hmax_left : |Real.log m| ≤ max |Real.log m| |Real.log M| :=
      le_max_left _ _
    exact
      le_trans (neg_le_neg hmax_left)
        (le_trans hneg_abs_m hlog_lower)
  have hright :
      Real.log x ≤ max |Real.log m| |Real.log M| := by
    have hlogM_le_abs : Real.log M ≤ |Real.log M| :=
      le_abs_self (Real.log M)
    have hmax_right : |Real.log M| ≤ max |Real.log m| |Real.log M| :=
      le_max_right _ _
    exact le_trans hlog_upper (le_trans hlogM_le_abs hmax_right)
  exact abs_le.mpr ⟨hleft, hright⟩

/-- A nonzero complex number whose norm has positive two-sided real bounds
has bounded principal logarithm. -/
theorem Complex.arctan_fixed_tail_log_norm_le_of_norm_bounds
    {m M : ℝ}
    (hm_pos : 0 < m)
    (hmM : m ≤ M)
    {z : ℂ}
    (hmz : m ≤ ‖z‖)
    (hzM : ‖z‖ ≤ M) :
    ‖Complex.log z‖ ≤
      max |Real.log m| |Real.log M| + Real.pi := by
  have hlog :
      |Real.log ‖z‖| ≤ max |Real.log m| |Real.log M| :=
    Real.arctan_fixed_tail_abs_log_le_max_abs_log_of_bounds
      hm_pos hmM hmz hzM
  calc
    ‖Complex.log z‖ ≤ |Real.log ‖z‖| + Real.pi :=
      Complex.arctan_fixed_tail_log_norm_le_abs_log_norm_add_pi z
    _ ≤ max |Real.log m| |Real.log M| + Real.pi :=
      add_le_add_right hlog _

/-- The upper-tail ratio can be rewritten without the common factor `w`. -/
theorem Complex.arctan_fixed_tail_ratio_eq
    (w : ℂ)
    (t : ℝ) :
    ((1 + ((t : ℂ) / w) * Complex.I) /
        (1 - ((t : ℂ) / w) * Complex.I)) =
      (w + (t : ℂ) * Complex.I) /
        (w - (t : ℂ) * Complex.I) := by
  by_cases hw : w = 0
  · subst w
    simp
  · rw [Complex.arctan_fixed_tail_one_add_real_div_mul_I_eq,
      Complex.arctan_fixed_tail_one_sub_real_div_mul_I_eq]
    field_simp [hw]

/-- The numerator in the arctangent ratio has norm bounded below by the fixed
positive real part. -/
theorem Complex.arctan_fixed_tail_ratio_numerator_lower
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (t : ℝ) :
    w.re ≤ ‖w + (t : ℂ) * Complex.I‖ := by
  have hre_nonneg : 0 ≤ (w + (t : ℂ) * Complex.I).re := by
    simpa using le_of_lt hw_re_pos
  have hre_abs_eq :
      |(w + (t : ℂ) * Complex.I).re| = w.re := by
    simp [Complex.add_re, Complex.mul_re, hre_nonneg]
  calc
    w.re = |(w + (t : ℂ) * Complex.I).re| := hre_abs_eq.symm
    _ ≤ ‖w + (t : ℂ) * Complex.I‖ := by
      simpa [Complex.normSq, norm_eq_abs] using
        Complex.abs_re_le_abs (w + (t : ℂ) * Complex.I)

/-- The denominator in the arctangent ratio has norm bounded below by the fixed
positive real part. -/
theorem Complex.arctan_fixed_tail_ratio_denominator_lower
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (t : ℝ) :
    w.re ≤ ‖w - (t : ℂ) * Complex.I‖ := by
  have hre_nonneg : 0 ≤ (w - (t : ℂ) * Complex.I).re := by
    simpa using le_of_lt hw_re_pos
  have hre_abs_eq :
      |(w - (t : ℂ) * Complex.I).re| = w.re := by
    simp [Complex.sub_re, Complex.mul_re, hre_nonneg]
  calc
    w.re = |(w - (t : ℂ) * Complex.I).re| := hre_abs_eq.symm
    _ ≤ ‖w - (t : ℂ) * Complex.I‖ := by
      simpa [Complex.normSq, norm_eq_abs] using
        Complex.abs_re_le_abs (w - (t : ℂ) * Complex.I)

/-- On the bounded part of the tail, the unnormalized numerator is bounded by
`3 * ‖w‖`. -/
theorem Complex.arctan_fixed_tail_numerator_le_three_norm
    {w : ℂ}
    {t : ℝ}
    (ht_nonneg : 0 ≤ t)
    (ht_le : t ≤ 2 * ‖w‖) :
    ‖w + (t : ℂ) * Complex.I‖ ≤ 3 * ‖w‖ := by
  have htI_norm : ‖(t : ℂ) * Complex.I‖ = t := by
    simp [norm_mul, ht_nonneg]
  calc
    ‖w + (t : ℂ) * Complex.I‖ ≤ ‖w‖ + ‖(t : ℂ) * Complex.I‖ :=
      norm_add_le _ _
    _ = ‖w‖ + t := by rw [htI_norm]
    _ ≤ ‖w‖ + 2 * ‖w‖ := add_le_add_left ht_le _
    _ = 3 * ‖w‖ := by ring

/-- On the bounded part of the tail, the unnormalized denominator is bounded
by `3 * ‖w‖`. -/
theorem Complex.arctan_fixed_tail_denominator_le_three_norm
    {w : ℂ}
    {t : ℝ}
    (ht_nonneg : 0 ≤ t)
    (ht_le : t ≤ 2 * ‖w‖) :
    ‖w - (t : ℂ) * Complex.I‖ ≤ 3 * ‖w‖ := by
  have htI_norm : ‖(t : ℂ) * Complex.I‖ = t := by
    simp [norm_mul, ht_nonneg]
  calc
    ‖w - (t : ℂ) * Complex.I‖ ≤ ‖w‖ + ‖(t : ℂ) * Complex.I‖ := by
      simpa [sub_eq_add_neg] using norm_add_le w (-((t : ℂ) * Complex.I))
    _ = ‖w‖ + t := by rw [norm_neg, htI_norm]
    _ ≤ ‖w‖ + 2 * ‖w‖ := add_le_add_left ht_le _
    _ = 3 * ‖w‖ := by ring

/-- On the far part of the tail, the two unnormalized branch distances are
within a factor `3` of one another. -/
theorem Complex.arctan_fixed_tail_far_ratio_bounds
    {w : ℂ}
    {t : ℝ}
    (ht_far : 2 * ‖w‖ ≤ t) :
    ‖w + (t : ℂ) * Complex.I‖ ≤
        3 * ‖w - (t : ℂ) * Complex.I‖ ∧
      ‖w - (t : ℂ) * Complex.I‖ ≤
        3 * ‖w + (t : ℂ) * Complex.I‖ := by
  have ht_nonneg : 0 ≤ t :=
    le_trans (mul_nonneg zero_le_two (norm_nonneg w)) ht_far
  have htI_norm : ‖(t : ℂ) * Complex.I‖ = t := by
    simp [norm_mul, ht_nonneg]
  have htail_upper : ‖w‖ + t ≤ 3 * (t - ‖w‖) := by
    linarith [ht_far]
  have hminus_lower :
      t - ‖w‖ ≤ ‖w - (t : ℂ) * Complex.I‖ := by
    have hrev :
        ‖(t : ℂ) * Complex.I‖ - ‖w‖ ≤
          ‖(t : ℂ) * Complex.I - w‖ :=
      norm_sub_norm_le ((t : ℂ) * Complex.I) w
    have hnorm_eq :
        ‖(t : ℂ) * Complex.I - w‖ =
          ‖w - (t : ℂ) * Complex.I‖ := by
      rw [← norm_neg (w - (t : ℂ) * Complex.I)]
      congr 1
      abel
    simpa [htI_norm, hnorm_eq] using hrev
  have hplus_lower :
      t - ‖w‖ ≤ ‖w + (t : ℂ) * Complex.I‖ := by
    have hrev :
        ‖(t : ℂ) * Complex.I‖ - ‖w‖ ≤
          ‖(t : ℂ) * Complex.I - (-w)‖ :=
      norm_sub_norm_le ((t : ℂ) * Complex.I) (-w)
    have hnorm_eq :
        ‖(t : ℂ) * Complex.I - (-w)‖ =
          ‖w + (t : ℂ) * Complex.I‖ := by
      rw [← norm_neg (w + (t : ℂ) * Complex.I)]
      congr 1
      abel
    simpa [htI_norm, hnorm_eq] using hrev
  have hplus_upper :
      ‖w + (t : ℂ) * Complex.I‖ ≤ ‖w‖ + t := by
    calc
      ‖w + (t : ℂ) * Complex.I‖ ≤ ‖w‖ + ‖(t : ℂ) * Complex.I‖ :=
        norm_add_le _ _
      _ = ‖w‖ + t := by rw [htI_norm]
  have hminus_upper :
      ‖w - (t : ℂ) * Complex.I‖ ≤ ‖w‖ + t := by
    calc
      ‖w - (t : ℂ) * Complex.I‖ ≤ ‖w‖ + ‖(t : ℂ) * Complex.I‖ := by
        simpa [sub_eq_add_neg] using norm_add_le w (-((t : ℂ) * Complex.I))
      _ = ‖w‖ + t := by rw [norm_neg, htI_norm]
  constructor
  · calc
      ‖w + (t : ℂ) * Complex.I‖ ≤ ‖w‖ + t := hplus_upper
      _ ≤ 3 * (t - ‖w‖) := htail_upper
      _ ≤ 3 * ‖w - (t : ℂ) * Complex.I‖ :=
        mul_le_mul_of_nonneg_left hminus_lower
          (by linarith [zero_le_two])
  · calc
      ‖w - (t : ℂ) * Complex.I‖ ≤ ‖w‖ + t := hminus_upper
      _ ≤ 3 * (t - ‖w‖) := htail_upper
      _ ≤ 3 * ‖w + (t : ℂ) * Complex.I‖ :=
        mul_le_mul_of_nonneg_left hplus_lower
          (by linarith [zero_le_two])

/-- Fixed-tail ratio bounds after clearing the common factor `w`. -/
theorem Complex.arctan_fixed_tail_ratio_norm_bounds_cleared
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ m M : ℝ,
      0 < m ∧
      m ≤ M ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          m ≤ ‖(w + (t : ℂ) * Complex.I) /
              (w - (t : ℂ) * Complex.I)‖ ∧
          ‖(w + (t : ℂ) * Complex.I) /
              (w - (t : ℂ) * Complex.I)‖ ≤ M := by
  have hw_ne_zero : w ≠ 0 := by
    intro hw_zero
    rw [hw_zero] at hw_re_pos
    exact (lt_irrefl (0 : ℝ)) hw_re_pos
  have hw_norm_pos : 0 < ‖w‖ :=
    norm_pos_iff.mpr hw_ne_zero
  let m : ℝ := min (w.re / (3 * ‖w‖)) (1 / 3)
  let M : ℝ := max (3 * ‖w‖ / w.re) 3
  have hthree_pos : (0 : ℝ) < 3 :=
    Real.arctan_fixed_tail_zero_lt_three
  have hden_const_pos : 0 < 3 * ‖w‖ :=
    mul_pos hthree_pos hw_norm_pos
  have hm_pos : 0 < m := by
    dsimp [m]
    exact
      lt_min
        (div_pos hw_re_pos hden_const_pos)
        (div_pos zero_lt_one hthree_pos)
  have hM_ge_three : 3 ≤ M := by
    dsimp [M]
    exact le_max_right _ _
  have hm_le_third : m ≤ (1 / 3 : ℝ) := by
    dsimp [m]
    exact min_le_right _ _
  have hm_le_bounded : m ≤ w.re / (3 * ‖w‖) := by
    dsimp [m]
    exact min_le_left _ _
  have hbounded_le_M : 3 * ‖w‖ / w.re ≤ M := by
    dsimp [M]
    exact le_max_left _ _
  refine ⟨m, M, hm_pos, ?_, ?_⟩
  · exact le_trans (le_of_lt hm_pos) hM_ge_three
  · intro t ht_tail
    have ht_nonneg : 0 ≤ t := by
      have hcut_nonneg : 0 ≤ ‖w‖ / 2 :=
        div_nonneg (norm_nonneg w) zero_le_two
      exact le_trans hcut_nonneg (le_of_lt ht_tail)
    have hnum_lower :
        w.re ≤ ‖w + (t : ℂ) * Complex.I‖ :=
      Complex.arctan_fixed_tail_ratio_numerator_lower hw_re_pos t
    have hden_lower :
        w.re ≤ ‖w - (t : ℂ) * Complex.I‖ :=
      Complex.arctan_fixed_tail_ratio_denominator_lower hw_re_pos t
    have hden_pos : 0 < ‖w - (t : ℂ) * Complex.I‖ :=
      lt_of_lt_of_le hw_re_pos hden_lower
    by_cases ht_bounded : t ≤ 2 * ‖w‖
    · have hnum_upper :
          ‖w + (t : ℂ) * Complex.I‖ ≤ 3 * ‖w‖ :=
        Complex.arctan_fixed_tail_numerator_le_three_norm
          ht_nonneg ht_bounded
      have hden_upper :
          ‖w - (t : ℂ) * Complex.I‖ ≤ 3 * ‖w‖ :=
        Complex.arctan_fixed_tail_denominator_le_three_norm
          ht_nonneg ht_bounded
      constructor
      · have hlower :
            w.re / (3 * ‖w‖) ≤
              ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ :=
          Real.arctan_fixed_tail_div_le_div_of_le_of_le'
            hw_re_pos hden_const_pos hden_pos
            hden_upper hnum_lower
        calc
          m ≤ w.re / (3 * ‖w‖) := hm_le_bounded
          _ ≤ ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ := hlower
          _ = ‖(w + (t : ℂ) * Complex.I) /
                (w - (t : ℂ) * Complex.I)‖ := by
            rw [norm_div]
      · have hupper :
            ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ ≤
              3 * ‖w‖ / w.re :=
          Real.arctan_fixed_tail_div_le_div_of_le_of_le
            hw_re_pos (norm_nonneg _)
            hnum_upper hden_lower
        calc
          ‖(w + (t : ℂ) * Complex.I) /
              (w - (t : ℂ) * Complex.I)‖ =
              ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ := by
            rw [norm_div]
          _ ≤ 3 * ‖w‖ / w.re := hupper
          _ ≤ M := hbounded_le_M
    · have ht_far : 2 * ‖w‖ ≤ t := le_of_not_ge ht_bounded
      rcases
          Complex.arctan_fixed_tail_far_ratio_bounds
            (w := w) (t := t) ht_far with
        ⟨hnum_le, hden_le⟩
      constructor
      · have hthird :
            (1 / 3 : ℝ) ≤
              ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ := by
          rw [le_div_iff₀ hden_pos]
          calc
            (1 / 3 : ℝ) *
                ‖w - (t : ℂ) * Complex.I‖ ≤
                (1 / 3 : ℝ) *
                  (3 * ‖w + (t : ℂ) * Complex.I‖) :=
              mul_le_mul_of_nonneg_left hden_le
                (div_nonneg zero_le_one (le_of_lt hthree_pos))
            _ = ‖w + (t : ℂ) * Complex.I‖ :=
              Real.arctan_fixed_tail_one_div_three_mul_three_mul
                ‖w + (t : ℂ) * Complex.I‖
        calc
          m ≤ (1 / 3 : ℝ) := hm_le_third
          _ ≤ ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ := hthird
          _ = ‖(w + (t : ℂ) * Complex.I) /
                (w - (t : ℂ) * Complex.I)‖ := by
            rw [norm_div]
      · have hthree :
            ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ ≤ 3 := by
          rw [div_le_iff₀ hden_pos]
          exact hnum_le
        calc
          ‖(w + (t : ℂ) * Complex.I) /
              (w - (t : ℂ) * Complex.I)‖ =
              ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ := by
            rw [norm_div]
          _ ≤ 3 := hthree
          _ ≤ M := hM_ge_three

/-- On the fixed upper split interval the Möbius ratio entering the arctangent
has norm bounded above and below by positive constants depending only on `w`. -/
theorem Complex.arctan_fixed_tail_ratio_norm_bounds
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ m M : ℝ,
      0 < m ∧
      m ≤ M ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          m ≤
            ‖(1 + ((t : ℂ) / w) * Complex.I) /
              (1 - ((t : ℂ) / w) * Complex.I)‖ ∧
          ‖(1 + ((t : ℂ) / w) * Complex.I) /
              (1 - ((t : ℂ) / w) * Complex.I)‖ ≤ M := by
  rcases
      Complex.arctan_fixed_tail_ratio_norm_bounds_cleared
        hw_re_pos with
    ⟨m, M, hm_pos, hmM, hbounds⟩
  refine ⟨m, M, hm_pos, hmM, ?_⟩
  intro t ht_tail
  simpa [Complex.arctan_fixed_tail_ratio_eq] using
    hbounds t ht_tail

/-- Fixed-ray branch separation gives a uniform bound for the logarithm in
the principal-arctangent formula. -/
theorem Complex.arctan_fixed_tail_log_ratio_bounded
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ L : ℝ,
      0 ≤ L ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          ‖Complex.log
            ((1 + ((t : ℂ) / w) * Complex.I) /
              (1 - ((t : ℂ) / w) * Complex.I))‖ ≤ L := by
  rcases
      Complex.arctan_fixed_tail_ratio_norm_bounds
        hw_re_pos with
    ⟨m, M, hm_pos, hmM, hbounds⟩
  refine ⟨max |Real.log m| |Real.log M| + Real.pi, ?_, ?_⟩
  · exact add_nonneg (le_max_of_le_left (abs_nonneg _)) Real.pi_pos.le
  · intro t ht_tail
    rcases hbounds t ht_tail with ⟨hlower, hupper⟩
    exact
      Complex.arctan_fixed_tail_log_norm_le_of_norm_bounds
        hm_pos hmM hlower hupper

/-- A uniform logarithm bound for the separated arctangent ratio bounds the
principal arctangent itself. -/
theorem Complex.arctan_fixed_tail_bounded_of_log_ratio_bound
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hlog :
      ∃ L : ℝ,
        0 ≤ L ∧
        ∀ t : ℝ,
          t ∈ Set.Ioi (‖w‖ / 2) →
            ‖Complex.log
              ((1 + ((t : ℂ) / w) * Complex.I) /
                (1 - ((t : ℂ) / w) * Complex.I))‖ ≤ L) :
    ∃ B : ℝ,
      0 ≤ B ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          ‖Complex.arctan ((t : ℂ) / w)‖ ≤ B := by
  rcases hlog with ⟨L, hL_nonneg, hL⟩
  refine ⟨L, hL_nonneg, ?_⟩
  intro t ht_tail
  let z : ℂ := (t : ℂ) / w
  have hfactor_norm_le_one : ‖(-Complex.I / 2 : ℂ)‖ ≤ (1 : ℝ) := by
    have hfactor_norm : ‖(-Complex.I / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
      simp [norm_div, Complex.normSq]
    calc
      ‖(-Complex.I / 2 : ℂ)‖ = (1 / 2 : ℝ) := hfactor_norm
      _ ≤ 1 := by linarith [zero_le_one]
  have hmul :
      ‖(-Complex.I / 2 : ℂ) *
          Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ ≤
        ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ := by
    calc
      ‖(-Complex.I / 2 : ℂ) *
          Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ ≤
          ‖(-Complex.I / 2 : ℂ)‖ *
            ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ :=
        norm_mul_le _ _
      _ ≤ 1 *
            ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ :=
        mul_le_mul_of_nonneg_right hfactor_norm_le_one (norm_nonneg _)
      _ = ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ := by
        rw [one_mul]
  calc
    ‖Complex.arctan ((t : ℂ) / w)‖ =
        ‖(-Complex.I / 2 : ℂ) *
          Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ := by
      simp [Complex.arctan, z]
    _ ≤ ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ := hmul
    _ ≤ L := hL t ht_tail

/-- Fixed-ray ratio bounds give a uniform bound for the principal arctangent
on the upper split interval. -/
theorem Complex.arctan_fixed_tail_bounded
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ B : ℝ,
      0 ≤ B ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          ‖Complex.arctan ((t : ℂ) / w)‖ ≤ B := by
  exact
    Complex.arctan_fixed_tail_bounded_of_log_ratio_bound
      hw_re_pos
      (Complex.arctan_fixed_tail_log_ratio_bounded hw_re_pos)

/-- A uniform arctangent bound on the upper split interval becomes a linear
bound because the split cutoff is strictly positive in the open right
half-plane. -/
theorem Complex.arctan_fixed_openRightHalfPlane_ray_tail_linear_bound_of_bounded
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hbounded :
      ∃ B : ℝ,
        0 ≤ B ∧
        ∀ t : ℝ,
          t ∈ Set.Ioi (‖w‖ / 2) →
            ‖Complex.arctan ((t : ℂ) / w)‖ ≤ B) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          ‖Complex.arctan ((t : ℂ) / w)‖ ≤ C * t := by
  rcases hbounded with ⟨B, hB_nonneg, hB⟩
  have hw_ne_zero : w ≠ 0 := by
    intro hw_zero
    rw [hw_zero] at hw_re_pos
    exact (lt_irrefl (0 : ℝ)) hw_re_pos
  have hw_norm_pos : 0 < ‖w‖ :=
    norm_pos_iff.mpr hw_ne_zero
  let C : ℝ := 2 * B / ‖w‖
  have hC_nonneg : 0 ≤ C :=
    div_nonneg (mul_nonneg zero_le_two hB_nonneg)
      (le_of_lt hw_norm_pos)
  refine ⟨C, hC_nonneg, ?_⟩
  intro t ht_tail
  have ht_lower : ‖w‖ / 2 ≤ t :=
    le_of_lt ht_tail
  have hC_mul_lower : B ≤ C * t := by
    have hmul :
        B ≤ C * (‖w‖ / 2) := by
      calc
        B = (2 * B / ‖w‖) * (‖w‖ / 2) :=
          (Real.arctan_fixed_tail_two_mul_div_mul_half_eq
            (B := B) (r := ‖w‖) hw_norm_pos.ne').symm
        _ = C * (‖w‖ / 2) := rfl
    have hC_mul_mono :
        C * (‖w‖ / 2) ≤ C * t :=
      mul_le_mul_of_nonneg_left ht_lower hC_nonneg
    exact le_trans hmul hC_mul_mono
  exact le_trans (hB t ht_tail) hC_mul_lower

/-- Along a fixed ray in the open right half-plane, the principal arctangent
is linearly bounded on every tail.

This is the exact fixed-ray arctangent owner estimate needed to prove
integrability of the Binet kernel before the downstream sectorial split file is
available. -/
theorem Complex.arctan_fixed_openRightHalfPlane_ray_tail_linear_bound
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          ‖Complex.arctan ((t : ℂ) / w)‖ ≤ C * t := by
  exact
    Complex.arctan_fixed_openRightHalfPlane_ray_tail_linear_bound_of_bounded
      hw_re_pos
      (Complex.arctan_fixed_tail_bounded hw_re_pos)

end

end LFunctions
end Boundary
