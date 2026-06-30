import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetMovingLogFarUpperArithmetic

/-!
# Far upper-center moving logarithmic spike estimates

This file owns the far upper-center branch of the denominator-side moving
logarithmic spike.  In this branch the moving singularity is located high
inside the bounded Binet window, so the exponential weight at the spike carries
an additional fixed exponential factor.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open Filter
open MeasureTheory

/-- In the far upper-center branch, the branch wall is located above
`3‖w‖/4`. -/
theorem Complex.binetSecondFormula_farUpperCenter_im_lower
    {w : ℂ}
    (hfar : (3 * ‖w‖) / 4 ≤ w.im) :
    (3 * ‖w‖) / 4 ≤ w.im :=
  hfar

/-- Points to the right of the moving center are at least `3‖w‖/4` in the
bounded tail variable. -/
theorem Complex.binetSecondFormula_farUpperCenter_rightSide_t_lower
    {w : ℂ}
    {t : ℝ}
    (hfar : (3 * ‖w‖) / 4 ≤ w.im)
    (hcenter_le : w.im ≤ t) :
    (3 * ‖w‖) / 4 ≤ t :=
  le_trans hfar hcenter_le

/-- Points just left of the far upper moving center remain above the
`5‖w‖/8` height line when the deleted collar has radius `‖w‖/8`. -/
theorem Complex.binetSecondFormula_farUpperCenter_nearLeft_t_lower
    {w : ℂ}
    {t : ℝ}
    (hfar : (3 * ‖w‖) / 4 ≤ w.im)
    (hnear_left : w.im - ‖w‖ / 8 ≤ t) :
    (5 * ‖w‖) / 8 ≤ t := by
  have hsub_lower :
      (3 * ‖w‖) / 4 - ‖w‖ / 8 ≤ w.im - ‖w‖ / 8 :=
    sub_le_sub_right hfar (‖w‖ / 8)
  have hcoeff :
      (3 * ‖w‖) / 4 - ‖w‖ / 8 = (5 * ‖w‖) / 8 := by
    have height_ne : (8 : ℝ) ≠ 0 :=
      ne_of_gt Real.zero_lt_eight
    calc
      (3 * ‖w‖) / 4 - ‖w‖ / 8 =
          (2 * (3 * ‖w‖)) / 8 - ‖w‖ / 8 := by
        have hleft :
            (2 * (3 * ‖w‖)) / 8 = (3 * ‖w‖) / 4 := by
          calc
            (2 * (3 * ‖w‖)) / 8 =
                (2 * (3 * ‖w‖)) / (2 * 4) := by
              exact congrArg (fun x : ℝ => (2 * (3 * ‖w‖)) / x)
                Real.eight_eq_two_mul_four
            _ = (3 * ‖w‖) / 4 := by
              exact mul_div_mul_left (3 * ‖w‖) 4 (ne_of_gt zero_lt_two)
        exact congrArg (fun x : ℝ => x - ‖w‖ / 8) hleft.symm
      _ = ((2 * (3 * ‖w‖)) - ‖w‖) / 8 := by
        exact (sub_div (2 * (3 * ‖w‖)) ‖w‖ 8).symm
      _ = ((6 * ‖w‖) - ‖w‖) / 8 := by
        exact congrArg (fun x : ℝ => (x - ‖w‖) / 8)
          (calc
            2 * (3 * ‖w‖) = (2 * 3) * ‖w‖ := by
              exact (mul_assoc (2 : ℝ) 3 ‖w‖).symm
            _ = 6 * ‖w‖ := by
              exact congrArg (fun x : ℝ => x * ‖w‖)
                Real.two_mul_three_eq_six)
      _ = (5 * ‖w‖) / 8 := by
        exact congrArg (fun x : ℝ => x / 8)
          (calc
            6 * ‖w‖ - ‖w‖ = 6 * ‖w‖ - 1 * ‖w‖ := by
              exact congrArg (fun x : ℝ => 6 * ‖w‖ - x) (one_mul ‖w‖).symm
            _ = (6 - 1) * ‖w‖ := by
              exact (sub_mul (6 : ℝ) 1 ‖w‖).symm
            _ = 5 * ‖w‖ := by
              exact congrArg (fun x : ℝ => x * ‖w‖)
                Real.six_sub_one_eq_five)
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ t)
      hcoeff
      (le_trans hsub_lower hnear_left)

/-- In the far upper-center branch, a point in the `‖w‖/8` collar around the
moving center lies above `5‖w‖/8`. -/
theorem Complex.binetSecondFormula_farUpperCenter_near_t_lower
    {w : ℂ}
    {t : ℝ}
    (hfar : (3 * ‖w‖) / 4 ≤ w.im)
    (hnear : |w.im - t| ≤ ‖w‖ / 8) :
    (5 * ‖w‖) / 8 ≤ t := by
  have hsub_le :
      w.im - ‖w‖ / 8 ≤ t := by
    have hmove :
        w.im - ‖w‖ / 8 ≤ w.im - |w.im - t| := by
      exact sub_le_sub_left hnear w.im
    have htarget :
        w.im - |w.im - t| ≤ t := by
      have habs_ge :
          w.im - t ≤ |w.im - t| :=
        le_abs_self (w.im - t)
      have hsub_nonpos :
          w.im - t - |w.im - t| ≤ 0 :=
        sub_nonpos.mpr habs_ge
      have hcalc :
          w.im - |w.im - t| - t = w.im - t - |w.im - t| := by
        calc
          w.im - |w.im - t| - t =
              w.im + -|w.im - t| + -t := by
            exact sub_eq_add_neg (w.im - |w.im - t|) t
          _ = w.im + -t + -|w.im - t| := by
            exact add_right_comm w.im (-|w.im - t|) (-t)
          _ = w.im - t - |w.im - t| := by
            exact congrArg (fun x : ℝ => x + -|w.im - t|)
              (sub_eq_add_neg w.im t).symm
      exact
        sub_nonpos.mp
          (Eq.subst
            (motive := fun x : ℝ => x ≤ 0)
            hcalc.symm
            hsub_nonpos)
    exact le_trans hmove htarget
  exact
    Complex.binetSecondFormula_farUpperCenter_nearLeft_t_lower
      hfar hsub_le

/-- On the far upper-center collar, the pure exponential weight has the
`5‖w‖/4` scale coming from `t ≥ 5‖w‖/8`. -/
theorem Complex.binetSecondFormula_farUpperCenter_near_exp_weight_le
    {w : ℂ}
    {t : ℝ}
    (hfar : (3 * ‖w‖) / 4 ≤ w.im)
    (hnear : |w.im - t| ≤ ‖w‖ / 8) :
    (Real.exp ((2 : ℝ) * Real.pi * t))⁻¹ ≤
      Real.exp (-((5 * Real.pi) / 4) * ‖w‖) := by
  have ht_lower :
      (5 * ‖w‖) / 8 ≤ t :=
    Complex.binetSecondFormula_farUpperCenter_near_t_lower hfar hnear
  exact Real.exp_two_pi_inv_le_five_pi_div_four_of_ge ht_lower

/-- Outside the `‖w‖/8` moving collar, the denominator-side moving distance is
at least `‖w‖/8`. -/
theorem Complex.binetSecondFormula_farUpperCenter_outer_distance_lower
    {w : ℂ}
    {t : ℝ}
    (houter : ‖w‖ / 8 ≤ |w.im - t|) :
    ‖w‖ / 8 ≤ max w.re |w.im - t| :=
  le_trans houter (le_max_right w.re |w.im - t|)

/-- On the outer part of the far upper-center branch, the denominator-side
moving logarithm is bounded by the fixed logarithm `log 24`. -/
theorem Complex.binetSecondFormula_farUpperCenter_outer_log_le_log_twentyfour
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    {t : ℝ}
    (houter : ‖w‖ / 8 ≤ |w.im - t|) :
    Real.log ((3 * ‖w‖) / max w.re |w.im - t|) ≤
      Real.log 24 := by
  have hN_pos : 0 < ‖w‖ :=
    Complex.norm_pos_of_re_pos hw_re_pos
  have hmax_pos : 0 < max w.re |w.im - t| :=
    Complex.binetSecondFormula_branchWall_distance_pos hw_re_pos t
  have hdist_lower :
      ‖w‖ / 8 ≤ max w.re |w.im - t| :=
    Complex.binetSecondFormula_farUpperCenter_outer_distance_lower houter
  have hN_le_eight_dist :
      ‖w‖ ≤ 8 * max w.re |w.im - t| := by
    have height_mul :
        8 * (‖w‖ / 8) ≤
          8 * max w.re |w.im - t| :=
      mul_le_mul_of_nonneg_left hdist_lower Real.zero_le_eight
    have hcancel :
        8 * (‖w‖ / 8) = ‖w‖ := by
      have height_ne : (8 : ℝ) ≠ 0 :=
        ne_of_gt Real.zero_lt_eight
      calc
        8 * (‖w‖ / 8) = (8 * ‖w‖) / 8 := by
          exact mul_div_assoc' 8 ‖w‖ 8
        _ = ‖w‖ := by
          exact mul_div_cancel_left₀ ‖w‖ height_ne
    exact
      Eq.subst
        (motive := fun x : ℝ => x ≤ 8 * max w.re |w.im - t|)
        hcancel
        height_mul
  have hthreeN_le :
      3 * ‖w‖ ≤ 24 * max w.re |w.im - t| := by
    have hmul :
        3 * ‖w‖ ≤
          3 * (8 * max w.re |w.im - t|) :=
      mul_le_mul_of_nonneg_left hN_le_eight_dist
        (le_of_lt Real.zero_lt_three)
    have hcoeff :
        3 * (8 * max w.re |w.im - t|) =
          24 * max w.re |w.im - t| := by
      calc
        3 * (8 * max w.re |w.im - t|) =
            (3 * 8) * max w.re |w.im - t| := by
          exact (mul_assoc (3 : ℝ) 8 (max w.re |w.im - t|)).symm
        _ = 24 * max w.re |w.im - t| := by
          exact congrArg (fun x : ℝ => x * max w.re |w.im - t|)
            Real.three_mul_eight_eq_twenty_four
    exact le_trans hmul (le_of_eq hcoeff)
  have harg_le :
      (3 * ‖w‖) / max w.re |w.im - t| ≤ 24 := by
    exact
      (div_le_iff₀ hmax_pos).mpr
        hthreeN_le
  have harg_pos :
      0 < (3 * ‖w‖) / max w.re |w.im - t| :=
    div_pos (mul_pos Real.zero_lt_three hN_pos) hmax_pos
  exact Real.log_le_log harg_pos harg_le

/-- Weighted outer-collar constant-log comparison in the far upper-center
branch. -/
theorem Complex.binetSecondFormula_farUpperCenter_outer_weighted_le_log_twentyfour
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    {t : ℝ}
    (houter : ‖w‖ / 8 ≤ |w.im - t|) :
    (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
        Real.exp ((2 : ℝ) * Real.pi * t) ≤
      (2 * Real.log 24) /
        Real.exp ((2 : ℝ) * Real.pi * t) := by
  have hlog_le :
      Real.log ((3 * ‖w‖) / max w.re |w.im - t|) ≤
        Real.log 24 :=
    Complex.binetSecondFormula_farUpperCenter_outer_log_le_log_twentyfour
      hw_re_pos houter
  have hnum_le :
      2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|) ≤
        2 * Real.log 24 :=
    mul_le_mul_of_nonneg_left hlog_le zero_le_two
  have hden_nonneg :
      0 ≤ Real.exp ((2 : ℝ) * Real.pi * t) :=
    le_of_lt (Real.exp_pos ((2 : ℝ) * Real.pi * t))
  exact div_le_div_of_nonneg_right hnum_le hden_nonneg

/-- The denominator-side moving logarithm is bounded by a square-root spike.
This is the pointwise replacement for exact logarithmic integration in the far
upper-center branch. -/
theorem Complex.binetSecondFormula_minusMovingLog_le_rpow_half_distance
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (t : ℝ) :
    Real.log ((3 * ‖w‖) / max w.re |w.im - t|) ≤
      ((3 * ‖w‖) / max w.re |w.im - t|) ^ ((1 : ℝ) / 2) /
        ((1 : ℝ) / 2) := by
  have hN_pos : 0 < ‖w‖ :=
    Complex.norm_pos_of_re_pos hw_re_pos
  have hdist_pos :
      0 < max w.re |w.im - t| :=
    Complex.binetSecondFormula_branchWall_distance_pos hw_re_pos t
  have harg_nonneg :
      0 ≤ (3 * ‖w‖) / max w.re |w.im - t| :=
    le_of_lt (div_pos (mul_pos Real.zero_lt_three hN_pos) hdist_pos)
  exact Real.log_le_rpow_div harg_nonneg one_half_pos

/-- Weighted pointwise domination of the denominator-side moving logarithm by
the square-root moving spike. -/
theorem Complex.binetSecondFormula_minusMovingLog_weighted_le_rpow_half_distance
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (t : ℝ) :
    (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
        Real.exp ((2 : ℝ) * Real.pi * t) ≤
      (2 *
          (((3 * ‖w‖) / max w.re |w.im - t|) ^ ((1 : ℝ) / 2) /
            ((1 : ℝ) / 2))) /
        Real.exp ((2 : ℝ) * Real.pi * t) := by
  have hlog_le :
      Real.log ((3 * ‖w‖) / max w.re |w.im - t|) ≤
        ((3 * ‖w‖) / max w.re |w.im - t|) ^ ((1 : ℝ) / 2) /
          ((1 : ℝ) / 2) :=
    Complex.binetSecondFormula_minusMovingLog_le_rpow_half_distance
      hw_re_pos t
  have hnum_le :
      2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|) ≤
        2 *
          (((3 * ‖w‖) / max w.re |w.im - t|) ^ ((1 : ℝ) / 2) /
            ((1 : ℝ) / 2)) :=
    mul_le_mul_of_nonneg_left hlog_le zero_le_two
  have hden_nonneg :
      0 ≤ Real.exp ((2 : ℝ) * Real.pi * t) :=
    le_of_lt (Real.exp_pos ((2 : ℝ) * Real.pi * t))
  exact div_le_div_of_nonneg_right hnum_le hden_nonneg

/-- On the far upper-center collar, the weighted moving logarithm is bounded
by the square-root moving spike times the far-upper exponential scale. -/
theorem Complex.binetSecondFormula_farUpperCenter_near_weighted_le_rpow_expScale
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hfar : (3 * ‖w‖) / 4 ≤ w.im)
    {t : ℝ}
    (hnear : |w.im - t| ≤ ‖w‖ / 8) :
    (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
        Real.exp ((2 : ℝ) * Real.pi * t) ≤
      (2 *
          (((3 * ‖w‖) / max w.re |w.im - t|) ^ ((1 : ℝ) / 2) /
            ((1 : ℝ) / 2))) *
        Real.exp (-((5 * Real.pi) / 4) * ‖w‖) := by
  let A : ℝ :=
    2 *
      (((3 * ‖w‖) / max w.re |w.im - t|) ^ ((1 : ℝ) / 2) /
        ((1 : ℝ) / 2))
  let E : ℝ := Real.exp ((2 : ℝ) * Real.pi * t)
  let Q : ℝ := Real.exp (-((5 * Real.pi) / 4) * ‖w‖)
  have hweighted :
      (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) / E ≤
        A / E :=
    Complex.binetSecondFormula_minusMovingLog_weighted_le_rpow_half_distance
      hw_re_pos t
  have hE_inv_le_Q :
      E⁻¹ ≤ Q :=
    Complex.binetSecondFormula_farUpperCenter_near_exp_weight_le
      hfar hnear
  have hA_nonneg : 0 ≤ A := by
    have hN_pos : 0 < ‖w‖ :=
      Complex.norm_pos_of_re_pos hw_re_pos
    have hdist_pos :
        0 < max w.re |w.im - t| :=
      Complex.binetSecondFormula_branchWall_distance_pos hw_re_pos t
    have hratio_nonneg :
        0 ≤ (3 * ‖w‖) / max w.re |w.im - t| :=
      le_of_lt (div_pos (mul_pos Real.zero_lt_three hN_pos) hdist_pos)
    have hrpow_nonneg :
        0 ≤ ((3 * ‖w‖) / max w.re |w.im - t|) ^ ((1 : ℝ) / 2) :=
      Real.rpow_nonneg hratio_nonneg ((1 : ℝ) / 2)
    have hdiv_nonneg :
        0 ≤
          ((3 * ‖w‖) / max w.re |w.im - t|) ^ ((1 : ℝ) / 2) /
            ((1 : ℝ) / 2) :=
      div_nonneg hrpow_nonneg (le_of_lt Real.zero_lt_one_half)
    exact mul_nonneg zero_le_two hdiv_nonneg
  have hA_scaled :
      A / E ≤ A * Q := by
    have hdiv_eq : A / E = A * E⁻¹ :=
      div_eq_mul_inv A E
    have hmul :
        A * E⁻¹ ≤ A * Q :=
      mul_le_mul_of_nonneg_left hE_inv_le_Q hA_nonneg
    exact
      Eq.subst
        (motive := fun x : ℝ => x ≤ A * Q)
        hdiv_eq.symm
        hmul
  exact le_trans hweighted hA_scaled

/-- In the far upper-center branch, the imaginary part is below the norm. -/
theorem Complex.binetSecondFormula_farUpperCenter_im_le_norm
    (w : ℂ) :
    w.im ≤ ‖w‖ := by
  have him_abs_le : |w.im| ≤ ‖w‖ :=
    Complex.abs_im_le_norm_owner w
  exact le_trans (le_abs_self w.im) him_abs_le

/-- The bounded Binet tail window lies inside the centered interval of radius
`2‖w‖` around the far upper moving center. -/
theorem Complex.binetSecondFormula_boundedTailWindow_subset_centered_twoNorm
    {w : ℂ}
    (hfar : (3 * ‖w‖) / 4 ≤ w.im) :
    Set.Ioc (‖w‖ / 2) (2 * ‖w‖) ⊆
      Set.Ioc (w.im - 2 * ‖w‖) (w.im + 2 * ‖w‖) := by
  intro t ht
  have hN_nonneg : 0 ≤ ‖w‖ :=
    norm_nonneg w
  have him_nonneg : 0 ≤ w.im := by
    have hthree_quarters_nonneg : 0 ≤ (3 * ‖w‖) / 4 :=
      div_nonneg
        (mul_nonneg (le_of_lt Real.zero_lt_three) hN_nonneg)
        zero_le_four
    exact le_trans hthree_quarters_nonneg hfar
  have him_le_norm :
      w.im ≤ ‖w‖ :=
    Complex.binetSecondFormula_farUpperCenter_im_le_norm w
  have hleft_target :
      w.im - 2 * ‖w‖ < t := by
    have hleft_le_half :
        w.im - 2 * ‖w‖ ≤ ‖w‖ / 2 := by
      have him_sub_le :
          w.im - 2 * ‖w‖ ≤ ‖w‖ - 2 * ‖w‖ :=
        sub_le_sub_right him_le_norm (2 * ‖w‖)
      have hcoeff :
          ‖w‖ - 2 * ‖w‖ ≤ ‖w‖ / 2 := by
        have hneg_le_half :
            -‖w‖ ≤ ‖w‖ / 2 := by
          have hzero_le_three_half :
              0 ≤ ‖w‖ + ‖w‖ / 2 := by
            exact add_nonneg hN_nonneg
              (div_nonneg hN_nonneg zero_le_two)
          have hmove :
              -‖w‖ ≤ ‖w‖ / 2 :=
            neg_le_iff_add_nonneg.mpr
              (Eq.subst
                (motive := fun x : ℝ => 0 ≤ x)
                (add_comm ‖w‖ (‖w‖ / 2))
                hzero_le_three_half)
          exact hmove
        have hsub_eq_neg :
            ‖w‖ - 2 * ‖w‖ = -‖w‖ := by
          calc
            ‖w‖ - 2 * ‖w‖ = 1 * ‖w‖ - 2 * ‖w‖ := by
              exact congrArg (fun x : ℝ => x - 2 * ‖w‖)
                (one_mul ‖w‖).symm
            _ = (1 - 2) * ‖w‖ := by
              exact (sub_mul (1 : ℝ) 2 ‖w‖).symm
            _ = -1 * ‖w‖ := by
              exact congrArg (fun x : ℝ => x * ‖w‖)
                Real.one_sub_two_eq_neg_one
            _ = -‖w‖ := by
              exact neg_one_mul ‖w‖
        exact
          Eq.subst
            (motive := fun x : ℝ => x ≤ ‖w‖ / 2)
            hsub_eq_neg.symm
            hneg_le_half
      exact le_trans him_sub_le hcoeff
    exact lt_of_le_of_lt hleft_le_half ht.1
  have hright_target :
      t ≤ w.im + 2 * ‖w‖ := by
    have htwoN_le_right :
        2 * ‖w‖ ≤ w.im + 2 * ‖w‖ := by
      have him_nonneg_enough :
          0 + 2 * ‖w‖ ≤ w.im + 2 * ‖w‖ :=
        add_le_add_right him_nonneg (2 * ‖w‖)
      exact
        Eq.subst
          (motive := fun x : ℝ => x ≤ w.im + 2 * ‖w‖)
          (zero_add (2 * ‖w‖))
          him_nonneg_enough
    exact le_trans ht.2 htwoN_le_right
  exact ⟨hleft_target, hright_target⟩

/-- The moving square-root denominator spike is bounded by the translated
`|w.im - t|^(-1/2)` spike away from its center. -/
theorem Complex.binetSecondFormula_farUpperCenter_rpow_spike_le_centered_spike
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hw_norm_two : 2 ≤ ‖w‖)
    {t : ℝ}
    (ht_ne : t ≠ w.im) :
    2 *
        (((3 * ‖w‖) / max w.re |w.im - t|) ^ ((1 : ℝ) / 2) /
          ((1 : ℝ) / 2)) ≤
      12 * ‖w‖ * |w.im - t| ^ (-(1 / 2 : ℝ)) := by
  let N : ℝ := ‖w‖
  let D : ℝ := max w.re |w.im - t|
  let U : ℝ := |w.im - t|
  have hN_nonneg : 0 ≤ N :=
    norm_nonneg w
  have hN_two : 2 ≤ N :=
    hw_norm_two
  have hN_pos : 0 < N :=
    lt_of_lt_of_le zero_lt_two hN_two
  have hD_pos : 0 < D :=
    Complex.binetSecondFormula_branchWall_distance_pos hw_re_pos t
  have hU_pos : 0 < U := by
    have hdiff_ne : w.im - t ≠ 0 := by
      intro hzero
      have hwm_eq_t : w.im = t :=
        sub_eq_zero.mp hzero
      exact ht_ne hwm_eq_t.symm
    exact abs_pos.mpr hdiff_ne
  have hU_nonneg : 0 ≤ U :=
    le_of_lt hU_pos
  have hD_ge_U : U ≤ D :=
    le_max_right w.re |w.im - t|
  have hratio_le :
      (3 * N) / D ≤ (3 * N) / U := by
    have hnum_nonneg : 0 ≤ 3 * N :=
      mul_nonneg (le_of_lt Real.zero_lt_three) hN_nonneg
    exact div_le_div_of_nonneg_left hnum_nonneg hU_pos hD_ge_U
  have hratio_nonneg :
      0 ≤ (3 * N) / D :=
    le_of_lt (div_pos (mul_pos Real.zero_lt_three hN_pos) hD_pos)
  have hratioU_nonneg :
      0 ≤ (3 * N) / U :=
    le_of_lt (div_pos (mul_pos Real.zero_lt_three hN_pos) hU_pos)
  have hrpow_le :
      ((3 * N) / D) ^ ((1 : ℝ) / 2) ≤
        ((3 * N) / U) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow hratio_nonneg hratio_le
      (le_of_lt Real.zero_lt_one_half)
  have hsplit :
      ((3 * N) / U) ^ ((1 : ℝ) / 2) =
        (3 * N) ^ ((1 : ℝ) / 2) / U ^ ((1 : ℝ) / 2) :=
    Real.div_rpow
      (mul_nonneg (le_of_lt Real.zero_lt_three) hN_nonneg)
      hU_nonneg
      ((1 : ℝ) / 2)
  have hthreeN_one :
      1 ≤ 3 * N := by
    have hN_one : 1 ≤ N :=
      le_trans one_le_two hN_two
    have htwo_le_threeN :
        2 ≤ 3 * N := by
      have htwo_mul :
          2 ≤ 2 * N :=
        Eq.subst
          (motive := fun x : ℝ => x ≤ 2 * N)
          (mul_one (2 : ℝ))
          (mul_le_mul_of_nonneg_left hN_one zero_le_two)
      have htwoN_le_threeN :
          2 * N ≤ 3 * N :=
        mul_le_mul_of_nonneg_right
          (show (2 : ℝ) ≤ 3 by
            have htwo_le_two_add_one : (2 : ℝ) ≤ 2 + 1 :=
              le_add_of_nonneg_right zero_le_one
            exact
              Eq.subst
                (motive := fun x : ℝ => (2 : ℝ) ≤ x)
                Real.two_add_one_eq_three
                htwo_le_two_add_one)
          hN_nonneg
      exact le_trans htwo_mul htwoN_le_threeN
    exact le_trans one_le_two htwo_le_threeN
  have hsqrt_threeN_le :
      (3 * N) ^ ((1 : ℝ) / 2) ≤ 3 * N :=
    Real.rpow_half_le_self_of_one_le hthreeN_one
  have hU_half_pos :
      0 < U ^ ((1 : ℝ) / 2) :=
    Real.rpow_pos_of_pos hU_pos ((1 : ℝ) / 2)
  have hdiv_le :
      (3 * N) ^ ((1 : ℝ) / 2) / U ^ ((1 : ℝ) / 2) ≤
        (3 * N) / U ^ ((1 : ℝ) / 2) :=
    div_le_div_of_nonneg_right hsqrt_threeN_le (le_of_lt hU_half_pos)
  have hneg_exp :
      -(1 / 2 : ℝ) = -((1 : ℝ) / 2) := by
    rfl
  have hU_neg :
      U ^ (-(1 / 2 : ℝ)) = (U ^ ((1 : ℝ) / 2))⁻¹ := by
    exact
      Eq.trans
        (congrArg (fun x : ℝ => U ^ x) hneg_exp)
        (Real.rpow_neg hU_nonneg ((1 : ℝ) / 2))
  have hthree_over :
      (3 * N) / U ^ ((1 : ℝ) / 2) =
        3 * N * U ^ (-(1 / 2 : ℝ)) := by
    calc
      (3 * N) / U ^ ((1 : ℝ) / 2) =
          (3 * N) * (U ^ ((1 : ℝ) / 2))⁻¹ := by
        exact div_eq_mul_inv (3 * N) (U ^ ((1 : ℝ) / 2))
      _ = 3 * N * U ^ (-(1 / 2 : ℝ)) := by
        exact congrArg (fun x : ℝ => 3 * N * x) hU_neg.symm
  have hbase :
      ((3 * N) / D) ^ ((1 : ℝ) / 2) ≤
        3 * N * U ^ (-(1 / 2 : ℝ)) :=
    le_trans hrpow_le
      (le_trans
        (Eq.subst
          (motive := fun x : ℝ =>
            x ≤ (3 * N) / U ^ ((1 : ℝ) / 2))
          hsplit.symm
          hdiv_le)
        (le_of_eq hthree_over))
  have hleft_scale :
      2 *
          (((3 * N) / D) ^ ((1 : ℝ) / 2) /
            ((1 : ℝ) / 2)) =
        4 * ((3 * N) / D) ^ ((1 : ℝ) / 2) := by
    calc
      2 *
          (((3 * N) / D) ^ ((1 : ℝ) / 2) /
            ((1 : ℝ) / 2)) =
        2 * (((3 * N) / D) ^ ((1 : ℝ) / 2) * (((1 : ℝ) / 2)⁻¹)) := by
        exact congrArg (fun x : ℝ => 2 * x)
          (div_eq_mul_inv (((3 * N) / D) ^ ((1 : ℝ) / 2)) ((1 : ℝ) / 2))
      _ = 2 * (((3 * N) / D) ^ ((1 : ℝ) / 2) * 2) := by
        exact congrArg
          (fun x : ℝ => 2 * (((3 * N) / D) ^ ((1 : ℝ) / 2) * x))
          Real.inv_one_half_eq_two
      _ = (2 * 2) * ((3 * N) / D) ^ ((1 : ℝ) / 2) := by
        calc
          2 * (((3 * N) / D) ^ ((1 : ℝ) / 2) * 2) =
              2 * (2 * ((3 * N) / D) ^ ((1 : ℝ) / 2)) := by
            exact congrArg (fun x : ℝ => 2 * x)
              (mul_comm (((3 * N) / D) ^ ((1 : ℝ) / 2)) 2)
          _ = (2 * 2) * ((3 * N) / D) ^ ((1 : ℝ) / 2) := by
            exact (mul_assoc (2 : ℝ) 2 (((3 * N) / D) ^ ((1 : ℝ) / 2))).symm
      _ = 4 * ((3 * N) / D) ^ ((1 : ℝ) / 2) := by
        exact congrArg (fun x : ℝ => x * ((3 * N) / D) ^ ((1 : ℝ) / 2))
          Real.two_mul_two_eq_four
  have hscaled :
      4 * ((3 * N) / D) ^ ((1 : ℝ) / 2) ≤
        4 * (3 * N * U ^ (-(1 / 2 : ℝ))) :=
    mul_le_mul_of_nonneg_left hbase zero_le_four
  have hright_scale :
      4 * (3 * N * U ^ (-(1 / 2 : ℝ))) =
        12 * N * U ^ (-(1 / 2 : ℝ)) := by
    calc
      4 * (3 * N * U ^ (-(1 / 2 : ℝ))) =
          (4 * 3) * N * U ^ (-(1 / 2 : ℝ)) := by
        exact
          Eq.trans
            (mul_assoc (4 : ℝ) (3 * N) (U ^ (-(1 / 2 : ℝ)))).symm
            (congrArg (fun x : ℝ => x * U ^ (-(1 / 2 : ℝ)))
              (mul_assoc (4 : ℝ) 3 N).symm)
      _ = 12 * N * U ^ (-(1 / 2 : ℝ)) := by
        exact congrArg (fun x : ℝ => x * N * U ^ (-(1 / 2 : ℝ)))
          Real.four_mul_three_eq_twelve
  exact
    Eq.subst
      (motive := fun x : ℝ =>
        x ≤ 12 * N * U ^ (-(1 / 2 : ℝ)))
      hleft_scale.symm
      (le_trans hscaled (le_of_eq hright_scale))

/-- The centered square-root spike over the bounded Binet window is controlled
by the symmetric centered interval of radius `2‖w‖`. -/
theorem Complex.binetSecondFormula_centered_spike_integral_boundedTailWindow_le
    {w : ℂ}
    (hfar : (3 * ‖w‖) / 4 ≤ w.im) :
    ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        |w.im - t| ^ (-(1 / 2 : ℝ)) ≤
      4 * (2 * ‖w‖) ^ ((1 : ℝ) / 2) := by
  let R : ℝ := 2 * ‖w‖
  let H : ℝ → ℝ := fun t : ℝ => |w.im - t| ^ (-(1 / 2 : ℝ))
  have hN_nonneg : 0 ≤ ‖w‖ :=
    norm_nonneg w
  have hR_nonneg : 0 ≤ R :=
    mul_nonneg zero_le_two hN_nonneg
  have hcenter_le :
      w.im - R ≤ w.im + R := by
    have hneg_le_pos : -R ≤ R :=
      neg_le_self hR_nonneg
    have hadd :
        w.im + -R ≤ w.im + R :=
      add_le_add_left hneg_le_pos w.im
    exact
      Eq.subst
        (motive := fun x : ℝ => x ≤ w.im + R)
        (sub_eq_add_neg w.im R).symm
        hadd
  have hH_interval :
      IntervalIntegrable H volume (w.im - R) (w.im + R) :=
    Real.intervalIntegrable_centered_abs_sub_rpow_neg_half hR_nonneg
  have hH_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioc (w.im - R) (w.im + R))] H :=
    Eventually.of_forall
      (fun t =>
        Real.rpow_nonneg (abs_nonneg (w.im - t)) (-(1 / 2 : ℝ)))
  have hsubset :
      Set.Ioc (‖w‖ / 2) (2 * ‖w‖) ≤ᵐ[volume]
        Set.Ioc (w.im - R) (w.im + R) :=
    Eventually.of_forall
      (fun t ht =>
        Complex.binetSecondFormula_boundedTailWindow_subset_centered_twoNorm
          hfar ht)
  have hmono :
      ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖), H t ≤
        ∫ t : ℝ in Set.Ioc (w.im - R) (w.im + R), H t :=
    setIntegral_mono_set hH_interval.1 hH_nonneg hsubset
  have hcenter_set_eq :
      ∫ t : ℝ in Set.Ioc (w.im - R) (w.im + R), H t =
        ∫ t in (w.im - R)..(w.im + R), H t := by
    exact (intervalIntegral.integral_of_le hcenter_le).symm
  have hcenter_value :
      (∫ t in (w.im - R)..(w.im + R), H t : ℝ) =
        4 * R ^ ((1 : ℝ) / 2) :=
    Real.integral_centered_abs_sub_rpow_neg_half_eq_four_mul hR_nonneg
  have htarget :
      ∫ t : ℝ in Set.Ioc (w.im - R) (w.im + R), H t =
        4 * (2 * ‖w‖) ^ ((1 : ℝ) / 2) := by
    exact Eq.trans hcenter_set_eq
      (Eq.trans hcenter_value
        (congrArg (fun x : ℝ => 4 * x)
          (congrArg (fun x : ℝ => x ^ ((1 : ℝ) / 2)) rfl)))
  exact le_trans hmono (le_of_eq htarget)

/-- The centered spike integral over the bounded Binet window has quadratic
height after multiplying by the moving-spike prefactor. -/
theorem Complex.binetSecondFormula_centered_spike_prefactor_integral_le_quadratic
    {w : ℂ}
    (hw_norm_two : 2 ≤ ‖w‖)
    (hfar : (3 * ‖w‖) / 4 ≤ w.im) :
    ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        12 * ‖w‖ * |w.im - t| ^ (-(1 / 2 : ℝ)) ≤
      96 * ‖w‖ ^ 2 := by
  let N : ℝ := ‖w‖
  let H : ℝ → ℝ := fun t : ℝ => |w.im - t| ^ (-(1 / 2 : ℝ))
  have hN_nonneg : 0 ≤ N :=
    norm_nonneg w
  have htwoN_two : 2 ≤ 2 * N := by
    have htwo_mul :
        2 * 1 ≤ 2 * N :=
      mul_le_mul_of_nonneg_left
        (le_trans one_le_two hw_norm_two)
        zero_le_two
    exact
      Eq.subst
        (motive := fun x : ℝ => x ≤ 2 * N)
        (mul_one (2 : ℝ))
        htwo_mul
  have hsqrt_le :
      (2 * N) ^ ((1 : ℝ) / 2) ≤ 2 * N :=
    Real.rpow_half_le_self_of_two_le htwoN_two
  have hspike :
      ∫ t : ℝ in Set.Ioc (N / 2) (2 * N), H t ≤
        4 * (2 * N) ^ ((1 : ℝ) / 2) :=
    Complex.binetSecondFormula_centered_spike_integral_boundedTailWindow_le
      hfar
  have hcoeff_nonneg : 0 ≤ 12 * N :=
    mul_nonneg
      (Eq.subst
        (motive := fun x : ℝ => 0 ≤ x)
        Real.three_mul_four_eq_twelve
        (mul_nonneg (le_of_lt Real.zero_lt_three) zero_le_four))
      hN_nonneg
  have hscaled :
      (12 * N) * ∫ t : ℝ in Set.Ioc (N / 2) (2 * N), H t ≤
        (12 * N) * (4 * (2 * N) ^ ((1 : ℝ) / 2)) :=
    mul_le_mul_of_nonneg_left hspike hcoeff_nonneg
  have htarget_scale :
      (12 * N) * (4 * (2 * N) ^ ((1 : ℝ) / 2)) ≤
        96 * N ^ 2 := by
    have hmul_sqrt :
        (12 * N) * (4 * (2 * N) ^ ((1 : ℝ) / 2)) ≤
          (12 * N) * (4 * (2 * N)) := by
      have hfour :
          4 * (2 * N) ^ ((1 : ℝ) / 2) ≤ 4 * (2 * N) :=
        mul_le_mul_of_nonneg_left hsqrt_le zero_le_four
      exact mul_le_mul_of_nonneg_left hfour hcoeff_nonneg
    have hright_eq :
        (12 * N) * (4 * (2 * N)) = 96 * N ^ 2 := by
      calc
        (12 * N) * (4 * (2 * N)) =
            (12 * 4 * 2) * (N * N) := by
          calc
            (12 * N) * (4 * (2 * N)) =
                12 * (N * (4 * (2 * N))) := by
              exact mul_assoc (12 : ℝ) N (4 * (2 * N))
            _ = 12 * ((4 * (2 * N)) * N) := by
              exact congrArg (fun x : ℝ => 12 * x)
                (mul_comm N (4 * (2 * N)))
            _ = 12 * (((4 * 2) * N) * N) := by
              exact congrArg (fun x : ℝ => 12 * (x * N))
                (mul_assoc (4 : ℝ) 2 N).symm
            _ = 12 * ((4 * 2) * (N * N)) := by
              exact congrArg (fun x : ℝ => 12 * x)
                (mul_assoc (4 * 2 : ℝ) N N)
            _ = (12 * (4 * 2)) * (N * N) := by
              exact (mul_assoc (12 : ℝ) (4 * 2) (N * N)).symm
            _ = (12 * 4 * 2) * (N * N) := by
              exact congrArg (fun x : ℝ => x * (N * N))
                (mul_assoc (12 : ℝ) 4 2).symm
        _ = 96 * (N * N) := by
          exact congrArg (fun x : ℝ => x * (N * N))
            Real.twelve_mul_four_mul_two_eq_ninety_six
        _ = 96 * N ^ 2 := by
          exact congrArg (fun x : ℝ => 96 * x) (pow_two N).symm
    exact le_trans hmul_sqrt (le_of_eq hright_eq)
  have hintegral_eq :
      ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
          12 * ‖w‖ * |w.im - t| ^ (-(1 / 2 : ℝ)) =
        (12 * N) * ∫ t : ℝ in Set.Ioc (N / 2) (2 * N), H t := by
    exact integral_mul_left (12 * N) H
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ 96 * ‖w‖ ^ 2)
      hintegral_eq.symm
      (le_trans hscaled htarget_scale)

/-- Far upper-center pointwise envelope: the moving logarithmic spike is
bounded by a harmless outer constant plus the centered square-root spike. -/
theorem Complex.binetSecondFormula_farUpperCenter_pointwise_le_const_plus_spike
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hw_norm_two : 2 ≤ ‖w‖)
    (hfar : (3 * ‖w‖) / 4 ≤ w.im)
    {t : ℝ}
    (ht_ne : t ≠ w.im) :
    (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
        Real.exp ((2 : ℝ) * Real.pi * t) ≤
      (2 * Real.log 24) / Real.exp ((2 : ℝ) * Real.pi * t) +
        (12 * ‖w‖ * |w.im - t| ^ (-(1 / 2 : ℝ))) *
          Real.exp (-((5 * Real.pi) / 4) * ‖w‖) := by
  let F : ℝ :=
    (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
      Real.exp ((2 : ℝ) * Real.pi * t)
  let G : ℝ :=
    (2 * Real.log 24) / Real.exp ((2 : ℝ) * Real.pi * t)
  let H : ℝ :=
    12 * ‖w‖ * |w.im - t| ^ (-(1 / 2 : ℝ))
  let Q : ℝ := Real.exp (-((5 * Real.pi) / 4) * ‖w‖)
  have hG_nonneg : 0 ≤ G := by
    have hlog_nonneg : 0 ≤ Real.log 24 :=
      Real.log_nonneg Real.one_le_twenty_four
    have hnum_nonneg : 0 ≤ 2 * Real.log 24 :=
      mul_nonneg zero_le_two hlog_nonneg
    have hden_nonneg :
        0 ≤ Real.exp ((2 : ℝ) * Real.pi * t) :=
      le_of_lt (Real.exp_pos ((2 : ℝ) * Real.pi * t))
    exact div_nonneg hnum_nonneg hden_nonneg
  have hH_nonneg : 0 ≤ H := by
    have hcoeff_nonneg : 0 ≤ 12 * ‖w‖ :=
      mul_nonneg
        (Eq.subst
          (motive := fun x : ℝ => 0 ≤ x)
          Real.three_mul_four_eq_twelve
          (mul_nonneg (le_of_lt Real.zero_lt_three) zero_le_four))
        (norm_nonneg w)
    have hspike_nonneg :
        0 ≤ |w.im - t| ^ (-(1 / 2 : ℝ)) :=
      Real.rpow_nonneg (abs_nonneg (w.im - t)) (-(1 / 2 : ℝ))
    exact mul_nonneg hcoeff_nonneg hspike_nonneg
  have hQ_nonneg : 0 ≤ Q :=
    le_of_lt (Real.exp_pos (-((5 * Real.pi) / 4) * ‖w‖))
  have hHQ_nonneg : 0 ≤ H * Q :=
    mul_nonneg hH_nonneg hQ_nonneg
  match le_total |w.im - t| (‖w‖ / 8) with
  | Or.inl hnear =>
      have hnear_bound :
          F ≤
            (2 *
                (((3 * ‖w‖) / max w.re |w.im - t|) ^ ((1 : ℝ) / 2) /
                  ((1 : ℝ) / 2))) * Q :=
        Complex.binetSecondFormula_farUpperCenter_near_weighted_le_rpow_expScale
          hw_re_pos hfar hnear
      have hrpow_bound :
          2 *
              (((3 * ‖w‖) / max w.re |w.im - t|) ^ ((1 : ℝ) / 2) /
                ((1 : ℝ) / 2)) ≤
            H :=
        Complex.binetSecondFormula_farUpperCenter_rpow_spike_le_centered_spike
          hw_re_pos hw_norm_two ht_ne
      have hnear_to_H :
          (2 *
              (((3 * ‖w‖) / max w.re |w.im - t|) ^ ((1 : ℝ) / 2) /
                ((1 : ℝ) / 2))) * Q ≤
            H * Q :=
        mul_le_mul_of_nonneg_right hrpow_bound hQ_nonneg
      have hH_le_sum :
          H * Q ≤ G + H * Q :=
        le_add_of_nonneg_left hG_nonneg
      exact le_trans hnear_bound (le_trans hnear_to_H hH_le_sum)
  | Or.inr houter =>
      have houter_bound :
          F ≤ G :=
        Complex.binetSecondFormula_farUpperCenter_outer_weighted_le_log_twentyfour
          hw_re_pos houter
      have hG_le_sum :
          G ≤ G + H * Q :=
        le_add_of_nonneg_right hHQ_nonneg
      exact le_trans houter_bound hG_le_sum

/-- Integrated far upper-center envelope: constant exponential tail plus the
integrated centered spike at the `5π/4` scale. -/
theorem Complex.binetSecondFormula_farUpperCenter_integral_le_expScale_plus_spike
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hw_norm_two : 2 ≤ ‖w‖)
    (hfar : (3 * ‖w‖) / 4 ≤ w.im) :
    ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
          Real.exp ((2 : ℝ) * Real.pi * t) ≤
      (2 * Real.log 24) * Real.exp (-Real.pi * ‖w‖) +
        96 * ‖w‖ ^ 2 *
          Real.exp (-((5 * Real.pi) / 4) * ‖w‖) := by
  let S : Set ℝ := Set.Ioc (‖w‖ / 2) (2 * ‖w‖)
  let F : ℝ → ℝ := fun t : ℝ =>
    (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
      Real.exp ((2 : ℝ) * Real.pi * t)
  let G : ℝ → ℝ := fun t : ℝ =>
    (2 * Real.log 24) / Real.exp ((2 : ℝ) * Real.pi * t)
  let H : ℝ → ℝ := fun t : ℝ =>
    12 * ‖w‖ * |w.im - t| ^ (-(1 / 2 : ℝ))
  let Q : ℝ := Real.exp (-((5 * Real.pi) / 4) * ‖w‖)
  let M : ℝ → ℝ := fun t : ℝ => G t + H t * Q
  have hF_integrable : IntegrableOn F S := by
    let Scc : Set ℝ := Set.Icc (‖w‖ / 2) (2 * ‖w‖)
    let B : ℝ → ℝ := fun t : ℝ => max w.re |w.im - t|
    let A : ℝ → ℝ := fun t : ℝ => (3 * ‖w‖) / B t
    let Fcc : ℝ → ℝ := fun t : ℝ =>
      (2 * Real.log (A t)) / Real.exp ((2 : ℝ) * Real.pi * t)
    have hw_norm_pos : 0 < ‖w‖ :=
      Complex.norm_pos_of_re_pos hw_re_pos
    have hB_pos : ∀ t : ℝ, 0 < B t := by
      intro t
      exact lt_of_lt_of_le hw_re_pos (le_max_left w.re |w.im - t|)
    have hA_pos : ∀ t : ℝ, 0 < A t := by
      intro t
      exact div_pos (mul_pos Real.zero_lt_three hw_norm_pos) (hB_pos t)
    have hdist_cont : Continuous fun t : ℝ => |w.im - t| :=
      (continuous_const.sub continuous_id).abs
    have hB_cont : Continuous B :=
      continuous_const.sup hdist_cont
    have hA_cont : Continuous A :=
      continuous_const.div hB_cont (fun t => (hB_pos t).ne')
    have hlog_contOn :
        ContinuousOn (fun t : ℝ => Real.log (A t)) Scc :=
      (hA_cont.continuousOn).log (fun t _ht => (hA_pos t).ne')
    have hnum_contOn :
        ContinuousOn (fun t : ℝ => 2 * Real.log (A t)) Scc :=
      continuousOn_const.mul hlog_contOn
    have hlinear_cont : Continuous fun t : ℝ => (2 : ℝ) * Real.pi * t :=
      (continuous_const.mul continuous_const).mul continuous_id
    have hden_cont : Continuous fun t : ℝ =>
        Real.exp ((2 : ℝ) * Real.pi * t) :=
      Real.continuous_exp.comp hlinear_cont
    have hden_ne :
        ∀ t : ℝ, t ∈ Scc →
          Real.exp ((2 : ℝ) * Real.pi * t) ≠ 0 := by
      intro t _ht
      exact (Real.exp_pos ((2 : ℝ) * Real.pi * t)).ne'
    have hFcc_contOn : ContinuousOn Fcc Scc :=
      hnum_contOn.div hden_cont.continuousOn hden_ne
    have hFcc_integrable : IntegrableOn Fcc Scc :=
      hFcc_contOn.integrableOn_Icc
    exact hFcc_integrable.mono_set Set.Ioc_subset_Icc_same
  have hG_integrable : IntegrableOn G S := by
    let Scc : Set ℝ := Set.Icc (‖w‖ / 2) (2 * ‖w‖)
    let Gcc : ℝ → ℝ := fun t : ℝ =>
      (2 * Real.log 24) / Real.exp ((2 : ℝ) * Real.pi * t)
    have hlinear_cont : Continuous fun t : ℝ => (2 : ℝ) * Real.pi * t :=
      (continuous_const.mul continuous_const).mul continuous_id
    have hden_cont : Continuous fun t : ℝ =>
        Real.exp ((2 : ℝ) * Real.pi * t) :=
      Real.continuous_exp.comp hlinear_cont
    have hden_ne :
        ∀ t : ℝ, t ∈ Scc →
          Real.exp ((2 : ℝ) * Real.pi * t) ≠ 0 := by
      intro t _ht
      exact (Real.exp_pos ((2 : ℝ) * Real.pi * t)).ne'
    have hGcc_contOn : ContinuousOn Gcc Scc :=
      continuousOn_const.div hden_cont.continuousOn hden_ne
    have hGcc_integrable : IntegrableOn Gcc Scc :=
      hGcc_contOn.integrableOn_Icc
    exact hGcc_integrable.mono_set Set.Ioc_subset_Icc_same
  have hH_integrable : IntegrableOn H S := by
    let R : ℝ := 2 * ‖w‖
    let H0 : ℝ → ℝ := fun t : ℝ => |w.im - t| ^ (-(1 / 2 : ℝ))
    have hR_nonneg : 0 ≤ R :=
      mul_nonneg zero_le_two (norm_nonneg w)
    have hH0_interval :
        IntervalIntegrable H0 volume (w.im - R) (w.im + R) :=
      Real.intervalIntegrable_centered_abs_sub_rpow_neg_half hR_nonneg
    have hsubset :
        S ⊆ Set.Ioc (w.im - R) (w.im + R) :=
      Complex.binetSecondFormula_boundedTailWindow_subset_centered_twoNorm hfar
    have hH0_integrable : IntegrableOn H0 S :=
      hH0_interval.1.mono_set hsubset
    exact hH0_integrable.const_mul (12 * ‖w‖)
  have hHQ_integrable : IntegrableOn (fun t : ℝ => H t * Q) S :=
    (hH_integrable.const_mul Q).congr
      ((ae_restrict_iff' measurableSet_Ioc).mpr
        (Eventually.of_forall
          (fun t _ht => (mul_comm Q (H t)))))
  have hM_integrable : IntegrableOn M S :=
    hG_integrable.add hHQ_integrable
  have hpoint :
      ∀ᵐ t ∂volume.restrict S, F t ≤ M t :=
    (ae_restrict_of_ae (Real.ae_ne_singleton w.im)).mono
      (fun t ht_ne =>
        Complex.binetSecondFormula_farUpperCenter_pointwise_le_const_plus_spike
          hw_re_pos hw_norm_two hfar ht_ne)
  have hmono :
      ∫ t : ℝ in S, F t ≤ ∫ t : ℝ in S, M t :=
    setIntegral_mono_ae_restrict hF_integrable hM_integrable hpoint
  have hsum_eq :
      ∫ t : ℝ in S, M t =
        (∫ t : ℝ in S, G t) + (∫ t : ℝ in S, H t * Q) := by
    exact
      show
        ∫ t : ℝ in S, G t + H t * Q =
          (∫ t : ℝ in S, G t) + (∫ t : ℝ in S, H t * Q) from
        integral_add hG_integrable hHQ_integrable
  have hconstant_nonneg : 0 ≤ 2 * Real.log 24 := by
    have hlog_nonneg : 0 ≤ Real.log 24 :=
      Real.log_nonneg Real.one_le_twenty_four
    exact mul_nonneg zero_le_two hlog_nonneg
  have hG_bound :
      ∫ t : ℝ in S, G t ≤
        (2 * Real.log 24) * Real.exp (-Real.pi * ‖w‖) :=
    Complex.binetSecondFormula_constant_expWeighted_integral_le_expScale
      (2 * Real.log 24) hconstant_nonneg w
  have hH_bound :
      ∫ t : ℝ in S, H t * Q ≤
        96 * ‖w‖ ^ 2 * Q := by
    have hH_integral :
        ∫ t : ℝ in S, H t ≤
          96 * ‖w‖ ^ 2 :=
      Complex.binetSecondFormula_centered_spike_prefactor_integral_le_quadratic
        hw_norm_two hfar
    have hQ_nonneg : 0 ≤ Q :=
      le_of_lt (Real.exp_pos (-((5 * Real.pi) / 4) * ‖w‖))
    have hmul :
        (∫ t : ℝ in S, H t) * Q ≤
          (96 * ‖w‖ ^ 2) * Q :=
      mul_le_mul_of_nonneg_right hH_integral hQ_nonneg
    have hintegral_eq :
        ∫ t : ℝ in S, H t * Q =
          (∫ t : ℝ in S, H t) * Q :=
      integral_mul_right Q H
    exact
      Eq.subst
        (motive := fun x : ℝ => x ≤ 96 * ‖w‖ ^ 2 * Q)
        hintegral_eq.symm
        hmul
  have hsum_bound :
      (∫ t : ℝ in S, G t) + (∫ t : ℝ in S, H t * Q) ≤
        (2 * Real.log 24) * Real.exp (-Real.pi * ‖w‖) +
          96 * ‖w‖ ^ 2 * Q :=
    add_le_add hG_bound hH_bound
  exact
    le_trans hmono
      (le_trans (le_of_eq hsum_eq) hsum_bound)

/-- A nonnegative height is bounded by its exponential. -/
theorem Real.self_le_exp_of_nonneg
    {N : ℝ}
    (hN_nonneg : 0 ≤ N) :
    N ≤ Real.exp N := by
  have hN_le_N_add_one : N ≤ N + 1 :=
    le_add_of_nonneg_right zero_le_one
  have hN_add_one_le_exp : N + 1 ≤ Real.exp N :=
    Real.add_one_le_exp N
  exact le_trans hN_le_N_add_one hN_add_one_le_exp

/-- A nonnegative height is bounded by four times a quarter-scale
exponential. -/
theorem Real.self_le_four_mul_exp_quarter_of_nonneg
    {N : ℝ}
    (hN_nonneg : 0 ≤ N) :
    N ≤ 4 * Real.exp (N / 4) := by
  have hquarter_nonneg : 0 ≤ N / 4 :=
    div_nonneg hN_nonneg zero_le_four
  have hquarter_le_exp :
      N / 4 ≤ Real.exp (N / 4) :=
    Real.self_le_exp_of_nonneg hquarter_nonneg
  have hmul :
      4 * (N / 4) ≤ 4 * Real.exp (N / 4) :=
    mul_le_mul_of_nonneg_left hquarter_le_exp zero_le_four
  have hcancel :
      4 * (N / 4) = N := by
    have hfour_ne : (4 : ℝ) ≠ 0 :=
      ne_of_gt zero_lt_four
    calc
      4 * (N / 4) = (4 * N) / 4 := by
        exact mul_div_assoc' 4 N 4
      _ = N := by
        exact mul_div_cancel_left₀ N hfour_ne
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ 4 * Real.exp (N / 4))
      hcancel
      hmul

/-- Two powers of a nonnegative height are absorbed by a half-π exponential,
up to an explicit constant. -/
theorem Real.sq_le_sixteen_mul_exp_half_pi_of_nonneg
    {N : ℝ}
    (hN_nonneg : 0 ≤ N) :
    N ^ 2 ≤ 16 * Real.exp ((Real.pi / 2) * N) := by
  have hN_le :
      N ≤ 4 * Real.exp (N / 4) :=
    Real.self_le_four_mul_exp_quarter_of_nonneg hN_nonneg
  have hsq_le :
      N ^ 2 ≤
        (4 * Real.exp (N / 4)) *
          (4 * Real.exp (N / 4)) := by
    have hN_nonneg' : 0 ≤ N :=
      hN_nonneg
    exact
      Eq.subst
        (motive := fun x : ℝ =>
          x ≤ (4 * Real.exp (N / 4)) *
            (4 * Real.exp (N / 4)))
        (pow_two N).symm
        (mul_le_mul hN_le hN_le hN_nonneg'
          (mul_nonneg zero_le_four (le_of_lt (Real.exp_pos (N / 4)))))
  have hexp_mul :
      (4 * Real.exp (N / 4)) *
          (4 * Real.exp (N / 4)) =
        16 * Real.exp (N / 2) := by
    calc
      (4 * Real.exp (N / 4)) *
          (4 * Real.exp (N / 4)) =
        (4 * 4) * (Real.exp (N / 4) * Real.exp (N / 4)) := by
        calc
          (4 * Real.exp (N / 4)) *
          (4 * Real.exp (N / 4)) =
            ((4 * Real.exp (N / 4)) * 4) * Real.exp (N / 4) := by
            exact (mul_assoc (4 * Real.exp (N / 4)) 4 (Real.exp (N / 4))).symm
          _ = ((4 * 4) * Real.exp (N / 4)) * Real.exp (N / 4) := by
            exact congrArg (fun x : ℝ => x * Real.exp (N / 4))
              (calc
                (4 * Real.exp (N / 4)) * 4 =
                    4 * (Real.exp (N / 4) * 4) := by
                  exact mul_assoc 4 (Real.exp (N / 4)) 4
                _ = 4 * (4 * Real.exp (N / 4)) := by
                  exact congrArg (fun x : ℝ => 4 * x)
                    (mul_comm (Real.exp (N / 4)) 4)
                _ = (4 * 4) * Real.exp (N / 4) := by
                  exact (mul_assoc (4 : ℝ) 4 (Real.exp (N / 4))).symm)
          _ = (4 * 4) *
              (Real.exp (N / 4) * Real.exp (N / 4)) := by
            exact mul_assoc (4 * 4) (Real.exp (N / 4)) (Real.exp (N / 4))
      _ = 16 * (Real.exp (N / 4) * Real.exp (N / 4)) := by
        exact congrArg (fun x : ℝ => x * (Real.exp (N / 4) * Real.exp (N / 4)))
          Real.four_mul_four_eq_sixteen
      _ = 16 * Real.exp ((N / 4) + (N / 4)) := by
        exact congrArg (fun x : ℝ => 16 * x)
          (Real.exp_add (N / 4) (N / 4)).symm
      _ = 16 * Real.exp (N / 2) := by
        have hhalf :
            N / 4 + N / 4 = N / 2 := by
          calc
            N / 4 + N / 4 = 2 * (N / 4) := by
              exact (two_mul (N / 4)).symm
            _ = (2 * N) / 4 := by
              exact mul_div_assoc' 2 N 4
            _ = N / 2 := by
              have htwo_ne : (2 : ℝ) ≠ 0 :=
                ne_of_gt zero_lt_two
              calc
                (2 * N) / 4 = (2 * N) / (2 * 2) := by
                  exact congrArg (fun x : ℝ => (2 * N) / x)
                    (show (4 : ℝ) = 2 * 2 by
                      exact Real.two_mul_two_eq_four.symm)
                _ = N / 2 := by
                  exact mul_div_mul_left N 2 htwo_ne
        exact congrArg (fun x : ℝ => 16 * Real.exp x) hhalf
  have hexp_scale :
      16 * Real.exp (N / 2) ≤
        16 * Real.exp ((Real.pi / 2) * N) := by
    have hcoeff :
        N / 2 ≤ (Real.pi / 2) * N := by
      have hone_le_pi : (1 : ℝ) ≤ Real.pi :=
        one_le_two.trans Real.two_le_pi
      have hmul :
          1 * N ≤ Real.pi * N :=
        mul_le_mul_of_nonneg_right hone_le_pi hN_nonneg
      have hdiv :
          (1 * N) / 2 ≤ (Real.pi * N) / 2 :=
        div_le_div_of_nonneg_right hmul zero_le_two
      have hleft :
          (1 * N) / 2 = N / 2 :=
        congrArg (fun x : ℝ => x / 2) (one_mul N)
      have hright :
          (Real.pi * N) / 2 = (Real.pi / 2) * N :=
        (div_mul_eq_mul_div Real.pi 2 N).symm
      exact
        Eq.subst
          (motive := fun x : ℝ => x ≤ (Real.pi / 2) * N)
          hleft
          (Eq.subst
            (motive := fun x : ℝ => (1 * N) / 2 ≤ x)
            hright
            hdiv)
    exact
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr hcoeff)
        (Eq.subst
          (motive := fun x : ℝ => 0 ≤ x)
          Real.four_mul_four_eq_sixteen
          (mul_nonneg zero_le_four zero_le_four))
  have hsq_to_half :
      N ^ 2 ≤ 16 * Real.exp (N / 2) :=
    Eq.subst
      (motive := fun x : ℝ => N ^ 2 ≤ x)
      hexp_mul
      hsq_le
  exact le_trans hsq_to_half hexp_scale

/-- A quadratic prefactor at the far upper-center exponential height is
absorbed into the standard left-endpoint exponential scale. -/
theorem Real.sq_mul_exp_neg_three_halves_pi_le_exp_neg_pi_of_two_le
    {N : ℝ}
    (hN_two : 2 ≤ N) :
    N ^ 2 * Real.exp (-((3 * Real.pi) / 2) * N) ≤
      16 * Real.exp (-Real.pi * N) := by
  have hN_nonneg : 0 ≤ N :=
    le_trans zero_le_two hN_two
  have hsq_le :
      N ^ 2 ≤ 16 * Real.exp ((Real.pi / 2) * N) :=
    Real.sq_le_sixteen_mul_exp_half_pi_of_nonneg hN_nonneg
  have hfactor_nonneg :
      0 ≤ Real.exp (-((3 * Real.pi) / 2) * N) :=
    le_of_lt (Real.exp_pos (-((3 * Real.pi) / 2) * N))
  have hmul :
      N ^ 2 * Real.exp (-((3 * Real.pi) / 2) * N) ≤
        (16 * Real.exp ((Real.pi / 2) * N)) *
          Real.exp (-((3 * Real.pi) / 2) * N) :=
    mul_le_mul_of_nonneg_right hsq_le hfactor_nonneg
  have hexp :
      (16 * Real.exp ((Real.pi / 2) * N)) *
          Real.exp (-((3 * Real.pi) / 2) * N) =
        16 * Real.exp (-Real.pi * N) := by
    calc
      (16 * Real.exp ((Real.pi / 2) * N)) *
          Real.exp (-((3 * Real.pi) / 2) * N) =
        16 *
          (Real.exp ((Real.pi / 2) * N) *
            Real.exp (-((3 * Real.pi) / 2) * N)) := by
        exact mul_assoc 16 (Real.exp ((Real.pi / 2) * N))
          (Real.exp (-((3 * Real.pi) / 2) * N))
      _ = 16 *
          Real.exp (((Real.pi / 2) * N) + (-((3 * Real.pi) / 2) * N)) := by
        exact congrArg (fun x : ℝ => 16 * x)
          (Real.exp_add ((Real.pi / 2) * N)
            (-((3 * Real.pi) / 2) * N)).symm
      _ = 16 * Real.exp ((((Real.pi / 2) - ((3 * Real.pi) / 2)) * N)) := by
        exact congrArg (fun x : ℝ => 16 * Real.exp x)
          (Eq.trans
            (congrArg
              (fun x : ℝ => (Real.pi / 2) * N + x)
              (neg_mul ((3 * Real.pi) / 2) N))
            (Eq.trans
              (sub_eq_add_neg ((Real.pi / 2) * N)
                (((3 * Real.pi) / 2) * N)).symm
              (Eq.symm (sub_mul (Real.pi / 2) ((3 * Real.pi) / 2) N))))
      _ = 16 * Real.exp (-Real.pi * N) := by
        have hcoeff :
            Real.pi / 2 - (3 * Real.pi) / 2 = -Real.pi := by
          calc
            Real.pi / 2 - (3 * Real.pi) / 2 =
                (Real.pi - 3 * Real.pi) / 2 := by
              exact (sub_div Real.pi (3 * Real.pi) 2).symm
            _ = ((1 * Real.pi) - 3 * Real.pi) / 2 := by
              exact congrArg (fun x : ℝ => (x - 3 * Real.pi) / 2)
                (one_mul Real.pi).symm
            _ = ((1 - 3) * Real.pi) / 2 := by
              exact congrArg (fun x : ℝ => x / 2)
                (Eq.symm (sub_mul (1 : ℝ) 3 Real.pi))
            _ = ((-2) * Real.pi) / 2 := by
              exact congrArg (fun x : ℝ => (x * Real.pi) / 2)
                Real.one_sub_three_eq_neg_two
            _ = -Real.pi := by
              have htwo_ne : (2 : ℝ) ≠ 0 :=
                ne_of_gt zero_lt_two
              calc
                ((-2) * Real.pi) / 2 =
                    (-(2 * Real.pi)) / 2 := by
                  exact congrArg (fun x : ℝ => x / 2)
                    (neg_mul (2 : ℝ) Real.pi)
                _ = -(2 * Real.pi / 2) := by
                  exact neg_div 2 (2 * Real.pi)
                _ = -Real.pi := by
                  exact congrArg Neg.neg
                    (mul_div_cancel_left₀ Real.pi htwo_ne)
        exact congrArg (fun x : ℝ => 16 * Real.exp (x * N)) hcoeff
  exact
    le_trans hmul
      (le_of_eq hexp)

/-- A nonnegative height is bounded by eight times an eighth-scale
exponential. -/
theorem Real.self_le_eight_mul_exp_eighth_of_nonneg
    {N : ℝ}
    (hN_nonneg : 0 ≤ N) :
    N ≤ 8 * Real.exp (N / 8) := by
  have heighth_nonneg : 0 ≤ N / 8 :=
    div_nonneg hN_nonneg Real.zero_le_eight
  have heighth_le_exp :
      N / 8 ≤ Real.exp (N / 8) :=
    Real.self_le_exp_of_nonneg heighth_nonneg
  have hmul :
      8 * (N / 8) ≤ 8 * Real.exp (N / 8) :=
    mul_le_mul_of_nonneg_left heighth_le_exp Real.zero_le_eight
  have hcancel :
      8 * (N / 8) = N := by
    have height_ne : (8 : ℝ) ≠ 0 :=
      ne_of_gt Real.zero_lt_eight
    calc
      8 * (N / 8) = (8 * N) / 8 := by
        exact mul_div_assoc' 8 N 8
      _ = N := by
        exact mul_div_cancel_left₀ N height_ne
  exact
    Eq.subst
      (motive := fun x : ℝ => x ≤ 8 * Real.exp (N / 8))
      hcancel
      hmul

/-- Two powers of a nonnegative height are absorbed by a quarter-π
exponential, up to an explicit constant. -/
theorem Real.sq_le_sixtyfour_mul_exp_quarter_pi_of_nonneg
    {N : ℝ}
    (hN_nonneg : 0 ≤ N) :
    N ^ 2 ≤ 64 * Real.exp ((Real.pi / 4) * N) := by
  have hN_le :
      N ≤ 8 * Real.exp (N / 8) :=
    Real.self_le_eight_mul_exp_eighth_of_nonneg hN_nonneg
  have hsq_le :
      N ^ 2 ≤
        (8 * Real.exp (N / 8)) *
          (8 * Real.exp (N / 8)) := by
    exact
      Eq.subst
        (motive := fun x : ℝ =>
          x ≤ (8 * Real.exp (N / 8)) *
            (8 * Real.exp (N / 8)))
        (pow_two N).symm
        (mul_le_mul hN_le hN_le hN_nonneg
          (mul_nonneg Real.zero_le_eight (le_of_lt (Real.exp_pos (N / 8)))))
  have hexp_mul :
      (8 * Real.exp (N / 8)) *
          (8 * Real.exp (N / 8)) =
        64 * Real.exp (N / 4) := by
    calc
      (8 * Real.exp (N / 8)) *
          (8 * Real.exp (N / 8)) =
        (8 * 8) * (Real.exp (N / 8) * Real.exp (N / 8)) := by
        calc
          (8 * Real.exp (N / 8)) *
          (8 * Real.exp (N / 8)) =
            ((8 * Real.exp (N / 8)) * 8) * Real.exp (N / 8) := by
            exact (mul_assoc (8 * Real.exp (N / 8)) 8 (Real.exp (N / 8))).symm
          _ = ((8 * 8) * Real.exp (N / 8)) * Real.exp (N / 8) := by
            exact congrArg (fun x : ℝ => x * Real.exp (N / 8))
              (calc
                (8 * Real.exp (N / 8)) * 8 =
                    8 * (Real.exp (N / 8) * 8) := by
                  exact mul_assoc 8 (Real.exp (N / 8)) 8
                _ = 8 * (8 * Real.exp (N / 8)) := by
                  exact congrArg (fun x : ℝ => 8 * x)
                    (mul_comm (Real.exp (N / 8)) 8)
                _ = (8 * 8) * Real.exp (N / 8) := by
                  exact (mul_assoc (8 : ℝ) 8 (Real.exp (N / 8))).symm)
          _ = (8 * 8) *
              (Real.exp (N / 8) * Real.exp (N / 8)) := by
            exact mul_assoc (8 * 8) (Real.exp (N / 8)) (Real.exp (N / 8))
      _ = 64 * (Real.exp (N / 8) * Real.exp (N / 8)) := by
        exact congrArg (fun x : ℝ => x * (Real.exp (N / 8) * Real.exp (N / 8)))
          Real.eight_mul_eight_eq_sixty_four
      _ = 64 * Real.exp ((N / 8) + (N / 8)) := by
        exact congrArg (fun x : ℝ => 64 * x)
          (Real.exp_add (N / 8) (N / 8)).symm
      _ = 64 * Real.exp (N / 4) := by
        have hquarter :
            N / 8 + N / 8 = N / 4 := by
          calc
            N / 8 + N / 8 = 2 * (N / 8) := by
              exact (two_mul (N / 8)).symm
            _ = (2 * N) / 8 := by
              exact mul_div_assoc' 2 N 8
            _ = N / 4 := by
              have htwo_ne : (2 : ℝ) ≠ 0 :=
                ne_of_gt zero_lt_two
              calc
                (2 * N) / 8 = (2 * N) / (2 * 4) := by
                  exact congrArg (fun x : ℝ => (2 * N) / x)
                    Real.eight_eq_two_mul_four
                _ = N / 4 := by
                  exact mul_div_mul_left N 4 htwo_ne
        exact congrArg (fun x : ℝ => 64 * Real.exp x) hquarter
  have hexp_scale :
      64 * Real.exp (N / 4) ≤
        64 * Real.exp ((Real.pi / 4) * N) := by
    have hcoeff :
        N / 4 ≤ (Real.pi / 4) * N := by
      have hone_le_pi : (1 : ℝ) ≤ Real.pi :=
        one_le_two.trans Real.two_le_pi
      have hmul :
          1 * N ≤ Real.pi * N :=
        mul_le_mul_of_nonneg_right hone_le_pi hN_nonneg
      have hdiv :
          (1 * N) / 4 ≤ (Real.pi * N) / 4 :=
        div_le_div_of_nonneg_right hmul zero_le_four
      have hleft :
          (1 * N) / 4 = N / 4 :=
        congrArg (fun x : ℝ => x / 4) (one_mul N)
      have hright :
          (Real.pi * N) / 4 = (Real.pi / 4) * N :=
        (div_mul_eq_mul_div Real.pi 4 N).symm
      exact
        Eq.subst
          (motive := fun x : ℝ => x ≤ (Real.pi / 4) * N)
          hleft
          (Eq.subst
            (motive := fun x : ℝ => (1 * N) / 4 ≤ x)
            hright
            hdiv)
    exact
      mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr hcoeff)
        (Eq.subst
          (motive := fun x : ℝ => 0 ≤ x)
          Real.eight_mul_eight_eq_sixty_four
          (mul_nonneg Real.zero_le_eight Real.zero_le_eight))
  have hsq_to_quarter :
      N ^ 2 ≤ 64 * Real.exp (N / 4) :=
    Eq.subst
      (motive := fun x : ℝ => N ^ 2 ≤ x)
      hexp_mul
      hsq_le
  exact le_trans hsq_to_quarter hexp_scale

/-- A quadratic prefactor at the `5π/4` far upper-center collar height is
absorbed into the standard left-endpoint exponential scale. -/
theorem Real.sq_mul_exp_neg_five_quarters_pi_le_exp_neg_pi_of_two_le
    {N : ℝ}
    (hN_two : 2 ≤ N) :
    N ^ 2 * Real.exp (-((5 * Real.pi) / 4) * N) ≤
      64 * Real.exp (-Real.pi * N) := by
  have hN_nonneg : 0 ≤ N :=
    le_trans zero_le_two hN_two
  have hsq_le :
      N ^ 2 ≤ 64 * Real.exp ((Real.pi / 4) * N) :=
    Real.sq_le_sixtyfour_mul_exp_quarter_pi_of_nonneg hN_nonneg
  have hfactor_nonneg :
      0 ≤ Real.exp (-((5 * Real.pi) / 4) * N) :=
    le_of_lt (Real.exp_pos (-((5 * Real.pi) / 4) * N))
  have hmul :
      N ^ 2 * Real.exp (-((5 * Real.pi) / 4) * N) ≤
        (64 * Real.exp ((Real.pi / 4) * N)) *
          Real.exp (-((5 * Real.pi) / 4) * N) :=
    mul_le_mul_of_nonneg_right hsq_le hfactor_nonneg
  have hexp :
      (64 * Real.exp ((Real.pi / 4) * N)) *
          Real.exp (-((5 * Real.pi) / 4) * N) =
        64 * Real.exp (-Real.pi * N) := by
    calc
      (64 * Real.exp ((Real.pi / 4) * N)) *
          Real.exp (-((5 * Real.pi) / 4) * N) =
        64 *
          (Real.exp ((Real.pi / 4) * N) *
            Real.exp (-((5 * Real.pi) / 4) * N)) := by
        exact mul_assoc 64 (Real.exp ((Real.pi / 4) * N))
          (Real.exp (-((5 * Real.pi) / 4) * N))
      _ = 64 *
          Real.exp (((Real.pi / 4) * N) + (-((5 * Real.pi) / 4) * N)) := by
        exact congrArg (fun x : ℝ => 64 * x)
          (Real.exp_add ((Real.pi / 4) * N)
            (-((5 * Real.pi) / 4) * N)).symm
      _ = 64 *
          Real.exp ((((Real.pi / 4) - ((5 * Real.pi) / 4)) * N)) := by
        exact congrArg (fun x : ℝ => 64 * Real.exp x)
          (Eq.trans
            (congrArg
              (fun x : ℝ => (Real.pi / 4) * N + x)
              (neg_mul ((5 * Real.pi) / 4) N))
            (Eq.trans
              (sub_eq_add_neg ((Real.pi / 4) * N)
                (((5 * Real.pi) / 4) * N)).symm
              (Eq.symm (sub_mul (Real.pi / 4) ((5 * Real.pi) / 4) N))))
      _ = 64 * Real.exp (-Real.pi * N) := by
        have hcoeff :
            Real.pi / 4 - (5 * Real.pi) / 4 = -Real.pi := by
          calc
            Real.pi / 4 - (5 * Real.pi) / 4 =
                (Real.pi - 5 * Real.pi) / 4 := by
              exact (sub_div Real.pi (5 * Real.pi) 4).symm
            _ = ((1 * Real.pi) - 5 * Real.pi) / 4 := by
              exact congrArg (fun x : ℝ => (x - 5 * Real.pi) / 4)
                (one_mul Real.pi).symm
            _ = ((1 - 5) * Real.pi) / 4 := by
              exact congrArg (fun x : ℝ => x / 4)
                (Eq.symm (sub_mul (1 : ℝ) 5 Real.pi))
            _ = ((-4) * Real.pi) / 4 := by
              exact congrArg (fun x : ℝ => (x * Real.pi) / 4)
                Real.one_sub_five_eq_neg_four
            _ = -Real.pi := by
              have hfour_ne : (4 : ℝ) ≠ 0 :=
                ne_of_gt zero_lt_four
              calc
                ((-4) * Real.pi) / 4 =
                    (-(4 * Real.pi)) / 4 := by
                  exact congrArg (fun x : ℝ => x / 4)
                    (neg_mul (4 : ℝ) Real.pi)
                _ = -(4 * Real.pi / 4) := by
                  exact neg_div 4 (4 * Real.pi)
                _ = -Real.pi := by
                  exact congrArg Neg.neg
                    (mul_div_cancel_left₀ Real.pi hfour_ne)
        exact congrArg (fun x : ℝ => 64 * Real.exp (x * N)) hcoeff
  exact le_trans hmul (le_of_eq hexp)

end

end LFunctions
end Boundary
