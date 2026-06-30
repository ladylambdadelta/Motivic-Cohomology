import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.SectorialFromBinet

/-!
# Moving branch-wall spikes for the Binet tail

This file owns the symmetric moving-distance bookkeeping for the arctangent
ratio in Binet's second formula.  The downstream branch-wall estimate must use
moving distances for both numerator and denominator before taking norms.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open Filter
open MeasureTheory

/-- The imaginary part of `w + t⋅I` is the numerator-side moving wall
coordinate. -/
theorem Complex.add_im_im
    (w : ℂ)
    (t : ℝ) :
    (w + (t : ℂ) * Complex.I).im = w.im + t := by
  calc
    (w + (t : ℂ) * Complex.I).im =
        w.im + ((t : ℂ) * Complex.I).im := by
      exact Complex.add_im w ((t : ℂ) * Complex.I)
    _ = w.im + (t : ℂ).re := by
      exact congrArg (fun x : ℝ => w.im + x)
        (Complex.mul_I_im (t : ℂ))
    _ = w.im + t := by
      exact congrArg (fun x : ℝ => w.im + x)
        (Complex.ofReal_re t)

/-- The numerator distance in the Binet arctangent ratio controls the
numerator-side moving branch-wall distance. -/
theorem Complex.binetSecondFormula_arctan_tail_numerator_branchWall_distance_le
    (w : ℂ)
    (t : ℝ) :
    |w.im + t| ≤ ‖w + (t : ℂ) * Complex.I‖ := by
  have him :
      (w + (t : ℂ) * Complex.I).im = w.im + t :=
    Complex.add_im_im w t
  calc
    |w.im + t| = |(w + (t : ℂ) * Complex.I).im| := by
      exact congrArg abs him.symm
    _ ≤ ‖w + (t : ℂ) * Complex.I‖ := by
      exact Complex.abs_im_le_abs (w + (t : ℂ) * Complex.I)

/-- The numerator distance package is bounded below by the real part. -/
theorem Complex.binetSecondFormula_numerator_branchWall_distance_re_le
    (w : ℂ)
    (t : ℝ) :
    w.re ≤ max w.re |w.im + t| := by
  exact le_max_left w.re |w.im + t|

/-- The numerator distance package is positive in the open right half-plane. -/
theorem Complex.binetSecondFormula_numerator_branchWall_distance_pos
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (t : ℝ) :
    0 < max w.re |w.im + t| := by
  exact lt_of_lt_of_le hw_re_pos
    (Complex.binetSecondFormula_numerator_branchWall_distance_re_le w t)

/-- On the bounded Binet tail window, the numerator-side moving branch-wall
distance is at most `3‖w‖`. -/
theorem Complex.binetSecondFormula_numerator_branchWall_distance_le_three_norm
    {w : ℂ}
    {t : ℝ}
    (ht_mem : t ∈ Set.Icc (‖w‖ / 2) (2 * ‖w‖)) :
    max w.re |w.im + t| ≤ 3 * ‖w‖ := by
  have hN_nonneg : 0 ≤ ‖w‖ :=
    norm_nonneg w
  have ht_lower : ‖w‖ / 2 ≤ t :=
    ht_mem.1
  have ht_upper : t ≤ 2 * ‖w‖ :=
    ht_mem.2
  have ht_nonneg : 0 ≤ t :=
    le_trans (div_nonneg hN_nonneg zero_le_two) ht_lower
  have hre_le_norm : w.re ≤ ‖w‖ := by
    have hre_abs_le : |w.re| ≤ ‖w‖ :=
      Complex.abs_re_le_abs w
    exact le_trans (le_abs_self w.re) hre_abs_le
  have him_abs_le_norm : |w.im| ≤ ‖w‖ :=
    Complex.abs_im_le_abs w
  have hplus_abs_le :
      |w.im + t| ≤ ‖w‖ + t :=
    have ht_abs : |t| = t :=
      abs_of_nonneg ht_nonneg
    have hraw :
        |w.im| + |t| ≤ ‖w‖ + t :=
      add_le_add him_abs_le_norm (le_of_eq ht_abs)
    le_trans (abs_add w.im t) hraw
  have hplus_abs_le_three :
      |w.im + t| ≤ 3 * ‖w‖ := by
    calc
      |w.im + t| ≤ ‖w‖ + t :=
        hplus_abs_le
      _ ≤ ‖w‖ + 2 * ‖w‖ :=
        add_le_add_left ht_upper ‖w‖
      _ = 3 * ‖w‖ :=
        Real.add_two_mul_eq_three_mul ‖w‖
  exact max_le
    (le_trans hre_le_norm
      (by
        calc
          ‖w‖ ≤ ‖w‖ + 2 * ‖w‖ :=
            le_add_of_nonneg_right (mul_nonneg zero_le_two hN_nonneg)
          _ = 3 * ‖w‖ :=
            Real.add_two_mul_eq_three_mul ‖w‖))
    hplus_abs_le_three

/-- On the bounded Binet tail window, the denominator-side moving branch-wall
distance is at most `3‖w‖`. -/
theorem Complex.binetSecondFormula_denominator_branchWall_distance_le_three_norm
    {w : ℂ}
    {t : ℝ}
    (ht_mem : t ∈ Set.Icc (‖w‖ / 2) (2 * ‖w‖)) :
    max w.re |w.im - t| ≤ 3 * ‖w‖ := by
  have hN_nonneg : 0 ≤ ‖w‖ :=
    norm_nonneg w
  have ht_lower : ‖w‖ / 2 ≤ t :=
    ht_mem.1
  have ht_upper : t ≤ 2 * ‖w‖ :=
    ht_mem.2
  have ht_nonneg : 0 ≤ t :=
    le_trans (div_nonneg hN_nonneg zero_le_two) ht_lower
  have hre_le_norm : w.re ≤ ‖w‖ := by
    have hre_abs_le : |w.re| ≤ ‖w‖ :=
      Complex.abs_re_le_abs w
    exact le_trans (le_abs_self w.re) hre_abs_le
  have him_abs_le_norm : |w.im| ≤ ‖w‖ :=
    Complex.abs_im_le_abs w
  have hminus_abs_le :
      |w.im - t| ≤ ‖w‖ + t := by
    calc
      |w.im - t| ≤ |w.im| + |t| :=
        abs_sub w.im t
      _ = |w.im| + t := by
        exact congrArg (fun x : ℝ => |w.im| + x) (abs_of_nonneg ht_nonneg)
      _ ≤ ‖w‖ + t :=
        add_le_add_right him_abs_le_norm t
  have hminus_abs_le_three :
      |w.im - t| ≤ 3 * ‖w‖ := by
    calc
      |w.im - t| ≤ ‖w‖ + t :=
        hminus_abs_le
      _ ≤ ‖w‖ + 2 * ‖w‖ :=
        add_le_add_left ht_upper ‖w‖
      _ = 3 * ‖w‖ :=
        Real.add_two_mul_eq_three_mul ‖w‖
  exact max_le
    (le_trans hre_le_norm
      (by
        calc
          ‖w‖ ≤ ‖w‖ + 2 * ‖w‖ :=
            le_add_of_nonneg_right (mul_nonneg zero_le_two hN_nonneg)
          _ = 3 * ‖w‖ :=
            Real.add_two_mul_eq_three_mul ‖w‖))
    hminus_abs_le_three

/-- The plus moving-log argument lies in `(0,1]` on the bounded tail window. -/
theorem Complex.binetSecondFormula_plusMovingLog_argument_mem_Ioc
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    {t : ℝ}
    (ht_mem : t ∈ Set.Icc (‖w‖ / 2) (2 * ‖w‖)) :
    (max w.re |w.im + t|) / (3 * ‖w‖) ∈ Set.Ioc (0 : ℝ) 1 := by
  have hN_pos : 0 < ‖w‖ :=
    Complex.norm_pos_of_re_pos hw_re_pos
  have hden_pos : 0 < 3 * ‖w‖ :=
    mul_pos Real.zero_lt_three hN_pos
  have hnum_pos : 0 < max w.re |w.im + t| :=
    Complex.binetSecondFormula_numerator_branchWall_distance_pos
      hw_re_pos t
  have hnum_le : max w.re |w.im + t| ≤ 3 * ‖w‖ :=
    Complex.binetSecondFormula_numerator_branchWall_distance_le_three_norm
      ht_mem
  exact
    ⟨div_pos hnum_pos hden_pos,
      (div_le_one hden_pos).mpr hnum_le⟩

/-- The reciprocal minus moving-log argument is at least `1` on the bounded
tail window. -/
theorem Complex.binetSecondFormula_minusMovingLog_argument_one_le
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    {t : ℝ}
    (ht_mem : t ∈ Set.Icc (‖w‖ / 2) (2 * ‖w‖)) :
    1 ≤ (3 * ‖w‖) / max w.re |w.im - t| := by
  have hN_pos : 0 < ‖w‖ :=
    Complex.norm_pos_of_re_pos hw_re_pos
  have hnum_pos : 0 < 3 * ‖w‖ :=
    mul_pos Real.zero_lt_three hN_pos
  have hden_pos : 0 < max w.re |w.im - t| :=
    Complex.binetSecondFormula_branchWall_distance_pos hw_re_pos t
  have hden_le : max w.re |w.im - t| ≤ 3 * ‖w‖ :=
    Complex.binetSecondFormula_denominator_branchWall_distance_le_three_norm
      ht_mem
  exact
    (one_le_div hden_pos).mpr hden_le

/-- On the bounded tail window the plus moving logarithm is nonpositive, so
its absolute value is its negative. -/
theorem Complex.binetSecondFormula_plusMovingLog_abs_eq_neg
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    {t : ℝ}
    (ht_mem : t ∈ Set.Icc (‖w‖ / 2) (2 * ‖w‖)) :
    |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))| =
      -Real.log ((max w.re |w.im + t|) / (3 * ‖w‖)) := by
  have harg :
      (max w.re |w.im + t|) / (3 * ‖w‖) ∈ Set.Ioc (0 : ℝ) 1 :=
    Complex.binetSecondFormula_plusMovingLog_argument_mem_Ioc
      hw_re_pos ht_mem
  have hlog_nonpos :
      Real.log ((max w.re |w.im + t|) / (3 * ‖w‖)) ≤ 0 :=
    Real.log_nonpos harg.1.le harg.2
  exact abs_of_nonpos hlog_nonpos

/-- On the bounded tail window the minus moving logarithm is nonnegative, so
its absolute value is itself. -/
theorem Complex.binetSecondFormula_minusMovingLog_abs_eq_self
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    {t : ℝ}
    (ht_mem : t ∈ Set.Icc (‖w‖ / 2) (2 * ‖w‖)) :
    |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| =
      Real.log ((3 * ‖w‖) / max w.re |w.im - t|) := by
  have harg_one_le :
      1 ≤ (3 * ‖w‖) / max w.re |w.im - t| :=
    Complex.binetSecondFormula_minusMovingLog_argument_one_le
      hw_re_pos ht_mem
  have hlog_nonneg :
      0 ≤ Real.log ((3 * ‖w‖) / max w.re |w.im - t|) :=
    Real.log_nonneg harg_one_le
  exact abs_of_nonneg hlog_nonneg

/-- The oriented denominator-side moving logarithm is nonnegative on the
bounded Binet tail window. -/
theorem Complex.binetSecondFormula_minusMovingLog_nonneg
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    {t : ℝ}
    (ht_mem : t ∈ Set.Icc (‖w‖ / 2) (2 * ‖w‖)) :
    0 ≤ Real.log ((3 * ‖w‖) / max w.re |w.im - t|) := by
  have harg_one_le :
      1 ≤ (3 * ‖w‖) / max w.re |w.im - t| :=
    Complex.binetSecondFormula_minusMovingLog_argument_one_le
      hw_re_pos ht_mem
  exact Real.log_nonneg harg_one_le

/-- The oriented denominator-side weighted logarithmic integrand is
nonnegative on the bounded Binet tail window. -/
theorem Complex.binetSecondFormula_minusMovingLog_weighted_nonneg
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    {t : ℝ}
    (ht_mem : t ∈ Set.Icc (‖w‖ / 2) (2 * ‖w‖)) :
    0 ≤
      (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
        Real.exp ((2 : ℝ) * Real.pi * t) := by
  have hlog_nonneg :
      0 ≤ Real.log ((3 * ‖w‖) / max w.re |w.im - t|) :=
    Complex.binetSecondFormula_minusMovingLog_nonneg
      hw_re_pos ht_mem
  have hnum_nonneg :
      0 ≤ 2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|) :=
    mul_nonneg zero_le_two hlog_nonneg
  have hden_pos :
      0 < Real.exp ((2 : ℝ) * Real.pi * t) :=
    Real.exp_pos ((2 : ℝ) * Real.pi * t)
  exact div_nonneg hnum_nonneg (le_of_lt hden_pos)

/-- Membership in the half-open bounded tail window gives membership in the
closed bounded tail window used by pointwise logarithmic estimates. -/
theorem Complex.binetSecondFormula_boundedTailWindow_Ioc_subset_Icc
    {w : ℂ}
    {t : ℝ}
    (ht_mem : t ∈ Set.Ioc (‖w‖ / 2) (2 * ‖w‖)) :
    t ∈ Set.Icc (‖w‖ / 2) (2 * ‖w‖) :=
  ⟨le_of_lt ht_mem.1, ht_mem.2⟩

/-- The oriented denominator-side weighted logarithmic integrand is
nonnegative on the half-open bounded Binet tail window. -/
theorem Complex.binetSecondFormula_minusMovingLog_weighted_nonneg_Ioc
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    {t : ℝ}
    (ht_mem : t ∈ Set.Ioc (‖w‖ / 2) (2 * ‖w‖)) :
    0 ≤
      (2 * Real.log ((3 * ‖w‖) / max w.re |w.im - t|)) /
        Real.exp ((2 : ℝ) * Real.pi * t) := by
  exact
    Complex.binetSecondFormula_minusMovingLog_weighted_nonneg
      hw_re_pos
      (Complex.binetSecondFormula_boundedTailWindow_Ioc_subset_Icc
        ht_mem)

/-- If the denominator-side moving branch-wall center is at or below the
left endpoint of the bounded tail window, then the wall distance dominates
the distance from that endpoint. -/
theorem Complex.binetSecondFormula_denominator_branchWall_distance_ge_leftEndpointDistance
    {w : ℂ}
    (hw_im_le_left : w.im ≤ ‖w‖ / 2)
    {t : ℝ}
    (ht_left : ‖w‖ / 2 ≤ t) :
    t - ‖w‖ / 2 ≤ max w.re |w.im - t| := by
  have hcenter_le_t : w.im ≤ t :=
    le_trans hw_im_le_left ht_left
  have hdiff_nonpos : w.im - t ≤ 0 :=
    sub_nonpos.mpr hcenter_le_t
  have habs :
      |w.im - t| = t - w.im := by
    calc
      |w.im - t| = -(w.im - t) :=
        abs_of_nonpos hdiff_nonpos
      _ = t - w.im := by
        exact neg_sub w.im t
  have hleft_le_abs :
      t - ‖w‖ / 2 ≤ |w.im - t| := by
    calc
      t - ‖w‖ / 2 ≤ t - w.im :=
        sub_le_sub_left hw_im_le_left t
      _ = |w.im - t| :=
        habs.symm
  exact le_trans hleft_le_abs (le_max_right w.re |w.im - t|)

/-- On the lower-center side, the reciprocal minus moving-log argument is
bounded by the reciprocal of the left-endpoint distance. -/
theorem Complex.binetSecondFormula_minusMovingLog_argument_le_leftEndpointDistance
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hw_im_le_left : w.im ≤ ‖w‖ / 2)
    {t : ℝ}
    (ht_left_strict : ‖w‖ / 2 < t) :
    (3 * ‖w‖) / max w.re |w.im - t| ≤
      (3 * ‖w‖) / (t - ‖w‖ / 2) := by
  have hN_pos : 0 < ‖w‖ :=
    Complex.norm_pos_of_re_pos hw_re_pos
  have hnum_nonneg : 0 ≤ 3 * ‖w‖ :=
    le_of_lt (mul_pos Real.zero_lt_three hN_pos)
  have hcut_distance_pos : 0 < t - ‖w‖ / 2 :=
    sub_pos.mpr ht_left_strict
  have hden_pos : 0 < max w.re |w.im - t| :=
    Complex.binetSecondFormula_branchWall_distance_pos hw_re_pos t
  have hcut_le_den :
      t - ‖w‖ / 2 ≤ max w.re |w.im - t| :=
    Complex.binetSecondFormula_denominator_branchWall_distance_ge_leftEndpointDistance
      hw_im_le_left
      (le_of_lt ht_left_strict)
  exact
    div_le_div_of_nonneg_left
      hnum_nonneg
      hcut_distance_pos
      hcut_le_den

/-- On the lower-center side, the minus moving logarithm is bounded by the
endpoint-distance logarithm. -/
theorem Complex.binetSecondFormula_minusMovingLog_le_leftEndpointDistance_log
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hw_im_le_left : w.im ≤ ‖w‖ / 2)
    {t : ℝ}
    (ht_left_strict : ‖w‖ / 2 < t) :
    Real.log ((3 * ‖w‖) / max w.re |w.im - t|) ≤
      Real.log ((3 * ‖w‖) / (t - ‖w‖ / 2)) := by
  have hN_pos : 0 < ‖w‖ :=
    Complex.norm_pos_of_re_pos hw_re_pos
  have hnum_pos : 0 < 3 * ‖w‖ :=
    mul_pos Real.zero_lt_three hN_pos
  have hden_pos : 0 < max w.re |w.im - t| :=
    Complex.binetSecondFormula_branchWall_distance_pos hw_re_pos t
  have harg_pos :
      0 < (3 * ‖w‖) / max w.re |w.im - t| :=
    div_pos hnum_pos hden_pos
  have harg_le :
      (3 * ‖w‖) / max w.re |w.im - t| ≤
        (3 * ‖w‖) / (t - ‖w‖ / 2) :=
    Complex.binetSecondFormula_minusMovingLog_argument_le_leftEndpointDistance
      hw_re_pos
      hw_im_le_left
      ht_left_strict
  exact Real.log_le_log harg_pos harg_le

/-- The denominator-side moving branch-wall center is either below the left
cutoff or at/above it. -/
theorem Complex.binetSecondFormula_denominator_branchWall_center_split
    (w : ℂ) :
    w.im ≤ ‖w‖ / 2 ∨ ‖w‖ / 2 ≤ w.im := by
  exact le_total w.im (‖w‖ / 2)

/-- If the denominator-side moving branch-wall center is at/above the left
cutoff, then it lies before the natural norm endpoint. -/
theorem Complex.binetSecondFormula_denominator_branchWall_center_mem_normWindow
    {w : ℂ}
    (hleft : ‖w‖ / 2 ≤ w.im) :
    w.im ∈ Set.Icc (‖w‖ / 2) ‖w‖ := by
  have him_abs_le_norm : |w.im| ≤ ‖w‖ :=
    Complex.abs_im_le_abs w
  have him_nonneg : 0 ≤ w.im :=
    le_trans (div_nonneg (norm_nonneg w) zero_le_two) hleft
  have him_abs_eq : |w.im| = w.im :=
    abs_of_nonneg him_nonneg
  have him_le_norm : w.im ≤ ‖w‖ := by
    calc
      w.im = |w.im| :=
        him_abs_eq.symm
      _ ≤ ‖w‖ :=
        him_abs_le_norm
  exact ⟨hleft, him_le_norm⟩

/-- If the denominator-side moving branch-wall center is at/above the left
cutoff, then it lies inside the full bounded Binet tail window. -/
theorem Complex.binetSecondFormula_denominator_branchWall_center_mem_boundedTailWindow
    {w : ℂ}
    (hleft : ‖w‖ / 2 ≤ w.im) :
    w.im ∈ Set.Icc (‖w‖ / 2) (2 * ‖w‖) := by
  have hcenter_norm :
      w.im ∈ Set.Icc (‖w‖ / 2) ‖w‖ :=
    Complex.binetSecondFormula_denominator_branchWall_center_mem_normWindow
      hleft
  have hnorm_le_two_norm : ‖w‖ ≤ 2 * ‖w‖ :=
    le_mul_of_one_le_left (norm_nonneg w) one_le_two
  exact ⟨hcenter_norm.1, le_trans hcenter_norm.2 hnorm_le_two_norm⟩

/-- The numerator in the arctangent ratio controls both the right-half-plane
indentation radius and the numerator-side moving branch-wall distance. -/
theorem Complex.binetSecondFormula_arctan_tail_numerator_max_branchWall_distance_le
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (t : ℝ) :
    max w.re |w.im + t| ≤ ‖w + (t : ℂ) * Complex.I‖ := by
  have hre :
      w.re ≤ ‖w + (t : ℂ) * Complex.I‖ := by
    have hreal :
        (w + (t : ℂ) * Complex.I).re = w.re :=
      Complex.add_im_re w t
    have hre_abs_eq :
        |(w + (t : ℂ) * Complex.I).re| = w.re := by
      calc
        |(w + (t : ℂ) * Complex.I).re| = |w.re| := by
          exact congrArg abs hreal
        _ = w.re := by
          exact abs_of_nonneg (le_of_lt hw_re_pos)
    calc
      w.re = |(w + (t : ℂ) * Complex.I).re| := hre_abs_eq.symm
      _ ≤ ‖w + (t : ℂ) * Complex.I‖ := by
        exact Complex.abs_re_le_abs (w + (t : ℂ) * Complex.I)
  exact
    max_le hre
      (Complex.binetSecondFormula_arctan_tail_numerator_branchWall_distance_le
        w t)

/-- Pointwise two-moving-wall control of the principal Binet tail kernel on
the bounded branch-wall window.

Both possible arctangent branch singularities are kept as moving distances:
`|w.im + t|` for the numerator and `|w.im - t|` for the denominator.  This is
the pointwise estimate needed before the later real-variable integration step. -/
theorem Complex.binetSecondFormula_principalTailKernel_norm_le_twoMovingLogWindow_boundedTailWindow
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    {t : ℝ}
    (ht_mem : t ∈ Set.Icc (‖w‖ / 2) (2 * ‖w‖)) :
    ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
      (max
          |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|
          |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| +
        Real.pi) /
        (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  let z : ℂ := (t : ℂ) / w
  let R : ℂ :=
    (1 + z * Complex.I) / (1 - z * Complex.I)
  let D : ℝ := Real.exp ((2 : ℝ) * Real.pi * t) - 1
  let Aplus : ℝ := max w.re |w.im + t|
  let Aminus : ℝ := max w.re |w.im - t|
  let N : ℝ := ‖w‖
  let m : ℝ := Aplus / (3 * N)
  let M : ℝ := (3 * N) / Aminus
  have hw_norm_pos : 0 < N :=
    Complex.norm_pos_of_re_pos hw_re_pos
  have ht_lower : N / 2 ≤ t :=
    ht_mem.1
  have ht_upper : t ≤ 2 * N :=
    ht_mem.2
  have hhalf_pos : 0 < N / 2 :=
    div_pos hw_norm_pos zero_lt_two
  have ht_pos : 0 < t :=
    lt_of_lt_of_le hhalf_pos ht_lower
  have ht_nonneg : 0 ≤ t :=
    le_of_lt ht_pos
  have hAplus_pos : 0 < Aplus :=
    Complex.binetSecondFormula_numerator_branchWall_distance_pos
      hw_re_pos t
  have hAminus_pos : 0 < Aminus :=
    Complex.binetSecondFormula_branchWall_distance_pos hw_re_pos t
  have hthreeN_pos : 0 < 3 * N :=
    mul_pos Real.zero_lt_three hw_norm_pos
  have hm_pos : 0 < m :=
    div_pos hAplus_pos hthreeN_pos
  have hratio_lower :
      m ≤ ‖R‖ := by
    have hw_ne_zero : w ≠ 0 := by
      intro hw_zero
      cases hw_zero
      exact (lt_irrefl (0 : ℝ)) hw_re_pos
    have hnum_lower :
        Aplus ≤ ‖w + (t : ℂ) * Complex.I‖ :=
      Complex.binetSecondFormula_arctan_tail_numerator_max_branchWall_distance_le
        hw_re_pos t
    have hden_upper :
        ‖w - (t : ℂ) * Complex.I‖ ≤ 3 * N := by
      calc
        ‖w - (t : ℂ) * Complex.I‖ ≤ ‖w‖ + ‖(t : ℂ) * Complex.I‖ := by
          calc
            ‖w - (t : ℂ) * Complex.I‖ =
                ‖w + -((t : ℂ) * Complex.I)‖ := by
              exact congrArg norm (sub_eq_add_neg w ((t : ℂ) * Complex.I))
            _ ≤ ‖w‖ + ‖-((t : ℂ) * Complex.I)‖ :=
              norm_add_le w (-((t : ℂ) * Complex.I))
            _ = ‖w‖ + ‖(t : ℂ) * Complex.I‖ := by
              exact congrArg (fun x : ℝ => ‖w‖ + x)
                (norm_neg ((t : ℂ) * Complex.I))
        _ = N + t := by
          have htI_norm : ‖(t : ℂ) * Complex.I‖ = t := by
            calc
              ‖(t : ℂ) * Complex.I‖ = |t| :=
                Complex.norm_real_mul_I t
              _ = t := abs_of_nonneg ht_nonneg
          exact congrArg (fun x : ℝ => ‖w‖ + x) htI_norm
        _ ≤ N + 2 * N :=
          add_le_add_left ht_upper N
        _ = 3 * N :=
          Real.add_two_mul_eq_three_mul N
    have hden_pos : 0 < ‖w - (t : ℂ) * Complex.I‖ := by
      have hden_lower :
          w.re ≤ ‖w - (t : ℂ) * Complex.I‖ :=
        Complex.binetSecondFormula_arctan_tail_ratio_denominator_lower
          hw_re_pos t
      exact lt_of_lt_of_le hw_re_pos hden_lower
    have hcleared :
        Aplus / (3 * N) ≤
          ‖(w + (t : ℂ) * Complex.I) /
            (w - (t : ℂ) * Complex.I)‖ := by
      calc
        Aplus / (3 * N) ≤
            ‖w + (t : ℂ) * Complex.I‖ /
              ‖w - (t : ℂ) * Complex.I‖ :=
          Real.div_le_div_of_le_of_le'
            hAplus_pos
            hthreeN_pos
            hden_pos
            hden_upper
            hnum_lower
        _ =
            ‖(w + (t : ℂ) * Complex.I) /
              (w - (t : ℂ) * Complex.I)‖ := by
          exact Eq.symm (norm_div _ _)
    calc
      m = Aplus / (3 * N) := rfl
      _ ≤ ‖(w + (t : ℂ) * Complex.I) /
              (w - (t : ℂ) * Complex.I)‖ := hcleared
      _ = ‖R‖ := by
        exact Eq.symm (Complex.binetSecondFormula_arctan_tail_ratio_eq_norm
          w hw_ne_zero t)
  have hratio_upper : ‖R‖ ≤ M := by
    calc
      ‖R‖ =
          ‖(1 + ((t : ℂ) / w) * Complex.I) /
            (1 - ((t : ℂ) / w) * Complex.I)‖ := rfl
      _ ≤ (3 * N) / Aminus :=
        Complex.binetSecondFormula_arctan_tail_ratio_norm_le_three_norm_div_branchWall_distance
          hw_re_pos ht_nonneg ht_upper
  have hmM : m ≤ M :=
    le_trans hratio_lower hratio_upper
  have hlog :
      ‖Complex.log R‖ ≤
        max |Real.log m| |Real.log M| + Real.pi :=
    Complex.log_norm_le_of_norm_bounds
      hm_pos hmM hratio_lower hratio_upper
  have harctan :
      ‖Complex.arctan ((t : ℂ) / w)‖ ≤
        max |Real.log m| |Real.log M| + Real.pi := by
    have hfactor_norm_le_one : ‖(-Complex.I / 2 : ℂ)‖ ≤ (1 : ℝ) :=
      Complex.norm_neg_I_div_two_le_one
    have hmul :
        ‖(-Complex.I / 2 : ℂ) * Complex.log R‖ ≤
          ‖Complex.log R‖ := by
      calc
        ‖(-Complex.I / 2 : ℂ) * Complex.log R‖ ≤
            ‖(-Complex.I / 2 : ℂ)‖ * ‖Complex.log R‖ :=
          norm_mul_le _ _
        _ ≤ 1 * ‖Complex.log R‖ :=
          mul_le_mul_of_nonneg_right hfactor_norm_le_one
            (norm_nonneg (Complex.log R))
        _ = ‖Complex.log R‖ :=
          one_mul ‖Complex.log R‖
    calc
      ‖Complex.arctan ((t : ℂ) / w)‖ =
          ‖(-Complex.I / 2 : ℂ) * Complex.log R‖ := by
        exact congrArg norm
          (Complex.binetSecondFormula_arctan_tail_expr_eq w t)
      _ ≤ ‖Complex.log R‖ := hmul
      _ ≤ max |Real.log m| |Real.log M| + Real.pi := hlog
  have hden_norm :
      ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ = D :=
    Complex.exp_tail_denominator_norm_eq t ht_pos
  have hD_nonneg : 0 ≤ D :=
    le_of_lt (Real.binetSecondFormula_exp_denominator_pos ht_pos)
  calc
    ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ =
        ‖Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ := by
      rfl
    _ =
        ‖Complex.arctan ((t : ℂ) / w)‖ /
          ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ := by
      exact norm_div _ _
    _ = ‖Complex.arctan ((t : ℂ) / w)‖ / D := by
      exact congrArg
        (fun x : ℝ => ‖Complex.arctan ((t : ℂ) / w)‖ / x)
        hden_norm
    _ ≤ (max |Real.log m| |Real.log M| + Real.pi) / D :=
      div_le_div_of_nonneg_right harctan hD_nonneg
    _ =
      (max
          |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|
          |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| +
        Real.pi) /
        (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
      rfl

/-- The numerator-side moving logarithmic spike is integrable on the
half-open bounded tail window. -/
theorem Complex.binetSecondFormula_branchWall_numeratorMovingLog_integrableOn_boundedTailWindow_Ioc
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    IntegrableOn
      (fun t : ℝ =>
        |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|)
      (Set.Ioc (‖w‖ / 2) (2 * ‖w‖)) := by
  let Scc : Set ℝ := Set.Icc (‖w‖ / 2) (2 * ‖w‖)
  let D : ℝ → ℝ := fun t : ℝ => max w.re |w.im + t|
  let A : ℝ → ℝ := fun t : ℝ => D t / (3 * ‖w‖)
  have hw_norm_pos : 0 < ‖w‖ :=
    Complex.norm_pos_of_re_pos hw_re_pos
  have hden_pos : 0 < 3 * ‖w‖ :=
    mul_pos Real.zero_lt_three hw_norm_pos
  have hD_pos : ∀ t : ℝ, 0 < D t := by
    intro t
    exact lt_of_lt_of_le hw_re_pos (le_max_left w.re |w.im + t|)
  have hA_pos : ∀ t : ℝ, 0 < A t := by
    intro t
    exact div_pos (hD_pos t) hden_pos
  have hdist_cont : Continuous fun t : ℝ => |w.im + t| :=
    (continuous_const.add continuous_id).abs
  have hD_cont : Continuous D :=
    continuous_const.sup hdist_cont
  have hA_cont : Continuous A :=
    hD_cont.div_const (3 * ‖w‖)
  have hlog_contOn :
      ContinuousOn (fun t : ℝ => Real.log (A t)) Scc :=
    (hA_cont.continuousOn).log (fun t _ht => (hA_pos t).ne')
  have habs_contOn :
      ContinuousOn (fun t : ℝ => |Real.log (A t)|) Scc :=
    hlog_contOn.abs
  have hIcc :
      IntegrableOn
        (fun t : ℝ =>
          |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|)
        Scc :=
    habs_contOn.integrableOn_Icc
  have hsubset :
      Set.Ioc (‖w‖ / 2) (2 * ‖w‖) ⊆
        Set.Icc (‖w‖ / 2) (2 * ‖w‖) := by
    intro t ht
    exact ⟨le_of_lt ht.1, ht.2⟩
  exact hIcc.mono_set hsubset

/-- The two-moving-wall logarithmic numerator is integrable on the half-open
bounded tail window. -/
theorem Complex.binetSecondFormula_branchWall_twoMovingLogWindow_integrableOn_boundedTailWindow_Ioc
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    IntegrableOn
      (fun t : ℝ =>
        max
          |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|
          |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| +
        Real.pi)
      (Set.Ioc (‖w‖ / 2) (2 * ‖w‖)) := by
  let Scc : Set ℝ := Set.Icc (‖w‖ / 2) (2 * ‖w‖)
  let Aplus : ℝ → ℝ := fun t : ℝ => max w.re |w.im + t|
  let Aminus : ℝ → ℝ := fun t : ℝ => max w.re |w.im - t|
  let Lplus : ℝ → ℝ := fun t : ℝ => Aplus t / (3 * ‖w‖)
  let Lminus : ℝ → ℝ := fun t : ℝ => (3 * ‖w‖) / Aminus t
  let H : ℝ → ℝ := fun t : ℝ =>
    max |Real.log (Lplus t)| |Real.log (Lminus t)| + Real.pi
  have hw_norm_pos : 0 < ‖w‖ :=
    Complex.norm_pos_of_re_pos hw_re_pos
  have hthree_norm_pos : 0 < 3 * ‖w‖ :=
    mul_pos Real.zero_lt_three hw_norm_pos
  have hAplus_pos : ∀ t : ℝ, 0 < Aplus t := by
    intro t
    exact lt_of_lt_of_le hw_re_pos (le_max_left w.re |w.im + t|)
  have hAminus_pos : ∀ t : ℝ, 0 < Aminus t := by
    intro t
    exact lt_of_lt_of_le hw_re_pos (le_max_left w.re |w.im - t|)
  have hLplus_pos : ∀ t : ℝ, 0 < Lplus t := by
    intro t
    exact div_pos (hAplus_pos t) hthree_norm_pos
  have hLminus_pos : ∀ t : ℝ, 0 < Lminus t := by
    intro t
    exact div_pos hthree_norm_pos (hAminus_pos t)
  have hplus_dist_cont : Continuous fun t : ℝ => |w.im + t| :=
    (continuous_const.add continuous_id).abs
  have hminus_dist_cont : Continuous fun t : ℝ => |w.im - t| :=
    (continuous_const.sub continuous_id).abs
  have hAplus_cont : Continuous Aplus :=
    continuous_const.sup hplus_dist_cont
  have hAminus_cont : Continuous Aminus :=
    continuous_const.sup hminus_dist_cont
  have hLplus_cont : Continuous Lplus :=
    hAplus_cont.div_const (3 * ‖w‖)
  have hLminus_cont : Continuous Lminus :=
    continuous_const.div hAminus_cont (fun t => (hAminus_pos t).ne')
  have hplus_log_contOn :
      ContinuousOn (fun t : ℝ => Real.log (Lplus t)) Scc :=
    (hLplus_cont.continuousOn).log (fun t _ht => (hLplus_pos t).ne')
  have hminus_log_contOn :
      ContinuousOn (fun t : ℝ => Real.log (Lminus t)) Scc :=
    (hLminus_cont.continuousOn).log (fun t _ht => (hLminus_pos t).ne')
  have hH_contOn : ContinuousOn H Scc :=
    (hplus_log_contOn.abs.sup hminus_log_contOn.abs).add continuousOn_const
  have hH_integrable_Icc :
      IntegrableOn
        (fun t : ℝ =>
          max
            |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|
            |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| +
          Real.pi)
        Scc :=
    hH_contOn.integrableOn_Icc
  exact hH_integrable_Icc.mono_set Set.Ioc_subset_Icc_self

/-- Integrated principal-tail control by the two-moving-wall exponential
envelope on the bounded branch-wall window.

This is the branch-wall correction to the older fixed-real-part envelope: both
arctangent branch singularities remain as moving distances before integration. -/
theorem Complex.binetSecondFormula_principalTailKernel_integral_le_expWeighted_twoMovingLogWindow_boundedTailWindow_Ioc
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hw_large : 2 ≤ ‖w‖) :
    ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
      ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (2 *
          (max
            |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|
            |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| +
            Real.pi)) /
          Real.exp ((2 : ℝ) * Real.pi * t) := by
  let S : Set ℝ := Set.Ioc (‖w‖ / 2) (2 * ‖w‖)
  let P : ℝ → ℝ := fun t : ℝ =>
    ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖
  let G : ℝ → ℝ := fun t : ℝ =>
    (2 *
      (max
        |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|
        |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| +
        Real.pi)) /
      Real.exp ((2 : ℝ) * Real.pi * t)
  have hP_integrable :
      IntegrableOn P S :=
    have hP_integrable_Ioi :
        IntegrableOn P (Set.Ioi (‖w‖ / 2)) := by
      exact
        (Complex.binetSecondFormula_arctanKernel_integrableOn_tail_interval_owner
          (w := w) hw_re_pos).norm
    hP_integrable_Ioi.mono_set Set.Ioc_subset_Ioi_self
  have hG_integrable : IntegrableOn G S := by
    let Scc : Set ℝ := Set.Icc (‖w‖ / 2) (2 * ‖w‖)
    let Aplus : ℝ → ℝ := fun t : ℝ => max w.re |w.im + t|
    let Aminus : ℝ → ℝ := fun t : ℝ => max w.re |w.im - t|
    let Lplus : ℝ → ℝ := fun t : ℝ =>
      (Aplus t) / (3 * ‖w‖)
    let Lminus : ℝ → ℝ := fun t : ℝ =>
      (3 * ‖w‖) / (Aminus t)
    let H : ℝ → ℝ := fun t : ℝ =>
      (2 *
        (max |Real.log (Lplus t)| |Real.log (Lminus t)| + Real.pi)) /
        Real.exp ((2 : ℝ) * Real.pi * t)
    have hw_norm_pos : 0 < ‖w‖ :=
      Complex.norm_pos_of_re_pos hw_re_pos
    have hthree_norm_pos : 0 < 3 * ‖w‖ :=
      mul_pos Real.zero_lt_three hw_norm_pos
    have hAplus_pos : ∀ t : ℝ, 0 < Aplus t := by
      intro t
      exact lt_of_lt_of_le hw_re_pos (le_max_left w.re |w.im + t|)
    have hAminus_pos : ∀ t : ℝ, 0 < Aminus t := by
      intro t
      exact lt_of_lt_of_le hw_re_pos (le_max_left w.re |w.im - t|)
    have hLplus_pos : ∀ t : ℝ, 0 < Lplus t := by
      intro t
      exact div_pos (hAplus_pos t) hthree_norm_pos
    have hLminus_pos : ∀ t : ℝ, 0 < Lminus t := by
      intro t
      exact div_pos hthree_norm_pos (hAminus_pos t)
    have hplus_dist_cont : Continuous fun t : ℝ => |w.im + t| :=
      (continuous_const.add continuous_id).abs
    have hminus_dist_cont : Continuous fun t : ℝ => |w.im - t| :=
      (continuous_const.sub continuous_id).abs
    have hAplus_cont : Continuous Aplus :=
      continuous_const.sup hplus_dist_cont
    have hAminus_cont : Continuous Aminus :=
      continuous_const.sup hminus_dist_cont
    have hLplus_cont : Continuous Lplus :=
      hAplus_cont.div_const (3 * ‖w‖)
    have hLminus_cont : Continuous Lminus :=
      continuous_const.div hAminus_cont (fun t => (hAminus_pos t).ne')
    have hplus_log_contOn :
        ContinuousOn (fun t : ℝ => Real.log (Lplus t)) Scc :=
      (hLplus_cont.continuousOn).log (fun t _ht => (hLplus_pos t).ne')
    have hminus_log_contOn :
        ContinuousOn (fun t : ℝ => Real.log (Lminus t)) Scc :=
      (hLminus_cont.continuousOn).log (fun t _ht => (hLminus_pos t).ne')
    have hwindow_contOn :
        ContinuousOn
          (fun t : ℝ =>
            max |Real.log (Lplus t)| |Real.log (Lminus t)| + Real.pi)
          Scc :=
      (hplus_log_contOn.abs.sup hminus_log_contOn.abs).add continuousOn_const
    have hnum_contOn :
        ContinuousOn
          (fun t : ℝ =>
            2 *
              (max |Real.log (Lplus t)| |Real.log (Lminus t)| +
                Real.pi))
          Scc :=
      continuousOn_const.mul hwindow_contOn
    have hlinear_cont : Continuous fun t : ℝ => (2 : ℝ) * Real.pi * t :=
      (continuous_const.mul continuous_const).mul continuous_id
    have hden_cont : Continuous fun t : ℝ =>
        Real.exp ((2 : ℝ) * Real.pi * t) :=
      Real.continuous_exp.comp hlinear_cont
    have hden_ne : ∀ t : ℝ, t ∈ Scc →
        Real.exp ((2 : ℝ) * Real.pi * t) ≠ 0 := by
      intro t _ht
      exact (Real.exp_pos ((2 : ℝ) * Real.pi * t)).ne'
    have hH_contOn : ContinuousOn H Scc :=
      hnum_contOn.div hden_cont.continuousOn hden_ne
    have hH_integrable_Icc : IntegrableOn H Scc :=
      hH_contOn.integrableOn_Icc
    exact hH_integrable_Icc.mono_set Set.Ioc_subset_Icc_self
  have hpoint :
      ∀ᵐ t ∂volume.restrict S, P t ≤ G t :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun t ht => by
        have ht_Icc : t ∈ Set.Icc (‖w‖ / 2) (2 * ‖w‖) :=
          And.intro (le_of_lt ht.1) ht.2
        let N : ℝ :=
          max
            |Real.log ((max w.re |w.im + t|) / (3 * ‖w‖))|
            |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| +
            Real.pi
        have hkernel :
            P t ≤
              N / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
          Complex.binetSecondFormula_principalTailKernel_norm_le_twoMovingLogWindow_boundedTailWindow
            hw_re_pos ht_Icc
        have hhalf_ge_one : (1 : ℝ) ≤ ‖w‖ / 2 := by
          exact (le_div_iff₀ zero_lt_two).2
            (calc
              (1 : ℝ) * 2 = 2 := one_mul 2
              _ ≤ ‖w‖ := hw_large)
        have ht_gt_one : t ∈ Set.Ioi (1 : ℝ) :=
          lt_of_le_of_lt hhalf_ge_one ht.1
        have hN_nonneg : 0 ≤ N :=
          add_nonneg
            (le_max_of_le_left
              (abs_nonneg
                (Real.log ((max w.re |w.im + t|) / (3 * ‖w‖)))))
            Real.pi_nonneg
        have hexp :
            N / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) ≤
              (2 * N) / Real.exp ((2 : ℝ) * Real.pi * t) :=
          Real.binetSecondFormula_nonneg_div_exp_denominator_le_two_mul_div_exp
            hN_nonneg ht_gt_one
        exact le_trans hkernel hexp)
  exact
    setIntegral_mono_ae_restrict hP_integrable hG_integrable hpoint

end

end LFunctions
end Boundary
