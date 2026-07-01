import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.SectorialLog.VerticalStripShift
import Mathlib.Analysis.Complex.Basic

/-!
# Vertical recurrence: common per-factor bounds

This file owns the common coordinate and one-factor estimates used by both the
vertical recurrence product bounds and the shifted angular radius comparison.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The imaginary coordinate of a deterministic recurrence factor is the
vertical height. -/
theorem Complex.gammaRecurrenceProduct_factor_im
    (x y : ℝ)
    (j : ℕ) :
    (Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im = y := by
  calc
    (Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im =
        (Complex.fixedRealPartVerticalPoint x y).im + (j : ℂ).im :=
      Complex.add_im (Complex.fixedRealPartVerticalPoint x y) (j : ℂ)
    _ = y + (j : ℂ).im := by
      exact congrArg
        (fun t : ℝ => t + (j : ℂ).im)
        (Complex.fixedRealPartVerticalPoint_im x y)
    _ = y + 0 := by
      exact congrArg (fun t : ℝ => y + t) (Complex.natCast_im j)
    _ = y :=
      add_zero y

/-- Each recurrence factor has norm at least the vertical height. -/
theorem Complex.gammaRecurrenceProduct_factor_height_le_norm
    (x y : ℝ)
    (j : ℕ) :
    ‖y‖ ≤ ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖ := by
  have him :
      (Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im = y :=
    Complex.gammaRecurrenceProduct_factor_im x y j
  have hbasic :
      |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im| ≤
        ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖ :=
    RCLike.abs_im_le_norm
      (Complex.fixedRealPartVerticalPoint x y + (j : ℂ))
  have hnorm_eq_abs : ‖y‖ = |y| :=
    Real.norm_eq_abs y
  calc
    ‖y‖ = |y| :=
      hnorm_eq_abs
    _ =
        |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im| :=
      (congrArg abs him).symm
    _ ≤ ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖ :=
      hbasic

/-- For height at least one, the factor lower bound is comparable to
`1 + |y|` with the explicit constant `1 / 2`. -/
theorem Complex.gammaRecurrenceProduct_factor_largeHeight_lower
    {x y : ℝ}
    (j : ℕ)
    (hy : (1 : ℝ) ≤ ‖y‖) :
    (1 / 2 : ℝ) * (1 + ‖y‖) ≤
      ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖ := by
  have htwo_pos : 0 < (2 : ℝ) :=
    two_pos
  have hy_nonneg : 0 ≤ ‖y‖ :=
    norm_nonneg y
  have hone_le_norm : 1 ≤ ‖y‖ :=
    hy
  have hsum_le_twice : 1 + ‖y‖ ≤ 2 * ‖y‖ := by
    calc
      1 + ‖y‖ ≤ ‖y‖ + ‖y‖ :=
        add_le_add_right hone_le_norm ‖y‖
      _ = 2 * ‖y‖ :=
        (two_mul ‖y‖).symm
  have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) :=
    le_of_lt (one_div_pos.mpr htwo_pos)
  have hhalf_sum_le_norm :
      (1 / 2 : ℝ) * (1 + ‖y‖) ≤ ‖y‖ := by
    have hmul :
        (1 / 2 : ℝ) * (1 + ‖y‖) ≤
          (1 / 2 : ℝ) * (2 * ‖y‖) :=
      mul_le_mul_of_nonneg_left hsum_le_twice hhalf_nonneg
    have hcollapse :
        (1 / 2 : ℝ) * (2 * ‖y‖) = ‖y‖ := by
      calc
        (1 / 2 : ℝ) * (2 * ‖y‖) =
            ((1 / 2 : ℝ) * 2) * ‖y‖ :=
          (mul_assoc (1 / 2 : ℝ) 2 ‖y‖).symm
        _ = 1 * ‖y‖ := by
          have htwo_ne : (2 : ℝ) ≠ 0 :=
            ne_of_gt htwo_pos
          exact congrArg (fun t : ℝ => t * ‖y‖)
            (one_div_mul_cancel htwo_ne)
        _ = ‖y‖ :=
          one_mul ‖y‖
    calc
      (1 / 2 : ℝ) * (1 + ‖y‖) ≤
          (1 / 2 : ℝ) * (2 * ‖y‖) :=
        hmul
      _ = ‖y‖ :=
        hcollapse
  exact
    le_trans hhalf_sum_le_norm
      (Complex.gammaRecurrenceProduct_factor_height_le_norm x y j)

/-- The real part of a deterministic recurrence factor is bounded uniformly on
the strip and for `j < N`. -/
theorem Complex.gammaRecurrenceProduct_factor_re_abs_le_stripConstant
    {A B x y : ℝ}
    {N j : ℕ}
    (hxA : A ≤ x)
    (hxB : x ≤ B)
    (hj : j < N) :
    |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).re| ≤
      max |A| |B| + N := by
  have hre :
      (Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).re =
        x + (j : ℝ) := by
    calc
      (Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).re =
          (Complex.fixedRealPartVerticalPoint x y).re + (j : ℂ).re :=
        Complex.add_re (Complex.fixedRealPartVerticalPoint x y) (j : ℂ)
      _ = x + (j : ℂ).re := by
        exact congrArg
          (fun t : ℝ => t + (j : ℂ).re)
          (Complex.fixedRealPartVerticalPoint_re x y)
      _ = x + (j : ℝ) := by
        exact congrArg (fun t : ℝ => x + t) (Complex.natCast_re j)
  have hx_abs : |x| ≤ max |A| |B| :=
    real_abs_le_max_abs_of_mem_Icc hxA hxB
  have hj_le_N : (j : ℝ) ≤ N :=
    Nat.cast_le.mpr (Nat.le_of_lt hj)
  have hj_abs : |(j : ℝ)| = (j : ℝ) :=
    abs_of_nonneg (Nat.cast_nonneg j)
  have hsum :
      |x + (j : ℝ)| ≤ max |A| |B| + N := by
    calc
      |x + (j : ℝ)| ≤ |x| + |(j : ℝ)| :=
        abs_add x (j : ℝ)
      _ ≤ max |A| |B| + |(j : ℝ)| :=
        add_le_add_right hx_abs |(j : ℝ)|
      _ = max |A| |B| + (j : ℝ) := by
        exact congrArg (fun t : ℝ => max |A| |B| + t) hj_abs
      _ ≤ max |A| |B| + N :=
        add_le_add_left hj_le_N (max |A| |B|)
  calc
    |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).re| =
        |x + (j : ℝ)| :=
      congrArg abs hre
    _ ≤ max |A| |B| + N :=
      hsum

/-- A recurrence factor is bounded above by a fixed strip constant times
`1 + |y|`. -/
theorem Complex.gammaRecurrenceProduct_factor_upper_on_verticalStrip
    (A B : ℝ)
    (N : ℕ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        ∀ j : ℕ,
          j < N →
            ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖ ≤
              C * (1 + ‖y‖) := by
  let C₀ : ℝ := max |A| |B| + N
  have hC₀_nonneg : 0 ≤ C₀ := by
    have hmax_nonneg : 0 ≤ max |A| |B| :=
      le_trans (abs_nonneg A) (le_max_left |A| |B|)
    have hN_nonneg : 0 ≤ (N : ℝ) :=
      Nat.cast_nonneg N
    exact add_nonneg hmax_nonneg hN_nonneg
  have hC_pos : 0 < C₀ + 1 :=
    add_pos_of_nonneg_of_pos hC₀_nonneg zero_lt_one
  have hpointwise :
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        ∀ j : ℕ,
          j < N →
            ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖ ≤
              (C₀ + 1) * (1 + ‖y‖) := by
    intro x y hxA hxB j hj
    have hnorm_coord :
        ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖ ≤
          |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).re| +
            |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im| :=
      calc
        ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖ =
            Complex.abs
              (Complex.fixedRealPartVerticalPoint x y + (j : ℂ)) :=
          Complex.norm_eq_abs
            (Complex.fixedRealPartVerticalPoint x y + (j : ℂ))
        _ ≤
            |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).re| +
              |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im| :=
          Complex.abs_le_abs_re_add_abs_im
            (Complex.fixedRealPartVerticalPoint x y + (j : ℂ))
    have hre_bound :
        |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).re| ≤ C₀ :=
      Complex.gammaRecurrenceProduct_factor_re_abs_le_stripConstant
        hxA hxB hj
    have him_eq :
        (Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im = y :=
      Complex.gammaRecurrenceProduct_factor_im x y j
    have him_abs_eq_norm :
        |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im| = ‖y‖ := by
      exact
        Eq.trans
          (congrArg abs him_eq)
          (Real.norm_eq_abs y).symm
    have hcoord_bound :
        |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).re| +
            |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im| ≤
          C₀ + ‖y‖ := by
      calc
        |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).re| +
            |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im| ≤
            C₀ +
              |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im| :=
          add_le_add_right hre_bound
            |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im|
        _ = C₀ + ‖y‖ := by
          exact congrArg (fun t : ℝ => C₀ + t) him_abs_eq_norm
    have hC_ge_one : 1 ≤ C₀ + 1 := by
      calc
        1 = 0 + 1 := (zero_add 1).symm
        _ ≤ C₀ + 1 := add_le_add_right hC₀_nonneg 1
    have hy_nonneg : 0 ≤ ‖y‖ :=
      norm_nonneg y
    have hlinear_to_product :
        C₀ + ‖y‖ ≤ (C₀ + 1) * (1 + ‖y‖) := by
      have hleft_const : C₀ ≤ C₀ + 1 :=
        le_add_of_nonneg_right zero_le_one
      have hleft_height : ‖y‖ ≤ (C₀ + 1) * ‖y‖ :=
        calc
          ‖y‖ = 1 * ‖y‖ := (one_mul ‖y‖).symm
          _ ≤ (C₀ + 1) * ‖y‖ :=
            mul_le_mul_of_nonneg_right hC_ge_one hy_nonneg
      have hsum :
          C₀ + ‖y‖ ≤ (C₀ + 1) + (C₀ + 1) * ‖y‖ :=
        add_le_add hleft_const hleft_height
      have htarget :
          (C₀ + 1) + (C₀ + 1) * ‖y‖ =
            (C₀ + 1) * (1 + ‖y‖) := by
        calc
          (C₀ + 1) + (C₀ + 1) * ‖y‖ =
              (C₀ + 1) * 1 + (C₀ + 1) * ‖y‖ := by
            exact congrArg (fun t : ℝ => t + (C₀ + 1) * ‖y‖)
              (mul_one (C₀ + 1)).symm
          _ = (C₀ + 1) * (1 + ‖y‖) :=
            (mul_add (C₀ + 1) 1 ‖y‖).symm
      calc
        C₀ + ‖y‖ ≤ (C₀ + 1) + (C₀ + 1) * ‖y‖ :=
          hsum
        _ = (C₀ + 1) * (1 + ‖y‖) :=
          htarget
    exact le_trans hnorm_coord (le_trans hcoord_bound hlinear_to_product)
  exact ⟨C₀ + 1, hC_pos, hpointwise⟩

end
end LFunctions
end Boundary
