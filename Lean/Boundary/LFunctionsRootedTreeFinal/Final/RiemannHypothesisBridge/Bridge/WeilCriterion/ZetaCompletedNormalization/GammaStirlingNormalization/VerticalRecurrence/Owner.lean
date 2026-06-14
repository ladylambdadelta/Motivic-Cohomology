import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.SectorialLog.Owner

/-!
# Vertical recurrence transport for Gamma

This file is a sequential owner sublayer split out of
`ZetaCompletedNormalization.GammaStirlingNormalization.Owner`.  Declaration order is preserved.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

def Complex.gammaRecurrenceProduct (z : ℂ) (N : ℕ) : ℂ :=
  ∏ j ∈ Finset.range N, z + (j : ℂ)

/-- The recurrence product is nonzero when all its factors are nonzero. -/
theorem Complex.gammaRecurrenceProduct_ne_zero
    {z : ℂ}
    {N : ℕ}
    (hfactor_ne :
      ∀ j : ℕ,
        j < N →
          z + (j : ℂ) ≠ 0) :
    Complex.gammaRecurrenceProduct z N ≠ 0 := by
  unfold Complex.gammaRecurrenceProduct
  exact Finset.prod_ne_zero_iff.mpr
    (fun j hj =>
      hfactor_ne j (Finset.mem_range.mp hj))

/-- Multiplicative form of the finite Gamma recurrence. -/
theorem Complex.Gamma_shifted_eq_gammaRecurrenceProduct_mul
    {z : ℂ}
    (N : ℕ)
    (hfactor_ne :
      ∀ j : ℕ,
        j < N →
          z + (j : ℂ) ≠ 0) :
    Complex.Gamma (z + (N : ℂ)) =
      Complex.gammaRecurrenceProduct z N * Complex.Gamma z := by
  induction N with
  | zero =>
      calc
        Complex.Gamma (z + ((0 : ℕ) : ℂ)) =
            Complex.Gamma z :=
          congrArg Complex.Gamma (add_zero z)
        _ = 1 * Complex.Gamma z :=
          (one_mul (Complex.Gamma z)).symm
        _ = Complex.gammaRecurrenceProduct z 0 * Complex.Gamma z := by
          unfold Complex.gammaRecurrenceProduct
          exact congrArg (fun t : ℂ => t * Complex.Gamma z)
            (Finset.prod_range_zero (fun j : ℕ => z + (j : ℂ))).symm
  | succ N ih =>
      have hfactor_prev :
          ∀ j : ℕ, j < N → z + (j : ℂ) ≠ 0 := by
        intro j hj
        exact hfactor_ne j (Nat.lt_trans hj (Nat.lt_succ_self N))
      have hN_factor : z + (N : ℂ) ≠ 0 :=
        hfactor_ne N (Nat.lt_succ_self N)
      have hsucc_arg :
          z + ((Nat.succ N : ℕ) : ℂ) =
            (z + (N : ℂ)) + 1 := by
        calc
          z + ((Nat.succ N : ℕ) : ℂ) =
              z + ((N : ℂ) + 1) := by
            exact congrArg (fun t : ℂ => z + t) (Nat.cast_succ N)
          _ = (z + (N : ℂ)) + 1 :=
            (add_assoc z (N : ℂ) 1).symm
      have hgamma_step :
          Complex.Gamma (z + ((Nat.succ N : ℕ) : ℂ)) =
            (z + (N : ℂ)) * Complex.Gamma (z + (N : ℂ)) := by
        exact Eq.trans
          (congrArg Complex.Gamma hsucc_arg)
          (Complex.Gamma_add_one (z + (N : ℂ)) hN_factor)
      have hprod_step :
          Complex.gammaRecurrenceProduct z (Nat.succ N) =
            Complex.gammaRecurrenceProduct z N * (z + (N : ℂ)) := by
        unfold Complex.gammaRecurrenceProduct
        exact Finset.prod_range_succ (fun j : ℕ => z + (j : ℂ)) N
      calc
        Complex.Gamma (z + ((Nat.succ N : ℕ) : ℂ)) =
            (z + (N : ℂ)) * Complex.Gamma (z + (N : ℂ)) :=
          hgamma_step
        _ = (z + (N : ℂ)) *
              (Complex.gammaRecurrenceProduct z N * Complex.Gamma z) := by
          exact congrArg (fun t : ℂ => (z + (N : ℂ)) * t)
            (ih hfactor_prev)
        _ =
            (Complex.gammaRecurrenceProduct z N * (z + (N : ℂ))) *
              Complex.Gamma z := by
          exact (mul_left_comm (z + (N : ℂ))
            (Complex.gammaRecurrenceProduct z N) (Complex.Gamma z)).symm
        _ =
            Complex.gammaRecurrenceProduct z (Nat.succ N) *
              Complex.Gamma z := by
          exact congrArg (fun t : ℂ => t * Complex.Gamma z) hprod_step.symm

/-- The deterministic shift as a complex horizontal translation. -/
theorem Complex.fixedRealPartVerticalPoint_add_verticalStripRightShift
    (A x y : ℝ) :
    Complex.fixedRealPartVerticalPoint (x + Complex.verticalStripRightShift A) y =
      Complex.fixedRealPartVerticalPoint x y +
        (Complex.verticalStripRightShift A : ℂ) := by
  exact Complex.ext
    (by
      calc
        (Complex.fixedRealPartVerticalPoint (x + Complex.verticalStripRightShift A) y).re =
            x + (Complex.verticalStripRightShift A : ℝ) :=
          Complex.fixedRealPartVerticalPoint_re
            (x + Complex.verticalStripRightShift A) y
        _ =
            (Complex.fixedRealPartVerticalPoint x y +
              (Complex.verticalStripRightShift A : ℂ)).re := by
          have hleft :
              (Complex.fixedRealPartVerticalPoint x y).re = x :=
            Complex.fixedRealPartVerticalPoint_re x y
          have hright :
              ((Complex.verticalStripRightShift A : ℂ)).re =
                (Complex.verticalStripRightShift A : ℝ) :=
            Complex.ofReal_re (Complex.verticalStripRightShift A : ℝ)
          exact
            (Eq.trans
              (Complex.add_re
                (Complex.fixedRealPartVerticalPoint x y)
                (Complex.verticalStripRightShift A : ℂ))
              (congrArg₂ HAdd.hAdd hleft hright)).symm)
    (by
      calc
        (Complex.fixedRealPartVerticalPoint (x + Complex.verticalStripRightShift A) y).im =
            y :=
          Complex.fixedRealPartVerticalPoint_im
            (x + Complex.verticalStripRightShift A) y
        _ =
            (Complex.fixedRealPartVerticalPoint x y +
              (Complex.verticalStripRightShift A : ℂ)).im := by
          have hleft :
              (Complex.fixedRealPartVerticalPoint x y).im = y :=
            Complex.fixedRealPartVerticalPoint_im x y
          have hright :
              ((Complex.verticalStripRightShift A : ℂ)).im = 0 :=
            Complex.ofReal_im (Complex.verticalStripRightShift A : ℝ)
          exact
            (Eq.trans
              (Complex.add_im
                (Complex.fixedRealPartVerticalPoint x y)
                (Complex.verticalStripRightShift A : ℂ))
              (Eq.trans (congrArg₂ HAdd.hAdd hleft hright) (add_zero y))).symm)

/-- A natural real-part shift is the corresponding complex horizontal
translation of a fixed vertical point. -/
theorem Complex.fixedRealPartVerticalPoint_add_natCast
    (x y : ℝ)
    (N : ℕ) :
    Complex.fixedRealPartVerticalPoint (x + N) y =
      Complex.fixedRealPartVerticalPoint x y + (N : ℂ) := by
  exact Complex.ext
    (by
      calc
        (Complex.fixedRealPartVerticalPoint (x + N) y).re =
            x + (N : ℝ) :=
          Complex.fixedRealPartVerticalPoint_re (x + N) y
        _ =
            (Complex.fixedRealPartVerticalPoint x y + (N : ℂ)).re := by
          have hleft :
              (Complex.fixedRealPartVerticalPoint x y).re = x :=
            Complex.fixedRealPartVerticalPoint_re x y
          have hright : ((N : ℂ)).re = (N : ℝ) :=
            Complex.natCast_re N
          exact
            (Eq.trans
              (Complex.add_re (Complex.fixedRealPartVerticalPoint x y) (N : ℂ))
              (congrArg₂ HAdd.hAdd hleft hright)).symm)
    (by
      calc
        (Complex.fixedRealPartVerticalPoint (x + N) y).im = y :=
          Complex.fixedRealPartVerticalPoint_im (x + N) y
        _ =
            (Complex.fixedRealPartVerticalPoint x y + (N : ℂ)).im := by
          have hleft :
              (Complex.fixedRealPartVerticalPoint x y).im = y :=
            Complex.fixedRealPartVerticalPoint_im x y
          have hright : ((N : ℂ)).im = 0 :=
            Complex.natCast_im N
          exact
            (Eq.trans
              (Complex.add_im (Complex.fixedRealPartVerticalPoint x y) (N : ℂ))
              (Eq.trans (congrArg₂ HAdd.hAdd hleft hright) (add_zero y))).symm)

/-- Gamma recurrence over a deterministic finite product.

For large vertical height the factors `z + j` avoid zero, so iterating
`Γ(s + 1) = s Γ(s)` gives the exact transport from `Γ z` to
`Γ(z + N)`. -/
theorem Complex.Gamma_eq_shifted_div_gammaRecurrenceProduct
    {z : ℂ}
    (N : ℕ)
    (hfactor_ne :
      ∀ j : ℕ,
        j < N →
          z + (j : ℂ) ≠ 0) :
    Complex.Gamma z =
      Complex.Gamma (z + (N : ℂ)) /
        Complex.gammaRecurrenceProduct z N := by
  have hprod_ne :
      Complex.gammaRecurrenceProduct z N ≠ 0 :=
    Complex.gammaRecurrenceProduct_ne_zero hfactor_ne
  have hshift :
      Complex.Gamma (z + (N : ℂ)) =
        Complex.gammaRecurrenceProduct z N * Complex.Gamma z :=
    Complex.Gamma_shifted_eq_gammaRecurrenceProduct_mul N hfactor_ne
  exact
    (calc
      Complex.Gamma (z + (N : ℂ)) /
          Complex.gammaRecurrenceProduct z N =
          (Complex.gammaRecurrenceProduct z N * Complex.Gamma z) /
            Complex.gammaRecurrenceProduct z N := by
        exact congrArg
          (fun t : ℂ => t / Complex.gammaRecurrenceProduct z N)
          hshift
      _ = Complex.Gamma z :=
        mul_div_cancel_left₀ (Complex.Gamma z) hprod_ne).symm

/-- Norm form of the finite Gamma recurrence transport. -/
theorem Complex.Gamma_norm_eq_shifted_norm_div_gammaRecurrenceProduct_norm
    {z : ℂ}
    (N : ℕ)
    (hfactor_ne :
      ∀ j : ℕ,
        j < N →
          z + (j : ℂ) ≠ 0) :
    ‖Complex.Gamma z‖ =
      ‖Complex.Gamma (z + (N : ℂ))‖ /
        ‖Complex.gammaRecurrenceProduct z N‖ := by
  have hgamma :
      Complex.Gamma z =
        Complex.Gamma (z + (N : ℂ)) /
          Complex.gammaRecurrenceProduct z N :=
    Complex.Gamma_eq_shifted_div_gammaRecurrenceProduct N hfactor_ne
  calc
    ‖Complex.Gamma z‖ =
        ‖Complex.Gamma (z + (N : ℂ)) /
          Complex.gammaRecurrenceProduct z N‖ :=
      congrArg norm hgamma
    _ =
        ‖Complex.Gamma (z + (N : ℂ))‖ /
          ‖Complex.gammaRecurrenceProduct z N‖ :=
      norm_div (Complex.Gamma (z + (N : ℂ)))
        (Complex.gammaRecurrenceProduct z N)

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
    Complex.abs_im_le_norm
      (Complex.fixedRealPartVerticalPoint x y + (j : ℂ))
  have hnorm_eq_abs : ‖y‖ = |y| :=
    Real.norm_eq_abs y
  exact
    Eq.subst
      (motive := fun t : ℝ =>
        t ≤ ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖)
      hnorm_eq_abs.symm
      (Eq.subst
        (motive := fun t : ℝ =>
          |t| ≤ ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖)
        him
        hbasic)

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
      _ = (1 + 1) * ‖y‖ := by
        exact (two_mul ‖y‖).symm
      _ = 2 * ‖y‖ := by
        exact congrArg (fun t : ℝ => t * ‖y‖) (one_add_one_eq_two)
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
            (inv_mul_cancel₀ htwo_ne)
        _ = ‖y‖ :=
          one_mul ‖y‖
    exact
      Eq.subst
        (motive := fun t : ℝ =>
          (1 / 2 : ℝ) * (1 + ‖y‖) ≤ t)
        hcollapse
        hmul
  exact
    le_trans hhalf_sum_le_norm
      (Complex.gammaRecurrenceProduct_factor_height_le_norm x y j)

/-- Bounded intervals have a uniform absolute-value bound by the endpoint
absolute values. -/
theorem real_abs_le_max_abs_of_mem_Icc
    {A B x : ℝ}
    (hxA : A ≤ x)
    (hxB : x ≤ B) :
    |x| ≤ max |A| |B| := by
  have hmax_A : |A| ≤ max |A| |B| :=
    le_max_left |A| |B|
  have hmax_B : |B| ≤ max |A| |B| :=
    le_max_right |A| |B|
  have hleft_endpoint : -|A| ≤ A :=
    neg_le_abs A
  have hleft_max : -max |A| |B| ≤ -|A| :=
    neg_le_neg hmax_A
  have hleft : -max |A| |B| ≤ x :=
    le_trans hleft_max (le_trans hleft_endpoint hxA)
  have hright_endpoint : B ≤ |B| :=
    le_abs_self B
  have hright : x ≤ max |A| |B| :=
    le_trans hxB (le_trans hright_endpoint hmax_B)
  exact abs_le.mpr ⟨hleft, hright⟩

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
  exact
    Eq.subst
      (motive := fun t : ℝ => |t| ≤ max |A| |B| + N)
      hre.symm
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
  refine ⟨C₀ + 1, ?_, ?_⟩
  · have hC₀_nonneg : 0 ≤ C₀ := by
      have hmax_nonneg : 0 ≤ max |A| |B| :=
        le_trans (abs_nonneg A) (le_max_left |A| |B|)
      have hN_nonneg : 0 ≤ (N : ℝ) :=
        Nat.cast_nonneg N
      exact add_nonneg hmax_nonneg hN_nonneg
    exact add_pos_of_nonneg_of_pos hC₀_nonneg zero_lt_one
  intro x y hxA hxB j hj
  have hnorm_coord :
      ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖ ≤
        |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).re| +
          |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im| :=
    Eq.subst
      (motive := fun t : ℝ =>
        t ≤
          |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).re| +
            |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im|)
      (Complex.norm_eq_abs
        (Complex.fixedRealPartVerticalPoint x y + (j : ℂ))).symm
      (Complex.abs_le_abs_re_add_abs_im
        (Complex.fixedRealPartVerticalPoint x y + (j : ℂ)))
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
    exact
      Eq.subst
        (motive := fun t : ℝ =>
          |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).re| +
            |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im| ≤
              C₀ + t)
        him_abs_eq_norm.symm
        (add_le_add_right hre_bound
          |(Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im|)
  have hC₀_nonneg : 0 ≤ C₀ := by
    have hmax_nonneg : 0 ≤ max |A| |B| :=
      le_trans (abs_nonneg A) (le_max_left |A| |B|)
    have hN_nonneg : 0 ≤ (N : ℝ) :=
      Nat.cast_nonneg N
    exact add_nonneg hmax_nonneg hN_nonneg
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
    exact
      Eq.subst
        (motive := fun t : ℝ => C₀ + ‖y‖ ≤ t)
        htarget
        hsum
  exact le_trans hnorm_coord (le_trans hcoord_bound hlinear_to_product)

/-- Per-factor two-sided bounds for deterministic recurrence factors on a fixed
vertical strip. -/
theorem Complex.gammaRecurrenceProduct_factor_twoSided_bounds_on_verticalStrip
    (A B : ℝ)
    (N : ℕ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ∀ j : ℕ,
            j < N →
              ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖ ≤
                C * (1 + ‖y‖) ∧
              c * (1 + ‖y‖) ≤
                ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖ := by
  rcases Complex.gammaRecurrenceProduct_factor_upper_on_verticalStrip A B N with
    ⟨C, hC_pos, hC⟩
  refine ⟨1, C, (1 / 2 : ℝ), zero_lt_one, hC_pos, ?_, ?_⟩
  · exact one_div_pos.mpr two_pos
  intro x y hxA hxB hy j hj
  constructor
  · exact hC x y hxA hxB j hj
  · exact Complex.gammaRecurrenceProduct_factor_largeHeight_lower j hy

/-- Norm of the deterministic recurrence product as the finite product of
factor norms. -/
theorem Complex.gammaRecurrenceProduct_norm_eq_prod_factor_norms
    (z : ℂ)
    (N : ℕ) :
    ‖Complex.gammaRecurrenceProduct z N‖ =
      ∏ j ∈ Finset.range N, ‖z + (j : ℂ)‖ := by
  unfold Complex.gammaRecurrenceProduct
  calc
    ‖∏ j ∈ Finset.range N, z + (j : ℂ)‖ =
        Complex.abs (∏ j ∈ Finset.range N, z + (j : ℂ)) :=
      Complex.norm_eq_abs (∏ j ∈ Finset.range N, z + (j : ℂ))
    _ = ∏ j ∈ Finset.range N, Complex.abs (z + (j : ℂ)) :=
      Complex.abs_prod (Finset.range N) (fun j : ℕ => z + (j : ℂ))
    _ = ∏ j ∈ Finset.range N, ‖z + (j : ℂ)‖ :=
      Finset.prod_congr rfl
        (fun j hj =>
          (Complex.norm_eq_abs (z + (j : ℂ))).symm)

/-- Uniform finite-product upper estimate from per-factor upper estimates. -/
theorem real_finset_range_prod_upper_of_factor_le
    (N : ℕ)
    {M : ℝ}
    {f : ℕ → ℝ}
    (hM_nonneg : 0 ≤ M)
    (hf_nonneg : ∀ j : ℕ, j < N → 0 ≤ f j)
    (hf_le : ∀ j : ℕ, j < N → f j ≤ M) :
    (∏ j ∈ Finset.range N, f j) ≤ M ^ N := by
  have hprod_le :
      (∏ j ∈ Finset.range N, f j) ≤
        ∏ j ∈ Finset.range N, M :=
    Finset.prod_le_prod
      (fun j hj => hf_nonneg j (Finset.mem_range.mp hj))
      (fun j hj => hf_le j (Finset.mem_range.mp hj))
  have hconst :
      (∏ j ∈ Finset.range N, M) = M ^ #(Finset.range N) :=
    Finset.prod_const M
  have hcard :
      #(Finset.range N) = N :=
    Finset.card_range N
  have hconst_N :
      (∏ j ∈ Finset.range N, M) = M ^ N :=
    Eq.trans hconst (congrArg (fun n : ℕ => M ^ n) hcard)
  exact le_trans hprod_le (le_of_eq hconst_N)

/-- Uniform finite-product lower estimate from per-factor lower estimates. -/
theorem real_finset_range_prod_lower_of_factor_ge
    (N : ℕ)
    {m : ℝ}
    {f : ℕ → ℝ}
    (hm_nonneg : 0 ≤ m)
    (hf_ge : ∀ j : ℕ, j < N → m ≤ f j) :
    m ^ N ≤ (∏ j ∈ Finset.range N, f j) := by
  have hprod_le :
      (∏ j ∈ Finset.range N, m) ≤
        ∏ j ∈ Finset.range N, f j :=
    Finset.prod_le_prod
      (fun j hj => hm_nonneg)
      (fun j hj => hf_ge j (Finset.mem_range.mp hj))
  have hconst :
      (∏ j ∈ Finset.range N, m) = m ^ #(Finset.range N) :=
    Finset.prod_const m
  have hcard :
      #(Finset.range N) = N :=
    Finset.card_range N
  have hconst_N :
      (∏ j ∈ Finset.range N, m) = m ^ N :=
    Eq.trans hconst (congrArg (fun n : ℕ => m ^ n) hcard)
  exact
    Eq.subst
      (motive := fun t : ℝ =>
        t ≤ ∏ j ∈ Finset.range N, f j)
      hconst_N
      hprod_le

/-- Convert a natural power to the real-power notation used by the Gamma
envelope statements. -/
theorem real_pow_natCast_eq_rpow
    {r : ℝ}
    (hr : 0 ≤ r)
    (N : ℕ) :
    r ^ N = r ^ (N : ℝ) := by
  exact Real.rpow_natCast r N

/-- Finite products preserve uniform per-factor polynomial upper/lower bounds
for the deterministic Gamma recurrence product. -/
theorem Complex.gammaRecurrenceProduct_verticalStrip_twoSided_bounds_of_factor_bounds
    (A B : ℝ)
    (N : ℕ)
    (hfactor :
      ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
        0 < H ∧
        0 < C ∧
        0 < c ∧
        ∀ x y : ℝ,
          A ≤ x →
          x ≤ B →
          H ≤ ‖y‖ →
            ∀ j : ℕ,
              j < N →
                ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖ ≤
                  C * (1 + ‖y‖) ∧
                c * (1 + ‖y‖) ≤
                  ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ‖Complex.gammaRecurrenceProduct
              (Complex.fixedRealPartVerticalPoint x y) N‖ ≤
            C * (1 + ‖y‖) ^ (N : ℝ) ∧
          c * (1 + ‖y‖) ^ (N : ℝ) ≤
            ‖Complex.gammaRecurrenceProduct
              (Complex.fixedRealPartVerticalPoint x y) N‖ := by
  rcases hfactor with ⟨H, C, c, hH_pos, hC_pos, hc_pos, hfactor_pointwise⟩
  refine ⟨H, C ^ N, c ^ N, hH_pos, ?_, ?_, ?_⟩
  · exact pow_pos hC_pos N
  · exact pow_pos hc_pos N
  intro x y hxA hxB hy
  let R : ℝ := 1 + ‖y‖
  have hR_nonneg : 0 ≤ R :=
    add_nonneg zero_le_one (norm_nonneg y)
  have hR_pos : 0 < R :=
    add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg y)
  have hCR_nonneg : 0 ≤ C * R :=
    mul_nonneg (le_of_lt hC_pos) hR_nonneg
  have hcR_nonneg : 0 ≤ c * R :=
    mul_nonneg (le_of_lt hc_pos) hR_nonneg
  have hprod_norm :
      ‖Complex.gammaRecurrenceProduct
          (Complex.fixedRealPartVerticalPoint x y) N‖ =
        ∏ j ∈ Finset.range N,
          ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖ :=
    Complex.gammaRecurrenceProduct_norm_eq_prod_factor_norms
      (Complex.fixedRealPartVerticalPoint x y) N
  have hupper_prod :
      (∏ j ∈ Finset.range N,
          ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖) ≤
        (C * R) ^ N :=
    real_finset_range_prod_upper_of_factor_le
      N
      hCR_nonneg
      (fun j hj =>
        norm_nonneg (Complex.fixedRealPartVerticalPoint x y + (j : ℂ)))
      (fun j hj =>
        (hfactor_pointwise x y hxA hxB hy j hj).1)
  have hlower_prod :
      (c * R) ^ N ≤
        (∏ j ∈ Finset.range N,
          ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖) :=
    real_finset_range_prod_lower_of_factor_ge
      N
      hcR_nonneg
      (fun j hj =>
        (hfactor_pointwise x y hxA hxB hy j hj).2)
  have hupper_target :
      (C * R) ^ N =
        C ^ N * R ^ (N : ℝ) := by
    have hmul_pow : (C * R) ^ N = C ^ N * R ^ N :=
      mul_pow C R N
    have hR_pow : R ^ N = R ^ (N : ℝ) :=
      real_pow_natCast_eq_rpow hR_nonneg N
    exact
      Eq.trans hmul_pow
        (congrArg (fun t : ℝ => C ^ N * t) hR_pow)
  have hlower_target :
      (c * R) ^ N =
        c ^ N * R ^ (N : ℝ) := by
    have hmul_pow : (c * R) ^ N = c ^ N * R ^ N :=
      mul_pow c R N
    have hR_pow : R ^ N = R ^ (N : ℝ) :=
      real_pow_natCast_eq_rpow hR_nonneg N
    exact
      Eq.trans hmul_pow
        (congrArg (fun t : ℝ => c ^ N * t) hR_pow)
  constructor
  · exact
      Eq.subst
        (motive := fun t : ℝ =>
          ‖Complex.gammaRecurrenceProduct
              (Complex.fixedRealPartVerticalPoint x y) N‖ ≤ t)
        hupper_target
        (Eq.subst
          (motive := fun t : ℝ => t ≤ (C * R) ^ N)
          hprod_norm.symm
          hupper_prod)
  · exact
      Eq.subst
        (motive := fun t : ℝ =>
          t ≤
            ‖Complex.gammaRecurrenceProduct
              (Complex.fixedRealPartVerticalPoint x y) N‖)
        hlower_target
        (Eq.subst
          (motive := fun t : ℝ => (c * R) ^ N ≤ t)
          hprod_norm
          hlower_prod)

/-- The exact finite-product geometry estimate for deterministic Gamma
recurrence factors on a fixed vertical strip.

The per-factor strip geometry is proved above; this theorem packages those
factor estimates with the finite product algebra over `j < N`. -/
theorem Complex.gammaRecurrenceProduct_verticalStrip_twoSided_bounds_finiteProductEstimate
    (A B : ℝ)
    (N : ℕ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ‖Complex.gammaRecurrenceProduct
              (Complex.fixedRealPartVerticalPoint x y) N‖ ≤
            C * (1 + ‖y‖) ^ (N : ℝ) ∧
          c * (1 + ‖y‖) ^ (N : ℝ) ≤
            ‖Complex.gammaRecurrenceProduct
              (Complex.fixedRealPartVerticalPoint x y) N‖ := by
  exact
    Complex.gammaRecurrenceProduct_verticalStrip_twoSided_bounds_of_factor_bounds
      A B N
      (Complex.gammaRecurrenceProduct_factor_twoSided_bounds_on_verticalStrip
        A B N)

/-- Finite recurrence products have uniform polynomial upper/lower bounds on a
fixed vertical strip after a deterministic shift.

This is the exact finite-product estimate needed for recurrence transport: for
fixed `N`, bounded real part and large `|y|` make each factor `x + i y + j`
comparable to `1 + |y|`, and therefore the whole product is comparable to
`(1 + |y|)^N`. -/
theorem Complex.gammaRecurrenceProduct_verticalStrip_twoSided_bounds
    (A B : ℝ)
    (N : ℕ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ‖Complex.gammaRecurrenceProduct
              (Complex.fixedRealPartVerticalPoint x y) N‖ ≤
            C * (1 + ‖y‖) ^ (N : ℝ) ∧
          c * (1 + ‖y‖) ^ (N : ℝ) ≤
            ‖Complex.gammaRecurrenceProduct
              (Complex.fixedRealPartVerticalPoint x y) N‖ := by
  exact
    Complex.gammaRecurrenceProduct_verticalStrip_twoSided_bounds_finiteProductEstimate
      A B N

/-- Large vertical height keeps all deterministic recurrence factors nonzero. -/
theorem Complex.gammaRecurrenceProduct_factors_ne_zero_on_verticalStrip_largeHeight
    (A B : ℝ)
    (N : ℕ) :
    ∃ H : ℝ,
      0 < H ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ∀ j : ℕ,
            j < N →
              Complex.fixedRealPartVerticalPoint x y + (j : ℂ) ≠ 0 := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro x y _hxA _hxB hy j _hj
  intro hzero
  have him_eq :
      (Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im = (0 : ℂ).im :=
    congrArg Complex.im hzero
  have hleft_im :
      (Complex.fixedRealPartVerticalPoint x y + (j : ℂ)).im = y :=
    Complex.gammaRecurrenceProduct_factor_im x y j
  have hzero_im : (0 : ℂ).im = (0 : ℝ) :=
    Complex.zero_im
  have hy_zero : y = 0 :=
    Eq.trans hleft_im.symm (Eq.trans him_eq hzero_im)
  have hnorm_zero : ‖y‖ = 0 :=
    congrArg norm hy_zero
  have hnot : ¬ (1 : ℝ) ≤ 0 :=
    not_le.mpr zero_lt_one
  exact hnot
    (Eq.subst
      (motive := fun t : ℝ => (1 : ℝ) ≤ t)
      hnorm_zero
      hy)

/-- The deterministic strip shift written as a local abbreviation for the
vertical-strip Stirling transport. -/
def Complex.verticalStripTransportShift (A : ℝ) : ℕ :=
  Complex.verticalStripRightShift A

/-- The deterministic transport shift moves the strip into the closed right
half-plane. -/
theorem Complex.verticalStripTransportShift_closedRightHalfPlaneSector
    {A x y : ℝ}
    (hx : A ≤ x) :
    Complex.closedRightHalfPlaneSector
      (Complex.fixedRealPartVerticalPoint
        (x + Complex.verticalStripTransportShift A) y) := by
  unfold Complex.verticalStripTransportShift
  exact
    Complex.fixedRealPartVerticalPoint_verticalStripRightShift_closedRightHalfPlaneSector
      hx

/-- Large vertical height gives the sectorial radius cutoff after the
deterministic transport shift. -/
theorem Complex.verticalStripTransportShift_radius_ge_of_height_ge
    {A x y H : ℝ}
    (hH : H ≤ ‖y‖) :
    H ≤
      ‖Complex.fixedRealPartVerticalPoint
        (x + Complex.verticalStripTransportShift A) y‖ := by
  unfold Complex.verticalStripTransportShift
  exact
    Complex.fixedRealPartVerticalPoint_verticalStripRightShift_radius_ge_of_height_ge
      hH

/-- The deterministic transport shift is the complex horizontal translation
appearing in the finite Gamma recurrence. -/
theorem Complex.fixedRealPartVerticalPoint_add_verticalStripTransportShift
    (A x y : ℝ) :
    Complex.fixedRealPartVerticalPoint
        (x + Complex.verticalStripTransportShift A) y =
      Complex.fixedRealPartVerticalPoint x y +
        (Complex.verticalStripTransportShift A : ℂ) := by
  unfold Complex.verticalStripTransportShift
  exact Complex.fixedRealPartVerticalPoint_add_verticalStripRightShift A x y

/-- Sectorial Stirling gives uniform two-sided bounds for the normalized
Stirling factor on the deterministically shifted vertical strip. -/
theorem Complex.sectorialStirling_shiftedNormalizedFactor_twoSided_bounds
    (hStirling : ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖)
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ‖Complex.Gamma
              (Complex.fixedRealPartVerticalPoint
                (x + Complex.verticalStripTransportShift A) y) *
              Complex.exp
                (Complex.fixedRealPartVerticalPoint
                  (x + Complex.verticalStripTransportShift A) y) *
              (Complex.fixedRealPartVerticalPoint
                (x + Complex.verticalStripTransportShift A) y) ^
                ((1 / 2 : ℂ) -
                  Complex.fixedRealPartVerticalPoint
                    (x + Complex.verticalStripTransportShift A) y)‖ ≤ C ∧
          c ≤
            ‖Complex.Gamma
              (Complex.fixedRealPartVerticalPoint
                (x + Complex.verticalStripTransportShift A) y) *
              Complex.exp
                (Complex.fixedRealPartVerticalPoint
                  (x + Complex.verticalStripTransportShift A) y) *
              (Complex.fixedRealPartVerticalPoint
                (x + Complex.verticalStripTransportShift A) y) ^
                ((1 / 2 : ℂ) -
                  Complex.fixedRealPartVerticalPoint
                    (x + Complex.verticalStripTransportShift A) y)‖ := by
  rcases hStirling with ⟨R, K, hR_pos, hK_pos, hStirling_pointwise⟩
  let s : ℝ := Real.sqrt (2 * Real.pi)
  let H : ℝ := max R (max (4 * K / s) 1)
  refine ⟨H, 2 * s, s / 2, ?_, ?_, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one
      (le_trans
        (le_max_right (4 * K / s) 1)
        (le_max_right R (max (4 * K / s) 1)))
  · exact mul_pos two_pos (Real.sqrt_pos.mpr (mul_pos two_pos Real.pi_pos))
  · exact half_pos (Real.sqrt_pos.mpr (mul_pos two_pos Real.pi_pos))
  intro x y hxA _hxB hy
  let w : ℂ :=
    Complex.fixedRealPartVerticalPoint
      (x + Complex.verticalStripTransportShift A) y
  have hw_sector : Complex.closedRightHalfPlaneSector w :=
    Complex.verticalStripTransportShift_closedRightHalfPlaneSector hxA
  have hw_radius_H : H ≤ ‖w‖ :=
    Complex.verticalStripTransportShift_radius_ge_of_height_ge hy
  have hw_R : R ≤ ‖w‖ :=
    le_trans (le_max_left R (max (4 * K / s) 1)) hw_radius_H
  have hw_one : 1 ≤ ‖w‖ :=
    le_trans
      (le_trans
        (le_max_right (4 * K / s) 1)
        (le_max_right R (max (4 * K / s) 1)))
      hw_radius_H
  have hw_norm_pos : 0 < ‖w‖ :=
    lt_of_lt_of_le zero_lt_one hw_one
  have hw_cutoff_half : 4 * K / s ≤ ‖w‖ :=
    le_trans
      (le_trans
        (le_max_left (4 * K / s) 1)
        (le_max_right R (max (4 * K / s) 1)))
      hw_radius_H
  have herror_half :
      K / ‖w‖ ≤ s / 2 :=
    real_stirlingError_div_norm_le_half_sqrt_two_pi_of_cutoff
      K ‖w‖ hK_pos hw_norm_pos hw_cutoff_half
  have hhalf_le_s : s / 2 ≤ s := by
    have hs_nonneg : 0 ≤ s :=
      Real.sqrt_nonneg (2 * Real.pi)
    exact
      (div_le_iff₀ zero_lt_two).mpr
        (by
          calc
            s ≤ s + s := le_add_of_nonneg_right hs_nonneg
            _ = 2 * s := (two_mul s).symm
            _ = s * 2 := mul_comm 2 s)
  have herror_full :
      K / ‖w‖ ≤ s :=
    le_trans herror_half hhalf_le_s
  constructor
  · exact
      Complex.normalizedGammaFactor_norm_le_two_sqrt_two_pi_of_exponentialStirling_error
        R K hStirling_pointwise w hw_sector hw_R herror_full
  · exact
      Complex.half_sqrt_two_pi_le_normalizedGammaFactor_norm_of_exponentialStirling_error
        R K hStirling_pointwise w hw_sector hw_R herror_half

/-- Positivity of the exponential/power denominator in normalized Stirling away
from the origin. -/
theorem Complex.stirlingDenominator_pos_of_ne_zero
    {w : ℂ}
    (hw_ne : w ≠ 0) :
    0 < ‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖ := by
  have hexp_pos : 0 < ‖Complex.exp w‖ :=
    norm_pos_iff.mpr (Complex.exp_ne_zero w)
  have hcpow_ne : w ^ ((1 / 2 : ℂ) - w) ≠ 0 := by
    intro hzero
    have hbase_zero : w = 0 :=
      ((cpow_eq_zero_iff w ((1 / 2 : ℂ) - w)).mp hzero).1
    exact hw_ne hbase_zero
  have hcpow_pos : 0 < ‖w ^ ((1 / 2 : ℂ) - w)‖ :=
    norm_pos_iff.mpr hcpow_ne
  exact mul_pos hexp_pos hcpow_pos

/-- Elementary arctangent majorization used to quantify the angular defect of a
right-half-plane vertical ray. -/
theorem Real.arctan_le_self_of_nonneg
    {t : ℝ}
    (ht : 0 ≤ t) :
    Real.arctan t ≤ t := by
  have harctan_nonneg : 0 ≤ Real.arctan t := by
    have hzero_le :
        Real.arctan 0 ≤ Real.arctan t :=
      Real.arctan_strictMono.monotone ht
    exact Eq.subst
      (motive := fun r : ℝ => r ≤ Real.arctan t)
      Real.arctan_zero
      hzero_le
  have harctan_lt_half_pi : Real.arctan t < Real.pi / 2 :=
    Real.arctan_lt_pi_div_two t
  have hle_tan :
      Real.arctan t ≤ Real.tan (Real.arctan t) :=
    Real.le_tan harctan_nonneg harctan_lt_half_pi
  exact Eq.subst
    (motive := fun r : ℝ => Real.arctan t ≤ r)
    (Real.tan_arctan t)
    hle_tan

/-- Multiplicative form of `Real.arctan_le_self_of_nonneg` after the scale
change `t = u / |y|`. -/
theorem Real.norm_mul_arctan_div_norm_le_self_of_nonneg
    {u y : ℝ}
    (hu : 0 ≤ u) :
    ‖y‖ * Real.arctan (u / ‖y‖) ≤ u := by
  by_cases hy_zero : ‖y‖ = 0
  · have hleft_eq_zero :
        ‖y‖ * Real.arctan (u / ‖y‖) = 0 := by
      exact Eq.trans
        (congrArg (fun r : ℝ => r * Real.arctan (u / ‖y‖)) hy_zero)
        (zero_mul (Real.arctan (u / ‖y‖)))
    exact Eq.subst
      (motive := fun r : ℝ => r ≤ u)
      hleft_eq_zero.symm
      hu
  · have hy_pos : 0 < ‖y‖ :=
      lt_of_le_of_ne (norm_nonneg y) hy_zero.symm
    have hratio_nonneg : 0 ≤ u / ‖y‖ :=
      div_nonneg hu (le_of_lt hy_pos)
    have harctan_le : Real.arctan (u / ‖y‖) ≤ u / ‖y‖ :=
      Real.arctan_le_self_of_nonneg hratio_nonneg
    have hmul :
        ‖y‖ * Real.arctan (u / ‖y‖) ≤ ‖y‖ * (u / ‖y‖) :=
      mul_le_mul_of_nonneg_left harctan_le (le_of_lt hy_pos)
    have hcancel :
        ‖y‖ * (u / ‖y‖) = u :=
      mul_div_cancel₀ u hy_zero
    exact Eq.subst
      (motive := fun r : ℝ => ‖y‖ * Real.arctan (u / ‖y‖) ≤ r)
      hcancel.symm
      hmul

/-- Principal-argument formula for a right-half-plane ray above the real axis,
written in the reciprocal arctangent form suited to the linear defect estimate. -/
theorem Complex.arg_fixedRealPartVerticalPoint_of_pos_im_eq_pi_div_two_sub_arctan
    {u y : ℝ}
    (hu : 0 ≤ u)
    (hy : 0 < y) :
    Complex.arg (Complex.fixedRealPartVerticalPoint u y) =
      Real.pi / 2 - Real.arctan (u / y) := by
  let z : ℂ := Complex.fixedRealPartVerticalPoint u y
  by_cases hu_zero : u = 0
  · have hz_re_zero : z.re = 0 := by
      calc
        z.re = u := Complex.fixedRealPartVerticalPoint_re u y
        _ = 0 := hu_zero
    have hz_im_pos : 0 < z.im := by
      exact Eq.subst
        (motive := fun r : ℝ => 0 < r)
        (Complex.fixedRealPartVerticalPoint_im u y).symm
        hy
    have harg_axis : Complex.arg z = Real.pi / 2 :=
      Complex.arg_eq_pi_div_two_iff.mpr ⟨hz_re_zero, hz_im_pos⟩
    have hratio_zero : u / y = 0 := by
      calc
        u / y = 0 / y := congrArg (fun r : ℝ => r / y) hu_zero
        _ = 0 := zero_div y
    have hatan_zero : Real.arctan (u / y) = 0 :=
      Eq.trans (congrArg Real.arctan hratio_zero) Real.arctan_zero
    calc
      Complex.arg (Complex.fixedRealPartVerticalPoint u y) = Real.pi / 2 :=
        harg_axis
      _ = Real.pi / 2 - 0 := (sub_zero (Real.pi / 2)).symm
      _ = Real.pi / 2 - Real.arctan (u / y) := by
        exact congrArg (fun r : ℝ => Real.pi / 2 - r) hatan_zero.symm
  · have hu_pos : 0 < u :=
      lt_of_le_of_ne hu hu_zero.symm
    have hz_re_pos : 0 < z.re := by
      exact Eq.subst
        (motive := fun r : ℝ => 0 < r)
        (Complex.fixedRealPartVerticalPoint_re u y).symm
        hu_pos
    have hz_im_pos : 0 < z.im := by
      exact Eq.subst
        (motive := fun r : ℝ => 0 < r)
        (Complex.fixedRealPartVerticalPoint_im u y).symm
        hy
    have harg_gt_neg_half : -(Real.pi / 2) < Complex.arg z :=
      Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hz_re_pos)
    have harg_lt_half : Complex.arg z < Real.pi / 2 :=
      Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hz_re_pos)
    have htan_arg : Real.tan (Complex.arg z) = y / u := by
      calc
        Real.tan (Complex.arg z) = z.im / z.re := Complex.tan_arg z
        _ = y / z.re := by
          exact congrArg (fun r : ℝ => r / z.re)
            (Complex.fixedRealPartVerticalPoint_im u y)
        _ = y / u := by
          exact congrArg (fun r : ℝ => y / r)
            (Complex.fixedRealPartVerticalPoint_re u y)
    have harg_eq_atan : Real.arctan (y / u) = Complex.arg z :=
      Real.arctan_eq_of_tan_eq htan_arg
        ⟨harg_gt_neg_half, harg_lt_half⟩
    have hratio_pos : 0 < y / u :=
      div_pos hy hu_pos
    have hinv_eq : (y / u)⁻¹ = u / y :=
      inv_div
    have hrecip :
        Real.arctan (u / y) = Real.pi / 2 - Real.arctan (y / u) := by
      exact Eq.subst
        (motive := fun r : ℝ =>
          Real.arctan r = Real.pi / 2 - Real.arctan (y / u))
        hinv_eq
        (Real.arctan_inv_of_pos hratio_pos)
    have hswap :
        Real.arctan (y / u) = Real.pi / 2 - Real.arctan (u / y) := by
      have hsum :
          Real.arctan (u / y) + Real.arctan (y / u) = Real.pi / 2 := by
        exact (eq_sub_iff_add_eq.mp hrecip)
      exact (eq_sub_iff_add_eq.mpr hsum.symm)
    calc
      Complex.arg (Complex.fixedRealPartVerticalPoint u y) = Complex.arg z := rfl
      _ = Real.arctan (y / u) := harg_eq_atan.symm
      _ = Real.pi / 2 - Real.arctan (u / y) := hswap

/-- Principal-argument formula for a right-half-plane ray below the real axis,
written in the reciprocal arctangent form suited to the linear defect estimate. -/
theorem Complex.arg_fixedRealPartVerticalPoint_of_neg_im_eq_neg_pi_div_two_add_arctan
    {u y : ℝ}
    (hu : 0 ≤ u)
    (hy : y < 0) :
    Complex.arg (Complex.fixedRealPartVerticalPoint u y) =
      -(Real.pi / 2) + Real.arctan (u / ‖y‖) := by
  let z : ℂ := Complex.fixedRealPartVerticalPoint u y
  by_cases hu_zero : u = 0
  · have hz_re_zero : z.re = 0 := by
      calc
        z.re = u := Complex.fixedRealPartVerticalPoint_re u y
        _ = 0 := hu_zero
    have hz_im_neg : z.im < 0 := by
      exact Eq.subst
        (motive := fun r : ℝ => r < 0)
        (Complex.fixedRealPartVerticalPoint_im u y).symm
        hy
    have harg_axis : Complex.arg z = -(Real.pi / 2) :=
      Complex.arg_eq_neg_pi_div_two_iff.mpr ⟨hz_re_zero, hz_im_neg⟩
    have hratio_zero : u / ‖y‖ = 0 := by
      calc
        u / ‖y‖ = 0 / ‖y‖ := congrArg (fun r : ℝ => r / ‖y‖) hu_zero
        _ = 0 := zero_div ‖y‖
    have hatan_zero : Real.arctan (u / ‖y‖) = 0 :=
      Eq.trans (congrArg Real.arctan hratio_zero) Real.arctan_zero
    calc
      Complex.arg (Complex.fixedRealPartVerticalPoint u y) = -(Real.pi / 2) :=
        harg_axis
      _ = -(Real.pi / 2) + 0 := (add_zero (-(Real.pi / 2))).symm
      _ = -(Real.pi / 2) + Real.arctan (u / ‖y‖) := by
        exact congrArg (fun r : ℝ => -(Real.pi / 2) + r) hatan_zero.symm
  · have hu_pos : 0 < u :=
      lt_of_le_of_ne hu hu_zero.symm
    have hy_norm_pos : 0 < ‖y‖ :=
      Real.norm_pos_iff.mpr (ne_of_lt hy)
    have hz_re_pos : 0 < z.re := by
      exact Eq.subst
        (motive := fun r : ℝ => 0 < r)
        (Complex.fixedRealPartVerticalPoint_re u y).symm
        hu_pos
    have hz_im_neg : z.im < 0 := by
      exact Eq.subst
        (motive := fun r : ℝ => r < 0)
        (Complex.fixedRealPartVerticalPoint_im u y).symm
        hy
    have harg_gt_neg_half : -(Real.pi / 2) < Complex.arg z :=
      Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hz_re_pos)
    have harg_lt_half : Complex.arg z < Real.pi / 2 :=
      Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hz_re_pos)
    have hy_eq_neg_norm : y = -‖y‖ := by
      have hnorm : ‖y‖ = -y :=
        Real.norm_of_nonpos (le_of_lt hy)
      exact hnorm.symm ▸ rfl
    have htan_arg : Real.tan (Complex.arg z) = y / u := by
      calc
        Real.tan (Complex.arg z) = z.im / z.re := Complex.tan_arg z
        _ = y / z.re := by
          exact congrArg (fun r : ℝ => r / z.re)
            (Complex.fixedRealPartVerticalPoint_im u y)
        _ = y / u := by
          exact congrArg (fun r : ℝ => y / r)
            (Complex.fixedRealPartVerticalPoint_re u y)
    have harg_eq_atan : Real.arctan (y / u) = Complex.arg z :=
      Real.arctan_eq_of_tan_eq htan_arg
        ⟨harg_gt_neg_half, harg_lt_half⟩
    have hatan_neg_norm :
        Real.arctan (y / u) = -Real.arctan (‖y‖ / u) := by
      have hdiv_eq : y / u = -(‖y‖ / u) := by
        calc
          y / u = (-‖y‖) / u := congrArg (fun r : ℝ => r / u) hy_eq_neg_norm
          _ = -(‖y‖ / u) := neg_div ‖y‖ u
      exact Eq.trans
        (congrArg Real.arctan hdiv_eq)
        (Real.arctan_neg (‖y‖ / u))
    have hratio_pos : 0 < ‖y‖ / u :=
      div_pos hy_norm_pos hu_pos
    have hinv_eq : (‖y‖ / u)⁻¹ = u / ‖y‖ :=
      inv_div
    have hrecip :
        Real.arctan (u / ‖y‖) =
          Real.pi / 2 - Real.arctan (‖y‖ / u) := by
      exact Eq.subst
        (motive := fun r : ℝ =>
          Real.arctan r = Real.pi / 2 - Real.arctan (‖y‖ / u))
        hinv_eq
        (Real.arctan_inv_of_pos hratio_pos)
    have hneg_atan_eq :
        -Real.arctan (‖y‖ / u) =
          -(Real.pi / 2) + Real.arctan (u / ‖y‖) := by
      calc
        -Real.arctan (‖y‖ / u) =
            -(Real.pi / 2 - Real.arctan (u / ‖y‖)) := by
          have hswap :
              Real.arctan (‖y‖ / u) =
                Real.pi / 2 - Real.arctan (u / ‖y‖) := by
            have hsum :
                Real.arctan (u / ‖y‖) + Real.arctan (‖y‖ / u) =
                  Real.pi / 2 :=
              eq_sub_iff_add_eq.mp hrecip
            exact eq_sub_iff_add_eq.mpr hsum.symm
          exact congrArg Neg.neg hswap
        _ = -(Real.pi / 2) + Real.arctan (u / ‖y‖) := by
          exact neg_sub (Real.pi / 2) (Real.arctan (u / ‖y‖))
    calc
      Complex.arg (Complex.fixedRealPartVerticalPoint u y) = Complex.arg z := rfl
      _ = Real.arctan (y / u) := harg_eq_atan.symm
      _ = -Real.arctan (‖y‖ / u) := hatan_neg_norm
      _ = -(Real.pi / 2) + Real.arctan (u / ‖y‖) := hneg_atan_eq

/-- Exact arctangent form of the principal-argument defect on the ray `u + i y`
inside the closed right half-plane. -/
theorem Complex.rightHalfPlaneVertical_arg_linear_defect_abs_eq_norm_mul_arctan
    {u y : ℝ}
    (hu : 0 ≤ u) :
    |(Real.pi / 2) * ‖y‖ -
        Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y| =
      ‖y‖ * Real.arctan (u / ‖y‖) := by
  rcases lt_trichotomy y 0 with hy_neg | hy_zero | hy_pos
  · let n : ℝ := ‖y‖
    let a : ℝ := Real.arctan (u / n)
    let p : ℝ := Real.pi / 2
    have hn_pos : 0 < n :=
      Real.norm_pos_iff.mpr (ne_of_lt hy_neg)
    have hy_eq_neg_n : y = -n := by
      have hnorm : ‖y‖ = -y :=
        Real.norm_of_nonpos (le_of_lt hy_neg)
      have hneg_norm : -n = y := by
        calc
          -n = -‖y‖ := rfl
          _ = -(-y) := congrArg Neg.neg hnorm
          _ = y := neg_neg y
      exact hneg_norm.symm
    have harg :
        Complex.arg (Complex.fixedRealPartVerticalPoint u y) = -p + a :=
      Complex.arg_fixedRealPartVerticalPoint_of_neg_im_eq_neg_pi_div_two_add_arctan
        hu hy_neg
    have ha_nonneg : 0 ≤ a := by
      have hratio_nonneg : 0 ≤ u / n :=
        div_nonneg hu (le_of_lt hn_pos)
      have hzero_le :
          Real.arctan 0 ≤ Real.arctan (u / n) :=
        Real.arctan_strictMono.monotone hratio_nonneg
      exact Eq.subst
        (motive := fun r : ℝ => r ≤ a)
        Real.arctan_zero
        hzero_le
    have hprod_nonneg : 0 ≤ a * n :=
      mul_nonneg ha_nonneg (le_of_lt hn_pos)
    have harg_mul :
        Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y =
          p * n - a * n := by
      calc
        Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y =
            (-p + a) * (-n) := by
          exact congrArg₂
            (fun r s : ℝ => r * s)
            harg
            hy_eq_neg_n
        _ = -((-p + a) * n) := by
          exact mul_neg (-p + a) n
        _ = -((-p) * n + a * n) := by
          exact congrArg Neg.neg (add_mul (-p) a n)
        _ = -((-p) * n) + -(a * n) := by
          exact neg_add ((-p) * n) (a * n)
        _ = p * n + -(a * n) := by
          have hneg_left : -((-p) * n) = p * n := by
            calc
              -((-p) * n) = -(-(p * n)) := by
                exact congrArg Neg.neg (neg_mul p n)
              _ = p * n := neg_neg (p * n)
          exact congrArg (fun r : ℝ => r + -(a * n)) hneg_left
        _ = p * n - a * n := (sub_eq_add_neg (p * n) (a * n)).symm
    have hinside :
        (Real.pi / 2) * ‖y‖ -
            Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y =
          a * n := by
      calc
        (Real.pi / 2) * ‖y‖ -
            Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y =
            p * n - (p * n - a * n) := by
          exact congrArg₂
            (fun r s : ℝ => r - s)
            rfl
            harg_mul
        _ = a * n := sub_sub_self (p * n) (a * n)
    calc
      |(Real.pi / 2) * ‖y‖ -
          Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y| =
          |a * n| := congrArg abs hinside
      _ = a * n := abs_of_nonneg hprod_nonneg
      _ = n * a := mul_comm a n
      _ = ‖y‖ * Real.arctan (u / ‖y‖) := rfl
  · have hy_subst : y = 0 := hy_zero
    subst y
    have hnorm_zero : ‖(0 : ℝ)‖ = 0 :=
      norm_zero
    calc
      |(Real.pi / 2) * ‖(0 : ℝ)‖ -
          Complex.arg (Complex.fixedRealPartVerticalPoint u 0) * (0 : ℝ)| =
          |(Real.pi / 2) * 0 -
            Complex.arg (Complex.fixedRealPartVerticalPoint u 0) * (0 : ℝ)| := by
        exact congrArg
          (fun r : ℝ =>
            |(Real.pi / 2) * r -
              Complex.arg (Complex.fixedRealPartVerticalPoint u 0) * (0 : ℝ)|)
          hnorm_zero
      _ = |0 - 0| := by
        have hleft : (Real.pi / 2) * (0 : ℝ) = 0 :=
          mul_zero (Real.pi / 2)
        have hright :
            Complex.arg (Complex.fixedRealPartVerticalPoint u 0) * (0 : ℝ) = 0 :=
          mul_zero (Complex.arg (Complex.fixedRealPartVerticalPoint u 0))
        exact congrArg₂ (fun r s : ℝ => |r - s|) hleft hright
      _ = 0 := by
        exact Eq.trans (congrArg abs (sub_zero (0 : ℝ))) abs_zero
      _ = ‖(0 : ℝ)‖ * Real.arctan (u / ‖(0 : ℝ)‖) := by
        have hright :
            ‖(0 : ℝ)‖ * Real.arctan (u / ‖(0 : ℝ)‖) = 0 := by
          exact Eq.trans
            (congrArg
              (fun r : ℝ => r * Real.arctan (u / ‖(0 : ℝ)‖))
              hnorm_zero)
            (zero_mul (Real.arctan (u / ‖(0 : ℝ)‖)))
        exact hright.symm
  · let n : ℝ := ‖y‖
    let a : ℝ := Real.arctan (u / y)
    let p : ℝ := Real.pi / 2
    have hn_eq_y : n = y :=
      Real.norm_of_nonneg (le_of_lt hy_pos)
    have hn_pos : 0 < n :=
      Eq.subst
        (motive := fun r : ℝ => 0 < r)
        hn_eq_y.symm
        hy_pos
    have harg :
        Complex.arg (Complex.fixedRealPartVerticalPoint u y) = p - a :=
      Complex.arg_fixedRealPartVerticalPoint_of_pos_im_eq_pi_div_two_sub_arctan
        hu hy_pos
    have ha_nonneg : 0 ≤ a := by
      have hratio_nonneg : 0 ≤ u / y :=
        div_nonneg hu (le_of_lt hy_pos)
      have hzero_le :
          Real.arctan 0 ≤ Real.arctan (u / y) :=
        Real.arctan_strictMono.monotone hratio_nonneg
      exact Eq.subst
        (motive := fun r : ℝ => r ≤ a)
        Real.arctan_zero
        hzero_le
    have hprod_nonneg : 0 ≤ a * y :=
      mul_nonneg ha_nonneg (le_of_lt hy_pos)
    have harg_mul :
        Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y =
          p * y - a * y := by
      calc
        Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y =
            (p - a) * y := by
          exact congrArg (fun r : ℝ => r * y) harg
        _ = p * y - a * y := sub_mul p a y
    have hinside :
        (Real.pi / 2) * ‖y‖ -
            Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y =
          a * y := by
      calc
        (Real.pi / 2) * ‖y‖ -
            Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y =
            p * y - (p * y - a * y) := by
          have hleft : (Real.pi / 2) * ‖y‖ = p * y := by
            exact congrArg (fun r : ℝ => (Real.pi / 2) * r) hn_eq_y
          exact congrArg₂ (fun r s : ℝ => r - s) hleft harg_mul
        _ = a * y := sub_sub_self (p * y) (a * y)
    calc
      |(Real.pi / 2) * ‖y‖ -
          Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y| =
          |a * y| := congrArg abs hinside
      _ = a * y := abs_of_nonneg hprod_nonneg
      _ = y * a := mul_comm a y
      _ = ‖y‖ * Real.arctan (u / ‖y‖) := by
        have harg_eq : a = Real.arctan (u / ‖y‖) := by
          exact congrArg (fun r : ℝ => Real.arctan (u / r)) hn_eq_y.symm
        exact congrArg₂ (fun r s : ℝ => r * s) hn_eq_y.symm harg_eq

/-- Principal-argument defect on a right-half-plane vertical ray.

For `u ≥ 0`, the angle of `u + i y` differs from `sign(y) · π/2` by at most
`u / |y|`; multiplying by `|y|` gives the displayed scale-free bound.  This is
the canonical `arg` geometry lemma behind the shifted-strip exponential defect. -/
theorem Complex.rightHalfPlaneVertical_arg_linear_defect_abs_le_re
    {u y : ℝ}
    (hu : 0 ≤ u) :
    |(Real.pi / 2) * ‖y‖ -
        Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y| ≤ u := by
  have hdef_eq :
      |(Real.pi / 2) * ‖y‖ -
          Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y| =
        ‖y‖ * Real.arctan (u / ‖y‖) :=
    Complex.rightHalfPlaneVertical_arg_linear_defect_abs_eq_norm_mul_arctan hu
  exact Eq.subst
    (motive := fun r : ℝ => r ≤ u)
    hdef_eq.symm
    (Real.norm_mul_arctan_div_norm_le_self_of_nonneg hu)

/-- Additive quantitative argument-defect estimate for shifted right-half-plane
vertical strips.

This is the exact arctangent-defect form behind the exponential comparison:
`-arg(w) y` differs from `-(π/2)|y|` by a bounded amount on every shifted
bounded vertical strip. -/
theorem Complex.shiftedVertical_arg_linear_defect_bounded
    (A B : ℝ) :
    ∃ H : ℝ, ∃ D : ℝ,
      0 < H ∧
      0 ≤ D ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          let w : ℂ :=
            Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y
          -(Complex.arg w * y) ≤ D + (-(Real.pi / 2) * ‖y‖) ∧
          (-(Real.pi / 2) * ‖y‖) - D ≤ -(Complex.arg w * y) := by
  let D : ℝ :=
    max |A + Complex.verticalStripTransportShift A|
      |B + Complex.verticalStripTransportShift A|
  refine ⟨1, D, zero_lt_one, ?_, ?_⟩
  · exact le_trans (abs_nonneg (A + Complex.verticalStripTransportShift A))
      (le_max_left
        |A + Complex.verticalStripTransportShift A|
        |B + Complex.verticalStripTransportShift A|)
  intro x y hxA hxB _hy
  let u : ℝ := x + Complex.verticalStripTransportShift A
  let w : ℂ :=
    Complex.fixedRealPartVerticalPoint
      (x + Complex.verticalStripTransportShift A) y
  have hu_nonneg : 0 ≤ u := by
    unfold Complex.verticalStripTransportShift
    have hshift : -A ≤ (Complex.verticalStripRightShift A : ℝ) :=
      Complex.neg_lower_le_verticalStripRightShift A
    calc
      0 = A + -A := by
        exact (add_right_neg A).symm
      _ ≤ x + (Complex.verticalStripRightShift A : ℝ) :=
        add_le_add hxA hshift
  have hu_abs_le_D : |u| ≤ D := by
    exact real_abs_le_max_abs_of_mem_Icc
      (add_le_add_right hxA (Complex.verticalStripTransportShift A))
      (add_le_add_right hxB (Complex.verticalStripTransportShift A))
  have hu_le_D : u ≤ D :=
    le_trans (le_abs_self u) hu_abs_le_D
  have hdef_abs :
      |(Real.pi / 2) * ‖y‖ - Complex.arg w * y| ≤ D := by
    have hray :
        |(Real.pi / 2) * ‖y‖ -
            Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y| ≤ u :=
      Complex.rightHalfPlaneVertical_arg_linear_defect_abs_le_re hu_nonneg
    exact le_trans hray hu_le_D
  have hdef_upper :
      (Real.pi / 2) * ‖y‖ - Complex.arg w * y ≤ D :=
    le_trans (le_abs_self ((Real.pi / 2) * ‖y‖ - Complex.arg w * y))
      hdef_abs
  have hdef_lower :
      -D ≤ (Real.pi / 2) * ‖y‖ - Complex.arg w * y := by
    have hneg_abs :
        -|(Real.pi / 2) * ‖y‖ - Complex.arg w * y| ≤
          (Real.pi / 2) * ‖y‖ - Complex.arg w * y :=
      neg_abs_le ((Real.pi / 2) * ‖y‖ - Complex.arg w * y)
    have hneg_bound :
        -D ≤ -|(Real.pi / 2) * ‖y‖ - Complex.arg w * y| :=
      neg_le_neg hdef_abs
    exact le_trans hneg_bound hneg_abs
  constructor
  · have htarget :
        - (Complex.arg w * y) ≤
          D + (-(Real.pi / 2) * ‖y‖) := by
      calc
        -(Complex.arg w * y) =
            ((Real.pi / 2) * ‖y‖ - Complex.arg w * y) +
              (-(Real.pi / 2) * ‖y‖) := by
          exact (add_neg_cancel_left ((Real.pi / 2) * ‖y‖)
            (-(Complex.arg w * y))).symm
        _ ≤ D + (-(Real.pi / 2) * ‖y‖) :=
          add_le_add_right hdef_upper (-(Real.pi / 2) * ‖y‖)
    exact htarget
  · have htarget :
        (-(Real.pi / 2) * ‖y‖) - D ≤
          -(Complex.arg w * y) := by
      calc
        (-(Real.pi / 2) * ‖y‖) - D =
            -D + (-(Real.pi / 2) * ‖y‖) := by
          calc
            (-(Real.pi / 2) * ‖y‖) - D =
                (-(Real.pi / 2) * ‖y‖) + -D :=
              sub_eq_add_neg (-(Real.pi / 2) * ‖y‖) D
            _ = -D + (-(Real.pi / 2) * ‖y‖) :=
              add_comm (-(Real.pi / 2) * ‖y‖) (-D)
        _ ≤ ((Real.pi / 2) * ‖y‖ - Complex.arg w * y) +
              (-(Real.pi / 2) * ‖y‖) :=
          add_le_add_right hdef_lower (-(Real.pi / 2) * ‖y‖)
        _ = -(Complex.arg w * y) := by
          exact add_neg_cancel_left ((Real.pi / 2) * ‖y‖)
            (-(Complex.arg w * y))
    exact htarget

/-- Quantitative arctangent-defect comparison for shifted right-half-plane
vertical strips.

For `w = x + N + i y` with `x` in a fixed bounded strip and `N` the deterministic
right-half-plane shift, the classical estimate
`|arg w - sign(y) · π/2| = O(1 / |y|)` gives a bounded multiplicative loss in
`exp (-arg(w) y)`.  This is the precise geometric input needed by the normalized
Stirling denominator comparison. -/
theorem Complex.shiftedVertical_arg_exponential_defect_comparable_quantitative
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
              (x + Complex.verticalStripTransportShift A) y
          Real.exp (-(Complex.arg w * y)) ≤
            C * Real.exp (-(Real.pi / 2) * ‖y‖) ∧
          c * Real.exp (-(Real.pi / 2) * ‖y‖) ≤
            Real.exp (-(Complex.arg w * y)) := by
  rcases Complex.shiftedVertical_arg_linear_defect_bounded A B with
    ⟨H, D, hH_pos, hD_nonneg, hdefect⟩
  refine ⟨H, Real.exp D, Real.exp (-D), hH_pos,
    Real.exp_pos D, Real.exp_pos (-D), ?_⟩
  intro x y hxA hxB hy
  let w : ℂ :=
    Complex.fixedRealPartVerticalPoint
      (x + Complex.verticalStripTransportShift A) y
  let b : ℝ := -(Real.pi / 2) * ‖y‖
  have hdef := hdefect x y hxA hxB hy
  constructor
  · have hexp_le :
        Real.exp (-(Complex.arg w * y)) ≤ Real.exp (D + b) :=
      Real.exp_le_exp.mpr hdef.1
    have hsplit :
        Real.exp (D + b) =
          Real.exp D * Real.exp b :=
      Real.exp_add D b
    exact le_trans hexp_le
      (le_of_eq
        (Eq.trans hsplit
          (by
            rfl)))
  · have hlower_exp :
        Real.exp (b - D) ≤ Real.exp (-(Complex.arg w * y)) :=
      Real.exp_le_exp.mpr hdef.2
    have hsplit :
        Real.exp (b - D) =
          Real.exp (-D) * Real.exp b := by
      calc
        Real.exp (b - D) =
            Real.exp (b + -D) := by
          exact congrArg Real.exp (sub_eq_add_neg b D)
        _ = Real.exp b * Real.exp (-D) :=
          Real.exp_add b (-D)
        _ = Real.exp (-D) * Real.exp b :=
          mul_comm (Real.exp b) (Real.exp (-D))
    exact le_trans (le_of_eq hsplit.symm) hlower_exp

/-- Quantitative vertical argument-defect estimate for shifted right-half-plane
strip points.

This is the real geometric core of the denominator comparison.  In a fixed
right-half-plane vertical strip, the principal argument approaches
`sign(y) * π/2`, and the defect contributes only a bounded exponential factor
to `exp (-arg(w) y)`. -/
theorem Complex.shiftedVertical_arg_exponential_defect_comparable
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
              (x + Complex.verticalStripTransportShift A) y
          Real.exp (-(Complex.arg w * y)) ≤
            C * Real.exp (-(Real.pi / 2) * ‖y‖) ∧
          c * Real.exp (-(Real.pi / 2) * ‖y‖) ≤
            Real.exp (-(Complex.arg w * y)) := by
  exact
    Complex.shiftedVertical_arg_exponential_defect_comparable_quantitative
      A B

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
              (x + Complex.verticalStripTransportShift A) y
          ‖w‖ ≤ C * (1 + ‖y‖) ∧
          c * (1 + ‖y‖) ≤ ‖w‖ := by
  rcases
      Complex.gammaRecurrenceProduct_factor_upper_on_verticalStrip
        (A + Complex.verticalStripTransportShift A)
        (B + Complex.verticalStripTransportShift A)
        1 with
    ⟨C, hC_pos, hupper⟩
  refine ⟨1, C, 1 / 2, zero_lt_one, hC_pos, one_div_pos.mpr two_pos, ?_⟩
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
          (x + Complex.verticalStripTransportShift A) y + (0 : ℂ)‖ ≤
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
    Eq.subst
      (motive := fun z : ℂ => ‖z‖ ≤ C * (1 + ‖y‖))
      hzero_add
      hupper_w
  have hlower_final :
      (1 / 2 : ℝ) * (1 + ‖y‖) ≤ ‖w‖ := by
    have hlower_raw :
        (1 / 2 : ℝ) * (1 + ‖y‖) ≤
          ‖Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y + (0 : ℂ)‖ :=
      Complex.gammaRecurrenceProduct_factor_largeHeight_lower 0 hy
    exact
      Eq.subst
        (motive := fun z : ℂ =>
          (1 / 2 : ℝ) * (1 + ‖y‖) ≤ ‖z‖)
        hzero_add
        hlower_raw
  exact ⟨hupper_final, hlower_final⟩

/-- Real bounded-exponent transport for radius powers.

If `R` is uniformly comparable to the height scale `Y`, and the exponent `e`
stays in a fixed bounded interval, then `R^e` is uniformly comparable to
`Y^e`.  This is the purely real step needed after the shifted-strip radius
comparison has removed all complex geometry. -/
theorem real_rpow_comparable_of_base_comparable_and_bounded_exponent
    (C c L U : ℝ)
    (hC_pos : 0 < C)
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
  refine ⟨K, k, Real.exp_pos (E * M), Real.exp_pos (-(E * M)), ?_⟩
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
    by_cases hlog_nonneg : 0 ≤ Real.log q
    · have hlog_le_C : Real.log q ≤ Real.log C :=
        Real.log_le_log hq_pos hq_upper
      have hlog_abs_eq : |Real.log q| = Real.log q :=
        abs_of_nonneg hlog_nonneg
      have hC_le_abs : Real.log C ≤ |Real.log C| :=
        le_abs_self (Real.log C)
      calc
        |Real.log q| = Real.log q := hlog_abs_eq
        _ ≤ Real.log C := hlog_le_C
        _ ≤ |Real.log C| := hC_le_abs
        _ ≤ |Real.log c| + |Real.log C| :=
          le_add_of_nonneg_left (abs_nonneg (Real.log c))
    · have hlog_nonpos : Real.log q ≤ 0 :=
        le_of_not_ge hlog_nonneg
      have hlog_c_le : Real.log c ≤ Real.log q :=
        Real.log_le_log hc_pos hq_lower
      have hneg_le : -Real.log q ≤ -Real.log c :=
        neg_le_neg hlog_c_le
      have hneg_c_le_abs : -Real.log c ≤ |Real.log c| :=
        neg_le_abs (Real.log c)
      have hlog_abs_eq : |Real.log q| = -Real.log q :=
        abs_of_nonpos hlog_nonpos
      calc
        |Real.log q| = -Real.log q := hlog_abs_eq
        _ ≤ -Real.log c := hneg_le
        _ ≤ |Real.log c| := hneg_c_le_abs
        _ ≤ |Real.log c| + |Real.log C| :=
          le_add_of_nonneg_right (abs_nonneg (Real.log C))
  have hmul_abs :
      |e * Real.log q| ≤ E * M := by
    calc
      |e * Real.log q| = |e| * |Real.log q| :=
        abs_mul e (Real.log q)
      _ ≤ E * M :=
        mul_le_mul he_abs hlog_abs hM_nonneg (abs_nonneg e)
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
    exact Eq.subst
      (motive := fun t : ℝ => t ≤ K)
      hq_pow_eq.symm
      (Eq.subst
        (motive := fun t : ℝ => Real.exp t ≤ K)
        hcomm
        (Real.exp_le_exp.mpr hupper_exp_arg))
  have hq_pow_lower : k ≤ q ^ e := by
    have hq_pow_eq : q ^ e = Real.exp (Real.log q * e) :=
      Real.rpow_def_of_pos hq_pos e
    have hcomm : Real.log q * e = e * Real.log q :=
      mul_comm (Real.log q) e
    exact Eq.subst
      (motive := fun t : ℝ => k ≤ t)
      hq_pow_eq.symm
      (Eq.subst
        (motive := fun t : ℝ => k ≤ Real.exp t)
        hcomm
        (Real.exp_le_exp.mpr hlower_exp_arg))
  have hY_pow_nonneg : 0 ≤ Y ^ e :=
    Real.rpow_nonneg hY_nonneg e
  have hR_pow_eq : R ^ e = q ^ e * Y ^ e := by
    calc
      R ^ e = (q * Y) ^ e := by
        exact congrArg (fun t : ℝ => t ^ e) hR_eq
      _ = q ^ e * Y ^ e :=
        Real.mul_rpow hq_nonneg hY_nonneg
  constructor
  · exact Eq.subst
      (motive := fun t : ℝ => t ≤ K * Y ^ e)
      hR_pow_eq.symm
      (mul_le_mul_of_nonneg_right hq_pow_upper hY_pow_nonneg)
  · exact Eq.subst
      (motive := fun t : ℝ => k * Y ^ e ≤ t)
      hR_pow_eq.symm
      (mul_le_mul_of_nonneg_right hq_pow_lower hY_pow_nonneg)

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
              (x + Complex.verticalStripTransportShift A) y
          ‖w‖ ^ (w.re - 1 / 2) ≤
            C * (1 + ‖y‖) ^ (x + Complex.verticalStripTransportShift A - 1 / 2) ∧
          c * (1 + ‖y‖) ^ (x + Complex.verticalStripTransportShift A - 1 / 2) ≤
            ‖w‖ ^ (w.re - 1 / 2) := by
  rcases Complex.shiftedVertical_radius_base_comparable A B with
    ⟨Hbase, Cbase, cbase, hHbase_pos, hCbase_pos, hcbase_pos, hbase⟩
  let L : ℝ := A + Complex.verticalStripTransportShift A - 1 / 2
  let U : ℝ := B + Complex.verticalStripTransportShift A - 1 / 2
  rcases
      real_rpow_comparable_of_base_comparable_and_bounded_exponent
        Cbase cbase L U hCbase_pos hcbase_pos with
    ⟨K, k, hK_pos, hk_pos, hrpow⟩
  refine ⟨Hbase, K, k, hHbase_pos, hK_pos, hk_pos, ?_⟩
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
    ⟨Eq.subst
        (motive := fun t : ℝ =>
          ‖w‖ ^ t ≤ K * Y ^ e)
        heq.symm
        hr.1,
      Eq.subst
        (motive := fun t : ℝ =>
          k * Y ^ e ≤ ‖w‖ ^ t)
        heq.symm
        hr.2⟩

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
              (x + Complex.verticalStripTransportShift A) y
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
              (x + Complex.verticalStripTransportShift A) y
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
  refine ⟨C, c, hC_pos, hc_pos, ?_⟩
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
    ⟨Eq.subst
        (motive := fun t : ℝ => Real.exp (-t) ≤ C)
        hw_re.symm
        hexp_upper,
      Eq.subst
        (motive := fun t : ℝ => c ≤ Real.exp (-t))
        hw_re.symm
        hexp_lower⟩

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

/-- Exact reciprocal shape of the normalized-Stirling denominator on a fixed
vertical point, after expanding `‖exp w‖` and the principal-branch power norm. -/
theorem Complex.stirlingDenominator_reciprocal_shape_fixedVertical
    {w : ℂ}
    {y : ℝ}
    (hw_ne : w ≠ 0)
    (hw_im : w.im = y) :
    1 / (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) =
      Real.exp (-(Complex.arg w * y)) *
        ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) := by
  have hR_pos : 0 < ‖w‖ :=
    norm_pos_iff.mpr hw_ne
  have hexp_norm :
      ‖Complex.exp w‖ = Real.exp w.re :=
    Complex.norm_exp_eq_exp_re w
  have hre_exp :
      ((1 / 2 : ℂ) - w).re = 1 / 2 - w.re :=
    Complex.half_minus_self_re w
  have him_exp :
      ((1 / 2 : ℂ) - w).im = -y := by
    exact Eq.trans (Complex.half_minus_self_im w) (congrArg Neg.neg hw_im)
  have hcpow_norm :
      ‖w ^ ((1 / 2 : ℂ) - w)‖ =
        ‖w‖ ^ (1 / 2 - w.re) /
          Real.exp (Complex.arg w * (-y)) := by
    have hraw :
        ‖w ^ ((1 / 2 : ℂ) - w)‖ =
          ‖w‖ ^ (((1 / 2 : ℂ) - w).re) /
            Real.exp (Complex.arg w * (((1 / 2 : ℂ) - w).im)) :=
      Complex.norm_cpow_eq_norm_rpow_div_exp_arg_mul_im_of_ne_zero hw_ne
    exact Eq.trans hraw
      (congrArg₂ HDiv.hDiv
        (congrArg (fun t : ℝ => ‖w‖ ^ t) hre_exp)
        (congrArg (fun t : ℝ => Real.exp (Complex.arg w * t)) him_exp))
  calc
    1 / (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) =
        1 / (Real.exp w.re *
          (‖w‖ ^ (1 / 2 - w.re) /
            Real.exp (Complex.arg w * (-y)))) := by
      exact congrArg
        (fun t : ℝ => 1 / t)
        (congrArg₂ HMul.hMul hexp_norm hcpow_norm)
    _ =
        Real.exp (-(Complex.arg w * y)) *
          ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) :=
      real_stirlingDenominator_reciprocal_shape
        ‖w‖ w.re (Complex.arg w) y hR_pos

/-- Reciprocal denominator comparison for the shifted vertical Stirling
normalization.

For `w = x + N + i y` in a fixed shifted right-half-plane strip, the
principal-branch identity
`log ‖w^(1/2-w)‖ = (1/2 - Re w) log ‖w‖ + arg(w) Im w`, together with
`‖exp w‖ = exp (Re w)`, shows that
`1 / (‖exp w‖ ‖w^(1/2-w)‖)` is comparable to
`exp (-π |y| / 2) (1 + |y|)^(Re w - 1/2)`.  This is the sharp vertical-line
branch comparison left after the normalized sectorial Stirling estimate has
been extracted. -/
theorem Complex.shiftedVerticalStirlingDenominator_reciprocal_comparable
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
              (x + Complex.verticalStripTransportShift A) y
          0 < ‖Complex.exp w‖ *
                ‖w ^ ((1 / 2 : ℂ) - w)‖ ∧
          1 / (‖Complex.exp w‖ *
                ‖w ^ ((1 / 2 : ℂ) - w)‖) ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope
              (x + Complex.verticalStripTransportShift A) y ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope
              (x + Complex.verticalStripTransportShift A) y ≤
            1 / (‖Complex.exp w‖ *
                ‖w ^ ((1 / 2 : ℂ) - w)‖) := by
  rcases Complex.shiftedVertical_arg_exponential_defect_comparable A B with
    ⟨Ha, Ca, ca, hHa_pos, hCa_pos, hca_pos, harg⟩
  rcases Complex.shiftedVertical_radiusPower_comparable A B with
    ⟨Hr, Cr, cr, hHr_pos, hCr_pos, hcr_pos, hradius⟩
  rcases Complex.shiftedVertical_realPartExp_bounded A B with
    ⟨Ce, ce, hCe_pos, hce_pos, hexpRe⟩
  let H : ℝ := max Ha Hr
  refine ⟨H, (Ca * Cr) * Ce, (ca * cr) * ce,
    lt_of_lt_of_le hHa_pos (le_max_left Ha Hr),
    mul_pos (mul_pos hCa_pos hCr_pos) hCe_pos,
    mul_pos (mul_pos hca_pos hcr_pos) hce_pos, ?_⟩
  intro x y hxA hxB hy
  have hy_a : Ha ≤ ‖y‖ :=
    le_trans (le_max_left Ha Hr) hy
  have hy_r : Hr ≤ ‖y‖ :=
    le_trans (le_max_right Ha Hr) hy
  let w : ℂ :=
    Complex.fixedRealPartVerticalPoint
      (x + Complex.verticalStripTransportShift A) y
  let Eexp : ℝ := Real.exp (-(Real.pi / 2) * ‖y‖)
  let P : ℝ := (1 + ‖y‖) ^
    (x + Complex.verticalStripTransportShift A - 1 / 2)
  have harg_xy := harg x y hxA hxB hy_a
  have hradius_xy := hradius x y hxA hxB hy_r
  have hexpRe_xy := hexpRe x y hxA hxB
  have hw_re :
      w.re = x + Complex.verticalStripTransportShift A :=
    Complex.fixedRealPartVerticalPoint_re
      (x + Complex.verticalStripTransportShift A) y
  have hw_ne : w ≠ 0 := by
    have hH_pos : 0 < H :=
      lt_of_lt_of_le hHa_pos (le_max_left Ha Hr)
    have hw_norm_pos : 0 < ‖w‖ :=
      lt_of_lt_of_le hH_pos
        (Complex.verticalStripTransportShift_radius_ge_of_height_ge hy)
    exact norm_pos_iff.mp hw_norm_pos
  have hden_pos :
      0 < ‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖ :=
    Complex.stirlingDenominator_pos_of_ne_zero hw_ne
  have hcpow_norm :
      ‖w ^ ((1 / 2 : ℂ) - w)‖ =
        ‖w‖ ^ (((1 / 2 : ℂ) - w).re) /
          Real.exp (Complex.arg w * (((1 / 2 : ℂ) - w).im)) :=
    Complex.norm_cpow_eq_norm_rpow_div_exp_arg_mul_im_of_ne_zero hw_ne
  have hreciprocal_shape :
      1 / (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) =
        Real.exp (-(Complex.arg w * y)) *
          ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) := by
    exact
      Complex.stirlingDenominator_reciprocal_shape_fixedVertical
        hw_ne
        (Complex.fixedRealPartVerticalPoint_im
          (x + Complex.verticalStripTransportShift A) y)
  constructor
  · exact hden_pos
  constructor
  · have hrad_upper :
        ‖w‖ ^ (w.re - 1 / 2) ≤ Cr * P := by
      exact Eq.subst
        (motive := fun t : ℝ => ‖w‖ ^ (t - 1 / 2) ≤ Cr * P)
        hw_re.symm
        hradius_xy.1
    have harg_upper :
        Real.exp (-(Complex.arg w * y)) ≤ Ca * Eexp :=
      harg_xy.1
    have hexpRe_upper :
        Real.exp (-w.re) ≤ Ce :=
      hexpRe_xy.1
    have hshape_bound :
        Real.exp (-(Complex.arg w * y)) *
            ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) ≤
          ((Ca * Cr) * Ce) *
            (Eexp * P) := by
      have harg_nonneg :
          0 ≤ Real.exp (-(Complex.arg w * y)) :=
        le_of_lt (Real.exp_pos (-(Complex.arg w * y)))
      have hrad_nonneg :
          0 ≤ ‖w‖ ^ (w.re - 1 / 2) :=
        Real.rpow_nonneg (norm_nonneg w) (w.re - 1 / 2)
      have hexpRe_nonneg :
          0 ≤ Real.exp (-w.re) :=
        le_of_lt (Real.exp_pos (-w.re))
      have hEexp_nonneg : 0 ≤ Eexp :=
        le_of_lt (Real.exp_pos (-(Real.pi / 2) * ‖y‖))
      have hP_nonneg : 0 ≤ P :=
        Real.rpow_nonneg (add_nonneg zero_le_one (norm_nonneg y))
          (x + Complex.verticalStripTransportShift A - 1 / 2)
      have hCrP_nonneg : 0 ≤ Cr * P :=
        mul_nonneg (le_of_lt hCr_pos) hP_nonneg
      have hCaE_nonneg : 0 ≤ Ca * Eexp :=
        mul_nonneg (le_of_lt hCa_pos) hEexp_nonneg
      have hfirst :
          Real.exp (-(Complex.arg w * y)) *
              ‖w‖ ^ (w.re - 1 / 2) ≤
            (Ca * Eexp) * (Cr * P) :=
        mul_le_mul harg_upper hrad_upper hrad_nonneg hCaE_nonneg
      have htarget_step :
          Real.exp (-(Complex.arg w * y)) *
              ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) ≤
            ((Ca * Eexp) * (Cr * P)) * Ce :=
        mul_le_mul hfirst hexpRe_upper hexpRe_nonneg
          (mul_nonneg hCaE_nonneg hCrP_nonneg)
      have htarget_eq :
          ((Ca * Eexp) * (Cr * P)) * Ce =
            ((Ca * Cr) * Ce) * (Eexp * P) := by
        calc
          ((Ca * Eexp) * (Cr * P)) * Ce =
              (Ca * Eexp) * ((Cr * P) * Ce) :=
            (mul_assoc (Ca * Eexp) (Cr * P) Ce).symm
          _ = (Ca * Eexp) * (Ce * (Cr * P)) := by
            exact congrArg
              (fun t : ℝ => (Ca * Eexp) * t)
              (mul_comm (Cr * P) Ce)
          _ = ((Ca * Eexp) * Ce) * (Cr * P) :=
            mul_assoc (Ca * Eexp) Ce (Cr * P)
          _ = (Ca * (Eexp * Ce)) * (Cr * P) := by
            exact congrArg
              (fun t : ℝ => t * (Cr * P))
              (mul_assoc Ca Eexp Ce)
          _ = (Ca * (Ce * Eexp)) * (Cr * P) := by
            exact congrArg
              (fun t : ℝ => (Ca * t) * (Cr * P))
              (mul_comm Eexp Ce)
          _ = ((Ca * Ce) * Eexp) * (Cr * P) := by
            exact congrArg
              (fun t : ℝ => t * (Cr * P))
              (mul_assoc Ca Ce Eexp).symm
          _ = (Ca * Ce) * (Eexp * (Cr * P)) :=
            (mul_assoc (Ca * Ce) Eexp (Cr * P)).symm
          _ = (Ca * Ce) * ((Cr * P) * Eexp) := by
            exact congrArg
              (fun t : ℝ => (Ca * Ce) * t)
              (mul_comm Eexp (Cr * P))
          _ = ((Ca * Ce) * (Cr * P)) * Eexp :=
            mul_assoc (Ca * Ce) (Cr * P) Eexp
          _ = (Ca * (Ce * (Cr * P))) * Eexp := by
            exact congrArg
              (fun t : ℝ => t * Eexp)
              (mul_assoc Ca Ce (Cr * P))
          _ = (Ca * ((Cr * P) * Ce)) * Eexp := by
            exact congrArg
              (fun t : ℝ => (Ca * t) * Eexp)
              (mul_comm Ce (Cr * P))
          _ = (Ca * (Cr * (P * Ce))) * Eexp := by
            exact congrArg
              (fun t : ℝ => (Ca * t) * Eexp)
              (mul_assoc Cr P Ce)
          _ = (Ca * (Cr * (Ce * P))) * Eexp := by
            exact congrArg
              (fun t : ℝ => (Ca * (Cr * t)) * Eexp)
              (mul_comm P Ce)
          _ = (Ca * ((Cr * Ce) * P)) * Eexp := by
            exact congrArg
              (fun t : ℝ => (Ca * t) * Eexp)
              (mul_assoc Cr Ce P).symm
          _ = ((Ca * (Cr * Ce)) * P) * Eexp :=
            congrArg (fun t : ℝ => t * Eexp)
              (mul_assoc Ca (Cr * Ce) P)
          _ = (((Ca * Cr) * Ce) * P) * Eexp := by
            exact congrArg
              (fun t : ℝ => (t * P) * Eexp)
              (mul_assoc Ca Cr Ce).symm
          _ = ((Ca * Cr) * Ce) * (P * Eexp) :=
            (mul_assoc ((Ca * Cr) * Ce) P Eexp).symm
          _ = ((Ca * Cr) * Ce) * (Eexp * P) := by
            exact congrArg
              (fun t : ℝ => ((Ca * Cr) * Ce) * t)
              (mul_comm P Eexp)
      exact le_trans htarget_step (le_of_eq htarget_eq)
    have henv_eq :
        Eexp * P =
          Complex.fixedRealPartVerticalStirlingEnvelope
            (x + Complex.verticalStripTransportShift A) y := by
      rfl
    exact Eq.subst
      (motive := fun t : ℝ =>
        t ≤ ((Ca * Cr) * Ce) *
          Complex.fixedRealPartVerticalStirlingEnvelope
            (x + Complex.verticalStripTransportShift A) y)
      hreciprocal_shape.symm
      (Eq.subst
        (motive := fun t : ℝ =>
            Real.exp (-(Complex.arg w * y)) *
                ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) ≤
            ((Ca * Cr) * Ce) * t)
        henv_eq
        hshape_bound)
  · have hrad_lower :
        cr * P ≤ ‖w‖ ^ (w.re - 1 / 2) := by
      exact Eq.subst
        (motive := fun t : ℝ => cr * P ≤ ‖w‖ ^ (t - 1 / 2))
        hw_re.symm
        hradius_xy.2
    have harg_lower :
        ca * Eexp ≤ Real.exp (-(Complex.arg w * y)) :=
      harg_xy.2
    have hexpRe_lower :
        ce ≤ Real.exp (-w.re) :=
      hexpRe_xy.2
    have hshape_bound :
        ((ca * cr) * ce) *
            (Eexp * P) ≤
          Real.exp (-(Complex.arg w * y)) *
            ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) := by
      have hEexp_nonneg : 0 ≤ Eexp :=
        le_of_lt (Real.exp_pos (-(Real.pi / 2) * ‖y‖))
      have hP_nonneg : 0 ≤ P :=
        Real.rpow_nonneg (add_nonneg zero_le_one (norm_nonneg y))
          (x + Complex.verticalStripTransportShift A - 1 / 2)
      have hce_nonneg : 0 ≤ ce :=
        le_of_lt hce_pos
      have hcrP_nonneg : 0 ≤ cr * P :=
        mul_nonneg (le_of_lt hcr_pos) hP_nonneg
      have hcaE_nonneg : 0 ≤ ca * Eexp :=
        mul_nonneg (le_of_lt hca_pos) hEexp_nonneg
      have hleft_eq :
          ((ca * cr) * ce) * (Eexp * P) =
            (ca * Eexp) * (cr * P) * ce := by
        calc
          ((ca * cr) * ce) * (Eexp * P) =
              (ca * cr) * (ce * (Eexp * P)) :=
            (mul_assoc (ca * cr) ce (Eexp * P)).symm
          _ = (ca * cr) * ((Eexp * P) * ce) := by
            exact congrArg
              (fun t : ℝ => (ca * cr) * t)
              (mul_comm ce (Eexp * P))
          _ = ((ca * cr) * (Eexp * P)) * ce :=
            mul_assoc (ca * cr) (Eexp * P) ce
          _ = (ca * (cr * (Eexp * P))) * ce := by
            exact congrArg
              (fun t : ℝ => t * ce)
              (mul_assoc ca cr (Eexp * P))
          _ = (ca * ((Eexp * P) * cr)) * ce := by
            exact congrArg
              (fun t : ℝ => (ca * t) * ce)
              (mul_comm cr (Eexp * P))
          _ = (ca * (Eexp * (P * cr))) * ce := by
            exact congrArg
              (fun t : ℝ => (ca * t) * ce)
              (mul_assoc Eexp P cr)
          _ = (ca * (Eexp * (cr * P))) * ce := by
            exact congrArg
              (fun t : ℝ => (ca * (Eexp * t)) * ce)
              (mul_comm P cr)
          _ = (ca * ((Eexp * cr) * P)) * ce := by
            exact congrArg
              (fun t : ℝ => (ca * t) * ce)
              (mul_assoc Eexp cr P).symm
          _ = (ca * ((cr * Eexp) * P)) * ce := by
            exact congrArg
              (fun t : ℝ => (ca * (t * P)) * ce)
              (mul_comm Eexp cr)
          _ = (ca * (cr * (Eexp * P))) * ce := by
            exact congrArg
              (fun t : ℝ => (ca * t) * ce)
              (mul_assoc cr Eexp P)
          _ = ((ca * cr) * (Eexp * P)) * ce := by
            exact congrArg
              (fun t : ℝ => t * ce)
              (mul_assoc ca cr (Eexp * P)).symm
          _ = ((ca * cr) * (P * Eexp)) * ce := by
            exact congrArg
              (fun t : ℝ => ((ca * cr) * t) * ce)
              (mul_comm Eexp P)
          _ = (ca * cr) * (P * Eexp) * ce := rfl
          _ = (ca * (cr * P) * Eexp) * ce := by
            exact congrArg
              (fun t : ℝ => t * ce)
              (by
                calc
                  (ca * cr) * (P * Eexp) =
                      ca * (cr * (P * Eexp)) :=
                    (mul_assoc ca cr (P * Eexp)).symm
                  _ = ca * ((cr * P) * Eexp) := by
                    exact congrArg
                      (fun t : ℝ => ca * t)
                      (mul_assoc cr P Eexp)
                  _ = ca * (cr * P) * Eexp :=
                    mul_assoc ca (cr * P) Eexp)
          _ = (Eexp * (ca * (cr * P))) * ce := by
            exact congrArg
              (fun t : ℝ => t * ce)
              (mul_comm (ca * (cr * P)) Eexp)
          _ = ((ca * (cr * P)) * Eexp) * ce := by
            exact congrArg
              (fun t : ℝ => t * ce)
              (mul_comm Eexp (ca * (cr * P)))
          _ = (ca * ((cr * P) * Eexp)) * ce := by
            exact congrArg
              (fun t : ℝ => t * ce)
              (mul_assoc ca (cr * P) Eexp).symm
          _ = (ca * (Eexp * (cr * P))) * ce := by
            exact congrArg
              (fun t : ℝ => (ca * t) * ce)
              (mul_comm (cr * P) Eexp)
          _ = ((ca * Eexp) * (cr * P)) * ce := by
            exact congrArg
              (fun t : ℝ => t * ce)
              (mul_assoc ca Eexp (cr * P))
          _ = (ca * Eexp) * (cr * P) * ce := rfl
      have hfirst :
          (ca * Eexp) * (cr * P) ≤
            Real.exp (-(Complex.arg w * y)) *
              ‖w‖ ^ (w.re - 1 / 2) :=
        mul_le_mul harg_lower hrad_lower hcrP_nonneg
          (le_of_lt (Real.exp_pos (-(Complex.arg w * y))))
      have hsecond :
          (ca * Eexp) * (cr * P) * ce ≤
            Real.exp (-(Complex.arg w * y)) *
              ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) :=
        mul_le_mul hfirst hexpRe_lower hce_nonneg
          (mul_nonneg
            (le_of_lt (Real.exp_pos (-(Complex.arg w * y))))
            (Real.rpow_nonneg (norm_nonneg w) (w.re - 1 / 2)))
      exact le_trans (le_of_eq hleft_eq) hsecond
    have henv_eq :
        Eexp * P =
          Complex.fixedRealPartVerticalStirlingEnvelope
            (x + Complex.verticalStripTransportShift A) y := by
      rfl
    exact Eq.subst
      (motive := fun t : ℝ =>
        ((ca * cr) * ce) *
          Complex.fixedRealPartVerticalStirlingEnvelope
            (x + Complex.verticalStripTransportShift A) y ≤ t)
      hreciprocal_shape.symm
      (Eq.subst
        (motive := fun t : ℝ =>
          ((ca * cr) * ce) * t ≤
            Real.exp (-(Complex.arg w * y)) *
              ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re))
        henv_eq
        hshape_bound)

/-- Sectorial normalized Stirling, on the shifted closed-right-half-plane
points, gives the raw two-sided Gamma envelope with shifted real part.

This is the branch/exponential extraction layer: it converts control of
`Γ(w) e^w w^(1/2-w)` into the classical
`exp (-π |y| / 2) (1 + |y|)^(Re w - 1/2)` profile for
`w = x + N + i y`.  The only analytic input is the sectorial Stirling
hypothesis; the rest is principal-branch norm algebra. -/

end
end LFunctions
end Boundary
