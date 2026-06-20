import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.VerticalRecurrence.Recurrence.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.SectorialLog.Owner

/-!
# Vertical recurrence: factor bounds

This file owns per-factor analysis on the vertical strip, including
imaginary-coordinate properties, real-part bounds, and two-sided estimates.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

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
    neg_abs_le A
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
  match Complex.gammaRecurrenceProduct_factor_upper_on_verticalStrip A B N with
  | ⟨C, hC_pos, hC⟩ =>
      let c : ℝ := 1 / 2
      have hc_pos : 0 < c :=
        one_div_pos.mpr two_pos
      have hpointwise :
          ∀ x y : ℝ,
            A ≤ x →
            x ≤ B →
            (1 : ℝ) ≤ ‖y‖ →
              ∀ j : ℕ,
                j < N →
                  ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖ ≤
                    C * (1 + ‖y‖) ∧
                  c * (1 + ‖y‖) ≤
                    ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖ := by
        intro x y hxA hxB hy j hj
        exact
          ⟨hC x y hxA hxB j hj,
            Complex.gammaRecurrenceProduct_factor_largeHeight_lower j hy⟩
      exact ⟨1, C, c, zero_lt_one, hC_pos, hc_pos, hpointwise⟩

/-- Norm of the deterministic recurrence product as the finite product of
factor norms. -/
theorem Complex.gammaRecurrenceProduct_norm_eq_prod_factor_norms
    (z : ℂ)
    (N : ℕ) :
    ‖Complex.gammaRecurrenceProduct z N‖ =
      Finset.prod (Finset.range N) (fun j : ℕ => ‖z + (j : ℂ)‖) := by
  calc
    ‖Complex.gammaRecurrenceProduct z N‖ =
        Complex.abs (Finset.prod (Finset.range N)
          (fun j : ℕ => z + (j : ℂ))) :=
      Complex.norm_eq_abs (Complex.gammaRecurrenceProduct z N)
    _ = Finset.prod (Finset.range N)
        (fun j : ℕ => Complex.abs (z + (j : ℂ))) :=
      Complex.abs_prod (Finset.range N) (fun j : ℕ => z + (j : ℂ))
    _ = Finset.prod (Finset.range N) (fun j : ℕ => ‖z + (j : ℂ)‖) :=
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
    Finset.prod (Finset.range N) f ≤ M ^ N := by
  have : 0 ≤ M :=
    hM_nonneg
  have hprod_le :
      Finset.prod (Finset.range N) f ≤
        Finset.prod (Finset.range N) (fun _ : ℕ => M) :=
    Finset.prod_le_prod
      (fun j hj => hf_nonneg j (Finset.mem_range.mp hj))
      (fun j hj => hf_le j (Finset.mem_range.mp hj))
  have hconst :
      Finset.prod (Finset.range N) (fun _ : ℕ => M) =
        M ^ (Finset.range N).card :=
    Finset.prod_const M
  have hcard :
      (Finset.range N).card = N :=
    Finset.card_range N
  have hconst_N :
      Finset.prod (Finset.range N) (fun _ : ℕ => M) = M ^ N :=
    Eq.trans hconst (congrArg (fun n : ℕ => M ^ n) hcard)
  exact le_trans hprod_le (le_of_eq hconst_N)

/-- Uniform finite-product lower estimate from per-factor lower estimates. -/
theorem real_finset_range_prod_lower_of_factor_ge
    (N : ℕ)
    {m : ℝ}
    {f : ℕ → ℝ}
    (hm_nonneg : 0 ≤ m)
    (hf_ge : ∀ j : ℕ, j < N → m ≤ f j) :
    m ^ N ≤ Finset.prod (Finset.range N) f := by
  have hprod_le :
      Finset.prod (Finset.range N) (fun _ : ℕ => m) ≤
        Finset.prod (Finset.range N) f :=
    Finset.prod_le_prod
      (fun j hj => hm_nonneg)
      (fun j hj => hf_ge j (Finset.mem_range.mp hj))
  have hconst :
      Finset.prod (Finset.range N) (fun _ : ℕ => m) =
        m ^ (Finset.range N).card :=
    Finset.prod_const m
  have hcard :
      (Finset.range N).card = N :=
    Finset.card_range N
  have hconst_N :
      Finset.prod (Finset.range N) (fun _ : ℕ => m) = m ^ N :=
    Eq.trans hconst (congrArg (fun n : ℕ => m ^ n) hcard)
  calc
    m ^ N = Finset.prod (Finset.range N) (fun _ : ℕ => m) :=
      hconst_N.symm
    _ ≤ Finset.prod (Finset.range N) f :=
      hprod_le

/-- Convert a natural power to the real-power notation used by the Gamma
envelope statements. -/
theorem real_pow_natCast_eq_rpow
    {r : ℝ}
    (hr : 0 ≤ r)
    (N : ℕ) :
    r ^ N = r ^ (N : ℝ) := by
  have : 0 ≤ r :=
    hr
  exact (Real.rpow_natCast r N).symm

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
  match hfactor with
  | ⟨H, C, c, hH_pos, hC_pos, hc_pos, hfactor_pointwise⟩ =>
      have hC_pow_pos : 0 < C ^ N :=
        pow_pos hC_pos N
      have hc_pow_pos : 0 < c ^ N :=
        pow_pos hc_pos N
      have hpointwise :
          ∀ x y : ℝ,
            A ≤ x →
            x ≤ B →
            H ≤ ‖y‖ →
              ‖Complex.gammaRecurrenceProduct
                  (Complex.fixedRealPartVerticalPoint x y) N‖ ≤
                C ^ N * (1 + ‖y‖) ^ (N : ℝ) ∧
              c ^ N * (1 + ‖y‖) ^ (N : ℝ) ≤
                ‖Complex.gammaRecurrenceProduct
                  (Complex.fixedRealPartVerticalPoint x y) N‖ := by
        intro x y hxA hxB hy
        let R : ℝ := 1 + ‖y‖
        have hR_nonneg : 0 ≤ R :=
          add_nonneg zero_le_one (norm_nonneg y)
        have hCR_nonneg : 0 ≤ C * R :=
          mul_nonneg (le_of_lt hC_pos) hR_nonneg
        have hcR_nonneg : 0 ≤ c * R :=
          mul_nonneg (le_of_lt hc_pos) hR_nonneg
        have hprod_norm :
            ‖Complex.gammaRecurrenceProduct
                (Complex.fixedRealPartVerticalPoint x y) N‖ =
              Finset.prod (Finset.range N)
                (fun j : ℕ =>
                  ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖) :=
          Complex.gammaRecurrenceProduct_norm_eq_prod_factor_norms
            (Complex.fixedRealPartVerticalPoint x y) N
        have hupper_prod :
            Finset.prod (Finset.range N)
                (fun j : ℕ =>
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
              Finset.prod (Finset.range N)
                (fun j : ℕ =>
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
        · calc
            ‖Complex.gammaRecurrenceProduct
                (Complex.fixedRealPartVerticalPoint x y) N‖ =
                Finset.prod (Finset.range N)
                  (fun j : ℕ =>
                    ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖) :=
              hprod_norm
            _ ≤ (C * R) ^ N :=
              hupper_prod
            _ = C ^ N * R ^ (N : ℝ) :=
              hupper_target
        · calc
            c ^ N * R ^ (N : ℝ) = (c * R) ^ N :=
              hlower_target.symm
            _ ≤
                Finset.prod (Finset.range N)
                  (fun j : ℕ =>
                    ‖Complex.fixedRealPartVerticalPoint x y + (j : ℂ)‖) :=
              hlower_prod
            _ =
                ‖Complex.gammaRecurrenceProduct
                  (Complex.fixedRealPartVerticalPoint x y) N‖ :=
              hprod_norm.symm
      exact ⟨H, C ^ N, c ^ N, hH_pos, hC_pow_pos, hc_pow_pos, hpointwise⟩

end

end LFunctions
end Boundary
