import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.CompletedZetaGrowth.PoleCleared.Owner

/-!
# Completed-zeta growth

This owner layer contains completed-zeta growth estimates assembled from zeta and Gamma factors.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- Helper: arithmetic normalization for far-right pole estimates. -/
private lemma completedGrowth_one_add_neg_two_eq_neg_one : (1 : ℝ) + (-2) = -1 := by
  calc
    (1 : ℝ) + (-2) = 1 + (-(1 + 1)) := by
      exact congrArg (fun x : ℝ => 1 + (-x)) (one_add_one_eq_two.symm)
    _ = 1 + ((-1) + (-1)) := by
      exact congrArg (fun x : ℝ => 1 + x) (neg_add 1 1)
    _ = (1 + (-1)) + (-1) := by
      exact (add_assoc 1 (-1) (-1)).symm
    _ = 0 + (-1) := by
      exact congrArg (fun x : ℝ => x + (-1)) (add_neg_cancel 1)
    _ = -1 := by
      exact zero_add (-1)

/-- Helper: normalize the two reciprocal pole terms. -/
private lemma completedGrowth_add_one_one_eq_add_two (P : ℝ) :
    P + 1 + 1 = P + 2 := by
  calc
    P + 1 + 1 = P + (1 + 1) := by
      exact add_assoc P 1 1
    _ = P + 2 := by
      exact congrArg (fun x : ℝ => P + x) one_add_one_eq_two

/-- Helper: coefficient regrouping for completed-zeta pole bounds. -/
private lemma completedGrowth_pole_coeff_regroup (P : ℝ) :
    (P + 2) + (2 * P + 1) = 3 * P + 3 := by
  calc
    (P + 2) + (2 * P + 1) =
        (P + 2 * P) + (2 + 1) := by
      exact add_add_add_comm P 2 (2 * P) 1
    _ = (P + 2 * P) + 3 := by
      have h : (2 : ℝ) + 1 = 3 := two_add_one_eq_three
      exact congrArg (fun x : ℝ => (P + 2 * P) + x) h
    _ = ((1 : ℝ) * P + 2 * P) + 3 := by
      exact congrArg (fun x : ℝ => (x + 2 * P) + 3) (one_mul P).symm
    _ = ((1 : ℝ) + 2) * P + 3 := by
      exact congrArg (fun x : ℝ => x + 3) (add_mul 1 2 P).symm
    _ = 3 * P + 3 := by
      have h : (1 : ℝ) + 2 = 3 :=
        (add_comm (1 : ℝ) 2).trans two_add_one_eq_three
      exact congrArg (fun x : ℝ => x * P + 3) h

/-- Helper: a nonnegative pole product absorbs the two pole terms. -/
private lemma completedGrowth_add_two_le_three_mul_add_one
    {P : ℝ} (hP_nonneg : 0 ≤ P) :
    P + 2 ≤ 3 * (P + 1) := by
  have h_two_P : 0 ≤ 2 * P :=
    mul_nonneg (le_of_lt zero_lt_two) hP_nonneg
  have h_sum_nonneg : 0 ≤ 2 * P + 1 :=
    add_nonneg h_two_P zero_le_one
  have h_poly : 3 * P + 3 = 3 * (P + 1) := by
    calc
      3 * P + 3 = 3 * P + 3 * 1 := by
        exact congrArg (fun t : ℝ => 3 * P + t) (mul_one 3).symm
      _ = 3 * (P + 1) := by
        exact (mul_add 3 P 1).symm
  calc
    P + 2 = (P + 2) + 0 := by
      exact (add_zero (P + 2)).symm
    _ ≤ (P + 2) + (2 * P + 1) := by
      exact add_le_add_left h_sum_nonneg (P + 2)
    _ = 3 * P + 3 := by
      exact completedGrowth_pole_coeff_regroup P
    _ = 3 * (P + 1) := h_poly

/-- Helper: reciprocal norm bound once the denominator has norm at least one. -/
private lemma completedGrowth_norm_one_div_le_one
    {z : ℂ} (hz_norm_ge_one : (1 : ℝ) ≤ ‖z‖) :
    ‖1 / z‖ ≤ (1 : ℝ) := by
  calc
    ‖1 / z‖ = ‖(1 : ℂ)‖ / ‖z‖ := by
      exact norm_div (1 : ℂ) z
    _ = 1 / ‖z‖ := by
      exact congrArg (fun x : ℝ => x / ‖z‖) norm_one
    _ ≤ 1 := by
      exact div_le_one_of_le₀ hz_norm_ge_one (norm_nonneg z)

/-- Direct compact bound for the pole-cleared completed-zeta entire part in the
right-critical strip.

This compact statement is the truthful replacement for a standalone compact `Gammaℝ`
bound, since the completed entire part already includes the pole cancellations. -/
theorem completedRiemannZeta₀_rightCriticalStrip_compact_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖z.im‖ ≤ 1 →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match completedRiemannZeta₀_rightCriticalStrip_compact_norm_bound with
  | ⟨C, hC, hbound⟩ =>
      exact
        ⟨C, 1, 0, hC, zero_lt_one,
          fun z hz0 hz2 hz_im =>
            have hz_mem : z ∈ completedRiemannZeta₀_rightCriticalStripCompactSet :=
              ⟨hz0, hz2, hz_im⟩
            have hraw : ‖completedRiemannZeta₀ z‖ ≤ C :=
              hbound z hz_mem
            have hfactor_ge_one : (1 : ℝ) ≤ Real.exp (1 * (1 + ‖z‖) ^ 0) := by
              have hone : (1 : ℝ) * (1 + ‖z‖) ^ 0 = 1 := by
                calc
                  (1 : ℝ) * (1 + ‖z‖) ^ 0 = 1 * 1 := by
                    exact congrArg (fun x : ℝ => 1 * x) (pow_zero (1 + ‖z‖))
                  _ = 1 := one_mul 1
              exact Eq.subst
                (motive := fun x : ℝ => (1 : ℝ) ≤ Real.exp x)
                hone.symm
                (Real.one_le_exp_iff.mpr zero_le_one)
            have hC_nonneg : 0 ≤ C :=
              le_of_lt hC
            have hC_le_scaled :
                C ≤ C * Real.exp (1 * (1 + ‖z‖) ^ 0) :=
              le_mul_of_one_le_right hC_nonneg hfactor_ge_one
            le_trans hraw hC_le_scaled⟩

private lemma completedGrowth_gamma_ne_zero_of_im_norm_ge_one
    {z : ℂ} (hz_im : (1 : ℝ) ≤ ‖z.im‖) : Complex.Gammaℝ z ≠ 0 := by
  intro hGamma
  have hzero_index : ∃ n : ℕ, z = -(2 * (n : ℂ)) :=
    Complex.Gammaℝ_eq_zero_iff.mp hGamma
  match hzero_index with
  | ⟨n, hn⟩ =>
      have him_zero : z.im = 0 := by
        calc
          z.im = (-(2 * (n : ℂ))).im := by
            exact congrArg Complex.im hn
          _ = -(2 * (n : ℂ)).im := Complex.neg_im _
          _ = -((2 : ℂ).re * (n : ℂ).im + (2 : ℂ).im * (n : ℂ).re) :=
            congrArg Neg.neg (Complex.mul_im 2 (n : ℂ))
          _ = -((2 : ℂ).re * 0 + 0 * (n : ℂ).re) :=
            congrArg Neg.neg (congrArg₂ (· + ·)
              (congrArg ((2 : ℂ).re * ·) (Complex.ofReal_im n))
              (congrArg (· * (n : ℂ).re) (Complex.ofReal_im 2)))
          _ = -(0 + 0) :=
            congrArg Neg.neg (congrArg₂ (· + ·) (mul_zero _) (zero_mul _))
          _ = 0 := by
            exact (congrArg Neg.neg (add_zero 0)).trans neg_zero
      have him_norm_zero : ‖z.im‖ = 0 := by
        calc
          ‖z.im‖ = ‖(0 : ℝ)‖ := by
            exact congrArg norm him_zero
          _ = 0 := by
            exact norm_zero
      have hone_le_zero : (1 : ℝ) ≤ 0 :=
        Eq.subst
          (motive := fun x : ℝ => (1 : ℝ) ≤ x)
          him_norm_zero
          hz_im
      exact not_lt_of_ge hone_le_zero zero_lt_one

private lemma completedGrowth_one_le_norm_of_im_norm_ge_one
    {z : ℂ} (hz_im : (1 : ℝ) ≤ ‖z.im‖) : (1 : ℝ) ≤ ‖z‖ :=
  le_trans hz_im (Complex.abs_im_le_abs z)

private lemma completedGrowth_one_le_norm_one_sub_of_im_norm_ge_one
    {z : ℂ} (hz_im : (1 : ℝ) ≤ ‖z.im‖) : (1 : ℝ) ≤ ‖1 - z‖ := by
  have him_abs_le : ‖((1 : ℂ) - z).im‖ ≤ ‖(1 : ℂ) - z‖ :=
    Complex.abs_im_le_abs ((1 : ℂ) - z)
  have him_eq : ((1 : ℂ) - z).im = -z.im := by
    calc
      ((1 : ℂ) - z).im = (1 : ℂ).im - z.im := by
        exact Complex.sub_im 1 z
      _ = 0 - z.im := by
        exact congrArg (fun x : ℝ => x - z.im) Complex.one_im
      _ = -z.im := by
        exact zero_sub z.im
  have him_norm_eq : ‖((1 : ℂ) - z).im‖ = ‖z.im‖ := by
    calc
      ‖((1 : ℂ) - z).im‖ = ‖-z.im‖ := by
        exact congrArg norm him_eq
      _ = ‖z.im‖ := by
        exact norm_neg z.im
  exact le_trans
    (Eq.subst
      (motive := fun x : ℝ => (1 : ℝ) ≤ x)
      him_norm_eq.symm
      hz_im)
    him_abs_le

private lemma completedGrowth_one_le_norm_sub_one_of_im_norm_ge_one
    {z : ℂ} (hz_im : (1 : ℝ) ≤ ‖z.im‖) : (1 : ℝ) ≤ ‖z - 1‖ := by
  have him_abs_le : ‖(z - (1 : ℂ)).im‖ ≤ ‖z - (1 : ℂ)‖ :=
    Complex.abs_im_le_abs (z - (1 : ℂ))
  have him_eq : (z - (1 : ℂ)).im = z.im := by
    calc
      (z - (1 : ℂ)).im = z.im - (1 : ℂ).im := by
        exact Complex.sub_im z 1
      _ = z.im - 0 := by
        exact congrArg (fun x : ℝ => z.im - x) Complex.one_im
      _ = z.im := by
        exact sub_zero z.im
  exact le_trans
    (Eq.subst
      (motive := fun x : ℝ => (1 : ℝ) ≤ x)
      (congrArg norm him_eq).symm
      hz_im)
    him_abs_le

/-- On the vertical tail of the right critical strip, the explicit pole terms are bounded
and the completed normalization is controlled by the pole-cleared zeta factor and `Gammaℝ`.
-/
theorem completedRiemannZeta₀_rightCriticalStrip_verticalTail_norm_le_poleCleared_zeta_gamma_plus_one :
    ∃ D : ℝ,
      0 < D ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖completedRiemannZeta₀ z‖ ≤
          D * (‖(z - 1) * riemannZeta z‖ * ‖Complex.Gammaℝ z‖ + 1) := by
  exact ⟨3, zero_lt_three, fun z _hz0 _hz2 hz_im =>
  have hz_ne_zero : z ≠ 0 := fun hz =>
    have him_zero : z.im = 0 := by
      calc
        z.im = (0 : ℂ).im := by
          exact congrArg Complex.im hz
        _ = 0 := by
          exact Complex.zero_im
    have him_norm_zero : ‖z.im‖ = 0 := by
      calc
        ‖z.im‖ = ‖(0 : ℝ)‖ := by
          exact congrArg norm him_zero
        _ = 0 := by
          exact norm_zero
    have hone_le_zero : (1 : ℝ) ≤ 0 :=
      Eq.subst
        (motive := fun x : ℝ => (1 : ℝ) ≤ x)
        him_norm_zero
        hz_im
    not_lt_of_ge hone_le_zero zero_lt_one
  have hone_sub_ne_zero : (1 : ℂ) - z ≠ 0 := fun hsub =>
    have him_zero : ((1 : ℂ) - z).im = 0 := by
      calc
        ((1 : ℂ) - z).im = (0 : ℂ).im := by
          exact congrArg Complex.im hsub
        _ = 0 := by
          exact Complex.zero_im
    have him_eq : ((1 : ℂ) - z).im = -z.im := by
      calc
        ((1 : ℂ) - z).im = (1 : ℂ).im - z.im := by
          exact Complex.sub_im 1 z
        _ = 0 - z.im := by
          exact congrArg (fun x : ℝ => x - z.im) Complex.one_im
        _ = -z.im := by
          exact zero_sub z.im
    have hneg_im_zero : -z.im = 0 :=
      Eq.trans him_eq.symm him_zero
    have him_zero_z : z.im = 0 :=
      neg_eq_zero.mp hneg_im_zero
    have him_norm_zero : ‖z.im‖ = 0 :=
      calc
        ‖z.im‖ = ‖(0 : ℝ)‖ := by
          exact congrArg norm him_zero_z
        _ = 0 := by
          exact norm_zero
    have hone_le_zero : (1 : ℝ) ≤ 0 :=
      Eq.subst
        (motive := fun x : ℝ => (1 : ℝ) ≤ x)
        him_norm_zero
        hz_im
    not_lt_of_ge hone_le_zero zero_lt_one
  have hz_minus_one_ne_zero : z - 1 ≠ 0 := fun hsub =>
    have hone_sub_zero : (1 : ℂ) - z = 0 := by
      calc
        (1 : ℂ) - z = -(z - 1) := (neg_sub z 1).symm
        _ = -0 := by
          exact congrArg Neg.neg hsub
        _ = 0 := by
          exact neg_zero
    hone_sub_ne_zero hone_sub_zero
  have hGamma_ne : Complex.Gammaℝ z ≠ 0 :=
    completedGrowth_gamma_ne_zero_of_im_norm_ge_one hz_im
  have hcompleted_factor :
      completedRiemannZeta z = riemannZeta z * Complex.Gammaℝ z := by
    have h := riemannZeta_def_of_ne_zero (s := z) hz_ne_zero
    have hmul := congrArg (fun x : ℂ => x * Complex.Gammaℝ z) h
    have hcancel :
        (completedRiemannZeta z / Complex.Gammaℝ z) * Complex.Gammaℝ z =
          completedRiemannZeta z := by
      exact div_mul_cancel₀ _ hGamma_ne
    exact (hmul.trans hcancel).symm
  have hdecomp :
      completedRiemannZeta₀ z =
        completedRiemannZeta z + 1 / z + 1 / (1 - z) := by
    have hformula :
        completedRiemannZeta z =
          completedRiemannZeta₀ z - 1 / z - 1 / (1 - z) :=
      completedRiemannZeta_eq z
    calc
      completedRiemannZeta₀ z =
          (completedRiemannZeta₀ z - 1 / z - 1 / (1 - z)) +
            1 / z + 1 / (1 - z) := by
        have h1 : completedRiemannZeta₀ z - (1 / z + 1 / (1 - z)) =
                  completedRiemannZeta₀ z - 1 / z - 1 / (1 - z) :=
          (sub_sub _ _ _).symm
        calc completedRiemannZeta₀ z =
            (completedRiemannZeta₀ z - (1 / z + 1 / (1 - z))) + (1 / z + 1 / (1 - z)) :=
              (sub_add_cancel _ _).symm
          _ = (completedRiemannZeta₀ z - 1 / z - 1 / (1 - z)) + (1 / z + 1 / (1 - z)) :=
              congrArg (· + (1 / z + 1 / (1 - z))) h1
          _ = (completedRiemannZeta₀ z - 1 / z - 1 / (1 - z)) + 1 / z + 1 / (1 - z) :=
              (add_assoc _ _ _).symm
      _ = completedRiemannZeta z + 1 / z + 1 / (1 - z) := by
        exact congrArg (fun w : ℂ => w + 1 / z + 1 / (1 - z)) hformula.symm
  have hz_norm_ge_one := completedGrowth_one_le_norm_of_im_norm_ge_one hz_im
  have hone_sub_norm_ge_one :=
    completedGrowth_one_le_norm_one_sub_of_im_norm_ge_one hz_im
  have hz_minus_one_norm_ge_one :=
    completedGrowth_one_le_norm_sub_one_of_im_norm_ge_one hz_im
  have hinv_z_le_one : ‖1 / z‖ ≤ (1 : ℝ) := by
    exact completedGrowth_norm_one_div_le_one hz_norm_ge_one
  have hinv_one_sub_le_one : ‖1 / (1 - z)‖ ≤ (1 : ℝ) := by
    exact completedGrowth_norm_one_div_le_one hone_sub_norm_ge_one
  have hpole_factor :
      ‖riemannZeta z‖ ≤ ‖(z - 1) * riemannZeta z‖ := by
    have hnorm_pos : 0 < ‖z - 1‖ :=
      lt_of_lt_of_le zero_lt_one hz_minus_one_norm_ge_one
    calc
      ‖riemannZeta z‖ =
          ‖(z - 1) * riemannZeta z / (z - 1)‖ := by
        have hcancel : (z - 1) * riemannZeta z / (z - 1) = riemannZeta z := by
          exact mul_div_cancel_left₀ (riemannZeta z) hz_minus_one_ne_zero
        exact congrArg norm hcancel.symm
      _ = ‖(z - 1) * riemannZeta z‖ / ‖z - 1‖ := by
        exact norm_div ((z - 1) * riemannZeta z) (z - 1)
      _ ≤ ‖(z - 1) * riemannZeta z‖ := by
        exact div_le_self (norm_nonneg ((z - 1) * riemannZeta z)) hz_minus_one_norm_ge_one
  have hnorm_decomp :
      ‖completedRiemannZeta₀ z‖ ≤
        ‖completedRiemannZeta z‖ + ‖1 / z‖ + ‖1 / (1 - z)‖ := by
    calc
      ‖completedRiemannZeta₀ z‖ =
          ‖completedRiemannZeta z + 1 / z + 1 / (1 - z)‖ := by
        exact congrArg (fun w : ℂ => ‖w‖) hdecomp
      _ ≤ ‖completedRiemannZeta z + 1 / z‖ + ‖1 / (1 - z)‖ := by
        exact norm_add_le (completedRiemannZeta z + 1 / z) (1 / (1 - z))
      _ ≤ (‖completedRiemannZeta z‖ + ‖1 / z‖) + ‖1 / (1 - z)‖ := by
        exact add_le_add_right
          (norm_add_le (completedRiemannZeta z) (1 / z))
          ‖1 / (1 - z)‖
      _ = ‖completedRiemannZeta z‖ + ‖1 / z‖ + ‖1 / (1 - z)‖ := by
        rfl
  let P : ℝ := ‖(z - 1) * riemannZeta z‖ * ‖Complex.Gammaℝ z‖
  have hP_nonneg : 0 ≤ P :=
    mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have hcompleted_norm_le :
      ‖completedRiemannZeta z‖ ≤ P := by
    calc
      ‖completedRiemannZeta z‖ = ‖riemannZeta z * Complex.Gammaℝ z‖ := by
        exact congrArg (fun w : ℂ => ‖w‖) hcompleted_factor
      _ = ‖riemannZeta z‖ * ‖Complex.Gammaℝ z‖ := by
        exact norm_mul (riemannZeta z) (Complex.Gammaℝ z)
      _ ≤ ‖(z - 1) * riemannZeta z‖ * ‖Complex.Gammaℝ z‖ := by
        exact mul_le_mul_of_nonneg_right hpole_factor (norm_nonneg _)
  have hsum_bound :
      ‖completedRiemannZeta z‖ + ‖1 / z‖ + ‖1 / (1 - z)‖ ≤ P + 2 := by
    calc
      ‖completedRiemannZeta z‖ + ‖1 / z‖ + ‖1 / (1 - z)‖ ≤
          P + 1 + ‖1 / (1 - z)‖ := by
        exact add_le_add_right
          (add_le_add hcompleted_norm_le hinv_z_le_one)
          ‖1 / (1 - z)‖
      _ ≤ P + 1 + 1 := by
        exact add_le_add_left hinv_one_sub_le_one (P + 1)
      _ = P + 2 := by
        exact completedGrowth_add_one_one_eq_add_two P
  have hP_two_le_three :
      P + 2 ≤ 3 * (P + 1) := by
    exact completedGrowth_add_two_le_three_mul_add_one hP_nonneg
  le_trans hnorm_decomp (le_trans hsum_bound hP_two_le_three)⟩

/-- A nonnegative exponent has exponential at least one.

This local analytic-growth helper is placed before the strip product estimate that needs it. -/
theorem one_le_exp_of_nonnegative_exponent_core
    {x : ℝ} (hx : 0 ≤ x) :
    (1 : ℝ) ≤ Real.exp x := by
  calc
    (1 : ℝ) ≤ x + 1 := by
      exact le_add_of_nonneg_left hx
    _ ≤ Real.exp x := by
      exact Real.add_one_le_exp x

/-- Product growth for the pole-cleared zeta factor and the Gamma factor on the vertical
tail of the right critical strip.

This separates the Gamma-growth estimate from the vertical-strip normalization comparison. -/
theorem poleCleared_zeta_gamma_rightCriticalStrip_verticalTail_product_plus_one_growth_bound
    (hzeta :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          1 ≤ ‖z.im‖ →
          ‖(z - 1) * riemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hGamma :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 < z.re →
          z.re ≤ 2 →
          1 ≤ ‖z.im‖ →
          ‖Complex.Gammaℝ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 < z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖(z - 1) * riemannZeta z‖ * ‖Complex.Gammaℝ z‖ + 1 ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match hzeta with
  | ⟨Az, Bz, mz, hAz, hBz, hzeta_bound⟩ =>
      match hGamma with
      | ⟨Ag, Bg, mg, hAg, hBg, hGamma_bound⟩ =>
          exact
            ⟨Az * Ag + 1, 2 * (Bz + Bg + 1), mz + mg,
              add_pos (mul_pos hAz hAg) zero_lt_one,
              mul_pos zero_lt_two (add_pos (add_pos hBz hBg) zero_lt_one),
              fun z hz0 hz2 hz_im =>
                let H : ℝ := 1 + ‖z‖
                have hH_ge_one : (1 : ℝ) ≤ H :=
                  le_add_of_nonneg_right (norm_nonneg z)
                have hH_nonneg : 0 ≤ H :=
                  le_trans zero_le_one hH_ge_one
                have hBz_nonneg : 0 ≤ Bz := le_of_lt hBz
                have hBg_nonneg : 0 ≤ Bg := le_of_lt hBg
                have hBsum_nonneg : 0 ≤ Bz + Bg + 1 :=
                  add_nonneg (add_nonneg hBz_nonneg hBg_nonneg) zero_le_one
                have hBtarget_nonneg : 0 ≤ 2 * (Bz + Bg + 1) :=
                  mul_nonneg zero_le_two hBsum_nonneg
                have hzeta_enlarge :
                    Az * Real.exp (Bz * H ^ mz) ≤
                      Az * Real.exp ((Bz + Bg + 1) * H ^ (mz + mg)) :=
                  exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                    (le_of_lt hAz)
                    (le_refl Az)
                    (by
                      calc
                        Bz ≤ Bz + Bg := le_add_of_nonneg_right hBg_nonneg
                        _ ≤ Bz + Bg + 1 := le_add_of_nonneg_right zero_le_one)
                    hBz_nonneg
                    (Nat.le_add_right mz mg)
                have hmg_le : mg ≤ mz + mg := by
                  exact Eq.subst
                    (motive := fun d : ℕ => mg ≤ d)
                    (Nat.add_comm mg mz)
                    (Nat.le_add_right mg mz)
                have hGamma_enlarge :
                    Ag * Real.exp (Bg * H ^ mg) ≤
                      Ag * Real.exp ((Bz + Bg + 1) * H ^ (mz + mg)) :=
                  exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                    (le_of_lt hAg)
                    (le_refl Ag)
                    (by
                      calc
                        Bg ≤ Bz + Bg := le_add_of_nonneg_left hBz_nonneg
                        _ ≤ Bz + Bg + 1 := le_add_of_nonneg_right zero_le_one)
                    hBg_nonneg
                    hmg_le
                have htarget_exponent_nonneg : 0 ≤ 2 * (Bz + Bg + 1) * H ^ (mz + mg) :=
                  mul_nonneg hBtarget_nonneg (pow_nonneg hH_nonneg (mz + mg))
                have hone_le_exp :
                    (1 : ℝ) ≤ Real.exp (2 * (Bz + Bg + 1) * H ^ (mz + mg)) :=
                  one_le_exp_of_nonnegative_exponent_core htarget_exponent_nonneg
                have hproduct_bound :
                    ‖(z - 1) * riemannZeta z‖ * ‖Complex.Gammaℝ z‖ ≤
                      (Az * Ag) * Real.exp (2 * (Bz + Bg + 1) * H ^ (mz + mg)) := by
                  have hzeta_to_target :
                      ‖(z - 1) * riemannZeta z‖ ≤
                        Az * Real.exp ((Bz + Bg + 1) * H ^ (mz + mg)) :=
                    le_trans (hzeta_bound z (le_of_lt hz0) hz2 hz_im) hzeta_enlarge
                  have hGamma_to_target :
                      ‖Complex.Gammaℝ z‖ ≤
                        Ag * Real.exp ((Bz + Bg + 1) * H ^ (mz + mg)) :=
                    le_trans (hGamma_bound z hz0 hz2 hz_im) hGamma_enlarge
                  have hmul :
                      ‖(z - 1) * riemannZeta z‖ * ‖Complex.Gammaℝ z‖ ≤
                        (Az * Real.exp ((Bz + Bg + 1) * H ^ (mz + mg))) *
                          (Ag * Real.exp ((Bz + Bg + 1) * H ^ (mz + mg))) :=
                    mul_le_mul hzeta_to_target hGamma_to_target (norm_nonneg _)
                      (mul_nonneg (le_of_lt hAz)
                        (le_of_lt (Real.exp_pos ((Bz + Bg + 1) * H ^ (mz + mg)))))
                  have hcollapse :
                      (Az * Real.exp ((Bz + Bg + 1) * H ^ (mz + mg))) *
                          (Ag * Real.exp ((Bz + Bg + 1) * H ^ (mz + mg))) =
                        (Az * Ag) * Real.exp (2 * (Bz + Bg + 1) * H ^ (mz + mg)) := by
                    let x := (Bz + Bg + 1) * H ^ (mz + mg)
                    calc
                      (Az * Real.exp x) * (Ag * Real.exp x) =
                        ((Az * Real.exp x) * Ag) * Real.exp x := by
                          exact (mul_assoc (Az * Real.exp x) Ag (Real.exp x)).symm
                      _ = (Az * (Real.exp x * Ag)) * Real.exp x := by
                          exact congrArg (· * Real.exp x) (mul_assoc Az (Real.exp x) Ag)
                      _ = (Az * (Ag * Real.exp x)) * Real.exp x := by
                          exact congrArg (· * Real.exp x) (congrArg (Az * ·) (mul_comm (Real.exp x) Ag))
                      _ = ((Az * Ag) * Real.exp x) * Real.exp x := by
                          exact congrArg (· * Real.exp x) ((mul_assoc Az Ag (Real.exp x)).symm)
                      _ = (Az * Ag) * (Real.exp x * Real.exp x) :=
                          mul_assoc (Az * Ag) (Real.exp x) (Real.exp x)
                      _ = (Az * Ag) * Real.exp (x + x) := by
                          exact congrArg (fun y : ℝ => (Az * Ag) * y)
                            (Real.exp_add x x).symm
                      _ = (Az * Ag) * Real.exp (2 * x) := by
                          have h : x + x = 2 * x := (two_mul x).symm
                          exact congrArg (Az * Ag * ·) (congrArg Real.exp h)
                      _ = (Az * Ag) *
                          Real.exp (2 * (Bz + Bg + 1) * H ^ (mz + mg)) := by
                          exact congrArg
                            (fun y : ℝ => (Az * Ag) * Real.exp y)
                            (mul_assoc 2 (Bz + Bg + 1) (H ^ (mz + mg))).symm
                  exact hmul.trans_eq hcollapse
                have hsum_bound :
                    ‖(z - 1) * riemannZeta z‖ * ‖Complex.Gammaℝ z‖ + 1 ≤
                      (Az * Ag + 1) * Real.exp (2 * (Bz + Bg + 1) * H ^ (mz + mg)) := by
                  have hleft :
                      ‖(z - 1) * riemannZeta z‖ * ‖Complex.Gammaℝ z‖ + 1 ≤
                        (Az * Ag) * Real.exp (2 * (Bz + Bg + 1) * H ^ (mz + mg)) +
                          Real.exp (2 * (Bz + Bg + 1) * H ^ (mz + mg)) :=
                    add_le_add hproduct_bound hone_le_exp
                  have hright :
                      (Az * Ag) * Real.exp (2 * (Bz + Bg + 1) * H ^ (mz + mg)) +
                          Real.exp (2 * (Bz + Bg + 1) * H ^ (mz + mg)) =
                        (Az * Ag + 1) * Real.exp (2 * (Bz + Bg + 1) * H ^ (mz + mg)) := by
                    let E : ℝ := Real.exp (2 * (Bz + Bg + 1) * H ^ (mz + mg))
                    calc
                      (Az * Ag) * E + E = (Az * Ag) * E + 1 * E := by
                        exact congrArg (fun x : ℝ => (Az * Ag) * E + x) (one_mul E).symm
                      _ = (Az * Ag + 1) * E := by
                        exact (add_mul (Az * Ag) 1 E).symm
                  exact hleft.trans_eq hright
                hsum_bound⟩

/-- The vertical-tail completed-zeta strip estimate follows mechanically from the
pole-cleared zeta tail, Gamma vertical-tail Stirling, and the normalization comparison. -/
theorem completedRiemannZeta₀_rightCriticalStrip_verticalTail_growth_bound_of_zeta_and_gamma
    (hzeta :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          1 ≤ ‖z.im‖ →
          ‖(z - 1) * riemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hGamma :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 < z.re →
          z.re ≤ 2 →
          1 ≤ ‖z.im‖ →
          ‖Complex.Gammaℝ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 < z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match poleCleared_zeta_gamma_rightCriticalStrip_verticalTail_product_plus_one_growth_bound
      hzeta hGamma with
  | ⟨Apg, Bpg, mpg, hApg, hBpg, hproduct_plus_one_bound⟩ =>
      match completedRiemannZeta₀_rightCriticalStrip_verticalTail_norm_le_poleCleared_zeta_gamma_plus_one with
      | ⟨D, hD, hnorm_bound⟩ =>
          exact
            ⟨D * Apg, Bpg, mpg, mul_pos hD hApg, hBpg,
              fun z hz0 hz2 hz_im =>
                have hscaled :
                    D * (‖(z - 1) * riemannZeta z‖ * ‖Complex.Gammaℝ z‖ + 1) ≤
                      D * (Apg * Real.exp (Bpg * (1 + ‖z‖) ^ mpg)) :=
                  mul_le_mul_of_nonneg_left
                    (hproduct_plus_one_bound z hz0 hz2 hz_im) (le_of_lt hD)
                have htarget :
                    D * (Apg * Real.exp (Bpg * (1 + ‖z‖) ^ mpg)) =
                      D * Apg * Real.exp (Bpg * (1 + ‖z‖) ^ mpg) := by
                  exact (mul_assoc D Apg (Real.exp (Bpg * (1 + ‖z‖) ^ mpg))).symm
                le_trans (hnorm_bound z (le_of_lt hz0) hz2 hz_im)
                  (hscaled.trans_eq htarget)⟩

/-- Vertical-tail bound for the pole-cleared completed-zeta entire part in the
right-critical strip. -/
theorem completedRiemannZeta₀_rightCriticalStrip_verticalTail_growth_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 < z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact completedRiemannZeta₀_rightCriticalStrip_verticalTail_growth_bound_of_zeta_and_gamma
    (riemannZeta_rightCriticalStrip_poleCleared_verticalTail_growth_bound
      hbranch hpartialOneTwo hcompactOneTwo
      (poleClearedRiemannZeta_rightCriticalStrip_ordinaryFiniteOrder_growth_from_functionalEquation_and_EulerMaclaurin
        hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary)
      hpartialLeft hcompactBoundary)
    (Gammaℝ_rightCriticalStrip_verticalTail_stirling_growth_bound hbranch)

/-- Compact and vertical-tail completed-zeta estimates combine to the right-critical-strip
finite-order bound. -/
theorem completedRiemannZeta₀_rightCriticalStrip_finiteOrder_growth_bound_of_compact_and_tail
    (hcompact :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖z.im‖ ≤ 1 →
          ‖completedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (htail :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 < z.re →
          z.re ≤ 2 →
          1 ≤ ‖z.im‖ →
          ‖completedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 < z.re →
        z.re ≤ 2 →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match hcompact with
  | ⟨Ac, Bc, mc, hAc, hBc, hc⟩ =>
      match htail with
      | ⟨At, Bt, mt, hAt, hBt, ht⟩ =>
          exact
            ⟨Ac + At, Bc + Bt, mc + mt,
              add_pos hAc hAt, add_pos hBc hBt,
              fun z hz0 hz2 =>
                have hAc_nonneg : 0 ≤ Ac := le_of_lt hAc
                have hAt_nonneg : 0 ≤ At := le_of_lt hAt
                have hBc_nonneg : 0 ≤ Bc := le_of_lt hBc
                have hBt_nonneg : 0 ≤ Bt := le_of_lt hBt
                match le_total ‖z.im‖ 1 with
                | Or.inl hcompact_im =>
                    le_trans (hc z (le_of_lt hz0) hz2 hcompact_im)
                      (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                        hAc_nonneg
                        (le_add_of_nonneg_right hAt_nonneg)
                        (le_add_of_nonneg_right hBt_nonneg)
                        hBc_nonneg
                        (Nat.le_add_right mc mt))
                | Or.inr htail_im =>
                    have hdegree : mt ≤ mc + mt := by
                      exact Eq.subst
                        (motive := fun d : ℕ => mt ≤ d)
                        (Nat.add_comm mt mc)
                        (Nat.le_add_right mt mc)
                    le_trans (ht z hz0 hz2 htail_im)
                      (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                        hAt_nonneg
                        (le_add_of_nonneg_left hAc_nonneg)
                        (le_add_of_nonneg_left hBc_nonneg)
                        hBt_nonneg
                        hdegree)⟩

/-- Finite-order growth in the right critical strip for the uncentered entire completed-zeta
part. -/
theorem completedRiemannZeta₀_rightCriticalStrip_finiteOrder_growth_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 < z.re →
        z.re ≤ 2 →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact completedRiemannZeta₀_rightCriticalStrip_finiteOrder_growth_bound_of_compact_and_tail
    completedRiemannZeta₀_rightCriticalStrip_compact_growth_bound
    (completedRiemannZeta₀_rightCriticalStrip_verticalTail_growth_bound
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary)

/-- Far-right logarithmic Stirling bound for the archimedean factor.

This far-right standard analytic primitive is the Gamma-side input for finite-order control
of the completed zero packet. -/
theorem Gammaℝ_farRightHalfPlane_stirling_log_growth_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ C : ℝ, ∃ m : ℕ,
      ∀ z : ℂ,
        2 ≤ z.re →
        Real.log ‖Complex.Gammaℝ z‖ ≤
          C * (1 + ‖z‖) ^ m :=
  match Gammaℝ_rightHalfPlane_stirling_log_growth_bound hbranch with
  | ⟨C, m, hC⟩ =>
      ⟨C, m, fun z hz =>
        hC z (lt_of_lt_of_le zero_lt_two hz) (one_le_norm_of_two_le_re hz)⟩

/-- Exponentiating the far-right logarithmic Stirling bound gives finite-order growth for
the archimedean factor. -/
theorem Gammaℝ_farRightHalfPlane_stirling_growth_bound_of_log_growth
    (hlog :
      ∃ C : ℝ, ∃ m : ℕ,
        ∀ z : ℂ,
          2 ≤ z.re →
          Real.log ‖Complex.Gammaℝ z‖ ≤
            C * (1 + ‖z‖) ^ m) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        2 ≤ z.re →
        ‖Complex.Gammaℝ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact Gammaℝ_finiteOrder_growth_bound_of_log_growth_on_region
    (fun z : ℂ => 2 ≤ z.re)
    hlog

/-- Far-right half-plane Stirling growth for the archimedean factor. -/
theorem Gammaℝ_farRightHalfPlane_stirling_growth_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        2 ≤ z.re →
        ‖Complex.Gammaℝ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact Gammaℝ_farRightHalfPlane_stirling_growth_bound_of_log_growth
    (Gammaℝ_farRightHalfPlane_stirling_log_growth_bound hbranch)

/-- Far-right pointwise normalization bound for the pole-cleared completed-zeta entire part.

This is the analytic decomposition step: away from the pole faces, the completed entire
part is controlled by the zeta-gamma product plus the explicit rational correction terms. -/
theorem completedRiemannZeta₀_farRightHalfPlane_norm_le_zeta_gamma_plus_one :
    ∃ D : ℝ,
      0 < D ∧
      ∀ z : ℂ,
        2 ≤ z.re →
        ‖completedRiemannZeta₀ z‖ ≤
          D * (‖riemannZeta z‖ * ‖Complex.Gammaℝ z‖ + 1) := by
  exact
    ⟨3, zero_lt_three,
      fun z hz_re =>
          have hz_re_pos : 0 < z.re :=
            lt_of_lt_of_le zero_lt_two hz_re
          have hz_ne_zero : z ≠ 0 :=
            fun hz =>
            have hre_zero : z.re = 0 :=
              congrArg Complex.re hz
            have hzero_lt_zero : (0 : ℝ) < 0 :=
              Eq.subst
                (motive := fun x : ℝ => (0 : ℝ) < x)
                hre_zero
                hz_re_pos
            (not_lt_of_ge (le_refl (0 : ℝ))) hzero_lt_zero
          have hGamma_ne : Complex.Gammaℝ z ≠ 0 :=
            Complex.Gammaℝ_ne_zero_of_re_pos hz_re_pos
          have hcompleted_factor :
              completedRiemannZeta z = riemannZeta z * Complex.Gammaℝ z := by
            have h := riemannZeta_def_of_ne_zero (s := z) hz_ne_zero
            have hmul := congrArg (fun x : ℂ => x * Complex.Gammaℝ z) h
            have hcancel :
                (completedRiemannZeta z / Complex.Gammaℝ z) * Complex.Gammaℝ z =
                  completedRiemannZeta z := by
              exact div_mul_cancel₀ _ hGamma_ne
            exact (hmul.trans hcancel).symm
          have hdecomp :
              completedRiemannZeta₀ z =
                completedRiemannZeta z + 1 / z + 1 / (1 - z) := by
            have hformula :
                completedRiemannZeta z =
                  completedRiemannZeta₀ z - 1 / z - 1 / (1 - z) :=
              completedRiemannZeta_eq z
            calc
              completedRiemannZeta₀ z =
                  (completedRiemannZeta₀ z - 1 / z - 1 / (1 - z)) +
                    1 / z + 1 / (1 - z) := by
                have h1 : completedRiemannZeta₀ z - (1 / z + 1 / (1 - z)) =
                          completedRiemannZeta₀ z - 1 / z - 1 / (1 - z) :=
                  (sub_sub _ _ _).symm
                calc completedRiemannZeta₀ z =
                    (completedRiemannZeta₀ z - (1 / z + 1 / (1 - z))) + (1 / z + 1 / (1 - z)) :=
                      (sub_add_cancel _ _).symm
                  _ = (completedRiemannZeta₀ z - 1 / z - 1 / (1 - z)) + (1 / z + 1 / (1 - z)) :=
                      congrArg (· + (1 / z + 1 / (1 - z))) h1
                  _ = (completedRiemannZeta₀ z - 1 / z - 1 / (1 - z)) + 1 / z + 1 / (1 - z) :=
                      (add_assoc _ _ _).symm
              _ = completedRiemannZeta z + 1 / z + 1 / (1 - z) := by
                exact congrArg (fun w : ℂ => w + 1 / z + 1 / (1 - z)) hformula.symm
          have hz_norm_ge_one : (1 : ℝ) ≤ ‖z‖ := by
            have hre_abs_le_norm : |z.re| ≤ ‖z‖ :=
              Complex.abs_re_le_abs z
            have hone_le_re_abs : (1 : ℝ) ≤ |z.re| := by
              exact le_trans
                one_le_two
                (le_trans hz_re (le_abs_self z.re))
            exact le_trans hone_le_re_abs hre_abs_le_norm
          have hone_sub_norm_ge_one : (1 : ℝ) ≤ ‖1 - z‖ := by
            have hre_abs_le_norm : |(1 - z).re| ≤ ‖1 - z‖ :=
              Complex.abs_re_le_abs (1 - z)
            have hre_eq : (1 - z).re = 1 - z.re := by
              exact Complex.sub_re 1 z
            have hone_le_abs : (1 : ℝ) ≤ |(1 - z).re| := by
              have hle : (1 - z.re) ≤ -1 := by
                calc
                  1 - z.re = 1 + (-z.re) := by
                    exact sub_eq_add_neg 1 z.re
                  _ ≤ 1 + (-2) := add_le_add_left (neg_le_neg hz_re) 1
                  _ = -1 := by
                    exact completedGrowth_one_add_neg_two_eq_neg_one
              have hle_zero : (1 - z.re) ≤ 0 :=
                le_trans hle (neg_nonpos.mpr zero_le_one)
              have habs_eq : |1 - z.re| = -(1 - z.re) :=
                abs_of_nonpos hle_zero
              have hone_le : (1 : ℝ) ≤ -(1 - z.re) := by
                have hneg : -((-1 : ℝ)) ≤ -(1 - z.re) :=
                  neg_le_neg hle
                exact Eq.subst
                  (motive := fun x : ℝ => x ≤ -(1 - z.re))
                  (neg_neg (1 : ℝ))
                  hneg
              exact Eq.subst
                (motive := fun x : ℝ => (1 : ℝ) ≤ |x|)
                hre_eq.symm
                (Eq.subst
                  (motive := fun x : ℝ => (1 : ℝ) ≤ x)
                  habs_eq.symm
                  hone_le)
            exact le_trans hone_le_abs hre_abs_le_norm
          have hinv_z_le_one : ‖1 / z‖ ≤ (1 : ℝ) := by
            exact completedGrowth_norm_one_div_le_one hz_norm_ge_one
          have hinv_one_sub_le_one : ‖1 / (1 - z)‖ ≤ (1 : ℝ) := by
            exact completedGrowth_norm_one_div_le_one hone_sub_norm_ge_one
          have hnorm_decomp :
              ‖completedRiemannZeta₀ z‖ ≤
                ‖completedRiemannZeta z‖ + ‖1 / z‖ + ‖1 / (1 - z)‖ := by
            calc
              ‖completedRiemannZeta₀ z‖ =
                  ‖completedRiemannZeta z + 1 / z + 1 / (1 - z)‖ := by
                exact congrArg (fun w : ℂ => ‖w‖) hdecomp
              _ ≤ ‖completedRiemannZeta z + 1 / z‖ + ‖1 / (1 - z)‖ := by
                exact norm_add_le (completedRiemannZeta z + 1 / z) (1 / (1 - z))
              _ ≤ (‖completedRiemannZeta z‖ + ‖1 / z‖) + ‖1 / (1 - z)‖ := by
                exact add_le_add_right
                  (norm_add_le (completedRiemannZeta z) (1 / z))
                  ‖1 / (1 - z)‖
              _ = ‖completedRiemannZeta z‖ + ‖1 / z‖ + ‖1 / (1 - z)‖ := by
                rfl
          have hcompleted_norm :
              ‖completedRiemannZeta z‖ =
                ‖riemannZeta z‖ * ‖Complex.Gammaℝ z‖ := by
            calc
              ‖completedRiemannZeta z‖ = ‖riemannZeta z * Complex.Gammaℝ z‖ := by
                exact congrArg (fun w : ℂ => ‖w‖) hcompleted_factor
              _ = ‖riemannZeta z‖ * ‖Complex.Gammaℝ z‖ := by
                exact norm_mul (riemannZeta z) (Complex.Gammaℝ z)
          let P : ℝ := ‖riemannZeta z‖ * ‖Complex.Gammaℝ z‖
          have hP_nonneg : 0 ≤ P :=
            mul_nonneg (norm_nonneg _) (norm_nonneg _)
          have hsum_bound :
              ‖completedRiemannZeta z‖ + ‖1 / z‖ + ‖1 / (1 - z)‖ ≤ P + 2 := by
            calc
              ‖completedRiemannZeta z‖ + ‖1 / z‖ + ‖1 / (1 - z)‖ =
                  P + ‖1 / z‖ + ‖1 / (1 - z)‖ := by
                exact congrArg
                  (fun x : ℝ => x + ‖1 / z‖ + ‖1 / (1 - z)‖)
                  hcompleted_norm
              _ ≤ P + 1 + ‖1 / (1 - z)‖ := by
                exact add_le_add_right (add_le_add_left hinv_z_le_one P) ‖1 / (1 - z)‖
              _ ≤ P + 1 + 1 := by
                exact add_le_add_left hinv_one_sub_le_one (P + 1)
              _ = P + 2 := by
                exact completedGrowth_add_one_one_eq_add_two P
          have hP_two_le_three :
              P + 2 ≤ 3 * (P + 1) := by
            exact completedGrowth_add_two_le_three_mul_add_one hP_nonneg
          le_trans hnorm_decomp (le_trans hsum_bound hP_two_le_three)⟩

/-- The pole-cleared completed-zeta normalization has finite-order growth in the far-right
half-plane once the Dirichlet-series zeta bound and the gamma Stirling estimate are known. -/
theorem completedRiemannZeta₀_farRightHalfPlane_poleCleared_growth_bound
    (hzeta :
      ∃ A : ℝ,
        0 < A ∧
        ∀ z : ℂ,
          2 ≤ z.re →
          ‖riemannZeta z‖ ≤ A)
    (hGamma :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          2 ≤ z.re →
          ‖Complex.Gammaℝ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        2 ≤ z.re →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match hzeta with
  | ⟨Az, hAz, hzeta_bound⟩ =>
      match hGamma with
      | ⟨Ag, Bg, mg, hAg, hBg, hGamma_bound⟩ =>
          match completedRiemannZeta₀_farRightHalfPlane_norm_le_zeta_gamma_plus_one with
          | ⟨D, hD, hnorm_bound⟩ =>
              exact
                ⟨D * (Az * Ag + 1), Bg, mg,
                  mul_pos hD (add_pos (mul_pos hAz hAg) zero_lt_one), hBg,
                  fun z hz =>
                    let H : ℝ := 1 + ‖z‖
                    have hH_nonneg : 0 ≤ H :=
                      le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))
                    have hexponent_nonneg : 0 ≤ Bg * H ^ mg :=
                      mul_nonneg (le_of_lt hBg) (pow_nonneg hH_nonneg mg)
                    have hone_le_exp : (1 : ℝ) ≤ Real.exp (Bg * H ^ mg) := by
                      calc
                        (1 : ℝ) ≤ Bg * H ^ mg + 1 := by
                          exact le_add_of_nonneg_left hexponent_nonneg
                        _ ≤ Real.exp (Bg * H ^ mg) := by
                          exact Real.add_one_le_exp (Bg * H ^ mg)
                    have hgamma_target_nonneg : 0 ≤ Ag * Real.exp (Bg * H ^ mg) :=
                      mul_nonneg (le_of_lt hAg) (le_of_lt (Real.exp_pos (Bg * H ^ mg)))
                      have hproduct_bound :
                          ‖riemannZeta z‖ * ‖Complex.Gammaℝ z‖ ≤
                            Az * (Ag * Real.exp (Bg * H ^ mg)) :=
                        mul_le_mul (hzeta_bound z hz) (hGamma_bound z hz) (norm_nonneg _)
                          (le_of_lt hAz)
                    have hproduct_reassoc :
                        Az * (Ag * Real.exp (Bg * H ^ mg)) =
                          (Az * Ag) * Real.exp (Bg * H ^ mg) := by
                      exact (mul_assoc Az Ag (Real.exp (Bg * H ^ mg))).symm
                    have hsum_bound :
                        ‖riemannZeta z‖ * ‖Complex.Gammaℝ z‖ + 1 ≤
                          (Az * Ag + 1) * Real.exp (Bg * H ^ mg) := by
                      have hleft :
                          ‖riemannZeta z‖ * ‖Complex.Gammaℝ z‖ + 1 ≤
                            (Az * Ag) * Real.exp (Bg * H ^ mg) +
                              Real.exp (Bg * H ^ mg) := by
                        exact add_le_add (hproduct_bound.trans_eq hproduct_reassoc) hone_le_exp
                      have hright :
                          (Az * Ag) * Real.exp (Bg * H ^ mg) +
                              Real.exp (Bg * H ^ mg) =
                            (Az * Ag + 1) * Real.exp (Bg * H ^ mg) := by
                        let E : ℝ := Real.exp (Bg * H ^ mg)
                        calc
                          (Az * Ag) * E + E = (Az * Ag) * E + 1 * E := by
                            exact congrArg (fun x : ℝ => (Az * Ag) * E + x) (one_mul E).symm
                          _ = (Az * Ag + 1) * E := by
                            exact (add_mul (Az * Ag) 1 E).symm
                      exact hleft.trans_eq hright
                    have hscaled :
                        D * (‖riemannZeta z‖ * ‖Complex.Gammaℝ z‖ + 1) ≤
                          D * ((Az * Ag + 1) * Real.exp (Bg * H ^ mg)) :=
                      mul_le_mul_of_nonneg_left hsum_bound (le_of_lt hD)
                    have htarget :
                        D * ((Az * Ag + 1) * Real.exp (Bg * H ^ mg)) =
                          D * (Az * Ag + 1) * Real.exp (Bg * H ^ mg) := by
                      exact (mul_assoc D (Az * Ag + 1) (Real.exp (Bg * H ^ mg))).symm
                    le_trans (hnorm_bound z hz) (hscaled.trans_eq htarget)⟩

/-- Finite-order growth in the far-right half-plane for the uncentered entire
completed-zeta part. -/
theorem completedRiemannZeta₀_farRightHalfPlane_finiteOrder_growth_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        2 ≤ z.re →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact completedRiemannZeta₀_farRightHalfPlane_poleCleared_growth_bound
    riemannZeta_farRightHalfPlane_dirichletSeries_bound
    (Gammaℝ_farRightHalfPlane_stirling_growth_bound hbranch)

/-- Right half-plane finite-order growth for the uncentered entire completed-zeta part. -/
theorem completedRiemannZeta₀_rightHalfPlane_finiteOrder_growth_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 < z.re →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact completedRiemannZeta₀_strictRightHalfPlane_finiteOrder_growth_bound_of_strip_and_farRight
    (completedRiemannZeta₀_rightCriticalStrip_finiteOrder_growth_bound
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary)
    (completedRiemannZeta₀_farRightHalfPlane_finiteOrder_growth_bound hbranch)

/-- Left half-plane finite-order growth for the uncentered entire completed-zeta part. -/
theorem completedRiemannZeta₀_leftHalfPlane_finiteOrder_growth_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact completedRiemannZeta₀_leftHalfPlane_finiteOrder_growth_bound_of_strictRightHalfPlane
    (completedRiemannZeta₀_rightHalfPlane_finiteOrder_growth_bound
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary)

/-- Owner finite-order growth for the uncentered entire completed-zeta part.

This is the analytic finite-order input actually used by completed-zeta zero counting in
the RH lane.  A more general Hurwitz finite-order theorem may imply it, but the zeta
normalization layer only needs this specialization. -/
theorem completedRiemannZeta₀_finiteOrder_growth_bound_ownerZeta
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact completedRiemannZeta₀_global_finiteOrder_growth_bound_of_strictRight_and_leftHalfPlanes
    (completedRiemannZeta₀_rightHalfPlane_finiteOrder_growth_bound
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary)
    (completedRiemannZeta₀_leftHalfPlane_finiteOrder_growth_bound
      hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary)

/-- Finite-order growth for the uncentered entire completed-zeta part. -/
theorem completedRiemannZeta₀_finiteOrder_growth_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (hpartialOneTwo : BoundaryLineOneAbelPartialMajorant)
    (hcompactOneTwo : PoleClearedOneTwoStripCompactBoundaryBound)
    (hfinite : PoleClearedRightCriticalStripAdmissibleGrowth)
    (hpartialLeft : ReflectedBoundaryAbelPartialMajorant)
    (hcompactBoundary : PoleClearedRightCriticalStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact completedRiemannZeta₀_finiteOrder_growth_bound_ownerZeta
    hbranch hpartialOneTwo hcompactOneTwo hfinite hpartialLeft hcompactBoundary

end
end LFunctions
end Boundary
