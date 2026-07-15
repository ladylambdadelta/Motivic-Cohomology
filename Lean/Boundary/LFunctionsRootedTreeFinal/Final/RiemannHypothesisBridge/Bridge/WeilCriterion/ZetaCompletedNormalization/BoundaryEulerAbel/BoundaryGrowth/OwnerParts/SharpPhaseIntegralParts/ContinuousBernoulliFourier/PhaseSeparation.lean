import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.Real.Pi.Bounds

/-!
# Post-cutoff Fourier phase separation

This file owns the elementary nonstationarity estimate used by the Fourier
proof for the first-periodic-Bernoulli logarithmic-phase integral.
-/

namespace Boundary
namespace LFunctions

noncomputable section

local notation "π" => Real.pi

/-- The canonical Fourier cutoff is positive. -/
theorem boundaryLineOnePointRealParam_fourier_cutoff_pos
    (t : ℝ) :
    0 < ⌊2 + ‖t‖⌋₊ := by
  have hone_le : (1 : ℝ) ≤ 2 + ‖t‖ := by
    have hnorm_nonneg : (0 : ℝ) ≤ ‖t‖ :=
      norm_nonneg t
    have hone_le_two : (1 : ℝ) ≤ 2 :=
      one_le_two
    exact le_trans hone_le_two (le_add_of_nonneg_right hnorm_nonneg)
  exact (Nat.one_le_floor_iff (2 + ‖t‖)).mpr hone_le

/-- The canonical cutoff dominates `1 + |t|`.  This elementary floor fact is
owned locally so the Fourier branch does not import the downstream Abel
transport chain merely for cutoff arithmetic. -/
theorem boundaryLineOnePointRealParam_fourier_one_add_norm_le_cutoff
    (t : ℝ) :
    (1 : ℝ) + ‖t‖ ≤ ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) := by
  have hsub_lt :
      (2 + ‖t‖ : ℝ) - 1 < ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) :=
    Nat.sub_one_lt_floor (2 + ‖t‖)
  have hone_add_eq :
      (1 : ℝ) + ‖t‖ = (2 + ‖t‖ : ℝ) - 1 := by
    have hone : (1 : ℝ) = 2 - 1 :=
      eq_sub_iff_add_eq.mpr
        (one_add_one_eq_two : (1 : ℝ) + 1 = 2)
    calc
      (1 : ℝ) + ‖t‖ = (2 - 1) + ‖t‖ :=
        congrArg (fun y : ℝ => y + ‖t‖) hone
      _ = (2 + ‖t‖) - 1 :=
        sub_add_eq_add_sub 2 1 ‖t‖
  exact le_trans (le_of_eq hone_add_eq) (le_of_lt hsub_lt)

/-- Past the canonical cutoff, the logarithmic phase speed has absolute value
at most one. -/
theorem boundaryLineOnePointRealParam_postCutoff_abs_div_le_one
    (t : ℝ)
    {x : ℝ}
    (hx : (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ x) :
    |t / x| ≤ 1 := by
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_fourier_cutoff_pos t
  have hcutoff_real_pos :
      (0 : ℝ) < (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr hcutoff_pos
  have hx_pos : 0 < x :=
    lt_of_lt_of_le hcutoff_real_pos hx
  have hnorm_le_cutoff :
      ‖t‖ ≤ (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) := by
    have hnorm_le_one_add : ‖t‖ ≤ (1 : ℝ) + ‖t‖ :=
      le_add_of_nonneg_left zero_le_one
    exact le_trans hnorm_le_one_add
      (boundaryLineOnePointRealParam_fourier_one_add_norm_le_cutoff t)
  have hnorm_le_x : ‖t‖ ≤ x :=
    le_trans hnorm_le_cutoff hx
  have hdiv : ‖t‖ / x ≤ 1 :=
    (div_le_one₀ hx_pos).mpr hnorm_le_x
  have habs_t : |t| = ‖t‖ :=
    (Real.norm_eq_abs t).symm
  have habs_x : |x| = x :=
    abs_of_pos hx_pos
  have habs_div : |t / x| = ‖t‖ / x := by
    calc
      |t / x| = |t| / |x| := abs_div t x
      _ = ‖t‖ / x := by
        exact congrArg₂ Div.div habs_t habs_x
  calc
    |t / x| = ‖t‖ / x := habs_div
    _ ≤ 1 := hdiv

/-- Every nonzero integral Fourier mode has frequency of absolute value at
least one after casting to the reals. -/
theorem boundaryLineOnePointRealParam_nonzeroIntMode_one_le_abs_cast
    {m : ℤ}
    (hm : m ≠ 0) :
    (1 : ℝ) ≤ |(m : ℝ)| := by
  have hint : (1 : ℤ) ≤ |m| :=
    Int.one_le_abs hm
  have hcast : ((1 : ℤ) : ℝ) ≤ ((|m| : ℤ) : ℝ) :=
    Int.cast_le.mpr hint
  have hone : ((1 : ℤ) : ℝ) = (1 : ℝ) :=
    Int.cast_one
  have habs : ((|m| : ℤ) : ℝ) = |(m : ℝ)| :=
    Int.cast_abs
  calc
    (1 : ℝ) = ((1 : ℤ) : ℝ) := hone.symm
    _ ≤ ((|m| : ℤ) : ℝ) := hcast
    _ = |(m : ℝ)| := habs

/-- A nonzero integral Fourier frequency has size at least two after
multiplication by `2π`. -/
theorem boundaryLineOnePointRealParam_nonzeroIntMode_two_le_abs_two_pi_mul
    {m : ℤ}
    (hm : m ≠ 0) :
    (2 : ℝ) ≤ |2 * π * (m : ℝ)| := by
  have hpi : (1 : ℝ) ≤ π := by
    have hone_le_two : (1 : ℝ) ≤ 2 :=
      one_le_two
    have htwo_le_three : (2 : ℝ) ≤ 3 := by
      have htwo_le_two_add_one : (2 : ℝ) ≤ 2 + 1 :=
        le_add_of_nonneg_right zero_le_one
      have htwo_add_one : (2 : ℝ) + 1 = 3 := by
        exact two_add_one_eq_three
      exact le_trans htwo_le_two_add_one (le_of_eq htwo_add_one)
    exact le_trans (le_trans hone_le_two htwo_le_three)
      (le_of_lt Real.pi_gt_three)
  have hm_abs : (1 : ℝ) ≤ |(m : ℝ)| :=
    boundaryLineOnePointRealParam_nonzeroIntMode_one_le_abs_cast hm
  have htwo_nonneg : (0 : ℝ) ≤ 2 :=
    zero_le_two
  have hpi_nonneg : (0 : ℝ) ≤ π :=
    le_trans zero_le_one hpi
  have hproduct :
      (2 : ℝ) * 1 * 1 ≤ 2 * π * |(m : ℝ)| :=
    mul_le_mul
      (mul_le_mul_of_nonneg_left hpi htwo_nonneg)
      hm_abs
      zero_le_one
      (mul_nonneg htwo_nonneg hpi_nonneg)
  have hleft : (2 : ℝ) * 1 * 1 = 2 := by
    exact Eq.trans (mul_one ((2 : ℝ) * 1)) (mul_one (2 : ℝ))
  have habs_product : |2 * π * (m : ℝ)| = 2 * π * |(m : ℝ)| := by
    calc
      |2 * π * (m : ℝ)| = |2 * π| * |(m : ℝ)| :=
        abs_mul (2 * π) (m : ℝ)
      _ = (2 * π) * |(m : ℝ)| := by
        exact congrArg (fun r : ℝ => r * |(m : ℝ)|)
          (abs_of_nonneg (mul_nonneg htwo_nonneg hpi_nonneg))
  calc
    (2 : ℝ) = (2 : ℝ) * 1 * 1 := hleft.symm
    _ ≤ 2 * π * |(m : ℝ)| := hproduct
    _ = |2 * π * (m : ℝ)| := habs_product.symm

/-- Uniform nonstationarity of every nonzero Fourier mode against the
logarithmic phase on the canonical post-cutoff interval. -/
theorem boundaryLineOnePointRealParam_postCutoff_fourierMode_phaseDerivative_abs_ge_one
    (t : ℝ)
    {m : ℤ}
    (hm : m ≠ 0)
    {x : ℝ}
    (hx : (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ≤ x) :
    (1 : ℝ) ≤ |2 * π * (m : ℝ) - t / x| := by
  let a : ℝ := 2 * π * (m : ℝ)
  let b : ℝ := t / x
  have ha : (2 : ℝ) ≤ |a| :=
    boundaryLineOnePointRealParam_nonzeroIntMode_two_le_abs_two_pi_mul hm
  have hb : |b| ≤ (1 : ℝ) :=
    boundaryLineOnePointRealParam_postCutoff_abs_div_le_one t hx
  have hsub : (2 : ℝ) - 1 ≤ |a| - |b| :=
    sub_le_sub ha hb
  have hone : (2 : ℝ) - 1 = 1 :=
    sub_eq_iff_eq_add.mpr (one_add_one_eq_two : (1 : ℝ) + 1 = 2).symm
  have hreverse : |a| - |b| ≤ |a - b| :=
    abs_sub_abs_le_abs_sub a b
  calc
    (1 : ℝ) = (2 : ℝ) - 1 := hone.symm
    _ ≤ |a| - |b| := hsub
    _ ≤ |a - b| := hreverse

end
end LFunctions
end Boundary
