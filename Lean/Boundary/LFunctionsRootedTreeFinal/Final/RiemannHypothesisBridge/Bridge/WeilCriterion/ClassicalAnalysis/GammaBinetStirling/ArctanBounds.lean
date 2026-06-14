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

end

end LFunctions
end Boundary
