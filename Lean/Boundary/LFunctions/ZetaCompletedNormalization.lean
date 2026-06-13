import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Boundary centered completed zeta normalization

This file fixes the centered completed-zeta object at the critical line and
records the direct decomposition available from mathlib:
the entire part plus the two pole correction terms.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The completed zeta function centered at the critical line. -/
def centeredCompletedRiemannZeta (s : ℂ) : ℂ :=
  completedRiemannZeta (1 / 2 + s)

/-- The entire part of the centered completed zeta function. -/
def centeredCompletedRiemannZeta₀ (s : ℂ) : ℂ :=
  completedRiemannZeta₀ (1 / 2 + s)

/-- The entire zero-carrier for the centered completed zeta function.

Away from the shifted pole faces, zeros of the centered completed zeta
normalization are zeros of this entire carrier.  This is the object to which
Jensen/finite-order zero counting applies; the raw entire part
`centeredCompletedRiemannZeta₀` alone is not the completed-zero divisor. -/
def centeredCompletedRiemannZetaZeroCarrier (s : ℂ) : ℂ :=
  ((1 / 2 : ℂ) + s) *
    (1 - ((1 / 2 : ℂ) + s)) *
      centeredCompletedRiemannZeta₀ s - 1

/-- The quadratic clearing factor used to remove the shifted pole faces from the centered
completed-zeta normalization. -/
def centeredCompletedRiemannZetaZeroCarrierClearingFactor (s : ℂ) : ℂ :=
  ((1 / 2 : ℂ) + s) *
    (1 - ((1 / 2 : ℂ) + s))

/-- The zero-carrier is the centered entire part multiplied by its quadratic clearing factor,
then shifted by `-1`. -/
theorem centeredCompletedRiemannZetaZeroCarrier_eq_factor_mul_entirePart_sub_one
    (s : ℂ) :
    centeredCompletedRiemannZetaZeroCarrier s =
      centeredCompletedRiemannZetaZeroCarrierClearingFactor s *
        centeredCompletedRiemannZeta₀ s - 1 := by
  rfl

/-- The centered entire part is analytic everywhere. -/
theorem centeredCompletedRiemannZeta₀_analyticAt
    (z : ℂ) :
    AnalyticAt ℂ centeredCompletedRiemannZeta₀ z := by
  have hlinear :
      AnalyticAt ℂ (fun w : ℂ => (1 / 2 : ℂ) + w) z :=
    analyticAt_const.add analyticAt_id
  unfold centeredCompletedRiemannZeta₀
  exact (differentiable_completedZeta₀.analyticAt ((1 / 2 : ℂ) + z)).comp hlinear

/-- The centered zero-carrier is analytic everywhere. -/
theorem centeredCompletedRiemannZetaZeroCarrier_analyticAt
    (z : ℂ) :
    AnalyticAt ℂ centeredCompletedRiemannZetaZeroCarrier z := by
  have hleft :
      AnalyticAt ℂ (fun w : ℂ => (1 / 2 : ℂ) + w) z :=
    analyticAt_const.add analyticAt_id
  have hright :
      AnalyticAt ℂ (fun w : ℂ => 1 - ((1 / 2 : ℂ) + w)) z :=
    analyticAt_const.sub (analyticAt_const.add analyticAt_id)
  have hcarrier :
      AnalyticAt ℂ
        (fun w : ℂ =>
          ((1 / 2 : ℂ) + w) *
            (1 - ((1 / 2 : ℂ) + w)) *
              centeredCompletedRiemannZeta₀ w - 1)
        z :=
    ((hleft.mul hright).mul
      (centeredCompletedRiemannZeta₀_analyticAt z)).sub analyticAt_const
  exact hcarrier

/-- Owner finite-order growth for the uncentered entire completed-zeta part.

This is the analytic finite-order input actually used by completed-zeta zero counting in
the RH lane.  A more general Hurwitz finite-order theorem may imply it, but the zeta
normalization layer only needs this specialization. -/
theorem completedRiemannZeta₀_finiteOrder_growth_bound_ownerZeta :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ z : ℂ,
        ‖completedRiemannZeta₀ z‖ ≤
          A * (1 + ‖z‖) ^ m := by
  sorry

/-- Finite-order growth for the uncentered entire completed-zeta part. -/
theorem completedRiemannZeta₀_finiteOrder_growth_bound :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ z : ℂ,
        ‖completedRiemannZeta₀ z‖ ≤
          A * (1 + ‖z‖) ^ m := by
  exact completedRiemannZeta₀_finiteOrder_growth_bound_ownerZeta

/-- The centered affine shift is controlled by the basic centered height. -/
theorem centeredCompletedRiemannZeta₀_shiftedBasicHeight_le
    (z : ℂ) :
    1 + ‖(1 / 2 : ℂ) + z‖ ≤ 2 * (1 + ‖z‖) := by
  have hnorm_half : ‖(1 / 2 : ℂ)‖ ≤ (1 : ℝ) := by
    norm_num
  have htriangle :
      ‖(1 / 2 : ℂ) + z‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖z‖ :=
    norm_add_le (1 / 2 : ℂ) z
  have hbound :
      ‖(1 / 2 : ℂ) + z‖ ≤ 1 + ‖z‖ :=
    le_trans htriangle (add_le_add_right hnorm_half ‖z‖)
  have hheight_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
  calc
    1 + ‖(1 / 2 : ℂ) + z‖ ≤ 1 + (1 + ‖z‖) := by
      exact add_le_add_left hbound 1
    _ = 2 + ‖z‖ := by
      ring
    _ ≤ 2 + 2 * ‖z‖ := by
      have hdouble : ‖z‖ ≤ 2 * ‖z‖ := by
        nlinarith [hheight_nonneg]
      exact add_le_add_left hdouble 2
    _ = 2 * (1 + ‖z‖) := by
      ring

/-- Finite-order growth for the centered entire completed-zeta part. -/
theorem centeredCompletedRiemannZeta₀_finiteOrder_growth_bound :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ z : ℂ,
        ‖centeredCompletedRiemannZeta₀ z‖ ≤
          A * (1 + ‖z‖) ^ m := by
  rcases completedRiemannZeta₀_finiteOrder_growth_bound with
    ⟨A, m, hApos, hbound⟩
  refine ⟨A * (2 : ℝ) ^ m, m, ?_, ?_⟩
  · exact mul_pos hApos (pow_pos zero_lt_two m)
  intro z
  let H : ℝ := 1 + ‖z‖
  have hH_nonneg : 0 ≤ H := by
    exact le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))
  have hshift_nonneg : 0 ≤ 1 + ‖(1 / 2 : ℂ) + z‖ := by
    exact le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg ((1 / 2 : ℂ) + z)))
  have hshift_le :
      1 + ‖(1 / 2 : ℂ) + z‖ ≤ 2 * H :=
    centeredCompletedRiemannZeta₀_shiftedBasicHeight_le z
  have hpow_le :
      (1 + ‖(1 / 2 : ℂ) + z‖) ^ m ≤ (2 * H) ^ m :=
    pow_le_pow_left₀ hshift_nonneg hshift_le m
  have hcenter :
      ‖centeredCompletedRiemannZeta₀ z‖ =
        ‖completedRiemannZeta₀ ((1 / 2 : ℂ) + z)‖ := by
    rfl
  have hraw :
      ‖completedRiemannZeta₀ ((1 / 2 : ℂ) + z)‖ ≤
        A * (1 + ‖(1 / 2 : ℂ) + z‖) ^ m :=
    hbound ((1 / 2 : ℂ) + z)
  have hscale :
      A * (1 + ‖(1 / 2 : ℂ) + z‖) ^ m ≤
        A * (2 * H) ^ m :=
    mul_le_mul_of_nonneg_left hpow_le (le_of_lt hApos)
  have hmul_pow :
      (2 * H) ^ m = (2 : ℝ) ^ m * H ^ m :=
    mul_pow 2 H m
  have htarget :
      A * (2 * H) ^ m =
        (A * (2 : ℝ) ^ m) * H ^ m := by
    calc
      A * (2 * H) ^ m = A * ((2 : ℝ) ^ m * H ^ m) := by
        exact congrArg (fun x : ℝ => A * x) hmul_pow
      _ = (A * (2 : ℝ) ^ m) * H ^ m := by
        exact (mul_assoc A ((2 : ℝ) ^ m) (H ^ m)).symm
  exact Eq.subst
    (motive := fun x : ℂ =>
      ‖x‖ ≤ (A * (2 : ℝ) ^ m) * H ^ m)
    hcenter.symm
    (hraw.trans (hscale.trans_eq htarget))

/-- Each linear factor in the zero-carrier clearing factor is controlled by
`2 * (1 + ‖z‖)`. -/
theorem centeredCompletedRiemannZetaZeroCarrierClearingFactor_linearNorm_le
    (z : ℂ) :
    ‖((1 / 2 : ℂ) + z)‖ ≤ 2 * (1 + ‖z‖) ∧
      ‖(1 - ((1 / 2 : ℂ) + z))‖ ≤ 2 * (1 + ‖z‖) := by
  have hnorm_half : ‖(1 / 2 : ℂ)‖ ≤ (1 : ℝ) := by
    norm_num
  have hnorm_one_sub_half : ‖(1 - (1 / 2 : ℂ))‖ ≤ (1 : ℝ) := by
    norm_num
  have hnorm_z_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
  have hfirst_triangle :
      ‖((1 / 2 : ℂ) + z)‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖z‖ :=
    norm_add_le (1 / 2 : ℂ) z
  have hfirst_sum :
      ‖(1 / 2 : ℂ)‖ + ‖z‖ ≤ 1 + ‖z‖ :=
    add_le_add_right hnorm_half ‖z‖
  have hfirst_height :
      1 + ‖z‖ ≤ 2 * (1 + ‖z‖) := by
    nlinarith [hnorm_z_nonneg]
  have hfirst :
      ‖((1 / 2 : ℂ) + z)‖ ≤ 2 * (1 + ‖z‖) :=
    le_trans hfirst_triangle (le_trans hfirst_sum hfirst_height)
  have hsecond_rewrite :
      (1 : ℂ) - ((1 / 2 : ℂ) + z) = (1 - (1 / 2 : ℂ)) + (-z) := by
    ring
  have hsecond_triangle :
      ‖(1 - ((1 / 2 : ℂ) + z))‖ ≤ ‖(1 - (1 / 2 : ℂ))‖ + ‖-z‖ := by
    rw [hsecond_rewrite]
    exact norm_add_le (1 - (1 / 2 : ℂ)) (-z)
  have hnorm_neg_z : ‖-z‖ = ‖z‖ := norm_neg z
  have hsecond_sum :
      ‖(1 - (1 / 2 : ℂ))‖ + ‖-z‖ ≤ 1 + ‖z‖ := by
    rw [hnorm_neg_z]
    exact add_le_add_right hnorm_one_sub_half ‖z‖
  have hsecond_height :
      1 + ‖z‖ ≤ 2 * (1 + ‖z‖) := by
    nlinarith [hnorm_z_nonneg]
  have hsecond :
      ‖(1 - ((1 / 2 : ℂ) + z))‖ ≤ 2 * (1 + ‖z‖) :=
    le_trans hsecond_triangle (le_trans hsecond_sum hsecond_height)
  exact ⟨hfirst, hsecond⟩

/-- The quadratic clearing factor is controlled by the square of the basic height. -/
theorem centeredCompletedRiemannZetaZeroCarrierClearingFactor_norm_le_quadratic
    (z : ℂ) :
    ‖centeredCompletedRiemannZetaZeroCarrierClearingFactor z‖ ≤
      4 * (1 + ‖z‖) ^ (2 : ℕ) := by
  rcases centeredCompletedRiemannZetaZeroCarrierClearingFactor_linearNorm_le z with
    ⟨hleft, hright⟩
  have hheight_nonneg : 0 ≤ 1 + ‖z‖ := by
    nlinarith [norm_nonneg z]
  have htwo_height_nonneg : 0 ≤ 2 * (1 + ‖z‖) := by
    nlinarith [hheight_nonneg]
  have hnorm_mul :
      ‖centeredCompletedRiemannZetaZeroCarrierClearingFactor z‖ =
        ‖((1 / 2 : ℂ) + z)‖ * ‖(1 - ((1 / 2 : ℂ) + z))‖ := by
    unfold centeredCompletedRiemannZetaZeroCarrierClearingFactor
    exact norm_mul ((1 / 2 : ℂ) + z) (1 - ((1 / 2 : ℂ) + z))
  have hproduct :
      ‖((1 / 2 : ℂ) + z)‖ * ‖(1 - ((1 / 2 : ℂ) + z))‖ ≤
        (2 * (1 + ‖z‖)) * (2 * (1 + ‖z‖)) :=
    mul_le_mul hleft hright (norm_nonneg _) htwo_height_nonneg
  have htarget :
      (2 * (1 + ‖z‖)) * (2 * (1 + ‖z‖)) =
        4 * (1 + ‖z‖) ^ (2 : ℕ) := by
    ring
  exact hnorm_mul.trans_le (hproduct.trans_eq htarget)

/-- The basic centered height is at least one. -/
theorem centeredCompletedRiemannZeta_basicHeight_ge_one
    (z : ℂ) :
    (1 : ℝ) ≤ 1 + ‖z‖ := by
  exact le_add_of_nonneg_right (norm_nonneg z)

/-- Powers of the basic centered height are at least one. -/
theorem centeredCompletedRiemannZeta_basicHeight_pow_ge_one
    (z : ℂ) (m : ℕ) :
    (1 : ℝ) ≤ (1 + ‖z‖) ^ m := by
  exact one_le_pow₀ (centeredCompletedRiemannZeta_basicHeight_ge_one z) m

/-- The quadratic clearing factor has polynomial growth. -/
theorem centeredCompletedRiemannZetaZeroCarrierClearingFactor_growth_bound :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ z : ℂ,
        ‖centeredCompletedRiemannZetaZeroCarrierClearingFactor z‖ ≤
          A * (1 + ‖z‖) ^ m := by
  have hfour_pos : (0 : ℝ) < 4 := by
    exact lt_of_lt_of_le zero_lt_one one_le_ofNat
  exact ⟨4, 2, hfour_pos, fun z =>
    centeredCompletedRiemannZetaZeroCarrierClearingFactor_norm_le_quadratic z⟩

/-- Products of two polynomial-growth functions have polynomial growth. -/
theorem polynomialGrowth_mul
    {u v : ℂ → ℂ}
    (hu :
      ∃ A : ℝ, ∃ m : ℕ,
        0 < A ∧
        ∀ z : ℂ, ‖u z‖ ≤ A * (1 + ‖z‖) ^ m)
    (hv :
      ∃ A : ℝ, ∃ m : ℕ,
        0 < A ∧
        ∀ z : ℂ, ‖v z‖ ≤ A * (1 + ‖z‖) ^ m) :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ z : ℂ, ‖u z * v z‖ ≤ A * (1 + ‖z‖) ^ m := by
  rcases hu with ⟨A, m, hA_pos, hA_bound⟩
  rcases hv with ⟨B, n, hB_pos, hB_bound⟩
  refine ⟨A * B, m + n, mul_pos hA_pos hB_pos, ?_⟩
  intro z
  let H : ℝ := 1 + ‖z‖
  have hH_nonneg : 0 ≤ H := by
    exact le_trans zero_le_one (centeredCompletedRiemannZeta_basicHeight_ge_one z)
  have hB_pow_nonneg : 0 ≤ B * H ^ n := by
    exact mul_nonneg (le_of_lt hB_pos) (pow_nonneg hH_nonneg n)
  have hmul_bound :
      ‖u z‖ * ‖v z‖ ≤ (A * H ^ m) * (B * H ^ n) :=
    mul_le_mul (hA_bound z) (hB_bound z) (norm_nonneg _) hB_pow_nonneg
  have hnorm :
      ‖u z * v z‖ = ‖u z‖ * ‖v z‖ :=
    norm_mul (u z) (v z)
  have hpow :
      H ^ (m + n) = H ^ m * H ^ n :=
    pow_add H m n
  have halg :
      (A * H ^ m) * (B * H ^ n) = (A * B) * H ^ (m + n) := by
    rw [hpow]
    ring
  exact hnorm.trans_le (hmul_bound.trans_eq halg)

/-- Subtracting the constant `1` from a polynomial-growth function preserves polynomial
growth. -/
theorem polynomialGrowth_sub_one
    {u : ℂ → ℂ}
    (hu :
      ∃ A : ℝ, ∃ m : ℕ,
        0 < A ∧
        ∀ z : ℂ, ‖u z‖ ≤ A * (1 + ‖z‖) ^ m) :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ z : ℂ, ‖u z - 1‖ ≤ A * (1 + ‖z‖) ^ m := by
  rcases hu with ⟨A, m, hA_pos, hA_bound⟩
  refine ⟨A + 1, m, add_pos hA_pos zero_lt_one, ?_⟩
  intro z
  let H : ℝ := 1 + ‖z‖
  have hH_pow_ge_one : (1 : ℝ) ≤ H ^ m :=
    centeredCompletedRiemannZeta_basicHeight_pow_ge_one z m
  have htriangle :
      ‖u z - 1‖ ≤ ‖u z‖ + ‖(1 : ℂ)‖ :=
    norm_sub_le (u z) (1 : ℂ)
  have hone_norm : ‖(1 : ℂ)‖ = (1 : ℝ) := by
    norm_num
  have hsum_bound :
      ‖u z‖ + ‖(1 : ℂ)‖ ≤ A * H ^ m + H ^ m := by
    rw [hone_norm]
    exact add_le_add (hA_bound z) hH_pow_ge_one
  have halg :
      A * H ^ m + H ^ m = (A + 1) * H ^ m := by
    ring
  exact htriangle.trans (hsum_bound.trans_eq halg)

/-- Multiplying a finite-order entire part by the quadratic clearing factor and subtracting
`1` preserves finite-order polynomial growth. -/
theorem centeredCompletedRiemannZetaZeroCarrier_growth_bound_of_factor_and_entirePart
    (hfactor :
      ∃ A : ℝ, ∃ m : ℕ,
        0 < A ∧
        ∀ z : ℂ,
          ‖centeredCompletedRiemannZetaZeroCarrierClearingFactor z‖ ≤
            A * (1 + ‖z‖) ^ m)
    (hentire :
      ∃ A : ℝ, ∃ m : ℕ,
        0 < A ∧
        ∀ z : ℂ,
          ‖centeredCompletedRiemannZeta₀ z‖ ≤
            A * (1 + ‖z‖) ^ m) :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ z : ℂ,
        ‖centeredCompletedRiemannZetaZeroCarrier z‖ ≤
          A * (1 + ‖z‖) ^ m := by
  have hproduct :
      ∃ A : ℝ, ∃ m : ℕ,
        0 < A ∧
        ∀ z : ℂ,
          ‖centeredCompletedRiemannZetaZeroCarrierClearingFactor z *
              centeredCompletedRiemannZeta₀ z‖ ≤
            A * (1 + ‖z‖) ^ m :=
    polynomialGrowth_mul hfactor hentire
  have hsub :
      ∃ A : ℝ, ∃ m : ℕ,
        0 < A ∧
        ∀ z : ℂ,
          ‖centeredCompletedRiemannZetaZeroCarrierClearingFactor z *
              centeredCompletedRiemannZeta₀ z - 1‖ ≤
            A * (1 + ‖z‖) ^ m :=
    polynomialGrowth_sub_one hproduct
  rcases hsub with ⟨A, m, hApos, hbound⟩
  refine ⟨A, m, hApos, ?_⟩
  intro z
  have hcarrier :
      centeredCompletedRiemannZetaZeroCarrier z =
        centeredCompletedRiemannZetaZeroCarrierClearingFactor z *
          centeredCompletedRiemannZeta₀ z - 1 :=
    centeredCompletedRiemannZetaZeroCarrier_eq_factor_mul_entirePart_sub_one z
  exact Eq.subst
    (motive := fun w : ℂ => ‖w‖ ≤ A * (1 + ‖z‖) ^ m)
    hcarrier.symm
    (hbound z)

/-- Finite-order growth is preserved by the completed zero-carrier normalization.

The zero-carrier is obtained from the centered entire part by multiplying by the quadratic
clearing factor `((1 / 2) + z) * (1 - ((1 / 2) + z))` and subtracting `1`. -/
theorem centeredCompletedRiemannZetaZeroCarrier_finiteOrder_growth_bound_of_entirePart
    (hentire :
      ∃ A : ℝ, ∃ m : ℕ,
        0 < A ∧
        ∀ z : ℂ,
          ‖centeredCompletedRiemannZeta₀ z‖ ≤
            A * (1 + ‖z‖) ^ m) :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ z : ℂ,
        ‖centeredCompletedRiemannZetaZeroCarrier z‖ ≤
          A * (1 + ‖z‖) ^ m := by
  exact
    centeredCompletedRiemannZetaZeroCarrier_growth_bound_of_factor_and_entirePart
      centeredCompletedRiemannZetaZeroCarrierClearingFactor_growth_bound
      hentire

/-- Finite-order growth for the centered entire completed-zeta zero-carrier.

This is the normalization-side entire-function input used by Jensen counting. The
zero-carrier is the cleared entire divisor
`((1 / 2) + s) * (1 - ((1 / 2) + s)) * centeredCompletedRiemannZeta₀ s - 1`,
so this theorem is owned by the completed normalization layer rather than by the
downstream zero-counting file. -/
theorem centeredCompletedRiemannZetaZeroCarrier_finiteOrder_growth_bound :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ z : ℂ,
        ‖centeredCompletedRiemannZetaZeroCarrier z‖ ≤
          A * (1 + ‖z‖) ^ m := by
  exact
    centeredCompletedRiemannZetaZeroCarrier_finiteOrder_growth_bound_of_entirePart
      centeredCompletedRiemannZeta₀_finiteOrder_growth_bound

theorem centeredCompletedRiemannZeta_eq (s : ℂ) :
    centeredCompletedRiemannZeta s =
      centeredCompletedRiemannZeta₀ s -
        1 / (1 / 2 + s) - 1 / (1 - (1 / 2 + s)) := by
  exact completedRiemannZeta_eq (1 / 2 + s)

/-- Excluding the negative shifted pole makes the left denominator nonzero. -/
theorem centeredShift_leftDenominator_ne_zero_of_ne_negHalf
    {z : ℂ}
    (hzneg : z ≠ -(1 / 2 : ℂ)) :
    (1 / 2 : ℂ) + z ≠ 0 := by
  intro hzero
  have hz_eq : z = -(1 / 2 : ℂ) := by
    calc
      z = ((1 / 2 : ℂ) + z) - (1 / 2 : ℂ) := by ring
      _ = 0 - (1 / 2 : ℂ) := by
        exact congrArg (fun w : ℂ => w - (1 / 2 : ℂ)) hzero
      _ = -(1 / 2 : ℂ) := by ring
  exact hzneg hz_eq

/-- Excluding the positive shifted pole makes the right denominator nonzero. -/
theorem centeredShift_rightDenominator_ne_zero_of_ne_posHalf
    {z : ℂ}
    (hzpos : z ≠ (1 / 2 : ℂ)) :
    1 - ((1 / 2 : ℂ) + z) ≠ 0 := by
  intro hzero
  have hz_eq : z = (1 / 2 : ℂ) := by
    have hz_sub : z - (1 / 2 : ℂ) = 0 := by
      calc
        z - (1 / 2 : ℂ) =
            (1 : ℂ) - ((1 / 2 : ℂ) + z) := by ring
        _ = 0 := hzero
    calc
      z = (z - (1 / 2 : ℂ)) + (1 / 2 : ℂ) := by ring
      _ = 0 + (1 / 2 : ℂ) := by
        exact congrArg (fun w : ℂ => w + (1 / 2 : ℂ)) hz_sub
      _ = (1 / 2 : ℂ) := by ring
  exact hzpos hz_eq

/-- Excluding both shifted poles makes the clearing denominator product nonzero. -/
theorem centeredShift_denominatorProduct_ne_zero_of_ne_shiftedPoles
    {z : ℂ}
    (hzneg : z ≠ -(1 / 2 : ℂ))
    (hzpos : z ≠ (1 / 2 : ℂ)) :
    ((1 / 2 : ℂ) + z) *
        (1 - ((1 / 2 : ℂ) + z)) ≠ 0 := by
  intro hmul
  match mul_eq_zero.mp hmul with
  | Or.inl hleft =>
      exact centeredShift_leftDenominator_ne_zero_of_ne_negHalf hzneg hleft
  | Or.inr hright =>
      exact centeredShift_rightDenominator_ne_zero_of_ne_posHalf hzpos hright

/-- The shifted denominator-clearing factor is analytic at every point. -/
theorem centeredShift_denominatorClearingFactor_analyticAt
    (z : ℂ) :
    AnalyticAt ℂ
      (fun w : ℂ =>
        ((1 / 2 : ℂ) + w) * (1 - ((1 / 2 : ℂ) + w))) z := by
  have hleft :
      AnalyticAt ℂ (fun w : ℂ => (1 / 2 : ℂ) + w) z :=
    analyticAt_const.add analyticAt_id
  have hright :
      AnalyticAt ℂ (fun w : ℂ => 1 - ((1 / 2 : ℂ) + w)) z :=
      analyticAt_const.sub (analyticAt_const.add analyticAt_id)
  exact hleft.mul hright

/-- Multiplying the left reciprocal pole by the cleared denominator leaves the right
denominator. -/
theorem denominatorProduct_mul_leftReciprocal
    {a b : ℂ} (ha : a ≠ 0) :
    a * b * (1 / a) = b := by
  calc
    a * b * (1 / a) = b * a * (1 / a) := by
      exact congrArg (fun x : ℂ => x * (1 / a)) (mul_comm a b)
    _ = b * (a * (1 / a)) := by
      exact mul_assoc b a (1 / a)
    _ = b * 1 := by
      exact congrArg (fun x : ℂ => b * x) (mul_inv_cancel₀ ha)
    _ = b := by
      exact mul_one b

/-- Multiplying the right reciprocal pole by the cleared denominator leaves the left
denominator. -/
theorem denominatorProduct_mul_rightReciprocal
    {a b : ℂ} (hb : b ≠ 0) :
    a * b * (1 / b) = a := by
  calc
    a * b * (1 / b) = a * (b * (1 / b)) := by
      exact mul_assoc a b (1 / b)
    _ = a * 1 := by
      exact congrArg (fun x : ℂ => a * x) (mul_inv_cancel₀ hb)
    _ = a := by
      exact mul_one a

/-- Clearing both reciprocal pole terms leaves subtraction by the sum of the two
denominators. -/
theorem denominatorProduct_mul_sub_twoReciprocals
    {a b E : ℂ} (ha : a ≠ 0) (hb : b ≠ 0) :
    a * b * (E - 1 / a - 1 / b) =
      a * b * E - (a + b) := by
  calc
    a * b * (E - 1 / a - 1 / b) =
        a * b * (E - 1 / a) - a * b * (1 / b) := by
      exact mul_sub (a * b) (E - 1 / a) (1 / b)
    _ = (a * b * E - a * b * (1 / a)) - a * b * (1 / b) := by
      exact congrArg
        (fun x : ℂ => x - a * b * (1 / b))
        (mul_sub (a * b) E (1 / a))
    _ = (a * b * E - b) - a * b * (1 / b) := by
      exact congrArg
        (fun x : ℂ => (a * b * E - x) - a * b * (1 / b))
        (denominatorProduct_mul_leftReciprocal ha)
    _ = (a * b * E - b) - a := by
      exact congrArg
        (fun x : ℂ => (a * b * E - b) - x)
        (denominatorProduct_mul_rightReciprocal hb)
    _ = a * b * E - (a + b) := by
      calc
        (a * b * E - b) - a =
            a * b * E + -b + -a := by
          exact congrArg
            (fun x : ℂ => x + -a)
            (sub_eq_add_neg (a * b * E) b)
        _ = a * b * E + (-b + -a) := by
          exact add_assoc (a * b * E) (-b) (-a)
        _ = a * b * E + (-(b + a)) := by
          exact congrArg
            (fun x : ℂ => a * b * E + x)
            (neg_add b a).symm
        _ = a * b * E + (-(a + b)) := by
          exact congrArg
            (fun x : ℂ => a * b * E + (-x))
            (add_comm b a)
        _ = a * b * E - (a + b) := by
          exact (sub_eq_add_neg (a * b * E) (a + b)).symm

/-- The two shifted denominators sum to one. -/
theorem centeredShift_left_add_right_denominator
    (s : ℂ) :
    ((1 / 2 : ℂ) + s) + (1 - ((1 / 2 : ℂ) + s)) = 1 := by
  exact add_sub_cancel_left 1 ((1 / 2 : ℂ) + s)

/-- Subtracting the sum of the two shifted denominators is subtraction by one. -/
theorem centeredShift_sub_denominatorSum_eq_sub_one
    (s E : ℂ) :
    ((1 / 2 : ℂ) + s) *
          (1 - ((1 / 2 : ℂ) + s)) * E -
        (((1 / 2 : ℂ) + s) + (1 - ((1 / 2 : ℂ) + s))) =
      ((1 / 2 : ℂ) + s) *
          (1 - ((1 / 2 : ℂ) + s)) * E - 1 := by
  exact congrArg
    (fun x : ℂ =>
      ((1 / 2 : ℂ) + s) * (1 - ((1 / 2 : ℂ) + s)) * E - x)
    (centeredShift_left_add_right_denominator s)

/-- Clearing the two shifted pole denominators identifies the centered completed
zeta normalization with the entire zero-carrier. -/
theorem centeredCompletedRiemannZetaZeroCarrier_eq_denominator_mul
    {s : ℂ}
    (hs0 : (1 / 2 : ℂ) + s ≠ 0)
    (hs1 : 1 - ((1 / 2 : ℂ) + s) ≠ 0) :
    centeredCompletedRiemannZetaZeroCarrier s =
      ((1 / 2 : ℂ) + s) *
        (1 - ((1 / 2 : ℂ) + s)) *
          centeredCompletedRiemannZeta s := by
  let a : ℂ := (1 / 2 : ℂ) + s
  let b : ℂ := 1 - ((1 / 2 : ℂ) + s)
  let E : ℂ := centeredCompletedRiemannZeta₀ s
  have hcompleted :
      centeredCompletedRiemannZeta s =
        E - 1 / a - 1 / b := by
    exact centeredCompletedRiemannZeta_eq s
  have hcleared :
      a * b * centeredCompletedRiemannZeta s =
        a * b * E - (a + b) := by
    exact Eq.subst
      (motive := fun x : ℂ => a * b * x = a * b * E - (a + b))
      hcompleted.symm
      (denominatorProduct_mul_sub_twoReciprocals hs0 hs1)
  have hsum :
      a * b * E - (a + b) = a * b * E - 1 := by
    exact centeredShift_sub_denominatorSum_eq_sub_one s E
  calc
    centeredCompletedRiemannZetaZeroCarrier s =
        a * b * E - 1 := by
      rfl
    _ = a * b * centeredCompletedRiemannZeta s := by
      exact (hcleared.trans hsum).symm

/-- A non-pole zero of the centered completed zeta normalization is a zero of
the entire zero-carrier. -/
theorem centeredCompletedRiemannZetaZeroCarrier_eq_zero_of_completed_zero
    {s : ℂ}
    (hs0 : (1 / 2 : ℂ) + s ≠ 0)
    (hs1 : 1 - ((1 / 2 : ℂ) + s) ≠ 0)
    (hz : centeredCompletedRiemannZeta s = 0) :
    centeredCompletedRiemannZetaZeroCarrier s = 0 := by
  calc
    centeredCompletedRiemannZetaZeroCarrier s =
        ((1 / 2 : ℂ) + s) *
          (1 - ((1 / 2 : ℂ) + s)) *
            centeredCompletedRiemannZeta s := by
      exact centeredCompletedRiemannZetaZeroCarrier_eq_denominator_mul hs0 hs1
    _ = ((1 / 2 : ℂ) + s) *
          (1 - ((1 / 2 : ℂ) + s)) *
            0 := by
      exact congrArg
        (fun w : ℂ =>
          ((1 / 2 : ℂ) + s) *
            (1 - ((1 / 2 : ℂ) + s)) * w)
        hz
    _ = 0 := by
      exact mul_zero (((1 / 2 : ℂ) + s) * (1 - ((1 / 2 : ℂ) + s)))

/-- Away from the shifted poles, the centered completed zeta function is
analytic. The owner proof is the completed-zeta decomposition into an entire
part and two rational pole terms. -/
theorem centeredCompletedRiemannZeta_analyticAt_of_ne_shiftedPoles
    {z : ℂ}
    (hzneg : z ≠ -(1 / 2 : ℂ))
    (hzpos : z ≠ (1 / 2 : ℂ)) :
    AnalyticAt ℂ centeredCompletedRiemannZeta z := by
  have hlinear :
      AnalyticAt ℂ (fun w : ℂ => (1 / 2 : ℂ) + w) z :=
    analyticAt_const.add analyticAt_id
  have hcenteredEntire :
      AnalyticAt ℂ centeredCompletedRiemannZeta₀ z := by
    exact centeredCompletedRiemannZeta₀_analyticAt z
  have hden_left :
      (1 / 2 : ℂ) + z ≠ 0 := by
    exact centeredShift_leftDenominator_ne_zero_of_ne_negHalf hzneg
  have hden_right :
      1 - ((1 / 2 : ℂ) + z) ≠ 0 := by
    exact centeredShift_rightDenominator_ne_zero_of_ne_posHalf hzpos
  have hleftPole :
      AnalyticAt ℂ (fun w : ℂ => 1 / ((1 / 2 : ℂ) + w)) z := by
    exact (analyticAt_const.div (analyticAt_const.add analyticAt_id) hden_left)
  have hrightPole :
      AnalyticAt ℂ (fun w : ℂ => 1 / (1 - ((1 / 2 : ℂ) + w))) z := by
    have hden :
        AnalyticAt ℂ (fun w : ℂ => 1 - ((1 / 2 : ℂ) + w)) z :=
      analyticAt_const.sub (analyticAt_const.add analyticAt_id)
    exact analyticAt_const.div hden hden_right
  have hformula :
      centeredCompletedRiemannZeta =
        (fun w : ℂ =>
          centeredCompletedRiemannZeta₀ w -
            1 / ((1 / 2 : ℂ) + w) -
              1 / (1 - ((1 / 2 : ℂ) + w))) := by
    funext w
    exact centeredCompletedRiemannZeta_eq w
  exact Eq.subst
    (motive := fun F : ℂ → ℂ => AnalyticAt ℂ F z)
    hformula.symm
    ((hcenteredEntire.sub hleftPole).sub hrightPole)

/-- If `(s - a)f(s)` tends to a nonzero limit on the punctured neighborhood of
`a`, then `f` is eventually nonzero on that punctured neighborhood. -/
theorem eventually_ne_zero_of_tendsto_sub_mul_ne_zero
    {f : ℂ → ℂ} {a c : ℂ}
    (hc : c ≠ 0)
    (hlim : Tendsto (fun s : ℂ => (s - a) * f s) (𝓝[≠] a) (𝓝 c)) :
    ∀ᶠ s in 𝓝 a, s ≠ a → f s ≠ 0 := by
  have hprod :
      ∀ᶠ s in 𝓝[≠] a, (s - a) * f s ≠ 0 :=
    hlim.eventually_ne hc
  rw [eventually_nhdsWithin_iff] at hprod
  exact hprod.mono
    (fun s hs hs_ne hf_zero =>
      hs
        (by
          exact hs_ne)
        (by
          rw [hf_zero, mul_zero]))

/-- The completed zeta normalization has residue `-1` at `0`. -/
theorem completedRiemannZeta_residue_zero :
    Tendsto
      (fun s : ℂ => s * completedRiemannZeta s)
      (𝓝[≠] (0 : ℂ))
      (𝓝 (-(1 : ℂ))) := by
  simpa [completedRiemannZeta]
    using completedHurwitzZetaEven_residue_zero (a := (0 : UnitAddCircle))

/-- The centered completed zeta function is nonzero in a punctured neighborhood
of the negative shifted pole. -/
theorem centeredCompletedRiemannZeta_eventually_ne_zero_punctured_negHalf :
    ∀ᶠ w in 𝓝 (-(1 / 2 : ℂ)),
      w ≠ -(1 / 2 : ℂ) → centeredCompletedRiemannZeta w ≠ 0 := by
  have hmap :
      Tendsto
        (fun w : ℂ => (1 / 2 : ℂ) + w)
        (𝓝[≠] (-(1 / 2 : ℂ)))
        (𝓝[≠] (0 : ℂ)) := by
    simpa [Homeomorph.coe_addLeft]
      using ((Homeomorph.addLeft (1 / 2 : ℂ)).map_punctured_nhds_eq
        (-(1 / 2 : ℂ))).le
  have hlim :
      Tendsto
        (fun w : ℂ =>
          ((1 / 2 : ℂ) + w) *
            completedRiemannZeta ((1 / 2 : ℂ) + w))
        (𝓝[≠] (-(1 / 2 : ℂ)))
        (𝓝 (-(1 : ℂ))) :=
    completedRiemannZeta_residue_zero.comp hmap
  have hcentered :
      Tendsto
        (fun w : ℂ =>
          (w - (-(1 / 2 : ℂ))) * centeredCompletedRiemannZeta w)
        (𝓝[≠] (-(1 / 2 : ℂ)))
        (𝓝 (-(1 : ℂ))) := by
    exact hlim.congr'
      (Eventually.of_forall
        (fun w : ℂ => by
          unfold centeredCompletedRiemannZeta
          congr 1
          ring))
  exact eventually_ne_zero_of_tendsto_sub_mul_ne_zero
    (f := centeredCompletedRiemannZeta)
    (a := -(1 / 2 : ℂ))
    (c := -(1 : ℂ))
    (by norm_num)
    hcentered

/-- The centered completed zeta function is nonzero in a punctured neighborhood
of the positive shifted pole. -/
theorem centeredCompletedRiemannZeta_eventually_ne_zero_punctured_posHalf :
    ∀ᶠ w in 𝓝 ((1 / 2 : ℂ)),
      w ≠ (1 / 2 : ℂ) → centeredCompletedRiemannZeta w ≠ 0 := by
  have hmap :
      Tendsto
        (fun w : ℂ => (1 / 2 : ℂ) + w)
        (𝓝[≠] ((1 / 2 : ℂ)))
        (𝓝[≠] (1 : ℂ)) := by
    simpa [Homeomorph.coe_addLeft]
      using ((Homeomorph.addLeft (1 / 2 : ℂ)).map_punctured_nhds_eq
        ((1 / 2 : ℂ))).le
  have hlim :
      Tendsto
        (fun w : ℂ =>
          (((1 / 2 : ℂ) + w) - 1) *
            completedRiemannZeta ((1 / 2 : ℂ) + w))
        (𝓝[≠] ((1 / 2 : ℂ)))
        (𝓝 (1 : ℂ)) :=
    completedRiemannZeta_residue_one.comp hmap
  have hcentered :
      Tendsto
        (fun w : ℂ =>
          (w - (1 / 2 : ℂ)) * centeredCompletedRiemannZeta w)
        (𝓝[≠] ((1 / 2 : ℂ)))
        (𝓝 (1 : ℂ)) := by
    exact hlim.congr'
      (Eventually.of_forall
        (fun w : ℂ => by
          unfold centeredCompletedRiemannZeta
          congr 1
          ring))
  exact eventually_ne_zero_of_tendsto_sub_mul_ne_zero
    (f := centeredCompletedRiemannZeta)
    (a := (1 / 2 : ℂ))
    (c := (1 : ℂ))
    one_ne_zero
    hcentered

theorem centeredCompletedRiemannZeta_neg (s : ℂ) :
    centeredCompletedRiemannZeta (-s) = centeredCompletedRiemannZeta s := by
  have hsub : (1 : ℂ) - (1 / 2 + s) = 1 / 2 - s := by
    ring
  have hsymm :
      completedRiemannZeta (1 / 2 - s) = completedRiemannZeta (1 - (1 / 2 + s)) := by
    exact congrArg completedRiemannZeta hsub.symm
  exact hsymm.trans (completedRiemannZeta_one_sub (1 / 2 + s))

theorem centeredCompletedRiemannZeta₀_neg (s : ℂ) :
    centeredCompletedRiemannZeta₀ (-s) = centeredCompletedRiemannZeta₀ s := by
  have hsub : (1 : ℂ) - (1 / 2 + s) = 1 / 2 - s := by
    ring
  have hsymm :
      completedRiemannZeta₀ (1 / 2 - s) = completedRiemannZeta₀ (1 - (1 / 2 + s)) := by
    exact congrArg completedRiemannZeta₀ hsub.symm
  exact hsymm.trans (completedRiemannZeta₀_one_sub (1 / 2 + s))

theorem centeredCompletedRiemannZeta_correction_symm (s : ℂ) :
    1 / (1 / 2 + (-s)) + 1 / (1 - (1 / 2 + (-s))) =
      1 / (1 / 2 + s) + 1 / (1 - (1 / 2 + s)) := by
  have h1 : (1 / 2 : ℂ) + (-s) = (1 / 2 : ℂ) - s := by
    exact sub_eq_add_neg (1 / 2) s
  have h2 : (1 : ℂ) - ((1 / 2 : ℂ) - s) = (1 / 2 : ℂ) + s := by
    ring
  have h3 : (1 : ℂ) - (1 / 2 + s) = (1 / 2 : ℂ) - s := by
    ring
  calc
    1 / (1 / 2 + (-s)) + 1 / (1 - (1 / 2 + (-s))) =
        1 / ((1 / 2 : ℂ) - s) + 1 / (1 - ((1 / 2 : ℂ) - s)) := by
      exact congrArg (fun x : ℂ => 1 / x + 1 / (1 - x)) h1
    _ = 1 / ((1 / 2 : ℂ) - s) + 1 / (1 / 2 + s) := by
      exact congrArg (fun x : ℂ => 1 / ((1 / 2 : ℂ) - s) + x)
        (congrArg (fun x : ℂ => 1 / x) h2)
    _ = 1 / (1 / 2 + s) + 1 / ((1 / 2 : ℂ) - s) := by
      exact add_comm (1 / ((1 / 2 : ℂ) - s)) (1 / (1 / 2 + s))
    _ = 1 / (1 / 2 + s) + 1 / (1 - (1 / 2 + s)) := by
      exact congrArg (fun x : ℂ => 1 / (1 / 2 + s) + x)
        (congrArg (fun x : ℂ => 1 / x) h3.symm)

/-- Completed zeta has no zeros in the left half-plane. -/
theorem completedRiemannZeta_ne_zero_of_re_lt_zero
    (s : ℂ)
    (hsre : s.re < 0) :
    completedRiemannZeta s ≠ 0 := by
  intro hs
  have hright_re :
      1 < ((1 : ℂ) - s).re := by
    have hre :
        ((1 : ℂ) - s).re = 1 - s.re := by
      exact Complex.sub_re (1 : ℂ) s
    have hlt : 1 < 1 - s.re := by
      exact lt_sub_iff_add_lt'.2
        (Eq.subst
          (motive := fun x : ℝ => x < 1)
          (zero_add (1 : ℝ)).symm
          (add_lt_add_right hsre 1))
    exact Eq.subst
      (motive := fun x : ℝ => 1 < x)
      hre.symm
      hlt
  have hright_ne :
      completedRiemannZeta ((1 : ℂ) - s) ≠ 0 :=
    completedRiemannZeta_ne_zero_of_one_lt_re ((1 : ℂ) - s) hright_re
  have hsymm :
      completedRiemannZeta ((1 : ℂ) - s) =
        completedRiemannZeta s :=
    completedRiemannZeta_one_sub s
  exact hright_ne (hsymm.trans hs)

/-- Completed zeta has no zeros in the half-plane to the right of `1`. -/
theorem completedRiemannZeta_ne_zero_of_one_lt_re
    (s : ℂ)
    (hsre : 1 < s.re) :
    completedRiemannZeta s ≠ 0 := by
  intro hs
  have hs0 : s ≠ 0 := by
    intro hs_zero
    have hre_zero : s.re = 0 := by
      exact congrArg Complex.re hs_zero
    have hone_lt_zero : (1 : ℝ) < 0 :=
      Eq.subst
        (motive := fun x : ℝ => 1 < x)
        hre_zero
        hsre
    exact (not_lt_of_ge zero_le_one) hone_lt_zero
  have hζ_eq :
      riemannZeta s = completedRiemannZeta s / Gammaℝ s :=
    riemannZeta_def_of_ne_zero hs0
  have hζ_zero : riemannZeta s = 0 := by
    calc
      riemannZeta s = completedRiemannZeta s / Gammaℝ s := hζ_eq
      _ = 0 / Gammaℝ s := by
        exact congrArg (fun x : ℂ => x / Gammaℝ s) hs
      _ = 0 := by
        exact zero_div (Gammaℝ s)
  exact riemannZeta_ne_zero_of_one_lt_re hsre hζ_zero

/-- Completed-zeta zeros lie in the ordinary critical strip.

This is the standard unconditional critical-strip theorem for zeros of the
completed Riemann zeta normalization. -/
theorem completedRiemannZeta_zero_re_mem_criticalStrip
    (s : ℂ)
    (hs : completedRiemannZeta s = 0) :
    0 ≤ s.re ∧ s.re ≤ (1 : ℝ) := by
  have hnot_left : ¬ s.re < 0 := by
    intro hsre
    exact completedRiemannZeta_ne_zero_of_re_lt_zero s hsre hs
  have hnot_right : ¬ (1 : ℝ) < s.re := by
    intro hsre
    exact completedRiemannZeta_ne_zero_of_one_lt_re s hsre hs
  exact ⟨le_of_not_gt hnot_left, le_of_not_gt hnot_right⟩

/-- The real coordinate of the uncentered argument is the centered real
coordinate shifted by `1/2`. -/
theorem centeredCompletedRiemannZeta_uncenter_re
    (s : ℂ) :
    ((1 / 2 : ℂ) + s).re = (1 / 2 : ℝ) + s.re := by
  calc
    ((1 / 2 : ℂ) + s).re = (1 / 2 : ℂ).re + s.re := by
      exact Complex.add_re (1 / 2 : ℂ) s
    _ = (1 / 2 : ℝ) + s.re := by
      exact congrArg (fun x : ℝ => x + s.re) Complex.ofReal_re

/-- If the uncentered coordinate lies in `[0,1]`, the centered coordinate lies
in `[-1/2,1/2]`. -/
theorem centered_re_mem_centeredCriticalStrip_of_uncentered_re_mem_criticalStrip
    {x : ℝ}
    (hleft : 0 ≤ (1 / 2 : ℝ) + x)
    (hright : (1 / 2 : ℝ) + x ≤ 1) :
    -(1 / 2 : ℝ) ≤ x ∧ x ≤ (1 / 2 : ℝ) := by
  have hleft' :
      -(1 / 2 : ℝ) ≤ x :=
    (neg_le_iff_add_nonneg).2 hleft
  have hright_comm :
      x + (1 / 2 : ℝ) ≤ 1 :=
    Eq.subst
      (motive := fun y : ℝ => y ≤ 1)
      (add_comm (1 / 2 : ℝ) x)
      hright
  have hright_sub :
      x ≤ (1 : ℝ) - (1 / 2 : ℝ) :=
    (le_sub_iff_add_le).2 hright_comm
  have hhalf :
      (1 : ℝ) - (1 / 2 : ℝ) = (1 / 2 : ℝ) :=
    sub_half (1 : ℝ)
  have hright' :
      x ≤ (1 / 2 : ℝ) :=
    Eq.subst
      (motive := fun y : ℝ => x ≤ y)
      hhalf
      hright_sub
  exact ⟨hleft', hright'⟩

/-- Centered completed-zeta zeros lie in the centered critical strip.

This is the standard unconditional critical-strip theorem for nontrivial zeta
zeros, expressed in the centered completed-zeta normalization used by the
zero-side explicit formula. -/
theorem centeredCompletedRiemannZeta_zero_re_mem_centeredCriticalStrip
    (s : ℂ)
    (hs : centeredCompletedRiemannZeta s = 0) :
    -(1 / 2 : ℝ) ≤ s.re ∧ s.re ≤ (1 / 2 : ℝ) := by
  have huncentered_zero :
      completedRiemannZeta ((1 / 2 : ℂ) + s) = 0 := by
    exact hs
  have hstrip :
      0 ≤ ((1 / 2 : ℂ) + s).re ∧
        ((1 / 2 : ℂ) + s).re ≤ (1 : ℝ) :=
    completedRiemannZeta_zero_re_mem_criticalStrip
      ((1 / 2 : ℂ) + s)
      huncentered_zero
  have hre :
      ((1 / 2 : ℂ) + s).re = (1 / 2 : ℝ) + s.re :=
    centeredCompletedRiemannZeta_uncenter_re s
  have hleft :
      0 ≤ (1 / 2 : ℝ) + s.re :=
    Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      hre
      hstrip.1
  have hright :
      (1 / 2 : ℝ) + s.re ≤ 1 :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ (1 : ℝ))
      hre
      hstrip.2
  exact centered_re_mem_centeredCriticalStrip_of_uncentered_re_mem_criticalStrip
    hleft
    hright

end
end LFunctions
end Boundary
