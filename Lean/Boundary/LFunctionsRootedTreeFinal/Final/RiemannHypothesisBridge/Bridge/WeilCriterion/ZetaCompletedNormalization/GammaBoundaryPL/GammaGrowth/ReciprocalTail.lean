import Mathlib.Data.Real.Pi.Bounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.FixedVerticalEnvelope.ReciprocalHalfStrip

/-!
# Reciprocal Gamma boundary growth tail

This file owns the reciprocal `Gammaℝ` finite-order vertical-tail transport on
the right critical half-strip.  It is split from `GammaGrowth.Owner` so the
large owner file only re-exports the completed construction.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- Division by two is the negative of division by two after negating the numerator. -/
theorem real_div_two_eq_neg_neg_div_two (x : ℝ) :
    x / 2 = -((-x) / 2) := by
  have hneg_left :
      x / 2 = -(-(x / 2)) :=
    (neg_neg (x / 2)).symm
  have hneg_div :
      -(x / 2) = (-x) / 2 :=
    (neg_div (2 : ℝ) x).symm
  exact Eq.trans hneg_left (congrArg Neg.neg hneg_div)

/-- Real-part transport for the negative half argument used by reciprocal tails. -/
theorem reciprocalTail_neg_halfArgument_re_eq_neg_re_div_two
    (z : ℂ) :
    (-z / 2 : ℂ).re = -z.re / 2 := by
  have hdiv : (-z / 2 : ℂ).re = (-z).re / (2 : ℝ) :=
    RCLike.div_re_ofReal (z := -z) (r := (2 : ℝ))
  have hneg : (-z).re = -z.re :=
    Complex.neg_re z
  calc
    (-z / 2 : ℂ).re = (-z).re / (2 : ℝ) := hdiv
    _ = -z.re / 2 := congrArg (fun x : ℝ => x / 2) hneg

/-- The reciprocal `π ^ (-z / 2)` normalization is uniformly bounded on
`0 ≤ Re z ≤ 1`. -/
theorem pi_cpow_neg_halfArgument_inv_norm_le_pi
    {z : ℂ}
    (hz_re_nonneg : 0 ≤ z.re)
    (hz_re_le_one : z.re ≤ 1) :
    ‖((π : ℂ) ^ (-z / 2 : ℂ))⁻¹‖ ≤ π := by
  let P : ℂ := (π : ℂ) ^ (-z / 2 : ℂ)
  have hpi_pos : (0 : ℝ) < π := Real.pi_pos
  have hpi_one_le : (1 : ℝ) ≤ π := by
    have hone_lt_three : (1 : ℝ) < 3 :=
      Nat.one_lt_ofNat
    exact le_of_lt (lt_trans hone_lt_three Real.pi_gt_three)
  have hnorm_eq : ‖P‖ = π ^ (-z / 2 : ℂ).re := by
    calc
      ‖P‖ = Complex.abs P := Complex.norm_eq_abs P
      _ = π ^ (-z / 2 : ℂ).re :=
        Complex.abs_cpow_eq_rpow_re_of_pos hpi_pos (-z / 2 : ℂ)
  have hinv_norm_eq : ‖P⁻¹‖ = ‖P‖⁻¹ :=
    norm_inv P
  have hre_neg_half : (-z / 2 : ℂ).re = -z.re / 2 :=
    reciprocalTail_neg_halfArgument_re_eq_neg_re_div_two z
  have hnorm_inv_rpow :
      ‖P‖⁻¹ = π ^ (z.re / 2) := by
    have hpow_neg :
        π ^ (z.re / 2) = (π ^ (-z.re / 2))⁻¹ := by
      have hneg : z.re / 2 = -(-z.re / 2) :=
        real_div_two_eq_neg_neg_div_two z.re
      exact Eq.trans
        (congrArg (fun u : ℝ => π ^ u) hneg)
        (Real.rpow_neg (le_of_lt hpi_pos) (-z.re / 2))
    calc
      ‖P‖⁻¹ = (π ^ (-z / 2 : ℂ).re)⁻¹ :=
        congrArg (fun u : ℝ => u⁻¹) hnorm_eq
      _ = (π ^ (-z.re / 2))⁻¹ :=
        congrArg (fun u : ℝ => u⁻¹)
          (congrArg (fun u : ℝ => π ^ u) hre_neg_half)
      _ = π ^ (z.re / 2) := hpow_neg.symm
  have hre_div_le_one : z.re / 2 ≤ 1 := by
    have htwo_pos : (0 : ℝ) < 2 := two_pos
    have hdiv_le_half : z.re / 2 ≤ 1 / 2 :=
      div_le_div_of_nonneg_right hz_re_le_one (le_of_lt htwo_pos)
    exact le_trans hdiv_le_half (div_le_self zero_le_one one_le_two)
  have hrpow_le_pi :
      π ^ (z.re / 2) ≤ π ^ (1 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hpi_one_le hre_div_le_one
  calc
    ‖((π : ℂ) ^ (-z / 2 : ℂ))⁻¹‖ = ‖P⁻¹‖ := rfl
    _ = ‖P‖⁻¹ := hinv_norm_eq
    _ = π ^ (z.re / 2) := hnorm_inv_rpow
    _ ≤ π ^ (1 : ℝ) := hrpow_le_pi
    _ = π := Real.rpow_one π

/-- The half-argument has real part at most `1 / 2` when the original real
part is at most `1`. -/
theorem halfArgument_re_le_half_of_re_le_one
    {z : ℂ}
    (hz_re_le_one : z.re ≤ 1) :
    (z / 2 : ℂ).re ≤ (1 / 2 : ℝ) := by
  have hdiv : (z / 2 : ℂ).re = z.re / 2 :=
    RCLike.div_re_ofReal (z := z) (r := (2 : ℝ))
  have hhalf : z.re / 2 ≤ 1 / 2 :=
    div_le_div_of_nonneg_right hz_re_le_one zero_le_two
  calc
    (z / 2 : ℂ).re = z.re / 2 := hdiv
    _ ≤ 1 / 2 := hhalf

/-- The half-argument imaginary coordinate has size at least `1 / 2` when the
original imaginary coordinate has size at least `1`. -/
theorem halfArgument_im_norm_ge_half_of_one_le_norm_im
    {z : ℂ}
    (hz_im_tail : 1 ≤ ‖z.im‖) :
    (1 / 2 : ℝ) ≤ ‖(z / 2 : ℂ).im‖ := by
  have him : (z / 2 : ℂ).im = z.im / 2 :=
    Complex.div_ofNat_im z 2
  have hnorm_div : ‖z.im / 2‖ = ‖z.im‖ / 2 := by
    calc
      ‖z.im / 2‖ = ‖z.im‖ / ‖(2 : ℝ)‖ := norm_div z.im 2
      _ = ‖z.im‖ / 2 := by
        exact congrArg (fun u : ℝ => ‖z.im‖ / u)
          (Real.norm_of_nonneg zero_le_two)
  have htail_div : (1 / 2 : ℝ) ≤ ‖z.im‖ / 2 := by
    have htwo_pos : (0 : ℝ) < 2 := two_pos
    calc
      (1 / 2 : ℝ) = 1 / 2 := rfl
      _ ≤ ‖z.im‖ / 2 :=
        div_le_div_of_nonneg_right hz_im_tail (le_of_lt htwo_pos)
  calc
    (1 / 2 : ℝ) ≤ ‖z.im‖ / 2 := htail_div
    _ = ‖z.im / 2‖ := hnorm_div.symm
    _ = ‖(z / 2 : ℂ).im‖ := congrArg norm him.symm

/-- The half-argument norm is bounded by the original norm. -/
theorem halfArgument_norm_le_norm (z : ℂ) :
    ‖z / 2‖ ≤ ‖z‖ := by
  have hnorm_div : ‖z / 2‖ = ‖z‖ / ‖(2 : ℂ)‖ :=
    norm_div z 2
  have htwo_norm : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    calc
      ‖(2 : ℂ)‖ = ‖(2 : ℝ)‖ := Complex.norm_real 2
      _ = (2 : ℝ) := Real.norm_of_nonneg zero_le_two
  have hdiv_le : ‖z‖ / 2 ≤ ‖z‖ :=
    div_le_self (norm_nonneg z) one_le_two
  calc
    ‖z / 2‖ = ‖z‖ / ‖(2 : ℂ)‖ := hnorm_div
    _ = ‖z‖ / 2 := congrArg (fun u : ℝ => ‖z‖ / u) htwo_norm
    _ ≤ ‖z‖ := hdiv_le

/-- The finite-order exponential envelope at the half-argument is bounded by
the same envelope at the original argument. -/
theorem halfArgument_exp_growth_le
    (A B : ℝ)
    (m : ℕ)
    (hA_pos : 0 < A)
    (hB_pos : 0 < B)
    (z : ℂ) :
    (A * Real.exp (B * (1 + ‖z / 2‖) ^ m)) * π ≤
      (A * Real.exp (B * (1 + ‖z‖) ^ m)) * π := by
  have hhalf_norm_le : ‖z / 2‖ ≤ ‖z‖ :=
    halfArgument_norm_le_norm z
  have hbase_le : 1 + ‖z / 2‖ ≤ 1 + ‖z‖ :=
    add_le_add_left hhalf_norm_le 1
  have hbase_nonneg : 0 ≤ 1 + ‖z / 2‖ :=
    le_trans zero_le_one
      (le_add_of_nonneg_right (norm_nonneg (z / 2)))
  have hpow_le :
      (1 + ‖z / 2‖) ^ m ≤ (1 + ‖z‖) ^ m :=
    pow_le_pow_left₀ hbase_nonneg hbase_le m
  have hexponent_le :
      B * (1 + ‖z / 2‖) ^ m ≤
        B * (1 + ‖z‖) ^ m :=
    mul_le_mul_of_nonneg_left hpow_le (le_of_lt hB_pos)
  have hexp_le :
      Real.exp (B * (1 + ‖z / 2‖) ^ m) ≤
        Real.exp (B * (1 + ‖z‖) ^ m) :=
    Real.exp_le_exp.mpr hexponent_le
  have hleft :
      A * Real.exp (B * (1 + ‖z / 2‖) ^ m) ≤
        A * Real.exp (B * (1 + ‖z‖) ^ m) :=
    mul_le_mul_of_nonneg_left hexp_le (le_of_lt hA_pos)
  exact mul_le_mul_of_nonneg_right hleft (le_of_lt Real.pi_pos)

/-- Move the `π` factor in the finite-order Gamma envelope to the leading
constant. -/
theorem gamma_growth_pi_assoc
    (A B : ℝ)
    (m : ℕ)
    (z : ℂ) :
    (A * Real.exp (B * (1 + ‖z‖) ^ m)) * π =
      (A * π) * Real.exp (B * (1 + ‖z‖) ^ m) := by
  calc
    (A * Real.exp (B * (1 + ‖z‖) ^ m)) * π =
        A * (Real.exp (B * (1 + ‖z‖) ^ m) * π) :=
      mul_assoc A (Real.exp (B * (1 + ‖z‖) ^ m)) π
    _ = A * (π * Real.exp (B * (1 + ‖z‖) ^ m)) := by
      exact congrArg (fun u : ℝ => A * u)
        (mul_comm (Real.exp (B * (1 + ‖z‖) ^ m)) π)
    _ = (A * π) * Real.exp (B * (1 + ‖z‖) ^ m) :=
      (mul_assoc A π (Real.exp (B * (1 + ‖z‖) ^ m))).symm

/-- Pointwise reciprocal finite-order Stirling bound for `Gammaℝ` on the
closed right critical half-strip, from the corresponding half-argument Gamma
bound. -/
theorem Gammaℝ_rightCriticalStrip_verticalTail_reciprocal_stirling_growth_pointwise
    (AΓ BΓ : ℝ)
    (mΓ : ℕ)
    (hAΓ_pos : 0 < AΓ)
    (hBΓ_pos : 0 < BΓ)
    (hΓ_bound :
      ∀ w : ℂ,
        0 ≤ w.re →
        w.re ≤ (1 / 2 : ℝ) →
        (1 / 2 : ℝ) ≤ ‖w.im‖ →
          ‖(Complex.Gamma w)⁻¹‖ ≤
            AΓ * Real.exp (BΓ * (1 + ‖w‖) ^ mΓ))
    (z : ℂ)
    (hz_re_nonneg : 0 ≤ z.re)
    (hz_re_le_one : z.re ≤ 1)
    (hz_im_tail : 1 ≤ ‖z.im‖) :
    ‖(Complex.Gammaℝ z)⁻¹‖ ≤
      (AΓ * π) * Real.exp (BΓ * (1 + ‖z‖) ^ mΓ) := by
  have hw_re_nonneg : 0 ≤ (z / 2 : ℂ).re :=
    halfArgument_re_nonneg_of_re_nonneg hz_re_nonneg
  have hw_re_half : (z / 2 : ℂ).re ≤ (1 / 2 : ℝ) :=
    halfArgument_re_le_half_of_re_le_one hz_re_le_one
  have hw_im_tail : (1 / 2 : ℝ) ≤ ‖(z / 2 : ℂ).im‖ :=
    halfArgument_im_norm_ge_half_of_one_le_norm_im hz_im_tail
  have hΓ :
      ‖(Complex.Gamma (z / 2))⁻¹‖ ≤
        AΓ * Real.exp (BΓ * (1 + ‖z / 2‖) ^ mΓ) :=
    hΓ_bound (z / 2) hw_re_nonneg hw_re_half hw_im_tail
  have hπ :
      ‖((π : ℂ) ^ (-z / 2 : ℂ))⁻¹‖ ≤ π :=
    pi_cpow_neg_halfArgument_inv_norm_le_pi
      hz_re_nonneg hz_re_le_one
  have hfactor :
      ‖(Complex.Gammaℝ z)⁻¹‖ =
        ‖(Complex.Gamma (z / 2))⁻¹‖ *
          ‖((π : ℂ) ^ (-z / 2 : ℂ))⁻¹‖ :=
    norm_inv_Gammaℝ_eq_norm_inv_complexGamma_half_mul_norm_inv_pi z
  have hπ_nonneg :
      0 ≤ ‖((π : ℂ) ^ (-z / 2 : ℂ))⁻¹‖ :=
    norm_nonneg (((π : ℂ) ^ (-z / 2 : ℂ))⁻¹)
  have hΓ_bound_nonneg :
      0 ≤ AΓ * Real.exp (BΓ * (1 + ‖z / 2‖) ^ mΓ) :=
    le_trans (norm_nonneg ((Complex.Gamma (z / 2))⁻¹)) hΓ
  have hproduct :
      ‖(Complex.Gamma (z / 2))⁻¹‖ *
          ‖((π : ℂ) ^ (-z / 2 : ℂ))⁻¹‖ ≤
        (AΓ * Real.exp (BΓ * (1 + ‖z / 2‖) ^ mΓ)) * π :=
    mul_le_mul hΓ hπ hπ_nonneg hΓ_bound_nonneg
  have hscaled_exp :
      (AΓ * Real.exp (BΓ * (1 + ‖z / 2‖) ^ mΓ)) * π ≤
        (AΓ * Real.exp (BΓ * (1 + ‖z‖) ^ mΓ)) * π :=
    halfArgument_exp_growth_le AΓ BΓ mΓ hAΓ_pos hBΓ_pos z
  have htarget_assoc :
      (AΓ * Real.exp (BΓ * (1 + ‖z‖) ^ mΓ)) * π =
        (AΓ * π) * Real.exp (BΓ * (1 + ‖z‖) ^ mΓ) :=
    gamma_growth_pi_assoc AΓ BΓ mΓ z
  calc
    ‖(Complex.Gammaℝ z)⁻¹‖ =
        ‖(Complex.Gamma (z / 2))⁻¹‖ *
          ‖((π : ℂ) ^ (-z / 2 : ℂ))⁻¹‖ := hfactor
    _ ≤ (AΓ * Real.exp (BΓ * (1 + ‖z / 2‖) ^ mΓ)) * π :=
      hproduct
    _ ≤ (AΓ * Real.exp (BΓ * (1 + ‖z‖) ^ mΓ)) * π :=
      hscaled_exp
    _ = (AΓ * π) * Real.exp (BΓ * (1 + ‖z‖) ^ mΓ) :=
      htarget_assoc

/-- Reciprocal finite-order Stirling bound for `Gammaℝ` on the closed
right critical half-strip. -/
theorem Gammaℝ_rightCriticalStrip_verticalTail_reciprocal_stirling_growth_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
          ‖(Complex.Gammaℝ z)⁻¹‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match Complex.Gamma_inv_zero_half_strip_verticalTail_finiteOrder_bound hbranch with
  | ⟨AΓ, BΓ, mΓ, hAΓ_pos, hBΓ_pos, hΓ_bound⟩ =>
      let A : ℝ := AΓ * π
      let B : ℝ := BΓ
      have hA_pos : 0 < A :=
        mul_pos hAΓ_pos Real.pi_pos
      have hB_pos : 0 < B := hBΓ_pos
      exact
        ⟨A, B, mΓ, hA_pos, hB_pos,
          fun z hz_re_nonneg hz_re_le_one hz_im_tail =>
            Gammaℝ_rightCriticalStrip_verticalTail_reciprocal_stirling_growth_pointwise
              AΓ BΓ mΓ hAΓ_pos hBΓ_pos hΓ_bound
              z hz_re_nonneg hz_re_le_one hz_im_tail⟩

end
end LFunctions
end Boundary
