import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.CompletedZetaGrowth.PoleCleared.OwnerParts.Part01_Foundation

/-!
# Pole-cleared zeta finite-order product algebra
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- Enlargement of a finite-order envelope over an explicit base at least one. -/
theorem finiteOrderEnvelope_le_of_coefficient_and_degree
    (A B B' H : ℝ)
    (m d : ℕ)
    (hA_nonnegative : 0 ≤ A)
    (hB_nonnegative : 0 ≤ B)
    (hB_le : B ≤ B')
    (hH_ge_one : 1 ≤ H)
    (hm_le : m ≤ d) :
    A * Real.exp (B * H ^ m) ≤ A * Real.exp (B' * H ^ d) := by
  have hH_nonnegative : 0 ≤ H := le_trans zero_le_one hH_ge_one
  have hpower_le : H ^ m ≤ H ^ d :=
    pow_le_pow_right₀ hH_ge_one hm_le
  have hfixed_coefficient : B * H ^ m ≤ B * H ^ d :=
    mul_le_mul_of_nonneg_left hpower_le hB_nonnegative
  have henlarged_coefficient : B * H ^ d ≤ B' * H ^ d :=
    mul_le_mul_of_nonneg_right hB_le (pow_nonneg hH_nonnegative d)
  have hexponent_le : B * H ^ m ≤ B' * H ^ d :=
    le_trans hfixed_coefficient henlarged_coefficient
  have hexponential_le :
      Real.exp (B * H ^ m) ≤ Real.exp (B' * H ^ d) :=
    Real.exp_le_exp.mpr hexponent_le
  exact mul_le_mul_of_nonneg_left hexponential_le hA_nonnegative

/-- The first factor in a finite-order product embeds into the common
coefficient and degree envelope. -/
theorem finiteOrderProduct_firstFactor_le_commonEnvelope
    (A B₁ B₂ H : ℝ)
    (m₁ m₂ : ℕ)
    (hA_nonnegative : 0 ≤ A)
    (hB₁_nonnegative : 0 ≤ B₁)
    (hB₂_nonnegative : 0 ≤ B₂)
    (hH_ge_one : 1 ≤ H) :
    A * Real.exp (B₁ * H ^ m₁) ≤
      A * Real.exp ((B₁ + B₂ + 1) * H ^ (m₁ + m₂)) :=
  finiteOrderEnvelope_le_of_coefficient_and_degree
    A B₁ (B₁ + B₂ + 1) H m₁ (m₁ + m₂)
    hA_nonnegative hB₁_nonnegative
    (le_trans
      (le_add_of_nonneg_right hB₂_nonnegative)
      (le_add_of_nonneg_right zero_le_one))
    hH_ge_one
    (Nat.le_add_right m₁ m₂)

/-- The second factor in a finite-order product embeds into the common
coefficient and degree envelope. -/
theorem finiteOrderProduct_secondFactor_le_commonEnvelope
    (A B₁ B₂ H : ℝ)
    (m₁ m₂ : ℕ)
    (hA_nonnegative : 0 ≤ A)
    (hB₁_nonnegative : 0 ≤ B₁)
    (hB₂_nonnegative : 0 ≤ B₂)
    (hH_ge_one : 1 ≤ H) :
    A * Real.exp (B₂ * H ^ m₂) ≤
      A * Real.exp ((B₁ + B₂ + 1) * H ^ (m₁ + m₂)) := by
  have hm₂_le : m₂ ≤ m₁ + m₂ :=
    Eq.subst
      (motive := fun degree : ℕ => m₂ ≤ degree)
      (Nat.add_comm m₂ m₁)
      (Nat.le_add_right m₂ m₁)
  exact
    finiteOrderEnvelope_le_of_coefficient_and_degree
      A B₂ (B₁ + B₂ + 1) H m₂ (m₁ + m₂)
      hA_nonnegative hB₂_nonnegative
      (le_trans
        (le_add_of_nonneg_left hB₁_nonnegative)
        (le_add_of_nonneg_right zero_le_one))
      hH_ge_one
      hm₂_le

/-- Two norm bounds in a common finite-order envelope give the standard
doubled-coefficient product bound. -/
theorem finiteOrderProduct_commonEnvelope_norm_bound
    (target first second : ℂ)
    (A₁ A₂ coefficient H : ℝ)
    (degree : ℕ)
    (hA₁_nonnegative : 0 ≤ A₁)
    (htarget_norm : ‖target‖ = ‖first‖ * ‖second‖)
    (hfirst : ‖first‖ ≤ A₁ * Real.exp (coefficient * H ^ degree))
    (hsecond : ‖second‖ ≤ A₂ * Real.exp (coefficient * H ^ degree)) :
    ‖target‖ ≤
      A₁ * A₂ * Real.exp ((2 * coefficient) * H ^ degree) := by
  have hproduct :
      ‖first‖ * ‖second‖ ≤
        (A₁ * Real.exp (coefficient * H ^ degree)) *
          (A₂ * Real.exp (coefficient * H ^ degree)) :=
    mul_le_mul hfirst hsecond
      (norm_nonneg second)
      (mul_nonneg hA₁_nonnegative
        (le_of_lt (Real.exp_pos (coefficient * H ^ degree))))
  have hcollapse :
      (A₁ * Real.exp (coefficient * H ^ degree)) *
          (A₂ * Real.exp (coefficient * H ^ degree)) =
        A₁ * A₂ * Real.exp ((2 * coefficient) * H ^ degree) :=
    finiteOrderGrowthProductEnvelope_exp_collapse
      A₁ A₂ coefficient (H ^ degree)
  exact Eq.subst
    (motive := fun value : ℝ =>
      value ≤ A₁ * A₂ * Real.exp ((2 * coefficient) * H ^ degree))
    htarget_norm.symm
    (hproduct.trans_eq hcollapse)

/-- Gamma/Stirling finite-order control of the reflected Gamma-real ratio on the
zero-one vertical band.

This is the special-function input for the raw completed-functional-equation
multiplier: sectorial/vertical recurrence Stirling bounds for
`Gammaℝ (1 - z) / Gammaℝ z`, uniformly on `0 ≤ Re z ≤ 1` and `|Im z| ≥ 1`. -/
theorem poleClearedRiemannZeta_zero_one_strip_GammaRatio_growth_ownerGammaStirling
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match Gammaℝ_one_sub_zeroOneStrip_verticalTail_stirling_growth_bound hbranch with
  | ⟨An, Bn, mn, hAn_pos, hBn_pos, hn_bound⟩ =>
      match Gammaℝ_rightCriticalStrip_verticalTail_reciprocal_stirling_growth_bound hbranch with
      | ⟨Ad, Bd, md, hAd_pos, hBd_pos, hd_bound⟩ =>
          exact
            ⟨An * Ad, 2 * (Bn + Bd + 1), mn + md,
              mul_pos hAn_pos hAd_pos,
              mul_pos zero_lt_two
                (add_pos (add_pos hBn_pos hBd_pos) zero_lt_one),
              fun z hz_re_nonneg hz_re_le_one hz_im_tail =>
                let H : ℝ := 1 + ‖z‖
                have hBn_nonnegative : 0 ≤ Bn := le_of_lt hBn_pos
                have hBd_nonnegative : 0 ≤ Bd := le_of_lt hBd_pos
                have hAn_nonnegative : 0 ≤ An := le_of_lt hAn_pos
                have hH_ge_one : 1 ≤ H :=
                  le_add_of_nonneg_right (norm_nonneg z)
                have hn_target :
                    ‖Complex.Gammaℝ ((1 : ℂ) - z)‖ ≤
                      An * Real.exp ((Bn + Bd + 1) * H ^ (mn + md)) :=
                  le_trans
                    (hn_bound z hz_re_nonneg hz_re_le_one hz_im_tail)
                    (finiteOrderProduct_firstFactor_le_commonEnvelope
                      An Bn Bd H mn md hAn_nonnegative
                      hBn_nonnegative hBd_nonnegative hH_ge_one)
                have hd_target :
                    ‖(Complex.Gammaℝ z)⁻¹‖ ≤
                      Ad * Real.exp ((Bn + Bd + 1) * H ^ (mn + md)) :=
                  le_trans
                    (hd_bound z hz_re_nonneg hz_re_le_one hz_im_tail)
                    (finiteOrderProduct_secondFactor_le_commonEnvelope
                      Ad Bn Bd H mn md (le_of_lt hAd_pos)
                      hBn_nonnegative hBd_nonnegative hH_ge_one)
                have hnorm :
                    ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ =
                      ‖Complex.Gammaℝ ((1 : ℂ) - z)‖ *
                        ‖(Complex.Gammaℝ z)⁻¹‖ := by
                  exact Eq.trans
                    (congrArg norm
                      (div_eq_mul_inv
                        (Complex.Gammaℝ ((1 : ℂ) - z))
                        (Complex.Gammaℝ z)))
                    (norm_mul
                      (Complex.Gammaℝ ((1 : ℂ) - z))
                      (Complex.Gammaℝ z)⁻¹)
                finiteOrderProduct_commonEnvelope_norm_bound
                  (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)
                  (Complex.Gammaℝ ((1 : ℂ) - z))
                  (Complex.Gammaℝ z)⁻¹
                  An Ad (Bn + Bd + 1) H (mn + md)
                  hAn_nonnegative hnorm hn_target hd_target⟩

/-- Product assembly for the raw completed-functional-equation multiplier on the
zero-one vertical band.

This is only finite-order bookkeeping: combine the pole-clearing quotient
envelope with the Gamma-ratio envelope and use multiplicativity of the norm. -/
theorem poleClearedRiemannZeta_zero_one_strip_raw_completedFunctionalEquationMultiplier_growth_of_poleClearingQuotient_and_GammaRatio
    (hpole :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 1 →
          1 ≤ ‖z.im‖ →
          ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hgamma :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 1 →
          1 ≤ ‖z.im‖ →
          ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 1 →
        1 ≤ ‖z.im‖ →
        ‖((z - 1) / (((1 : ℂ) - z) - 1)) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match hpole with
  | ⟨Ap, Bp, mp, hAp_pos, hBp_pos, hpole_bound⟩ =>
      match hgamma with
      | ⟨Ag, Bg, mg, hAg_pos, hBg_pos, hgamma_bound⟩ =>
          exact
            ⟨Ap * Ag, 2 * (Bp + Bg + 1), mp + mg,
              mul_pos hAp_pos hAg_pos,
              mul_pos zero_lt_two
                (add_pos (add_pos hBp_pos hBg_pos) zero_lt_one),
              fun z hz_re_nonneg hz_re_le_one hz_im_tail =>
                let H : ℝ := 1 + ‖z‖
                let poleFactor : ℂ :=
                  (z - 1) / (((1 : ℂ) - z) - 1)
                let gammaFactor : ℂ :=
                  Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z
                have hBp_nonnegative : 0 ≤ Bp := le_of_lt hBp_pos
                have hBg_nonnegative : 0 ≤ Bg := le_of_lt hBg_pos
                have hAp_nonnegative : 0 ≤ Ap := le_of_lt hAp_pos
                have hH_ge_one : 1 ≤ H :=
                  le_add_of_nonneg_right (norm_nonneg z)
                have hpole_target :
                    ‖poleFactor‖ ≤
                      Ap * Real.exp ((Bp + Bg + 1) * H ^ (mp + mg)) :=
                  le_trans
                    (hpole_bound z hz_re_nonneg hz_re_le_one hz_im_tail)
                    (finiteOrderProduct_firstFactor_le_commonEnvelope
                      Ap Bp Bg H mp mg hAp_nonnegative
                      hBp_nonnegative hBg_nonnegative hH_ge_one)
                have hgamma_target :
                    ‖gammaFactor‖ ≤
                      Ag * Real.exp ((Bp + Bg + 1) * H ^ (mp + mg)) :=
                  le_trans
                    (hgamma_bound z hz_re_nonneg hz_re_le_one hz_im_tail)
                    (finiteOrderProduct_secondFactor_le_commonEnvelope
                      Ag Bp Bg H mp mg (le_of_lt hAg_pos)
                      hBp_nonnegative hBg_nonnegative hH_ge_one)
                have hnorm :
                    ‖poleFactor * gammaFactor‖ =
                      ‖poleFactor‖ * ‖gammaFactor‖ :=
                  norm_mul poleFactor gammaFactor
                finiteOrderProduct_commonEnvelope_norm_bound
                  (poleFactor * gammaFactor) poleFactor gammaFactor
                  Ap Ag (Bp + Bg + 1) H (mp + mg)
                  hAp_nonnegative hnorm hpole_target hgamma_target⟩

end
end LFunctions
end Boundary
