import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.CompletedZetaGrowth.PoleCleared.OwnerParts.Part04_NonCircularGeometry

/-!
# Pole-cleared zeta noncircular zero-one strip assembly
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- The left half of the zero-one strip lies below the right boundary. -/
private theorem zeroOneLeftHalf_real_le_one
    {z : ℂ}
    (hz_half : z.re ≤ (1 / 2 : ℝ)) :
    z.re ≤ 1 :=
  le_trans hz_half
    (le_of_lt ((div_lt_one zero_lt_two).mpr one_lt_two))

/-- The second degree embeds in the sum of the two degrees. -/
private theorem secondDegree_le_degreeSum (mM mR : ℕ) :
    mR ≤ mM + mR :=
  Eq.subst
    (motive := fun degree : ℕ => mR ≤ degree)
    (Nat.add_comm mR mM)
    (Nat.le_add_right mR mM)

/-- The first finite-order envelope embeds in the common product envelope. -/
private theorem firstFiniteOrderEnvelope_le_commonEnvelope
    (A BM BR H : ℝ)
    (mM mR : ℕ)
    (hA_nonnegative : 0 ≤ A)
    (hBM_nonnegative : 0 ≤ BM)
    (hBR_nonnegative : 0 ≤ BR)
    (hH_ge_one : 1 ≤ H) :
    A * Real.exp (BM * H ^ mM) ≤
      A * Real.exp ((BM + BR + 1) * H ^ (mM + mR)) :=
  finiteOrderEnvelope_le_of_coefficient_and_degree
    A BM (BM + BR + 1) H mM (mM + mR)
    hA_nonnegative hBM_nonnegative
    (le_trans
      (le_add_of_nonneg_right hBR_nonnegative)
      (le_add_of_nonneg_right zero_le_one))
    hH_ge_one
    (Nat.le_add_right mM mR)

/-- The second finite-order envelope embeds in the common product envelope. -/
private theorem secondFiniteOrderEnvelope_le_commonEnvelope
    (A BM BR H : ℝ)
    (mM mR : ℕ)
    (hA_nonnegative : 0 ≤ A)
    (hBM_nonnegative : 0 ≤ BM)
    (hBR_nonnegative : 0 ≤ BR)
    (hH_ge_one : 1 ≤ H) :
    A * Real.exp (BR * H ^ mR) ≤
      A * Real.exp ((BM + BR + 1) * H ^ (mM + mR)) :=
  finiteOrderEnvelope_le_of_coefficient_and_degree
    A BR (BM + BR + 1) H mR (mM + mR)
    hA_nonnegative hBR_nonnegative
    (le_trans
      (le_add_of_nonneg_left hBM_nonnegative)
      (le_add_of_nonneg_right zero_le_one))
    hH_ge_one
    (secondDegree_le_degreeSum mM mR)

/-- Taking norms in the pole-cleared functional equation exposes the product
of the multiplier norm and the reflected-value norm. -/
private theorem poleClearedRiemannZeta_zeroOneStrip_functionalEquation_norm
    (z : ℂ)
    (hz_zero : 0 ≤ z.re)
    (hz_one : z.re ≤ 1)
    (hz_tail : 1 ≤ ‖z.im‖) :
    ‖poleClearedRiemannZeta z‖ =
      ‖poleClearedRiemannZeta_completedFunctionalEquationMultiplier z‖ *
        ‖poleClearedRiemannZeta ((1 : ℂ) - z)‖ := by
  have hidentity :
      poleClearedRiemannZeta z =
        poleClearedRiemannZeta_completedFunctionalEquationMultiplier z *
          poleClearedRiemannZeta ((1 : ℂ) - z) :=
    poleClearedRiemannZeta_zero_one_strip_completedFunctionalEquation_identity_ownerSelfReflection
      z hz_zero hz_one hz_tail
  exact Eq.trans (congrArg norm hidentity)
    (norm_mul
      (poleClearedRiemannZeta_completedFunctionalEquationMultiplier z)
      (poleClearedRiemannZeta ((1 : ℂ) - z)))

/-- Two estimates with the same enlarged exponential envelope collapse to the
standard doubled-coefficient product envelope. -/
private theorem poleClearedRiemannZeta_functionalEquation_commonEnvelope_product
    (z : ℂ)
    (AM AR coefficient : ℝ)
    (degree : ℕ)
    (hAM_nonnegative : 0 ≤ AM)
    (hnorm :
      ‖poleClearedRiemannZeta z‖ =
        ‖poleClearedRiemannZeta_completedFunctionalEquationMultiplier z‖ *
          ‖poleClearedRiemannZeta ((1 : ℂ) - z)‖)
    (hMultiplier :
      ‖poleClearedRiemannZeta_completedFunctionalEquationMultiplier z‖ ≤
        AM * Real.exp (coefficient * (1 + ‖z‖) ^ degree))
    (hReflected :
      ‖poleClearedRiemannZeta ((1 : ℂ) - z)‖ ≤
        AR * Real.exp (coefficient * (1 + ‖z‖) ^ degree)) :
    ‖poleClearedRiemannZeta z‖ ≤
      AM * AR * Real.exp ((2 * coefficient) * (1 + ‖z‖) ^ degree) := by
  have hproduct :
      ‖poleClearedRiemannZeta_completedFunctionalEquationMultiplier z‖ *
          ‖poleClearedRiemannZeta ((1 : ℂ) - z)‖ ≤
        (AM * Real.exp (coefficient * (1 + ‖z‖) ^ degree)) *
          (AR * Real.exp (coefficient * (1 + ‖z‖) ^ degree)) :=
    mul_le_mul hMultiplier hReflected
      (norm_nonneg (poleClearedRiemannZeta ((1 : ℂ) - z)))
      (mul_nonneg hAM_nonnegative
        (le_of_lt (Real.exp_pos (coefficient * (1 + ‖z‖) ^ degree))))
  have hcollapse :
      (AM * Real.exp (coefficient * (1 + ‖z‖) ^ degree)) *
          (AR * Real.exp (coefficient * (1 + ‖z‖) ^ degree)) =
        AM * AR * Real.exp ((2 * coefficient) * (1 + ‖z‖) ^ degree) :=
    finiteOrderGrowthProductEnvelope_exp_collapse
      AM AR coefficient ((1 + ‖z‖) ^ degree)
  exact Eq.subst
    (motive := fun value : ℝ =>
      value ≤ AM * AR *
        Real.exp ((2 * coefficient) * (1 + ‖z‖) ^ degree))
    hnorm.symm
    (hproduct.trans_eq hcollapse)

/-- Pointwise finite-order product assembly for the completed functional
equation on the left half of the zero-one strip. -/
private theorem poleClearedRiemannZeta_leftHalf_verticalTail_finiteOrder_of_multiplier_and_reflectedEnvelope
    (hmult :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧ 0 < B ∧
        ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta_completedFunctionalEquationMultiplier z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hreflected :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧ 0 < B ∧
        ∀ z : ℂ, 0 ≤ z.re → z.re ≤ (1 / 2 : ℝ) → 1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta ((1 : ℂ) - z)‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ (1 / 2 : ℝ) →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match hmult with
  | ⟨AM, BM, mM, hAM_pos, hBM_pos, hM⟩ =>
      match hreflected with
      | ⟨AR, BR, mR, hAR_pos, hBR_pos, hR⟩ =>
          exact
            ⟨AM * AR, 2 * (BM + BR + 1), mM + mR,
              mul_pos hAM_pos hAR_pos,
              mul_pos zero_lt_two (add_pos (add_pos hBM_pos hBR_pos) zero_lt_one),
              fun z hz_zero hz_half hz_tail =>
                let H : ℝ := 1 + ‖z‖
                have hz_one : z.re ≤ 1 :=
                  zeroOneLeftHalf_real_le_one hz_half
                have hBM_nonneg : 0 ≤ BM := le_of_lt hBM_pos
                have hBR_nonneg : 0 ≤ BR := le_of_lt hBR_pos
                have hAM_nonneg : 0 ≤ AM := le_of_lt hAM_pos
                have hAR_nonneg : 0 ≤ AR := le_of_lt hAR_pos
                have hH_ge_one : 1 ≤ H :=
                  le_add_of_nonneg_right (norm_nonneg z)
                have hM_target :
                    ‖poleClearedRiemannZeta_completedFunctionalEquationMultiplier z‖ ≤
                      AM * Real.exp ((BM + BR + 1) * H ^ (mM + mR)) :=
                  le_trans (hM z hz_zero hz_one hz_tail)
                    (firstFiniteOrderEnvelope_le_commonEnvelope
                      AM BM BR H mM mR hAM_nonneg hBM_nonneg hBR_nonneg
                      hH_ge_one)
                have hR_target :
                    ‖poleClearedRiemannZeta ((1 : ℂ) - z)‖ ≤
                      AR * Real.exp ((BM + BR + 1) * H ^ (mM + mR)) :=
                  le_trans (hR z hz_zero hz_half hz_tail)
                    (secondFiniteOrderEnvelope_le_commonEnvelope
                      AR BM BR H mM mR hAR_nonneg hBM_nonneg hBR_nonneg
                      hH_ge_one)
                have hnorm :
                    ‖poleClearedRiemannZeta z‖ =
                      ‖poleClearedRiemannZeta_completedFunctionalEquationMultiplier z‖ *
                        ‖poleClearedRiemannZeta ((1 : ℂ) - z)‖ :=
                  poleClearedRiemannZeta_zeroOneStrip_functionalEquation_norm
                    z hz_zero hz_one hz_tail
                poleClearedRiemannZeta_functionalEquation_commonEnvelope_product
                  z AM AR (BM + BR + 1) (mM + mR)
                  hAM_nonneg hnorm hM_target hR_target⟩

/-- The completed functional equation transports the direct positive-half
envelope to the left half. -/
private theorem poleClearedRiemannZeta_leftHalf_verticalTail_finiteOrder
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ (1 / 2 : ℝ) →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_leftHalf_verticalTail_finiteOrder_of_multiplier_and_reflectedEnvelope
      (poleClearedRiemannZeta_zero_one_strip_completedFunctionalEquationMultiplier_growth_ownerGammaStirling
        hbranch)
      poleClearedRiemannZeta_leftHalf_reflectedValue_verticalTail_finiteOrder

/-- The two half-strip estimates give a noncircular vertical-tail estimate on
the full closed zero-one strip. -/
private theorem poleClearedRiemannZeta_zeroOneStrip_verticalTail_finiteOrder_nonCircular
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧ 0 < B ∧
      ∀ z : ℂ, 0 ≤ z.re → z.re ≤ 1 → 1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match poleClearedRiemannZeta_positiveHalfStrip_verticalTail_finiteOrder with
  | ⟨AP, BP, mP, hAP, hBP, hP⟩ =>
      match poleClearedRiemannZeta_leftHalf_verticalTail_finiteOrder hbranch with
      | ⟨AL, BL, mL, hAL, hBL, hL⟩ =>
          exact
            ⟨AP + AL, BP + BL, mP + mL, add_pos hAP hAL, add_pos hBP hBL,
              fun z hz_zero hz_one hz_tail =>
                match le_total (1 / 2 : ℝ) z.re with
                | Or.inl hz_positive =>
                    le_trans (hP z hz_positive hz_one hz_tail)
                      (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                        (le_of_lt hAP) (le_add_of_nonneg_right (le_of_lt hAL))
                        (le_add_of_nonneg_right (le_of_lt hBL)) (le_of_lt hBP)
                        (Nat.le_add_right mP mL))
                | Or.inr hz_left =>
                    have hmL : mL ≤ mP + mL := by
                      exact Eq.subst (motive := fun n : ℕ => mL ≤ n)
                        (Nat.add_comm mL mP) (Nat.le_add_right mL mP)
                    le_trans (hL z hz_zero hz_left hz_tail)
                      (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                        (le_of_lt hAL) (le_add_of_nonneg_left (le_of_lt hAP))
                        (le_add_of_nonneg_left (le_of_lt hBP)) (le_of_lt hBL) hmL)⟩

/-- Compact patching turns the noncircular tail estimate into ordinary
finite-order growth on the closed zero-one strip. -/
private theorem poleClearedRiemannZeta_zeroOneStrip_ordinaryFiniteOrder_nonCircular
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    PoleClearedZeroOneStripOrdinaryFiniteOrderGrowth := by
  exact
    poleClearedRiemannZeta_zero_one_strip_growth_of_compactCore_and_verticalTail_for_nonCircularOwner
      poleClearedRiemannZeta_zero_one_strip_compactCore_growth_for_nonCircularOwner
      (poleClearedRiemannZeta_zeroOneStrip_verticalTail_finiteOrder_nonCircular hbranch)

/-- The canonical reflected envelope follows by applying the explicit
reflection transport to the independently proved zero-one ordinary bound. -/
theorem poleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope_nonCircular :
    PoleClearedZeroOneStripCanonicalSelfReflectedVerticalTailEnvelope := by
  exact
    poleClearedRiemannZeta_zero_one_strip_reflectedValue_verticalTail_growth_of_zeroOneOrdinaryFiniteOrder
      (poleClearedRiemannZeta_zeroOneStrip_ordinaryFiniteOrder_nonCircular
        Complex.binetSecondFormulaBranchUniformTailAbsorption_owner)
end
end LFunctions
end Boundary
