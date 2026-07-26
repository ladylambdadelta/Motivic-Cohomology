import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.PoleClearedBoundarySetup.Analysis.LeftBoundaryStirlingCore

/-!
# Boundary-line Gamma analysis and Abel-Plana assembly

## Helper lemmas for numeric bounds
-/

namespace Boundary
namespace LFunctions

/-- Helper: Large denominator positive. -/
private lemma ten_billion_pos : (0 : ℝ) < 10000000000 := by
  exact Nat.cast_pos.mpr (Nat.succ_pos 9999999999)

/-- Helper: Euler's constant approximation bound. -/
private lemma euler_approx_le_three : (27182818286 : ℕ) ≤ 3 * 10000000000 := by
  exact Nat.le.intro (show 27182818286 + 2817181714 = 3 * 10000000000 by rfl)

end LFunctions
end Boundary

/-!
# Boundary-line Gamma analysis and Abel-Plana assembly

This file owns the specific left-boundary applications of vertical Stirling estimates,
the concrete boundary-line zeta computations, and the Abel/Euler-Maclaurin infrastructure
for finite oscillatory sums along the critical line.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi
theorem classicalStirling_complexGamma_leftBoundary_twoGammaQuotient_vertical_sqrt_growth_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖(π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
            (π ^ (-((t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((t : ℂ) * Complex.I) / 2))‖ ≤
          A * Real.sqrt (1 + ‖t‖) := by
  exact match
    classicalStirling_unfoldedGammaℝLeftBoundaryRatioRealParam_vertical_sqrt_growth_bound_from_twoSidedVerticalStirling
      hbranch
    with
    | ⟨A, hA_pos, hbound⟩ =>
      ⟨A, hA_pos, fun t ht =>
        calc
          ‖(π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
                Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
              (π ^ (-((t : ℂ) * Complex.I) / 2) *
                Complex.Gamma (((t : ℂ) * Complex.I) / 2))‖ =
              ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ :=
            congrArg norm (unfoldedGammaℝLeftBoundaryRatioRealParam_eq_inline t)
          _ ≤ A * Real.sqrt (1 + ‖t‖) :=
            hbound t ht⟩

/-- Classical vertical Stirling control for the unfolded completed real Gamma ratio,
stated on the real parameter of the left boundary line.

This theorem is only the definitional transport from the two-Gamma quotient to the
local unfolded `Gammaℝ` ratio name. -/
theorem classicalStirling_unfoldedGammaℝLeftBoundaryRatioRealParam_vertical_sqrt_growth_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ ≤
          A * Real.sqrt (1 + ‖t‖) := by
  exact
    classicalStirling_unfoldedGammaℝLeftBoundaryRatioRealParam_vertical_sqrt_growth_bound_from_twoSidedVerticalStirling
      hbranch

/-- The named unfolded Gamma-ratio estimate is the older inline formula spelling. -/
theorem classicalStirling_unfoldedGammaℝ_leftBoundary_ratio_vertical_sqrt_growth_bound_realParam
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖(π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
            (π ^ (-((t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((t : ℂ) * Complex.I) / 2))‖ ≤
          A * Real.sqrt (1 + ‖t‖) := by
  exact match classicalStirling_unfoldedGammaℝLeftBoundaryRatioRealParam_vertical_sqrt_growth_bound
      hbranch with
    | ⟨A, hA_pos, hbound⟩ =>
      ⟨A, hA_pos, fun t ht =>
        calc
          ‖(π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
                Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
              (π ^ (-((t : ℂ) * Complex.I) / 2) *
                Complex.Gamma (((t : ℂ) * Complex.I) / 2))‖ =
              ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ :=
            congrArg norm (unfoldedGammaℝLeftBoundaryRatioRealParam_eq_inline t)
          _ ≤ A * Real.sqrt (1 + ‖t‖) :=
            hbound t ht⟩

/-- The unfolded vertical Stirling estimate is exactly the corresponding `Gammaℝ`
estimate after applying `Gammaℝ_def`. -/
theorem classicalStirling_Gammaℝ_leftBoundary_ratio_vertical_sqrt_growth_bound_realParam
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I) /
            Complex.Gammaℝ ((t : ℂ) * Complex.I)‖ ≤
          A * Real.sqrt (1 + ‖t‖) := by
  exact match classicalStirling_unfoldedGammaℝ_leftBoundary_ratio_vertical_sqrt_growth_bound_realParam
      hbranch with
    | ⟨A, hA_pos, hbound⟩ =>
      ⟨A, hA_pos, fun t ht => by
  calc
    ‖Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I) /
        Complex.Gammaℝ ((t : ℂ) * Complex.I)‖ =
        ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ :=
      norm_Gammaℝ_leftBoundary_ratio_realParam_eq_norm_unfolded t
    _ =
        ‖(π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
            (π ^ (-((t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((t : ℂ) * Complex.I) / 2))‖ := by
      exact congrArg norm (unfoldedGammaℝLeftBoundaryRatioRealParam_eq_inline t)
    _ ≤ A * Real.sqrt (1 + ‖t‖) :=
      hbound t ht⟩

/-- On the vertical-tail height range, the square-root height envelope is bounded by the
linear height envelope. -/
theorem sqrt_one_add_norm_le_one_add_norm
    (t : ℝ) :
    Real.sqrt (1 + ‖t‖) ≤ 1 + ‖t‖ := by
  let H : ℝ := 1 + ‖t‖
  have hH_ge_one : (1 : ℝ) ≤ H :=
    le_add_of_nonneg_right (norm_nonneg t)
  have hH_nonneg : 0 ≤ H :=
    le_trans zero_le_one hH_ge_one
  have hH_le_mul_self : H ≤ H * H := by
    have hone_mul_le : (1 : ℝ) * H ≤ H * H :=
      mul_le_mul_of_nonneg_right hH_ge_one hH_nonneg
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ H * H)
      (one_mul H)
      hone_mul_le
  have hH_le_sq : H ≤ H ^ (2 : ℕ) :=
    Eq.subst
      (motive := fun x : ℝ => H ≤ x)
      (pow_two H).symm
      hH_le_mul_self
  exact (Real.sqrt_le_left hH_nonneg).mpr hH_le_sq

/-- Classical vertical Stirling control for the completed real Gamma ratio, stated on
the real parameter of the left boundary line.

This is the linear envelope consumed downstream; its only analytic input is the sharper
unfolded square-root Stirling estimate. -/
theorem classicalStirling_Gammaℝ_leftBoundary_ratio_vertical_linear_growth_bound_realParam
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I) /
            Complex.Gammaℝ ((t : ℂ) * Complex.I)‖ ≤
          A * (1 + ‖t‖) := by
  exact match classicalStirling_Gammaℝ_leftBoundary_ratio_vertical_sqrt_growth_bound_realParam
      hbranch with
    | ⟨A, hA_pos, hbound⟩ =>
      ⟨A, hA_pos, fun t ht => by
  have hsqrt_to_linear :
      A * Real.sqrt (1 + ‖t‖) ≤ A * (1 + ‖t‖) :=
    mul_le_mul_of_nonneg_left
      (sqrt_one_add_norm_le_one_add_norm t)
      (le_of_lt hA_pos)
  exact le_trans (hbound t ht) hsqrt_to_linear⟩

/-- The real-parameter square-root Stirling estimate transported to the full left
boundary line. -/
theorem classicalStirling_Gammaℝ_leftBoundary_ratio_vertical_sqrt_growth_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * Real.sqrt (1 + ‖z.im‖) := by
  exact match classicalStirling_Gammaℝ_leftBoundary_ratio_vertical_sqrt_growth_bound_realParam
      hbranch with
    | ⟨A, hA_pos, hbound⟩ =>
      ⟨A, hA_pos, fun z hz_re hz_im => by
  have hz_axis : z = (z.im : ℂ) * Complex.I :=
    leftBoundary_eq_im_mul_I z hz_re
  have haxis_bound :
      ‖Complex.Gammaℝ ((1 : ℂ) - (z.im : ℂ) * Complex.I) /
          Complex.Gammaℝ ((z.im : ℂ) * Complex.I)‖ ≤
        A * Real.sqrt (1 + ‖z.im‖) :=
    hbound z.im hz_im
  exact Eq.subst
    (motive := fun w : ℂ =>
      ‖Complex.Gammaℝ ((1 : ℂ) - w) / Complex.Gammaℝ w‖ ≤
        A * Real.sqrt (1 + ‖z.im‖))
    hz_axis.symm
    haxis_bound⟩

/-- Classical two-sided vertical Stirling control for the completed real Gamma ratio on
the left boundary line, in the sharp polynomial degree needed by the critical-line
functional-equation transport. -/
theorem classicalStirling_Gammaℝ_leftBoundary_ratio_vertical_linear_growth_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * (1 + ‖z.im‖) := by
  exact match classicalStirling_Gammaℝ_leftBoundary_ratio_vertical_sqrt_growth_bound
      hbranch with
    | ⟨A, hA_pos, hbound⟩ =>
      ⟨A, hA_pos, fun z hz_re hz_im => by
  have hsqrt_to_linear :
      A * Real.sqrt (1 + ‖z.im‖) ≤ A * (1 + ‖z.im‖) :=
    mul_le_mul_of_nonneg_left
      (sqrt_one_add_norm_le_one_add_norm z.im)
      (le_of_lt hA_pos)
  exact le_trans (hbound z hz_re hz_im) hsqrt_to_linear⟩

/-- A vertical linear bound is the degree-one polynomial envelope used downstream. -/
theorem Gammaℝ_leftBoundary_ratio_vertical_polynomial_growth_bound_of_linear
    (hlinear :
      ∃ A : ℝ,
        0 < A ∧
        ∀ z : ℂ,
          z.re = 0 →
          1 ≤ ‖z.im‖ →
          ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
            A * (1 + ‖z.im‖)) :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * (1 + ‖z.im‖) ^ m := by
  exact match hlinear with
    | ⟨A, hA_pos, hbound⟩ =>
      ⟨A, 1, hA_pos, fun z hz_re hz_im => by
  have hpow_one : (1 + ‖z.im‖) ^ (1 : ℕ) = 1 + ‖z.im‖ := by
    exact pow_one (1 + ‖z.im‖)
  exact Eq.subst
    (motive := fun x : ℝ =>
      ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤ A * x)
    hpow_one.symm
    (hbound z hz_re hz_im)⟩

/-- Standard polynomial Stirling control for the completed real Gamma ratio on the left
vertical tail.

This is the classical two-sided vertical Gamma-ratio estimate after substituting the
left boundary line `z = it`: the ratio is controlled by a fixed polynomial in `|t|`. -/
theorem Gammaℝ_leftBoundary_ratio_vertical_polynomial_stirling_growth_bound_standard
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * (1 + ‖z.im‖) ^ m := by
  exact Gammaℝ_leftBoundary_ratio_vertical_polynomial_growth_bound_of_linear
    (classicalStirling_Gammaℝ_leftBoundary_ratio_vertical_linear_growth_bound hbranch)

/-! Coordinate-free form of the same owner estimate.  This is the form needed
by the strip transport, while retaining the sharp degree-one boundary input. -/
theorem Gammaℝ_leftBoundary_ratio_complexHeight_polynomial_growth_bound_standard
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * (1 + ‖z‖) ^ m := by
  exact match classicalStirling_Gammaℝ_leftBoundary_ratio_vertical_linear_growth_bound
      hbranch with
    | ⟨A, hA_pos, hbound⟩ =>
      ⟨A, 1, hA_pos, fun z hz_re hz_im => by
        have hheight : 1 + ‖z.im‖ ≤ 1 + ‖z‖ := by
          exact add_le_add_left (Complex.norm_im_le_norm z) 1
        have hlinear : A * (1 + ‖z.im‖) ≤ A * (1 + ‖z‖) := by
          exact mul_le_mul_of_nonneg_left hheight (le_of_lt hA_pos)
        have hboundary := hbound z hz_re hz_im
        have hpow : (1 + ‖z‖) ^ (1 : ℕ) = 1 + ‖z‖ := by
          exact pow_one (1 + ‖z‖)
        exact le_trans hboundary
          (Eq.subst
            (motive := fun u : ℝ => A * (1 + ‖z‖) ≤ A * u)
            hpow.symm
            hlinear)⟩

theorem Gammaℝ_leftBoundary_completedFunctionalEquation_multiplier_polynomial_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖((z - 1) / (((1 : ℂ) - z) - 1)) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)‖ ≤
          A * (1 + ‖z‖) ^ m := by
  match Gammaℝ_leftBoundary_ratio_complexHeight_polynomial_growth_bound_standard hbranch with
  | ⟨Ag, mg, hAg, hgamma⟩ =>
      match leftBoundary_completedFunctionalEquation_poleClearing_ratio_polynomial_bound with
      | ⟨Ar, mr, hAr, hratio⟩ =>
          refine ⟨Ar * Ag, mr + mg, mul_pos hAr hAg,
            fun z hz_re hz_im => ?_⟩
          let H : ℝ := 1 + ‖z‖
          have hH_nonneg : 0 ≤ H := by
            exact le_trans zero_le_one
              (le_add_of_nonneg_right (norm_nonneg z))
          have hratio_bound :
              ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ ≤ Ar * H ^ mr := by
            exact hratio z hz_re hz_im
          have hgamma_bound :
              ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
                Ag * H ^ mg := by
            exact hgamma z hz_re hz_im
          have hproduct :
              ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ *
                  ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
                (Ar * H ^ mr) * (Ag * H ^ mg) := by
            exact mul_le_mul hratio_bound hgamma_bound
              (norm_nonneg _)
              (mul_nonneg (le_of_lt hAr) (pow_nonneg hH_nonneg mr))
          have halgebra :
              (Ar * H ^ mr) * (Ag * H ^ mg) =
                (Ar * Ag) * H ^ (mr + mg) := by
            calc
              (Ar * H ^ mr) * (Ag * H ^ mg) =
                  (Ar * Ag) * (H ^ mr * H ^ mg) := by
                exact mul_mul_mul_comm Ar (H ^ mr) Ag (H ^ mg)
              _ = (Ar * Ag) * H ^ (mr + mg) := by
                exact congrArg (fun u : ℝ => (Ar * Ag) * u)
                  (pow_add H mr mg).symm
          calc
            ‖((z - 1) / (((1 : ℂ) - z) - 1)) *
                (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)‖ =
                ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ *
                  ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ :=
              norm_mul _ _
            _ ≤ (Ar * H ^ mr) * (Ag * H ^ mg) := hproduct
            _ = (Ar * Ag) * H ^ (mr + mg) := halgebra
            _ = (Ar * Ag) * (1 + ‖z‖) ^ (mr + mg) := by
              exact congrArg (fun u : ℝ => (Ar * Ag) * u) rfl

/-- Standard finite-order Stirling control for the completed real Gamma ratio on the left
vertical tail, converted from the polynomial vertical-height Stirling statement.

This is the exact analytic statement left after the elementary pole-clearing ratio has
been separated from the completed-functional-equation multiplier. -/
theorem Gammaℝ_leftBoundary_ratio_vertical_stirling_growth_bound_standard
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * Real.exp (B * (1 + ‖z.im‖) ^ m) := by
  exact vertical_polynomial_growth_bound_to_exponential_growth_bound
    (Gammaℝ_leftBoundary_ratio_vertical_polynomial_stirling_growth_bound_standard hbranch)

/-- A vertical-height Gamma-ratio Stirling estimate implies the complex-height envelope
used by the completed-functional-equation multiplier. -/
theorem Gammaℝ_leftBoundary_ratio_growth_bound_of_vertical_stirling
    (hStirling :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 0 →
          1 ≤ ‖z.im‖ →
          ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
            A * Real.exp (B * (1 + ‖z.im‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact match hStirling with
    | ⟨A, B, m, hA, hB, hbound⟩ =>
      ⟨A, B, m, hA, hB, fun z hz_re hz_im =>
        le_trans (hbound z hz_re hz_im)
          (finiteOrder_vertical_envelope_le_complex_envelope
            (le_of_lt hA)
            (le_of_lt hB))⟩

/-- Standard finite-order Stirling control for the completed real Gamma ratio on the left
vertical tail, in the complex-height envelope used downstream. -/
theorem Gammaℝ_leftBoundary_ratio_stirling_growth_bound_standard
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact Gammaℝ_leftBoundary_ratio_growth_bound_of_vertical_stirling
    (Gammaℝ_leftBoundary_ratio_vertical_stirling_growth_bound_standard hbranch)

/-- A two-sided Stirling ratio estimate on the left boundary is exactly the current
finite-order Gamma-ratio envelope. -/
theorem Gammaℝ_leftBoundary_ratio_growth_bound_of_standard_twoSided_stirling_ratio
    (hstandard :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 0 →
          1 ≤ ‖z.im‖ →
          ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact hstandard

/-- The Gamma-ratio Stirling input on the left vertical tail.

This owner primitive is now only the standard vertical-tail Gamma-ratio estimate. -/
theorem Gammaℝ_leftBoundary_ratio_stirling_growth_bound_ownerPrimitive
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact Gammaℝ_leftBoundary_ratio_stirling_growth_bound_standard hbranch

/-- Product of two left-edge finite-order envelopes is again a left-edge finite-order
envelope.  This core version is placed before the completed-functional-equation multiplier
so the multiplier can be a product wrapper. -/
theorem leftBoundary_finiteOrder_product_growth_bound_core
    {f g : ℂ → ℂ}
    (hf :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 0 →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hg :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 0 →
          1 ≤ ‖z.im‖ →
          ‖g z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖f z‖ * ‖g z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact match hf, hg with
    | ⟨Af, Bf, mf, hAf, hBf, hf_bound⟩,
      ⟨Ag, Bg, mg, hAg, hBg, hg_bound⟩ =>
      ⟨Af * Ag, 2 * (Bf + Bg + 1), mf + mg,
        mul_pos hAf hAg,
        mul_pos zero_lt_two (add_pos (add_pos hBf hBg) zero_lt_one),
        fun z hz_re hz_im => by
  let H : ℝ := 1 + ‖z‖
  have hBf_nonneg : 0 ≤ Bf := le_of_lt hBf
  have hBg_nonneg : 0 ≤ Bg := le_of_lt hBg
  have hf_enlarge :
      Af * Real.exp (Bf * H ^ mf) ≤
        Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) :=
    exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
      (le_of_lt hAf)
      (le_refl Af)
      (by
        calc
          Bf ≤ Bf + Bg := le_add_of_nonneg_right hBg_nonneg
          _ ≤ Bf + Bg + 1 := le_add_of_nonneg_right zero_le_one)
      hBf_nonneg
      (Nat.le_add_right mf mg)
  have hmg_le : mg ≤ mf + mg := by
    exact Eq.subst
      (motive := fun d : ℕ => mg ≤ d)
      (Nat.add_comm mg mf)
      (Nat.le_add_right mg mf)
  have hg_enlarge :
      Ag * Real.exp (Bg * H ^ mg) ≤
        Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) :=
    exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
      (le_of_lt hAg)
      (le_refl Ag)
      (by
        calc
          Bg ≤ Bf + Bg := le_add_of_nonneg_left hBf_nonneg
          _ ≤ Bf + Bg + 1 := le_add_of_nonneg_right zero_le_one)
      hBg_nonneg
      hmg_le
  have hf_target :
      ‖f z‖ ≤ Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) :=
    le_trans (hf_bound z hz_re hz_im) hf_enlarge
  have hg_target :
      ‖g z‖ ≤ Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) :=
    le_trans (hg_bound z hz_re hz_im) hg_enlarge
  have hmul :
      ‖f z‖ * ‖g z‖ ≤
        (Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) *
          (Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) :=
    mul_le_mul hf_target hg_target (norm_nonneg (g z))
      (mul_nonneg (le_of_lt hAf)
        (le_of_lt (Real.exp_pos ((Bf + Bg + 1) * H ^ (mf + mg)))))
  have hcollapse :
      (Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) *
          (Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) =
        Af * Ag * Real.exp ((2 * (Bf + Bg + 1)) * H ^ (mf + mg)) := by
    calc
      (Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) *
          (Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) =
        (Af * Ag) *
          (Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) *
            Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) := by
        exact mul_mul_mul_comm Af
          (Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)))
          Ag
          (Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)))
      _ = (Af * Ag) *
          Real.exp (((Bf + Bg + 1) * H ^ (mf + mg)) +
            ((Bf + Bg + 1) * H ^ (mf + mg))) := by
        exact congrArg (fun x : ℝ => (Af * Ag) * x)
          (Real.exp_add ((Bf + Bg + 1) * H ^ (mf + mg))
            ((Bf + Bg + 1) * H ^ (mf + mg))).symm
      _ = Af * Ag * Real.exp ((2 * (Bf + Bg + 1)) * H ^ (mf + mg)) := by
        have htwo :
            ((Bf + Bg + 1) * H ^ (mf + mg)) +
                ((Bf + Bg + 1) * H ^ (mf + mg)) =
              (2 * (Bf + Bg + 1)) * H ^ (mf + mg) := by
          calc
            ((Bf + Bg + 1) * H ^ (mf + mg)) +
                ((Bf + Bg + 1) * H ^ (mf + mg)) =
              2 * ((Bf + Bg + 1) * H ^ (mf + mg)) := by
                exact (two_mul ((Bf + Bg + 1) * H ^ (mf + mg))).symm
            _ = (2 * (Bf + Bg + 1)) * H ^ (mf + mg) := by
                exact (mul_assoc 2 (Bf + Bg + 1) (H ^ (mf + mg))).symm
        exact congrArg (fun x : ℝ => Af * Ag * Real.exp x) htwo
  exact le_trans hmul (le_of_eq hcollapse)⟩

/-- The exact Gamma-ratio Stirling input for the left-edge completed-functional-equation
transport.

The proof is now only the product of the elementary pole-clearing ratio and the
peeled Gamma-ratio Stirling theorem. -/
theorem Gammaℝ_leftBoundary_completedFunctionalEquation_multiplier_stirling_growth_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖((z - 1) / (((1 : ℂ) - z) - 1)) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact match leftBoundary_finiteOrder_product_growth_bound_core
      leftBoundary_completedFunctionalEquation_poleClearing_ratio_growth_bound
      (Gammaℝ_leftBoundary_ratio_stirling_growth_bound_ownerPrimitive hbranch) with
    | ⟨A, B, m, hA, hB, hproduct⟩ =>
      ⟨A, B, m, hA, hB, fun z hz_re hz_im => by
  have hnorm :
      ‖((z - 1) / (((1 : ℂ) - z) - 1)) *
          (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)‖ =
        ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ *
          ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ :=
    norm_mul
      ((z - 1) / (((1 : ℂ) - z) - 1))
      (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)
  calc
    ‖((z - 1) / (((1 : ℂ) - z) - 1)) *
        (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)‖ =
      ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ *
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ :=
      hnorm
    _ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) :=
      hproduct z hz_re hz_im⟩

/-- Product of two left-edge finite-order envelopes is again a left-edge finite-order
envelope. -/
theorem leftBoundary_finiteOrder_product_growth_bound
    {f g : ℂ → ℂ}
    (hf :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 0 →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hg :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 0 →
          1 ≤ ‖z.im‖ →
          ‖g z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖f z‖ * ‖g z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact match hf, hg with
    | ⟨Af, Bf, mf, hAf, hBf, hf_bound⟩,
      ⟨Ag, Bg, mg, hAg, hBg, hg_bound⟩ =>
      ⟨Af * Ag, 2 * (Bf + Bg + 1), mf + mg,
        mul_pos hAf hAg,
        mul_pos zero_lt_two (add_pos (add_pos hBf hBg) zero_lt_one),
        fun z hz_re hz_im => by
  let H : ℝ := 1 + ‖z‖
  have hH_ge_one : (1 : ℝ) ≤ H :=
    le_add_of_nonneg_right (norm_nonneg z)
  have hH_nonneg : 0 ≤ H :=
    le_trans zero_le_one hH_ge_one
  have hBf_nonneg : 0 ≤ Bf := le_of_lt hBf
  have hBg_nonneg : 0 ≤ Bg := le_of_lt hBg
  have hf_enlarge :
      Af * Real.exp (Bf * H ^ mf) ≤
        Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) :=
    exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
      (le_of_lt hAf)
      (le_refl Af)
      (by
        calc
          Bf ≤ Bf + Bg := le_add_of_nonneg_right hBg_nonneg
          _ ≤ Bf + Bg + 1 := le_add_of_nonneg_right zero_le_one)
      hBf_nonneg
      (Nat.le_add_right mf mg)
  have hmg_le : mg ≤ mf + mg := by
    exact Eq.subst
      (motive := fun d : ℕ => mg ≤ d)
      (Nat.add_comm mg mf)
      (Nat.le_add_right mg mf)
  have hg_enlarge :
      Ag * Real.exp (Bg * H ^ mg) ≤
        Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) :=
    exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
      (le_of_lt hAg)
      (le_refl Ag)
      (by
        calc
          Bg ≤ Bf + Bg := le_add_of_nonneg_left hBf_nonneg
          _ ≤ Bf + Bg + 1 := le_add_of_nonneg_right zero_le_one)
      hBg_nonneg
      hmg_le
  have hf_target :
      ‖f z‖ ≤ Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) :=
    le_trans (hf_bound z hz_re hz_im) hf_enlarge
  have hg_target :
      ‖g z‖ ≤ Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) :=
    le_trans (hg_bound z hz_re hz_im) hg_enlarge
  have hmul :
      ‖f z‖ * ‖g z‖ ≤
        (Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) *
          (Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) :=
    mul_le_mul hf_target hg_target (norm_nonneg (g z))
      (mul_nonneg (le_of_lt hAf)
        (le_of_lt (Real.exp_pos ((Bf + Bg + 1) * H ^ (mf + mg)))))
  have hcollapse :
      (Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) *
          (Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) =
        Af * Ag * Real.exp ((2 * (Bf + Bg + 1)) * H ^ (mf + mg)) := by
    calc
      (Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) *
          (Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) =
        (Af * Ag) *
          (Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) *
            Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) := by
        exact mul_mul_mul_comm Af
          (Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)))
          Ag
          (Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)))
      _ = (Af * Ag) *
          Real.exp (((Bf + Bg + 1) * H ^ (mf + mg)) +
            ((Bf + Bg + 1) * H ^ (mf + mg))) := by
        exact congrArg (fun x : ℝ => (Af * Ag) * x)
          (Real.exp_add ((Bf + Bg + 1) * H ^ (mf + mg))
            ((Bf + Bg + 1) * H ^ (mf + mg))).symm
      _ = Af * Ag * Real.exp ((2 * (Bf + Bg + 1)) * H ^ (mf + mg)) := by
        have htwo :
            ((Bf + Bg + 1) * H ^ (mf + mg)) +
                ((Bf + Bg + 1) * H ^ (mf + mg)) =
              (2 * (Bf + Bg + 1)) * H ^ (mf + mg) := by
          calc
            ((Bf + Bg + 1) * H ^ (mf + mg)) +
                ((Bf + Bg + 1) * H ^ (mf + mg)) =
              2 * ((Bf + Bg + 1) * H ^ (mf + mg)) := by
                exact (two_mul ((Bf + Bg + 1) * H ^ (mf + mg))).symm
            _ = (2 * (Bf + Bg + 1)) * H ^ (mf + mg) := by
                exact (mul_assoc 2 (Bf + Bg + 1) (H ^ (mf + mg))).symm
        exact congrArg (fun x : ℝ => Af * Ag * Real.exp x) htwo
  exact le_trans hmul (le_of_eq hcollapse)⟩

/-- Product of an unconditional left-edge finite-order envelope and a conditional
left-edge finite-order envelope is again a conditional left-edge finite-order envelope. -/
theorem leftBoundary_finiteOrder_product_growth_bound_of_condition
    {f g : ℂ → ℂ}
    (P : ℂ → Prop)
    (hf :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 0 →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hg :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 0 →
          1 ≤ ‖z.im‖ →
          P z →
          ‖g z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        P z →
        ‖f z‖ * ‖g z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact match hf, hg with
    | ⟨Af, Bf, mf, hAf, hBf, hf_bound⟩,
      ⟨Ag, Bg, mg, hAg, hBg, hg_bound⟩ =>
      ⟨Af * Ag, 2 * (Bf + Bg + 1), mf + mg,
        mul_pos hAf hAg,
        mul_pos zero_lt_two (add_pos (add_pos hBf hBg) zero_lt_one),
        fun z hz_re hz_im hP => by
  let H : ℝ := 1 + ‖z‖
  have hH_ge_one : (1 : ℝ) ≤ H :=
    le_add_of_nonneg_right (norm_nonneg z)
  have hH_nonneg : 0 ≤ H :=
    le_trans zero_le_one hH_ge_one
  have hBf_nonneg : 0 ≤ Bf := le_of_lt hBf
  have hBg_nonneg : 0 ≤ Bg := le_of_lt hBg
  have hf_enlarge :
      Af * Real.exp (Bf * H ^ mf) ≤
        Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) :=
    exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
      (le_of_lt hAf)
      (le_refl Af)
      (by
        calc
          Bf ≤ Bf + Bg := le_add_of_nonneg_right hBg_nonneg
          _ ≤ Bf + Bg + 1 := le_add_of_nonneg_right zero_le_one)
      hBf_nonneg
      (Nat.le_add_right mf mg)
  have hmg_le : mg ≤ mf + mg := by
    exact Eq.subst
      (motive := fun d : ℕ => mg ≤ d)
      (Nat.add_comm mg mf)
      (Nat.le_add_right mg mf)
  have hg_enlarge :
      Ag * Real.exp (Bg * H ^ mg) ≤
        Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) :=
    exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
      (le_of_lt hAg)
      (le_refl Ag)
      (by
        calc
          Bg ≤ Bf + Bg := le_add_of_nonneg_left hBf_nonneg
          _ ≤ Bf + Bg + 1 := le_add_of_nonneg_right zero_le_one)
      hBg_nonneg
      hmg_le
  have hf_target :
      ‖f z‖ ≤ Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) :=
    le_trans (hf_bound z hz_re hz_im) hf_enlarge
  have hg_target :
      ‖g z‖ ≤ Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) :=
    le_trans (hg_bound z hz_re hz_im hP) hg_enlarge
  have hmul :
      ‖f z‖ * ‖g z‖ ≤
        (Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) *
          (Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) :=
    mul_le_mul hf_target hg_target (norm_nonneg (g z))
      (mul_nonneg (le_of_lt hAf)
        (le_of_lt (Real.exp_pos ((Bf + Bg + 1) * H ^ (mf + mg)))))
  have hcollapse :
      (Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) *
          (Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) =
        Af * Ag * Real.exp ((2 * (Bf + Bg + 1)) * H ^ (mf + mg)) := by
    calc
      (Af * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) *
          (Ag * Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) =
        (Af * Ag) *
          (Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)) *
            Real.exp ((Bf + Bg + 1) * H ^ (mf + mg))) := by
        exact mul_mul_mul_comm Af
          (Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)))
          Ag
          (Real.exp ((Bf + Bg + 1) * H ^ (mf + mg)))
      _ = (Af * Ag) *
          Real.exp (((Bf + Bg + 1) * H ^ (mf + mg)) +
            ((Bf + Bg + 1) * H ^ (mf + mg))) := by
        exact congrArg (fun x : ℝ => (Af * Ag) * x)
          (Real.exp_add ((Bf + Bg + 1) * H ^ (mf + mg))
            ((Bf + Bg + 1) * H ^ (mf + mg))).symm
      _ = Af * Ag * Real.exp ((2 * (Bf + Bg + 1)) * H ^ (mf + mg)) := by
        have htwo :
            ((Bf + Bg + 1) * H ^ (mf + mg)) +
                ((Bf + Bg + 1) * H ^ (mf + mg)) =
              (2 * (Bf + Bg + 1)) * H ^ (mf + mg) := by
          calc
            ((Bf + Bg + 1) * H ^ (mf + mg)) +
                ((Bf + Bg + 1) * H ^ (mf + mg)) =
              2 * ((Bf + Bg + 1) * H ^ (mf + mg)) := by
                exact (two_mul ((Bf + Bg + 1) * H ^ (mf + mg))).symm
            _ = (2 * (Bf + Bg + 1)) * H ^ (mf + mg) := by
                exact (mul_assoc 2 (Bf + Bg + 1) (H ^ (mf + mg))).symm
        exact congrArg (fun x : ℝ => Af * Ag * Real.exp x) htwo
  exact le_trans hmul (le_of_eq hcollapse)⟩

end
end LFunctions
end Boundary
