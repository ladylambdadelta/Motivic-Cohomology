import Mathlib.Analysis.Complex.PhragmenLindelof
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

open scoped Filter Topology

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

/-- A finite-order estimate can be enlarged in constants and exponent.

This early algebraic helper is used by the first analytic decompositions before the
general normalization section below. -/
theorem exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
    {A B A' B' : ℝ} {m d : ℕ} {z : ℂ}
    (hA : 0 ≤ A)
    (hAle : A ≤ A')
    (hBle : B ≤ B')
    (hBnonneg : 0 ≤ B)
    (hmd : m ≤ d) :
    A * Real.exp (B * (1 + ‖z‖) ^ m) ≤
      A' * Real.exp (B' * (1 + ‖z‖) ^ d) := by
  let H : ℝ := 1 + ‖z‖
  have hH_ge_one : (1 : ℝ) ≤ H :=
    le_add_of_nonneg_right (norm_nonneg z)
  have hH_nonneg : 0 ≤ H :=
    le_trans zero_le_one hH_ge_one
  have hpow_le : H ^ m ≤ H ^ d :=
    pow_le_pow_right₀ hH_ge_one hmd
  have hB_pow_le : B * H ^ m ≤ B * H ^ d :=
    mul_le_mul_of_nonneg_left hpow_le hBnonneg
  have hB_le_B'pow : B * H ^ d ≤ B' * H ^ d :=
    mul_le_mul_of_nonneg_right hBle (pow_nonneg hH_nonneg d)
  have hexponent_le : B * H ^ m ≤ B' * H ^ d :=
    le_trans hB_pow_le hB_le_B'pow
  have hexp_le :
      Real.exp (B * H ^ m) ≤ Real.exp (B' * H ^ d) :=
    Real.exp_le_exp.mpr hexponent_le
  have hexp_nonneg : 0 ≤ Real.exp (B * H ^ m) :=
    le_of_lt (Real.exp_pos (B * H ^ m))
  have hA'nonneg : 0 ≤ A' :=
    le_trans hA hAle
  exact mul_le_mul hAle hexp_le hexp_nonneg hA'nonneg

/-- The compact right-critical-strip rectangle for the pole-cleared completed entire part. -/
def completedRiemannZeta₀_rightCriticalStripCompactSet : Set ℂ :=
  {z : ℂ | 0 ≤ z.re ∧ z.re ≤ 2 ∧ ‖z.im‖ ≤ 1}

/-- The right-critical-strip compact rectangle is closed. -/
theorem completedRiemannZeta₀_rightCriticalStripCompactSet_isClosed :
    IsClosed completedRiemannZeta₀_rightCriticalStripCompactSet := by
  have hleft : IsClosed {z : ℂ | 0 ≤ z.re} :=
    isClosed_le continuous_const Complex.continuous_re
  have hright : IsClosed {z : ℂ | z.re ≤ 2} :=
    isClosed_le Complex.continuous_re continuous_const
  have him : IsClosed {z : ℂ | ‖z.im‖ ≤ 1} :=
    isClosed_le (Complex.continuous_im.norm) continuous_const
  have hset :
      completedRiemannZeta₀_rightCriticalStripCompactSet =
        {z : ℂ | 0 ≤ z.re} ∩ {z : ℂ | z.re ≤ 2} ∩ {z : ℂ | ‖z.im‖ ≤ 1} := by
    ext z
    constructor
    · intro hz
      exact ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩
    · intro hz
      exact ⟨hz.1.1, hz.1.2, hz.2⟩
  exact Eq.subst
    (motive := fun S : Set ℂ => IsClosed S)
    hset.symm
    ((hleft.inter hright).inter him)

/-- The right-critical-strip compact rectangle is bounded. -/
theorem completedRiemannZeta₀_rightCriticalStripCompactSet_isBounded :
    Bornology.IsBounded completedRiemannZeta₀_rightCriticalStripCompactSet := by
  refine isBounded_iff_forall_norm_le.2 ⟨4, ?_⟩
  intro z hz
  have hz_re_abs_le_two : |z.re| ≤ 2 := by
    have hz_re_abs_eq : |z.re| = z.re :=
      abs_of_nonneg hz.1
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ 2)
      hz_re_abs_eq.symm
      hz.2.1
  have hz_abs_le_three : ‖z‖ ≤ 3 := by
    have hcomplex :
        ‖z‖ ≤ |z.re| + |z.im| :=
      Eq.subst
        (motive := fun x : ℝ => x ≤ |z.re| + |z.im|)
        (Complex.norm_eq_abs z).symm
        (Complex.abs_le_abs_re_add_abs_im z)
    have him :
        |z.im| ≤ 1 := by
      exact Eq.subst
        (motive := fun x : ℝ => x ≤ 1)
        (Real.norm_eq_abs z.im)
        hz.2.2
    have hsum : |z.re| + |z.im| ≤ 2 + 1 :=
      add_le_add hz_re_abs_le_two him
    exact le_trans hcomplex (hsum.trans_eq (by norm_num : (2 : ℝ) + 1 = 3))
  exact le_trans hz_abs_le_three (by norm_num : (3 : ℝ) ≤ 4)

/-- The right-critical-strip rectangle is compact. -/
theorem completedRiemannZeta₀_rightCriticalStripCompactSet_isCompact :
    IsCompact completedRiemannZeta₀_rightCriticalStripCompactSet :=
  Metric.isCompact_of_isClosed_isBounded
    completedRiemannZeta₀_rightCriticalStripCompactSet_isClosed
    completedRiemannZeta₀_rightCriticalStripCompactSet_isBounded

/-- The completed entire part is continuous on the right-critical-strip compact rectangle. -/
theorem completedRiemannZeta₀_continuousOn_rightCriticalStripCompactSet :
    ContinuousOn completedRiemannZeta₀
      completedRiemannZeta₀_rightCriticalStripCompactSet :=
  differentiable_completedZeta₀.continuous.continuousOn

/-- Compact boundedness of the pole-cleared completed-zeta entire part on the right
critical strip rectangle. -/
theorem completedRiemannZeta₀_rightCriticalStrip_compact_norm_bound :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ completedRiemannZeta₀_rightCriticalStripCompactSet →
        ‖completedRiemannZeta₀ z‖ ≤ C := by
  rcases IsCompact.exists_bound_of_continuousOn
      completedRiemannZeta₀_rightCriticalStripCompactSet_isCompact
      completedRiemannZeta₀_continuousOn_rightCriticalStripCompactSet with
    ⟨C0, hC0⟩
  refine ⟨max C0 0 + 1, ?_, ?_⟩
  · exact add_pos_of_nonneg_of_pos (le_max_right C0 0) zero_lt_one
  intro z hz
  have hraw : ‖completedRiemannZeta₀ z‖ ≤ C0 :=
    hC0 z hz
  exact le_trans hraw (le_trans (le_max_left C0 0) (le_add_of_nonneg_right zero_le_one))

/-- A logarithmic `Gammaℝ` growth estimate on a region gives exponential finite-order
growth on that region. -/
theorem Gammaℝ_finiteOrder_growth_bound_of_log_growth_on_region
    (P : ℂ → Prop)
    (hlog :
      ∃ C : ℝ, ∃ m : ℕ,
        ∀ z : ℂ,
          P z →
          Real.log ‖Complex.Gammaℝ z‖ ≤
            C * (1 + ‖z‖) ^ m) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        P z →
        ‖Complex.Gammaℝ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hlog with ⟨C, m, hC⟩
  refine ⟨1, |C| + 1, m, zero_lt_one, ?_, ?_⟩
  · exact add_pos_of_nonneg_of_pos (abs_nonneg C) zero_lt_one
  intro z hzP
  have hC_le : C * (1 + ‖z‖) ^ m ≤ (|C| + 1) * (1 + ‖z‖) ^ m := by
    have hC_abs : C ≤ |C| + 1 := le_trans (le_abs_self C) (le_add_of_nonneg_right zero_le_one)
    exact mul_le_mul_of_nonneg_right hC_abs
      (pow_nonneg (le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))) m)
  have hlog_le :
      Real.log ‖Complex.Gammaℝ z‖ ≤ (|C| + 1) * (1 + ‖z‖) ^ m :=
    le_trans (hC z hzP) hC_le
  by_cases hzero : ‖Complex.Gammaℝ z‖ = 0
  · exact Eq.subst
      (motive := fun x : ℝ =>
        x ≤ 1 * Real.exp ((|C| + 1) * (1 + ‖z‖) ^ m))
      hzero.symm
      (le_of_lt (mul_pos zero_lt_one (Real.exp_pos ((|C| + 1) * (1 + ‖z‖) ^ m))))
  · have hpos : 0 < ‖Complex.Gammaℝ z‖ :=
      lt_of_le_of_ne (norm_nonneg (Complex.Gammaℝ z)) (Ne.symm hzero)
    have hexp_log : Real.exp (Real.log ‖Complex.Gammaℝ z‖) = ‖Complex.Gammaℝ z‖ :=
      Real.exp_log hpos
    have hnorm_eq :
        ‖Complex.Gammaℝ z‖ = Real.exp (Real.log ‖Complex.Gammaℝ z‖) := hexp_log.symm
    have hexp_le :
        Real.exp (Real.log ‖Complex.Gammaℝ z‖) ≤
          Real.exp ((|C| + 1) * (1 + ‖z‖) ^ m) :=
      Real.exp_le_exp.mpr hlog_le
    exact Eq.subst
      (motive := fun x : ℝ =>
        x ≤ 1 * Real.exp ((|C| + 1) * (1 + ‖z‖) ^ m))
      hnorm_eq
      (by
        calc
          Real.exp (Real.log ‖Complex.Gammaℝ z‖) ≤
              Real.exp ((|C| + 1) * (1 + ‖z‖) ^ m) := hexp_le
          _ = 1 * Real.exp ((|C| + 1) * (1 + ‖z‖) ^ m) := by
            exact (one_mul (Real.exp ((|C| + 1) * (1 + ‖z‖) ^ m))).symm)

/-- The corrected right-half-plane Gamma/Stirling region avoids the `Gammaℝ` zero at `0`.

Mathlib's `Complex.Gamma` and `Complex.Gammaℝ` are finite-valued at the classical pole
faces, with those faces represented by zeros. -/
theorem Gammaℝ_ne_zero_of_re_nonneg_and_one_le_norm
    {z : ℂ}
    (hz_re : 0 ≤ z.re)
    (hz_norm : 1 ≤ ‖z‖) :
    Complex.Gammaℝ z ≠ 0 := by
  intro hzero
  rcases Complex.Gammaℝ_eq_zero_iff.mp hzero with ⟨n, hz⟩
  subst z
  cases n with
  | zero =>
      norm_num at hz_norm
  | succ n =>
      norm_num at hz_re

/-- Points with real part at least `1` have norm at least `1`. -/
theorem one_le_norm_of_one_le_re
    {z : ℂ}
    (hz_re : 1 ≤ z.re) :
    1 ≤ ‖z‖ := by
  have hre_nonneg : 0 ≤ z.re :=
    le_trans zero_le_one hz_re
  have hre_abs_le_norm : |z.re| ≤ ‖z‖ := by
    simpa [Complex.normSq, norm_eq_abs] using Complex.abs_re_le_abs z
  have hre_abs_eq : |z.re| = z.re :=
    abs_of_nonneg hre_nonneg
  exact le_trans hz_re
    (Eq.subst
      (motive := fun x : ℝ => x ≤ ‖z‖)
      hre_abs_eq
      hre_abs_le_norm)

/-- Points with real part at least `2` lie in the large-norm region. -/
theorem one_le_norm_of_two_le_re
    {z : ℂ}
    (hz_re : 2 ≤ z.re) :
    1 ≤ ‖z‖ :=
  one_le_norm_of_one_le_re (le_trans one_le_two hz_re)

/-- Points whose imaginary coordinate has norm at least `1` have complex norm at least `1`. -/
theorem one_le_norm_of_one_le_norm_im
    {z : ℂ}
    (hz_im : 1 ≤ ‖z.im‖) :
    1 ≤ ‖z‖ := by
  have him_abs_le_norm : |z.im| ≤ ‖z‖ := by
    simpa [Complex.normSq, norm_eq_abs] using Complex.abs_im_le_abs z
  have him_norm_eq : ‖z.im‖ = |z.im| := Real.norm_eq_abs z.im
  exact le_trans
    (Eq.subst (motive := fun x : ℝ => 1 ≤ x) him_norm_eq hz_im)
    him_abs_le_norm

/-- The unfolded normalized real-Gamma factor. -/
def unfoldedNormalizedGammaℝFactor (z : ℂ) : ℂ :=
  π ^ (-z / 2) * Complex.Gamma (z / 2)

/-- `Gammaℝ` is definitionally the unfolded normalized real-Gamma factor. -/
theorem Gammaℝ_eq_unfoldedNormalizedGammaℝFactor
    (z : ℂ) :
    Complex.Gammaℝ z = unfoldedNormalizedGammaℝFactor z := by
  exact Complex.Gammaℝ_def z

/-- Norm-level form of the unfolded `Gammaℝ` normalization. -/
theorem norm_Gammaℝ_eq_norm_unfoldedNormalizedGammaℝFactor
    (z : ℂ) :
    ‖Complex.Gammaℝ z‖ = ‖unfoldedNormalizedGammaℝFactor z‖ := by
  exact congrArg norm (Gammaℝ_eq_unfoldedNormalizedGammaℝFactor z)

/-- Log-norm form of the unfolded `Gammaℝ` normalization. -/
theorem log_norm_Gammaℝ_eq_log_norm_unfoldedNormalizedGammaℝFactor
    (z : ℂ) :
    Real.log ‖Complex.Gammaℝ z‖ =
      Real.log ‖unfoldedNormalizedGammaℝFactor z‖ := by
  exact congrArg Real.log (norm_Gammaℝ_eq_norm_unfoldedNormalizedGammaℝFactor z)

/-- The unfolded normalized real-Gamma factor is nonzero on the right-half-plane
Stirling region. -/
theorem unfoldedNormalizedGammaℝFactor_ne_zero_of_re_nonneg_and_one_le_norm
    {z : ℂ}
    (hz_re : 0 ≤ z.re)
    (hz_norm : 1 ≤ ‖z‖) :
    unfoldedNormalizedGammaℝFactor z ≠ 0 := by
  intro hzero
  have hGammaℝ_ne : Complex.Gammaℝ z ≠ 0 :=
    Gammaℝ_ne_zero_of_re_nonneg_and_one_le_norm hz_re hz_norm
  have hGammaℝ_zero : Complex.Gammaℝ z = 0 :=
    Eq.trans (Gammaℝ_eq_unfoldedNormalizedGammaℝFactor z) hzero
  exact hGammaℝ_ne hGammaℝ_zero

/-- The unfolded normalized real-Gamma factor has positive norm on the right-half-plane
Stirling region. -/
theorem norm_unfoldedNormalizedGammaℝFactor_pos_of_re_nonneg_and_one_le_norm
    {z : ℂ}
    (hz_re : 0 ≤ z.re)
    (hz_norm : 1 ≤ ‖z‖) :
    0 < ‖unfoldedNormalizedGammaℝFactor z‖ := by
  exact norm_pos_iff.mpr
    (unfoldedNormalizedGammaℝFactor_ne_zero_of_re_nonneg_and_one_le_norm
      hz_re hz_norm)

/-- Classical complex-Stirling growth for the half-argument normalized Gamma factor.

This is the exact special-function input behind the right-half-plane `Gammaℝ`
normalization.  The proof is the classical Stirling argument for
`π^(-z/2) Γ(z/2)` on `0 ≤ re z`, with the small angular sector at the origin
removed by `1 ≤ ‖z‖`; cf. DLMF §5.11. -/
theorem classicalStirling_complexGamma_halfArgument_normalized_rightHalfPlane_log_linear_growth_bound_degree_one :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        1 ≤ ‖z‖ →
        Real.log ‖π ^ (-z / 2) * Complex.Gamma (z / 2)‖ ≤
          C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
  -- Classical complex Stirling for `π^(-z/2) Γ(z/2)` on the closed right
  -- half-plane, away from the origin.
  sorry

/-- Classical complex-Stirling growth for the unfolded normalized real-Gamma factor.

This theorem is only the definitional transport from the half-argument Gamma
formula to the local unfolded `Gammaℝ` name. -/
theorem classicalStirling_unfoldedNormalizedGammaℝFactor_rightHalfPlane_log_linear_growth_bound_degree_one :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        1 ≤ ‖z‖ →
        Real.log ‖unfoldedNormalizedGammaℝFactor z‖ ≤
          C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
  exact
    classicalStirling_complexGamma_halfArgument_normalized_rightHalfPlane_log_linear_growth_bound_degree_one

/-- Classical Stirling growth for the completed real Gamma factor after unfolding
`Gammaℝ`.

This keeps the exact classical input in unfolded normalized form while exposing the
older formula spelling used by the surrounding normalization wrappers. -/
theorem classicalStirling_unfoldedGammaℝ_rightHalfPlane_log_linear_growth_bound_degree_one :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        1 ≤ ‖z‖ →
        Real.log ‖π ^ (-z / 2) * Complex.Gamma (z / 2)‖ ≤
          C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
  exact classicalStirling_unfoldedNormalizedGammaℝFactor_rightHalfPlane_log_linear_growth_bound_degree_one

/-- The unfolded normalized classical Stirling estimate transfers to `Gammaℝ` by the
definitional normalization identity. -/
theorem Gammaℝ_rightHalfPlane_log_linear_growth_bound_degree_one_of_unfoldedNormalized
    (hStirling :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          1 ≤ ‖z‖ →
          Real.log ‖unfoldedNormalizedGammaℝFactor z‖ ≤
            C * (1 + ‖z‖) * Real.log (2 + ‖z‖)) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        1 ≤ ‖z‖ →
        Real.log ‖Complex.Gammaℝ z‖ ≤
          C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
  rcases hStirling with ⟨C, hC_pos, hC⟩
  refine ⟨C, hC_pos, ?_⟩
  intro z hz_re hz_norm
  calc
    Real.log ‖Complex.Gammaℝ z‖ =
        Real.log ‖unfoldedNormalizedGammaℝFactor z‖ :=
      log_norm_Gammaℝ_eq_log_norm_unfoldedNormalizedGammaℝFactor z
    _ ≤ C * (1 + ‖z‖) * Real.log (2 + ‖z‖) :=
      hC z hz_re hz_norm

/-- Classical right-half-plane logarithmic Stirling growth for the completed real Gamma
factor away from `0`, in the usual fixed-degree log-linear Stirling shape. -/
theorem classicalStirling_Gammaℝ_rightHalfPlane_log_linear_growth_bound_degree_one :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        1 ≤ ‖z‖ →
        Real.log ‖Complex.Gammaℝ z‖ ≤
          C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
  exact Gammaℝ_rightHalfPlane_log_linear_growth_bound_degree_one_of_unfoldedNormalized
    classicalStirling_unfoldedNormalizedGammaℝFactor_rightHalfPlane_log_linear_growth_bound_degree_one

/-- Standard right-half-plane logarithmic Stirling growth for the completed real Gamma
factor away from `0`, in the usual fixed-degree log-linear Stirling shape.

The exclusion `1 ≤ ‖z‖` is necessary for the classical right-half-plane Stirling
region; in Mathlib's finite-valued `Gammaℝ`, the classical pole faces are represented by
zeros, and this region avoids the zero at `0`. -/
theorem Gammaℝ_rightHalfPlane_stirling_log_linear_growth_bound_degree_one_standard :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        1 ≤ ‖z‖ →
        Real.log ‖Complex.Gammaℝ z‖ ≤
          C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
  exact classicalStirling_Gammaℝ_rightHalfPlane_log_linear_growth_bound_degree_one

/-- Standard right-half-plane logarithmic Stirling growth for the completed real Gamma
factor away from `0`, converted from the fixed-degree owner statement into the finite
degree envelope used downstream. -/
theorem Gammaℝ_rightHalfPlane_stirling_log_linear_growth_bound_standard :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        1 ≤ ‖z‖ →
        Real.log ‖Complex.Gammaℝ z‖ ≤
          C * (1 + ‖z‖) ^ m * Real.log (2 + ‖z‖) := by
  rcases Gammaℝ_rightHalfPlane_stirling_log_linear_growth_bound_degree_one_standard with
    ⟨C, hC_pos, hbound⟩
  refine ⟨C, 1, hC_pos, ?_⟩
  intro z hz_re hz_norm
  have hpow_one : (1 + ‖z‖) ^ (1 : ℕ) = 1 + ‖z‖ := by
    exact pow_one (1 + ‖z‖)
  exact Eq.subst
    (motive := fun x : ℝ =>
      Real.log ‖Complex.Gammaℝ z‖ ≤ C * x * Real.log (2 + ‖z‖))
    hpow_one.symm
    (hbound z hz_re hz_norm)

/-- The log-linear right-half-plane Stirling estimate implies the coarser finite-power
logarithmic envelope used by the completed-zeta normalization chain. -/
theorem Gammaℝ_rightHalfPlane_stirling_log_growth_bound_of_log_linear
    (hStirling :
      ∃ C : ℝ, ∃ m : ℕ,
        0 < C ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          1 ≤ ‖z‖ →
          Real.log ‖Complex.Gammaℝ z‖ ≤
            C * (1 + ‖z‖) ^ m * Real.log (2 + ‖z‖)) :
    ∃ C : ℝ, ∃ m : ℕ,
      ∀ z : ℂ,
        0 ≤ z.re →
        1 ≤ ‖z‖ →
        Real.log ‖Complex.Gammaℝ z‖ ≤
          C * (1 + ‖z‖) ^ m := by
  rcases hStirling with ⟨C, m, hC_pos, hbound⟩
  refine ⟨2 * C, m + 1, ?_⟩
  intro z hz_re hz_norm
  let H : ℝ := 1 + ‖z‖
  have hH_nonneg : 0 ≤ H :=
    le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))
  have hH_pos : 0 < H :=
    lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right (norm_nonneg z))
  have hlog_arg_pos : 0 < 2 + ‖z‖ := by
    exact add_pos_of_pos_of_nonneg (by norm_num : (0 : ℝ) < 2) (norm_nonneg z)
  have hlog_le_arg :
      Real.log (2 + ‖z‖) ≤ 2 + ‖z‖ :=
    Real.log_le_self hlog_arg_pos.le
  have harg_eq : 2 + ‖z‖ = H + 1 := by
    change 2 + ‖z‖ = (1 + ‖z‖) + 1
    ring
  have harg_le_twoH : 2 + ‖z‖ ≤ 2 * H := by
    rw [harg_eq]
    have hone_le_H : (1 : ℝ) ≤ H :=
      le_add_of_nonneg_right (norm_nonneg z)
    nlinarith
  have hlog_le_twoH :
      Real.log (2 + ‖z‖) ≤ 2 * H :=
    le_trans hlog_le_arg harg_le_twoH
  have hleft_nonneg : 0 ≤ C * H ^ m :=
    mul_nonneg (le_of_lt hC_pos) (pow_nonneg hH_nonneg m)
  have hmul_log_le :
      C * H ^ m * Real.log (2 + ‖z‖) ≤ C * H ^ m * (2 * H) :=
    mul_le_mul_of_nonneg_left hlog_le_twoH hleft_nonneg
  have htarget_eq :
      C * H ^ m * (2 * H) = (2 * C) * H ^ (m + 1) := by
    rw [pow_succ]
    ring
  exact le_trans (hbound z hz_re hz_norm)
    (Eq.subst
      (motive := fun x : ℝ => C * H ^ m * Real.log (2 + ‖z‖) ≤ x)
      htarget_eq
      hmul_log_le)

/-- Standard right-half-plane logarithmic Stirling growth for the completed real Gamma
factor away from `0`. -/
theorem Gammaℝ_rightHalfPlane_stirling_log_growth_bound_standard :
    ∃ C : ℝ, ∃ m : ℕ,
      ∀ z : ℂ,
        0 ≤ z.re →
        1 ≤ ‖z‖ →
        Real.log ‖Complex.Gammaℝ z‖ ≤
          C * (1 + ‖z‖) ^ m := by
  exact Gammaℝ_rightHalfPlane_stirling_log_growth_bound_of_log_linear
    Gammaℝ_rightHalfPlane_stirling_log_linear_growth_bound_standard

/-- Right-half-plane logarithmic Stirling growth for the archimedean factor away from `0`.

This is the canonical owner primitive for Mathlib's completed real Gamma factor. -/
theorem Gammaℝ_rightHalfPlane_stirling_log_growth_bound_ownerPrimitive :
    ∃ C : ℝ, ∃ m : ℕ,
      ∀ z : ℂ,
        0 ≤ z.re →
        1 ≤ ‖z‖ →
        Real.log ‖Complex.Gammaℝ z‖ ≤
          C * (1 + ‖z‖) ^ m := by
  exact Gammaℝ_rightHalfPlane_stirling_log_growth_bound_standard

/-- Right-half-plane logarithmic Stirling growth for the archimedean factor away from `0`.

This public owner theorem is the thin wrapper used by the completed-normalization
finite-order chain. -/
theorem Gammaℝ_rightHalfPlane_stirling_log_growth_bound :
    ∃ C : ℝ, ∃ m : ℕ,
      ∀ z : ℂ,
        0 ≤ z.re →
        1 ≤ ‖z‖ →
        Real.log ‖Complex.Gammaℝ z‖ ≤
          C * (1 + ‖z‖) ^ m := by
  exact Gammaℝ_rightHalfPlane_stirling_log_growth_bound_ownerPrimitive

/-- Vertical-tail logarithmic Stirling estimate for `Gammaℝ` in the right critical strip. -/
theorem Gammaℝ_rightCriticalStrip_verticalTail_stirling_log_growth_bound :
    ∃ C : ℝ, ∃ m : ℕ,
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        Real.log ‖Complex.Gammaℝ z‖ ≤
          C * (1 + ‖z‖) ^ m := by
  rcases Gammaℝ_rightHalfPlane_stirling_log_growth_bound with
    ⟨C, m, hC⟩
  refine ⟨C, m, ?_⟩
  intro z hz0 _hz2 hzim
  exact hC z hz0 (one_le_norm_of_one_le_norm_im hzim)

/-- Exponentiated right-half-plane Stirling growth for `Gammaℝ`, away from the pole at `0`. -/
theorem Gammaℝ_rightHalfPlane_stirling_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        1 ≤ ‖z‖ →
        ‖Complex.Gammaℝ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases Gammaℝ_finiteOrder_growth_bound_of_log_growth_on_region
    (fun z : ℂ => 0 ≤ z.re ∧ 1 ≤ ‖z‖)
    (by
      rcases Gammaℝ_rightHalfPlane_stirling_log_growth_bound with
        ⟨C, m, hC⟩
      exact ⟨C, m, fun z hz => hC z hz.1 hz.2⟩) with
    ⟨A, B, m, hA, hB, hbound⟩
  exact ⟨A, B, m, hA, hB, fun z hz_re hz_norm => hbound z ⟨hz_re, hz_norm⟩⟩

/-- Vertical-tail Stirling estimate for `Gammaℝ` in the right critical strip.

This is a standard analytic primitive for the zero ledger: it supplies the
archimedean part of finite-order control on the completed zero packet. -/
theorem Gammaℝ_rightCriticalStrip_verticalTail_stirling_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖Complex.Gammaℝ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases Gammaℝ_rightHalfPlane_stirling_growth_bound with
    ⟨A, B, m, hA, hB, hbound⟩
  refine ⟨A, B, m, hA, hB, ?_⟩
  intro z hz0 _hz2 hzim
  exact hbound z hz0 (one_le_norm_of_one_le_norm_im hzim)

/-- Mathlib's bounded-boundary vertical-strip Phragmen-Lindelöf theorem, specialized to
complex-valued functions and exposed in the local strip-growth language.

The damping proof of the polynomial/exponential strip theorem reduces to this bounded
form after multiplying by the standard strip damping factor. -/
theorem strip_uniform_bound_of_holomorphic_boundary_bound_and_mathlib_growth
    (f : ℂ → ℂ)
    (a b C : ℝ)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hgrowth :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hleft :
      ∀ z : ℂ,
        z.re = a →
        ‖f z‖ ≤ C)
    (hright :
      ∀ z : ℂ,
        z.re = b →
        ‖f z‖ ≤ C) :
    ∀ z : ℂ,
      a ≤ z.re →
      z.re ≤ b →
      ‖f z‖ ≤ C := by
  intro z hza hzb
  exact PhragmenLindelof.vertical_strip
    (f := f)
    (a := a)
    (b := b)
    (C := C)
    hhol
    hgrowth
    hleft
    hright
    hza
    hzb

/-- Separate finite-order boundary envelopes on the two vertical sides can be dominated by
a single common finite-order envelope.

This is the algebraic normalization used before applying the strip damping argument. -/
theorem strip_boundary_growth_envelopes_common_bound
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hleft :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = a →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hright :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = b →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      (∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) ∧
      (∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) := by
  rcases hleft with ⟨Al, Bl, ml, hAl, hBl, hleft_bound⟩
  rcases hright with ⟨Ar, Br, mr, hAr, hBr, hright_bound⟩
  refine ⟨Al + Ar, Bl + Br, ml + mr, add_pos hAl hAr, add_pos hBl hBr, ?_, ?_⟩
  · intro z hz_re hz_im
    exact le_trans (hleft_bound z hz_re hz_im)
      (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
        (le_of_lt hAl)
        (le_add_of_nonneg_right (le_of_lt hAr))
        (le_add_of_nonneg_right (le_of_lt hBr))
        (le_of_lt hBl)
        (Nat.le_add_right ml mr))
  · intro z hz_re hz_im
    have hdegree : mr ≤ ml + mr := by
      exact Eq.subst
        (motive := fun d : ℕ => mr ≤ d)
        (Nat.add_comm mr ml)
        (Nat.le_add_right mr ml)
    exact le_trans (hright_bound z hz_re hz_im)
      (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
        (le_of_lt hAr)
        (le_add_of_nonneg_left (le_of_lt hAl))
        (le_add_of_nonneg_left (le_of_lt hBl))
        (le_of_lt hBr)
        hdegree)

/-- In a bounded vertical strip, the basic complex height is controlled by the vertical
height. -/
theorem strip_basicHeight_le_verticalHeight
    (a b : ℝ)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    1 + ‖z‖ ≤ (|a| + |b| + 2) * (1 + ‖z.im‖) := by
  let S : ℝ := |a| + |b|
  let Y : ℝ := |z.im|
  have hS_nonneg : 0 ≤ S := by
    exact add_nonneg (abs_nonneg a) (abs_nonneg b)
  have hY_nonneg : 0 ≤ Y := by
    exact abs_nonneg z.im
  have hre_abs_le_S : |z.re| ≤ S := by
    have hleft : -S ≤ z.re := by
      have hnegS_le_neg_abs_a : -S ≤ -|a| := by
        calc
          -S = -|a| - |b| := by
            change -(|a| + |b|) = -|a| - |b|
            ring
          _ ≤ -|a| := by
            exact sub_le_self (-|a|) (abs_nonneg b)
      have hneg_abs_a_le_a : -|a| ≤ a :=
        neg_abs_le a
      exact le_trans hnegS_le_neg_abs_a (le_trans hneg_abs_a_le_a hza)
    have hright : z.re ≤ S := by
      have hb_le_abs_b : b ≤ |b| :=
        le_abs_self b
      have habs_b_le_S : |b| ≤ S := by
        exact le_add_of_nonneg_left (abs_nonneg a)
      exact le_trans hzb (le_trans hb_le_abs_b habs_b_le_S)
    exact abs_le.mpr ⟨hleft, hright⟩
  have hnorm_le : ‖z‖ ≤ S + Y := by
    have hcomplex :
        ‖z‖ ≤ |z.re| + |z.im| :=
      Eq.subst
        (motive := fun x : ℝ => x ≤ |z.re| + |z.im|)
        (Complex.norm_eq_abs z).symm
        (Complex.abs_le_abs_re_add_abs_im z)
    exact le_trans hcomplex (add_le_add_right hre_abs_le_S Y)
  have hlinear :
      1 + ‖z‖ ≤ 1 + (S + Y) :=
    add_le_add_left hnorm_le 1
  have htarget :
      1 + (S + Y) ≤ (S + 2) * (1 + Y) := by
    nlinarith [hS_nonneg, hY_nonneg]
  have him_norm_eq : ‖z.im‖ = Y :=
    Real.norm_eq_abs z.im
  exact Eq.subst
    (motive := fun T : ℝ => 1 + ‖z‖ ≤ (S + 2) * (1 + T))
    him_norm_eq.symm
    (le_trans hlinear htarget)

/-- On a bounded vertical strip, a finite-order envelope in complex height is dominated by
one in vertical height. -/
theorem finiteOrder_norm_envelope_le_strip_vertical_envelope
    {A B a b : ℝ} {m : ℕ} {z : ℂ}
    (hA : 0 ≤ A)
    (hB : 0 ≤ B)
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    A * Real.exp (B * (1 + ‖z‖) ^ m) ≤
      A * Real.exp ((B * (|a| + |b| + 2) ^ m) * (1 + ‖z.im‖) ^ m) := by
  let K : ℝ := |a| + |b| + 2
  let H : ℝ := 1 + ‖z‖
  let T : ℝ := 1 + ‖z.im‖
  have hH_nonneg : 0 ≤ H := by
    exact le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))
  have hT_nonneg : 0 ≤ T := by
    exact le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z.im))
  have hheight : H ≤ K * T :=
    strip_basicHeight_le_verticalHeight a b hza hzb
  have hpow_le : H ^ m ≤ (K * T) ^ m :=
    pow_le_pow_left₀ hH_nonneg hheight m
  have hpow_eq : (K * T) ^ m = K ^ m * T ^ m :=
    mul_pow K T m
  have hexponent_le :
      B * H ^ m ≤ (B * K ^ m) * T ^ m := by
    have hfirst : B * H ^ m ≤ B * (K * T) ^ m :=
      mul_le_mul_of_nonneg_left hpow_le hB
    exact le_trans hfirst
      (le_of_eq
        (calc
          B * (K * T) ^ m = B * (K ^ m * T ^ m) := by
            exact congrArg (fun x : ℝ => B * x) hpow_eq
          _ = (B * K ^ m) * T ^ m := by
            exact (mul_assoc B (K ^ m) (T ^ m)).symm))
  have hexp_le :
      Real.exp (B * H ^ m) ≤ Real.exp ((B * K ^ m) * T ^ m) :=
    Real.exp_le_exp.mpr hexponent_le
  exact mul_le_mul_of_nonneg_left hexp_le hA

/-- The common boundary envelope can be rewritten in terms of vertical height on a bounded
strip. -/
theorem strip_common_boundary_envelope_vertical_height_bound
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hab : a < b)
    (hboundary :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        (∀ z : ℂ,
          z.re = a →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) ∧
        (∀ z : ℂ,
          z.re = b →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      (∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) ∧
      (∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) := by
  rcases hboundary with ⟨A, B, m, hA, hB, hleft, hright⟩
  let K : ℝ := |a| + |b| + 2
  have hK_pos : 0 < K := by
    have hsum_nonneg : 0 ≤ |a| + |b| :=
      add_nonneg (abs_nonneg a) (abs_nonneg b)
    have htwo_pos : (0 : ℝ) < 2 := by
      norm_num
    have htwo_le : (2 : ℝ) ≤ K := by
      change (2 : ℝ) ≤ |a| + |b| + 2
      exact le_add_of_nonneg_left hsum_nonneg
    exact lt_of_lt_of_le htwo_pos htwo_le
  refine ⟨A, B * K ^ m, m, hA, mul_pos hB (pow_pos hK_pos m), ?_, ?_⟩
  · intro z hz_re hz_im
    have hza : a ≤ z.re := by
      exact le_of_eq hz_re.symm
    have hzb : z.re ≤ b := by
      exact le_trans (le_of_eq hz_re) (le_of_lt hab)
    exact le_trans (hleft z hz_re hz_im)
      (finiteOrder_norm_envelope_le_strip_vertical_envelope
        (le_of_lt hA)
        (le_of_lt hB)
        hza
        hzb)
  · intro z hz_re hz_im
    have hza : a ≤ z.re := by
      exact le_trans (le_of_lt hab) (le_of_eq hz_re.symm)
    have hzb : z.re ≤ b := by
      exact le_of_eq hz_re
    exact le_trans (hright z hz_re hz_im)
      (finiteOrder_norm_envelope_le_strip_vertical_envelope
        (le_of_lt hA)
        (le_of_lt hB)
        hza
        hzb)

/-- The vertical-height boundary envelope becomes uniformly bounded after multiplying by
the matching real exponential damping factor. -/
theorem strip_vertical_boundary_envelope_exp_damped_bound
    (f : ℂ → ℂ)
    (a b A B : ℝ)
    (m : ℕ)
    (hboundary :
      (∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) ∧
      (∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m))) :
    (∀ z : ℂ,
      z.re = a →
      1 ≤ ‖z.im‖ →
      Real.exp (-(B * (1 + ‖z.im‖) ^ m)) * ‖f z‖ ≤ A) ∧
    (∀ z : ℂ,
      z.re = b →
      1 ≤ ‖z.im‖ →
      Real.exp (-(B * (1 + ‖z.im‖) ^ m)) * ‖f z‖ ≤ A) := by
  constructor
  · intro z hz_re hz_im
    let X : ℝ := B * (1 + ‖z.im‖) ^ m
    have hbound :
        ‖f z‖ ≤ A * Real.exp X :=
      hboundary.1 z hz_re hz_im
    have hdamp_nonneg : 0 ≤ Real.exp (-X) :=
      le_of_lt (Real.exp_pos (-X))
    have hscaled :
        Real.exp (-X) * ‖f z‖ ≤ Real.exp (-X) * (A * Real.exp X) :=
      mul_le_mul_of_nonneg_left hbound hdamp_nonneg
    have hcollapse :
        Real.exp (-X) * (A * Real.exp X) = A := by
      calc
        Real.exp (-X) * (A * Real.exp X) =
            A * (Real.exp (-X) * Real.exp X) := by
          ring
        _ = A * Real.exp ((-X) + X) := by
          exact congrArg (fun t : ℝ => A * t) (Real.exp_add (-X) X).symm
        _ = A * Real.exp 0 := by
          ring
        _ = A := by
          rw [Real.exp_zero, mul_one]
    exact hscaled.trans_eq hcollapse
  · intro z hz_re hz_im
    let X : ℝ := B * (1 + ‖z.im‖) ^ m
    have hbound :
        ‖f z‖ ≤ A * Real.exp X :=
      hboundary.2 z hz_re hz_im
    have hdamp_nonneg : 0 ≤ Real.exp (-X) :=
      le_of_lt (Real.exp_pos (-X))
    have hscaled :
        Real.exp (-X) * ‖f z‖ ≤ Real.exp (-X) * (A * Real.exp X) :=
      mul_le_mul_of_nonneg_left hbound hdamp_nonneg
    have hcollapse :
        Real.exp (-X) * (A * Real.exp X) = A := by
      calc
        Real.exp (-X) * (A * Real.exp X) =
            A * (Real.exp (-X) * Real.exp X) := by
          ring
        _ = A * Real.exp ((-X) + X) := by
          exact congrArg (fun t : ℝ => A * t) (Real.exp_add (-X) X).symm
        _ = A * Real.exp 0 := by
          ring
        _ = A := by
          rw [Real.exp_zero, mul_one]
    exact hscaled.trans_eq hcollapse

/-- The vertical height is bounded by the ordinary complex height. -/
theorem vertical_basicHeight_le_complex_basicHeight
    (z : ℂ) :
    1 + ‖z.im‖ ≤ 1 + ‖z‖ := by
  have him_le_norm : ‖z.im‖ ≤ ‖z‖ := by
    have him_abs_le_norm : |z.im| ≤ ‖z‖ := by
      simpa [Complex.norm_eq_abs] using
        Complex.abs_im_le_abs z
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ ‖z‖)
      (Real.norm_eq_abs z.im).symm
      him_abs_le_norm
  exact add_le_add_left him_le_norm 1

/-- A vertical-height finite-order boundary envelope is also a complex-height envelope. -/
theorem finiteOrder_vertical_envelope_le_complex_envelope
    {A B : ℝ} {m : ℕ} {z : ℂ}
    (hA : 0 ≤ A)
    (hB : 0 ≤ B) :
    A * Real.exp (B * (1 + ‖z.im‖) ^ m) ≤
      A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  have hvertical_nonneg : 0 ≤ 1 + ‖z.im‖ := by
    exact le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z.im))
  have hheight_le :
      1 + ‖z.im‖ ≤ 1 + ‖z‖ :=
    vertical_basicHeight_le_complex_basicHeight z
  have hpow_le :
      (1 + ‖z.im‖) ^ m ≤ (1 + ‖z‖) ^ m :=
    pow_le_pow_left₀ hvertical_nonneg hheight_le m
  have hexponent_le :
      B * (1 + ‖z.im‖) ^ m ≤ B * (1 + ‖z‖) ^ m :=
    mul_le_mul_of_nonneg_left hpow_le hB
  have hexp_le :
      Real.exp (B * (1 + ‖z.im‖) ^ m) ≤
        Real.exp (B * (1 + ‖z‖) ^ m) :=
    Real.exp_le_exp.mpr hexponent_le
  exact mul_le_mul_of_nonneg_left hexp_le hA

/-- Vertical-height boundary data can be reused as ordinary complex-height boundary data. -/
theorem strip_vertical_boundary_envelope_complex_height_bound
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hboundary :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        (∀ z : ℂ,
          z.re = a →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) ∧
        (∀ z : ℂ,
          z.re = b →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m))) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      (∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) ∧
      (∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) := by
  rcases hboundary with ⟨A, B, m, hA, hB, hleft, hright⟩
  refine ⟨A, B, m, hA, hB, ?_, ?_⟩
  · intro z hz_re hz_im
    exact le_trans (hleft z hz_re hz_im)
      (finiteOrder_vertical_envelope_le_complex_envelope
        (le_of_lt hA)
        (le_of_lt hB))
  · intro z hz_re hz_im
    exact le_trans (hright z hz_re hz_im)
      (finiteOrder_vertical_envelope_le_complex_envelope
        (le_of_lt hA)
        (le_of_lt hB))

/-- Vertical-height boundary Phragmen-Lindelöf damping in a strip.

This is the analytic epsilon step after the boundary envelope has been normalized from
complex height to vertical height. -/
theorem strip_finite_order_growth_of_vertical_boundary_envelope_damped_family
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hboundary :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        (∀ z : ℂ,
          z.re = a →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m)) ∧
        (∀ z : ℂ,
          z.re = b →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m))) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  have hcomplex_boundary :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        (∀ z : ℂ,
          z.re = a →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) ∧
        (∀ z : ℂ,
          z.re = b →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :=
    strip_vertical_boundary_envelope_complex_height_bound f a b hboundary
  rcases hcomplex_boundary with
    ⟨Ac, Bc, mc, hAc, hBc, hleft_complex, hright_complex⟩
  rcases hboundary with ⟨A, B, m, hA, hB, hleft, hright⟩
  have hdamped_boundary :
      (∀ z : ℂ,
        z.re = a →
        1 ≤ ‖z.im‖ →
        Real.exp (-(B * (1 + ‖z.im‖) ^ m)) * ‖f z‖ ≤ A) ∧
      (∀ z : ℂ,
        z.re = b →
        1 ≤ ‖z.im‖ →
        Real.exp (-(B * (1 + ‖z.im‖) ^ m)) * ‖f z‖ ≤ A) :=
    strip_vertical_boundary_envelope_exp_damped_bound f a b A B m ⟨hleft, hright⟩
  exact strip_finite_order_growth_of_vertical_boundary_envelope_damped_family
    f a b hab hhol hfinite
    ⟨A, B, m, hA, hB, hdamped_boundary.1, hdamped_boundary.2⟩

/-- The explicit damped-family Phragmen-Lindelöf normalization theorem.

This is the remaining analytic epsilon/damping primitive: after introducing the standard
damped family, apply `strip_uniform_bound_of_holomorphic_boundary_bound_and_mathlib_growth`
to the damped family and then absorb the damping parameter back into the same finite-order
envelope. -/
theorem strip_finite_order_growth_of_common_boundary_envelope_damped_family
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hboundary :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        (∀ z : ℂ,
          z.re = a →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) ∧
        (∀ z : ℂ,
          z.re = b →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact strip_finite_order_growth_of_vertical_boundary_envelope_damped_family
    f a b hab hhol hfinite
    (strip_common_boundary_envelope_vertical_height_bound f a b hab hboundary)

/-- The standard strip damping theorem with a single common finite-order boundary envelope.

This wrapper exposes the canonical owner theorem. Its proof is exactly the reduction to the
explicit damped-family normalization theorem. -/
theorem strip_finite_order_growth_of_common_boundary_envelope_by_damping
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hboundary :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        (∀ z : ℂ,
          z.re = a →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) ∧
        (∀ z : ℂ,
          z.re = b →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact strip_finite_order_growth_of_common_boundary_envelope_damped_family
    f a b hab hhol hfinite hboundary

/-- Classical vertical-strip Phragmen-Lindelöf growth theorem.

This is the generic analytic pillar needed for the pole-cleared zeta strip estimate:
holomorphy on the open strip, admissible finite-order growth in the strip, and
finite-order boundary growth on both vertical edges propagate finite-order growth
through the strip.  The analytic damping primitive is
`strip_finite_order_growth_of_common_boundary_envelope_damped_family`; this theorem
first consolidates the two boundary envelopes and then applies that primitive. -/
theorem strip_finite_order_growth_reduces_to_bounded_boundary_phragmenLindelof
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hleft :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = a →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hright :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = b →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact strip_finite_order_growth_of_common_boundary_envelope_by_damping
    f a b hab hhol hfinite
    (strip_boundary_growth_envelopes_common_bound f a b hleft hright)

/-- Classical vertical-strip Phragmen-Lindelöf finite-growth theorem.

This wrapper exposes the canonical owner theorem.  Its proof is exactly the damping
reduction to the bounded-boundary strip theorem. -/
theorem strip_growth_bound_of_holomorphic_boundary_growth_and_finite_order
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hab : a < b)
    (hhol : DiffContOnCl ℂ f (Complex.re ⁻¹' Set.Ioo a b))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (b - a) ∧
        ∃ D : ℝ,
          f =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hleft :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = a →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hright :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = b →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact strip_finite_order_growth_reduces_to_bounded_boundary_phragmenLindelof
    f a b hab hhol hfinite hleft hright

/-- The removable pole-cleared zeta factor, normalized by the residue value at `1`. -/
def poleClearedRiemannZeta (z : ℂ) : ℂ :=
  Function.update (fun w : ℂ => (w - 1) * riemannZeta w) 1 1 z

/-- Away from the pole face, the removable pole-cleared factor is the ordinary product. -/
theorem poleClearedRiemannZeta_eq_of_ne_one
    {z : ℂ}
    (hz : z ≠ 1) :
    poleClearedRiemannZeta z = (z - 1) * riemannZeta z := by
  unfold poleClearedRiemannZeta
  exact Function.update_noteq hz 1 (fun w : ℂ => (w - 1) * riemannZeta w)

/-- At the pole face, the removable pole-cleared factor has residue value `1`. -/
theorem poleClearedRiemannZeta_one :
    poleClearedRiemannZeta 1 = 1 := by
  unfold poleClearedRiemannZeta
  exact Function.update_same 1 1 (fun w : ℂ => (w - 1) * riemannZeta w)

/-- The removable pole-cleared zeta factor is continuous everywhere. -/
theorem poleClearedRiemannZeta_continuousAt
    (z : ℂ) :
    ContinuousAt poleClearedRiemannZeta z := by
  by_cases hz : z = 1
  · subst z
    unfold poleClearedRiemannZeta
    simpa only [continuousAt_update_same] using riemannZeta_residue_one
  · have hraw :
        ContinuousAt (fun w : ℂ => (w - 1) * riemannZeta w) z :=
      (continuousAt_id.sub continuousAt_const).mul
        ((differentiableAt_riemannZeta hz).continuousAt)
    have hevent :
        poleClearedRiemannZeta =ᶠ[𝓝 z]
          (fun w : ℂ => (w - 1) * riemannZeta w) := by
      filter_upwards [eventually_ne_nhds hz] with w hw
      exact poleClearedRiemannZeta_eq_of_ne_one hw
    exact hraw.congr_of_eventuallyEq hevent

/-- The removable pole-cleared zeta factor is continuous on the right critical compact
rectangle. -/
theorem poleClearedRiemannZeta_continuousOn_rightCriticalStripCompactSet :
    ContinuousOn poleClearedRiemannZeta
      completedRiemannZeta₀_rightCriticalStripCompactSet := by
  intro z _hz
  exact (poleClearedRiemannZeta_continuousAt z).continuousWithinAt

/-- Compact boundedness for the removable pole-cleared zeta factor. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_compact_norm_bound :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        z ∈ completedRiemannZeta₀_rightCriticalStripCompactSet →
        ‖poleClearedRiemannZeta z‖ ≤ C := by
  rcases IsCompact.exists_bound_of_continuousOn
      completedRiemannZeta₀_rightCriticalStripCompactSet_isCompact
      poleClearedRiemannZeta_continuousOn_rightCriticalStripCompactSet with
    ⟨C0, hC0⟩
  refine ⟨max C0 0 + 1, ?_, ?_⟩
  · exact add_pos_of_nonneg_of_pos (le_max_right C0 0) zero_lt_one
  intro z hz
  have hraw : ‖poleClearedRiemannZeta z‖ ≤ C0 :=
    hC0 z hz
  exact le_trans hraw (le_trans (le_max_left C0 0) (le_add_of_nonneg_right zero_le_one))

/-- Compact part of the pole-cleared zeta strip estimate. -/
theorem riemannZeta_rightCriticalStrip_poleCleared_compact_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖z.im‖ ≤ 1 →
        ‖(z - 1) * riemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases poleClearedRiemannZeta_rightCriticalStrip_compact_norm_bound with
    ⟨C, hC, hbound⟩
  refine ⟨C, 1, 0, hC, zero_lt_one, ?_⟩
  intro z hz0 hz2 hz_im
  have hz_mem : z ∈ completedRiemannZeta₀_rightCriticalStripCompactSet :=
    ⟨hz0, hz2, hz_im⟩
  have hfactor_ge_one : (1 : ℝ) ≤ Real.exp (1 * (1 + ‖z‖) ^ 0) := by
    have hone : (1 : ℝ) * (1 + ‖z‖) ^ 0 = 1 := by
      ring
    exact Eq.subst
      (motive := fun x : ℝ => (1 : ℝ) ≤ Real.exp x)
      hone.symm
      (Real.one_le_exp_iff.mpr zero_le_one)
  have hC_nonneg : 0 ≤ C :=
    le_of_lt hC
  have hC_le_scaled :
      C ≤ C * Real.exp (1 * (1 + ‖z‖) ^ 0) :=
    le_mul_of_one_le_right hC_nonneg hfactor_ge_one
  by_cases hz1 : z = 1
  · subst z
    have hzero :
        ((1 : ℂ) - 1) * riemannZeta (1 : ℂ) = 0 := by
      ring
    have hnorm_zero :
        ‖((1 : ℂ) - 1) * riemannZeta (1 : ℂ)‖ = 0 := by
      calc
        ‖((1 : ℂ) - 1) * riemannZeta (1 : ℂ)‖ = ‖(0 : ℂ)‖ := by
          exact congrArg norm hzero
        _ = 0 := by
          exact norm_zero
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ C * Real.exp (1 * (1 + ‖(1 : ℂ)‖) ^ 0))
      hnorm_zero.symm
      (le_trans (le_of_lt hC) hC_le_scaled)
  · have hpc_eq :
        poleClearedRiemannZeta z = (z - 1) * riemannZeta z :=
      poleClearedRiemannZeta_eq_of_ne_one hz1
    have hraw :
        ‖(z - 1) * riemannZeta z‖ ≤ C := by
      exact Eq.subst
        (motive := fun w : ℂ => ‖w‖ ≤ C)
        hpc_eq
        (hbound z hz_mem)
    exact le_trans hraw hC_le_scaled

/-- Reflection sends the left edge of the zeta strip to the vertical line `re = 1`. -/
theorem one_sub_leftBoundary_re_eq_one
    {z : ℂ}
    (hz_re : z.re = 0) :
    ((1 : ℂ) - z).re = 1 := by
  calc
    ((1 : ℂ) - z).re = (1 : ℂ).re - z.re := by
      exact Complex.sub_re (1 : ℂ) z
    _ = 1 - z.re := by
      norm_num
    _ = 1 := by
      rw [hz_re]
      ring

/-- On the left vertical tail, neither `z`, `1-z`, nor `Gammaℝ z` hits the exceptional
faces used in the completed-zeta normalization. -/
theorem Gammaℝ_leftBoundary_nonzero_of_verticalTail
    {z : ℂ}
    (hz_re : z.re = 0)
    (hz_im : 1 ≤ ‖z.im‖) :
    z ≠ 0 ∧ (1 : ℂ) - z ≠ 0 ∧
      Complex.Gammaℝ z ≠ 0 ∧ Complex.Gammaℝ ((1 : ℂ) - z) ≠ 0 := by
  have hz_ne_zero : z ≠ 0 := by
    intro hz
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
    exact not_lt_of_ge hone_le_zero zero_lt_one
  have hone_sub_ne_zero : (1 : ℂ) - z ≠ 0 := by
    intro hsub
    have hre_zero : ((1 : ℂ) - z).re = 0 := by
      calc
        ((1 : ℂ) - z).re = (0 : ℂ).re := by
          exact congrArg Complex.re hsub
        _ = 0 := by
          exact Complex.zero_re
    have hre_one : ((1 : ℂ) - z).re = 1 := by
      exact one_sub_leftBoundary_re_eq_one hz_re
    have hone_eq_zero : (1 : ℝ) = 0 := by
      calc
        (1 : ℝ) = ((1 : ℂ) - z).re := hre_one.symm
        _ = 0 := hre_zero
    norm_num at hone_eq_zero
  have hGamma_ne : Complex.Gammaℝ z ≠ 0 := by
    exact Gammaℝ_ne_zero_of_re_nonneg_and_one_le_norm
      (le_of_eq hz_re.symm)
      (one_le_norm_of_one_le_norm_im hz_im)
  have hGamma_reflected_ne : Complex.Gammaℝ ((1 : ℂ) - z) ≠ 0 := by
    have hw_re_nonneg : 0 ≤ ((1 : ℂ) - z).re := by
      exact le_trans zero_le_one (le_of_eq (one_sub_leftBoundary_re_eq_one hz_re).symm)
    have hw_norm_ge_one : 1 ≤ ‖(1 : ℂ) - z‖ := by
      have him_abs_le : ‖((1 : ℂ) - z).im‖ ≤ ‖(1 : ℂ) - z‖ :=
        Complex.abs_im_le_abs ((1 : ℂ) - z)
      have him_eq : ((1 : ℂ) - z).im = -z.im := by
        calc
          ((1 : ℂ) - z).im = (1 : ℂ).im - z.im := by
            exact Complex.sub_im (1 : ℂ) z
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
        (Eq.subst (motive := fun x : ℝ => 1 ≤ x) him_norm_eq.symm hz_im)
        him_abs_le
    exact Gammaℝ_ne_zero_of_re_nonneg_and_one_le_norm hw_re_nonneg hw_norm_ge_one
  exact ⟨hz_ne_zero, hone_sub_ne_zero, hGamma_ne, hGamma_reflected_ne⟩

/-- The elementary pole-clearing ratio on the left boundary has finite-order growth.

This is the algebraic factor
`(z - 1) / (((1 : ℂ) - z) - 1)` separated from the Gamma-ratio Stirling input. -/
theorem leftBoundary_completedFunctionalEquation_poleClearing_ratio_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  refine ⟨2, 1, 1, by norm_num, zero_lt_one, ?_⟩
  intro z hz_re hz_im
  have hz_norm_ge_one : (1 : ℝ) ≤ ‖z‖ :=
    one_le_norm_of_one_le_norm_im hz_im
  have hden_eq : (((1 : ℂ) - z) - 1) = -z := by
    ring
  have hnum_norm_le : ‖z - 1‖ ≤ ‖z‖ + 1 :=
    le_trans (norm_sub_le z (1 : ℂ))
      (by
        exact le_of_eq
          (congrArg (fun x : ℝ => ‖z‖ + x) (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))))
  have hnum_norm_le_two_norm : ‖z - 1‖ ≤ 2 * ‖z‖ := by
    calc
      ‖z - 1‖ ≤ ‖z‖ + 1 := hnum_norm_le
      _ ≤ ‖z‖ + ‖z‖ := add_le_add_left hz_norm_ge_one ‖z‖
      _ = 2 * ‖z‖ := by ring
  have hz_norm_pos : 0 < ‖z‖ :=
    lt_of_lt_of_le zero_lt_one hz_norm_ge_one
  have hratio_le_two : ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ ≤ (2 : ℝ) := by
    calc
      ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ =
          ‖z - 1‖ / ‖z‖ := by
        calc
          ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ =
              ‖z - 1‖ / ‖(((1 : ℂ) - z) - 1)‖ := by
            exact norm_div (z - 1) (((1 : ℂ) - z) - 1)
          _ = ‖z - 1‖ / ‖z‖ := by
            exact congrArg (fun x : ℝ => ‖z - 1‖ / x)
              (by
                calc
                  ‖(((1 : ℂ) - z) - 1)‖ = ‖-z‖ := by
                    exact congrArg norm hden_eq
                  _ = ‖z‖ := norm_neg z)
      _ ≤ (2 * ‖z‖) / ‖z‖ := div_le_div_of_nonneg_right hnum_norm_le_two_norm (norm_nonneg z)
      _ = 2 := by
        exact mul_div_cancel_right₀ 2 (ne_of_gt hz_norm_pos)
  have hone_le_exp :
      (1 : ℝ) ≤ Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ)) := by
    have hbase_nonneg : 0 ≤ (1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ) := by
      exact mul_nonneg zero_le_one
        (pow_nonneg (le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))) 1)
    exact le_trans (le_add_of_nonneg_left hbase_nonneg)
      (Real.add_one_le_exp ((1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ)))
  calc
    ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ ≤ 2 := hratio_le_two
    _ ≤ 2 * Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ)) := by
      exact le_mul_of_one_le_right (by norm_num : (0 : ℝ) ≤ 2) hone_le_exp

/-- A positive polynomial vertical-height bound is an exponential finite-order bound in the
same vertical-height variable. -/
theorem vertical_polynomial_growth_bound_to_exponential_growth_bound
    {f : ℂ → ℂ}
    (hpoly :
      ∃ A : ℝ, ∃ m : ℕ,
        0 < A ∧
        ∀ z : ℂ,
          z.re = 0 →
          1 ≤ ‖z.im‖ →
          ‖f z‖ ≤ A * (1 + ‖z.im‖) ^ m) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z.im‖) ^ m) := by
  rcases hpoly with ⟨A, m, hA_pos, hbound⟩
  refine ⟨A, 1, m, hA_pos, zero_lt_one, ?_⟩
  intro z hz_re hz_im
  let H : ℝ := (1 + ‖z.im‖) ^ m
  have hH_nonneg : 0 ≤ H :=
    pow_nonneg
      (le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z.im)))
      m
  have hH_le_exp : H ≤ Real.exp ((1 : ℝ) * H) := by
    have hone_mul : (1 : ℝ) * H = H := by
      exact one_mul H
    exact Eq.subst
      (motive := fun x : ℝ => H ≤ Real.exp x)
      hone_mul.symm
      (Real.le_exp_self H)
  have hscaled :
      A * H ≤ A * Real.exp ((1 : ℝ) * H) :=
    mul_le_mul_of_nonneg_left hH_le_exp (le_of_lt hA_pos)
  exact le_trans (hbound z hz_re hz_im) hscaled

/-- A point on the left boundary line is its vertical coordinate times `I`. -/
theorem leftBoundary_eq_im_mul_I
    (z : ℂ)
    (hz_re : z.re = 0) :
    z = (z.im : ℂ) * Complex.I := by
  ext
  · exact hz_re
  · rfl

/-- The unfolded completed real-Gamma ratio on the left boundary line `z = it`. -/
def unfoldedGammaℝLeftBoundaryRatioRealParam (t : ℝ) : ℂ :=
  (π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
      Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
    (π ^ (-((t : ℂ) * Complex.I) / 2) *
      Complex.Gamma (((t : ℂ) * Complex.I) / 2))

/-- The real-parameter unfolded Gamma-ratio is exactly the inline two-Gamma formula. -/
theorem unfoldedGammaℝLeftBoundaryRatioRealParam_eq_inline
    (t : ℝ) :
    unfoldedGammaℝLeftBoundaryRatioRealParam t =
      (π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
          Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
        (π ^ (-((t : ℂ) * Complex.I) / 2) *
          Complex.Gamma (((t : ℂ) * Complex.I) / 2)) := by
  rfl

/-- The completed real-Gamma ratio on the left boundary unfolds to the classical
two-Gamma ratio. -/
theorem Gammaℝ_leftBoundary_ratio_realParam_eq_unfolded
    (t : ℝ) :
    Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I) /
        Complex.Gammaℝ ((t : ℂ) * Complex.I) =
      unfoldedGammaℝLeftBoundaryRatioRealParam t := by
  rw [unfoldedGammaℝLeftBoundaryRatioRealParam_eq_inline]
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def]

/-- Norm form of the completed real-Gamma ratio unfolding on the left boundary. -/
theorem norm_Gammaℝ_leftBoundary_ratio_realParam_eq_norm_unfolded
    (t : ℝ) :
    ‖Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I) /
        Complex.Gammaℝ ((t : ℂ) * Complex.I)‖ =
      ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ := by
  exact congrArg norm (Gammaℝ_leftBoundary_ratio_realParam_eq_unfolded t)

/-- Classical vertical Stirling control for the two-Gamma quotient on the left boundary.

This is the exact special-function input after substituting `z = it` and unfolding
`Γℝ(s) = π^(-s/2) Γ(s/2)`.  It follows from the two-sided vertical Stirling formula
for the two Gamma factors; cf. DLMF §5.11. -/
theorem classicalStirling_complexGamma_leftBoundary_twoGammaQuotient_vertical_sqrt_growth_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖(π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
            (π ^ (-((t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((t : ℂ) * Complex.I) / 2))‖ ≤
          A * Real.sqrt (1 + ‖t‖) := by
  -- Classical vertical Stirling for the quotient
  -- `π^(-(1-it)/2) Γ((1-it)/2) / (π^(-it/2) Γ(it/2))`.
  sorry

/-- Classical vertical Stirling control for the unfolded completed real Gamma ratio,
stated on the real parameter of the left boundary line.

This theorem is only the definitional transport from the two-Gamma quotient to the
local unfolded `Gammaℝ` ratio name. -/
theorem classicalStirling_unfoldedGammaℝLeftBoundaryRatioRealParam_vertical_sqrt_growth_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ ≤
          A * Real.sqrt (1 + ‖t‖) := by
  rcases classicalStirling_complexGamma_leftBoundary_twoGammaQuotient_vertical_sqrt_growth_bound with
    ⟨A, hA_pos, hbound⟩
  refine ⟨A, hA_pos, ?_⟩
  intro t ht
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ A * Real.sqrt (1 + ‖t‖))
    (congrArg norm (unfoldedGammaℝLeftBoundaryRatioRealParam_eq_inline t)).symm
    (hbound t ht)

/-- The named unfolded Gamma-ratio estimate is the older inline formula spelling. -/
theorem classicalStirling_unfoldedGammaℝ_leftBoundary_ratio_vertical_sqrt_growth_bound_realParam :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖(π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
            (π ^ (-((t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((t : ℂ) * Complex.I) / 2))‖ ≤
          A * Real.sqrt (1 + ‖t‖) := by
  rcases classicalStirling_unfoldedGammaℝLeftBoundaryRatioRealParam_vertical_sqrt_growth_bound with
    ⟨A, hA_pos, hbound⟩
  refine ⟨A, hA_pos, ?_⟩
  intro t ht
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ A * Real.sqrt (1 + ‖t‖))
    (congrArg norm (unfoldedGammaℝLeftBoundaryRatioRealParam_eq_inline t))
    (hbound t ht)

/-- The unfolded vertical Stirling estimate is exactly the corresponding `Gammaℝ`
estimate after applying `Gammaℝ_def`. -/
theorem classicalStirling_Gammaℝ_leftBoundary_ratio_vertical_sqrt_growth_bound_realParam :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I) /
            Complex.Gammaℝ ((t : ℂ) * Complex.I)‖ ≤
          A * Real.sqrt (1 + ‖t‖) := by
  rcases classicalStirling_unfoldedGammaℝ_leftBoundary_ratio_vertical_sqrt_growth_bound_realParam with
    ⟨A, hA_pos, hbound⟩
  refine ⟨A, hA_pos, ?_⟩
  intro t ht
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
      hbound t ht

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
theorem classicalStirling_Gammaℝ_leftBoundary_ratio_vertical_linear_growth_bound_realParam :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I) /
            Complex.Gammaℝ ((t : ℂ) * Complex.I)‖ ≤
          A * (1 + ‖t‖) := by
  rcases classicalStirling_Gammaℝ_leftBoundary_ratio_vertical_sqrt_growth_bound_realParam with
    ⟨A, hA_pos, hbound⟩
  refine ⟨A, hA_pos, ?_⟩
  intro t ht
  have hsqrt_to_linear :
      A * Real.sqrt (1 + ‖t‖) ≤ A * (1 + ‖t‖) :=
    mul_le_mul_of_nonneg_left
      (sqrt_one_add_norm_le_one_add_norm t)
      (le_of_lt hA_pos)
  exact le_trans (hbound t ht) hsqrt_to_linear

/-- The real-parameter square-root Stirling estimate transported to the full left
boundary line. -/
theorem classicalStirling_Gammaℝ_leftBoundary_ratio_vertical_sqrt_growth_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * Real.sqrt (1 + ‖z.im‖) := by
  rcases classicalStirling_Gammaℝ_leftBoundary_ratio_vertical_sqrt_growth_bound_realParam with
    ⟨A, hA_pos, hbound⟩
  refine ⟨A, hA_pos, ?_⟩
  intro z hz_re hz_im
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
    haxis_bound

/-- Classical two-sided vertical Stirling control for the completed real Gamma ratio on
the left boundary line, in the sharp polynomial degree needed by the critical-line
functional-equation transport. -/
theorem classicalStirling_Gammaℝ_leftBoundary_ratio_vertical_linear_growth_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * (1 + ‖z.im‖) := by
  rcases classicalStirling_Gammaℝ_leftBoundary_ratio_vertical_sqrt_growth_bound with
    ⟨A, hA_pos, hbound⟩
  refine ⟨A, hA_pos, ?_⟩
  intro z hz_re hz_im
  have hsqrt_to_linear :
      A * Real.sqrt (1 + ‖z.im‖) ≤ A * (1 + ‖z.im‖) :=
    mul_le_mul_of_nonneg_left
      (sqrt_one_add_norm_le_one_add_norm z.im)
      (le_of_lt hA_pos)
  exact le_trans (hbound z hz_re hz_im) hsqrt_to_linear

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
  rcases hlinear with ⟨A, hA_pos, hbound⟩
  refine ⟨A, 1, hA_pos, ?_⟩
  intro z hz_re hz_im
  have hpow_one : (1 + ‖z.im‖) ^ (1 : ℕ) = 1 + ‖z.im‖ := by
    exact pow_one (1 + ‖z.im‖)
  exact Eq.subst
    (motive := fun x : ℝ =>
      ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤ A * x)
    hpow_one.symm
    (hbound z hz_re hz_im)

/-- Standard polynomial Stirling control for the completed real Gamma ratio on the left
vertical tail.

This is the classical two-sided vertical Gamma-ratio estimate after substituting the
left boundary line `z = it`: the ratio is controlled by a fixed polynomial in `|t|`. -/
theorem Gammaℝ_leftBoundary_ratio_vertical_polynomial_stirling_growth_bound_standard :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * (1 + ‖z.im‖) ^ m := by
  exact Gammaℝ_leftBoundary_ratio_vertical_polynomial_growth_bound_of_linear
    classicalStirling_Gammaℝ_leftBoundary_ratio_vertical_linear_growth_bound

/-- Standard finite-order Stirling control for the completed real Gamma ratio on the left
vertical tail, converted from the polynomial vertical-height Stirling statement.

This is the exact analytic statement left after the elementary pole-clearing ratio has
been separated from the completed-functional-equation multiplier. -/
theorem Gammaℝ_leftBoundary_ratio_vertical_stirling_growth_bound_standard :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * Real.exp (B * (1 + ‖z.im‖) ^ m) := by
  exact vertical_polynomial_growth_bound_to_exponential_growth_bound
    Gammaℝ_leftBoundary_ratio_vertical_polynomial_stirling_growth_bound_standard

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
  rcases hStirling with ⟨A, B, m, hA, hB, hbound⟩
  refine ⟨A, B, m, hA, hB, ?_⟩
  intro z hz_re hz_im
  exact le_trans (hbound z hz_re hz_im)
    (finiteOrder_vertical_envelope_le_complex_envelope
      (le_of_lt hA)
      (le_of_lt hB))

/-- Standard finite-order Stirling control for the completed real Gamma ratio on the left
vertical tail, in the complex-height envelope used downstream. -/
theorem Gammaℝ_leftBoundary_ratio_stirling_growth_bound_standard :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact Gammaℝ_leftBoundary_ratio_growth_bound_of_vertical_stirling
    Gammaℝ_leftBoundary_ratio_vertical_stirling_growth_bound_standard

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
theorem Gammaℝ_leftBoundary_ratio_stirling_growth_bound_ownerPrimitive :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact Gammaℝ_leftBoundary_ratio_stirling_growth_bound_standard

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
  rcases hf with ⟨Af, Bf, mf, hAf, hBf, hf_bound⟩
  rcases hg with ⟨Ag, Bg, mg, hAg, hBg, hg_bound⟩
  refine ⟨Af * Ag, 2 * (Bf + Bg + 1), mf + mg,
    mul_pos hAf hAg,
    mul_pos zero_lt_two (add_pos (add_pos hBf hBg) zero_lt_one), ?_⟩
  intro z hz_re hz_im
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
        ring
      _ = (Af * Ag) *
          Real.exp (((Bf + Bg + 1) * H ^ (mf + mg)) +
            ((Bf + Bg + 1) * H ^ (mf + mg))) := by
        exact congrArg (fun x : ℝ => (Af * Ag) * x)
          (Real.exp_add ((Bf + Bg + 1) * H ^ (mf + mg))
            ((Bf + Bg + 1) * H ^ (mf + mg))).symm
      _ = Af * Ag * Real.exp ((2 * (Bf + Bg + 1)) * H ^ (mf + mg)) := by
        ring
  exact le_trans hmul (hcollapse ▸ le_rfl)

/-- The exact Gamma-ratio Stirling input for the left-edge completed-functional-equation
transport.

The proof is now only the product of the elementary pole-clearing ratio and the
peeled Gamma-ratio Stirling theorem. -/
theorem Gammaℝ_leftBoundary_completedFunctionalEquation_multiplier_stirling_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖((z - 1) / (((1 : ℂ) - z) - 1)) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases leftBoundary_finiteOrder_product_growth_bound_core
      leftBoundary_completedFunctionalEquation_poleClearing_ratio_growth_bound
      Gammaℝ_leftBoundary_ratio_stirling_growth_bound_ownerPrimitive with
    ⟨A, B, m, hA, hB, hproduct⟩
  refine ⟨A, B, m, hA, hB, ?_⟩
  intro z hz_re hz_im
  have hnorm :
      ‖((z - 1) / (((1 : ℂ) - z) - 1)) *
          (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)‖ =
        ‖(z - 1) / (((1 : ℂ) - z) - 1)‖ *
          ‖Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z‖ :=
    norm_mul
      ((z - 1) / (((1 : ℂ) - z) - 1))
      (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    hnorm.symm
    (hproduct z hz_re hz_im)

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
  rcases hf with ⟨Af, Bf, mf, hAf, hBf, hf_bound⟩
  rcases hg with ⟨Ag, Bg, mg, hAg, hBg, hg_bound⟩
  refine ⟨Af * Ag, 2 * (Bf + Bg + 1), mf + mg,
    mul_pos hAf hAg,
    mul_pos zero_lt_two (add_pos (add_pos hBf hBg) zero_lt_one), ?_⟩
  intro z hz_re hz_im
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
        ring
      _ = (Af * Ag) *
          Real.exp (((Bf + Bg + 1) * H ^ (mf + mg)) +
            ((Bf + Bg + 1) * H ^ (mf + mg))) := by
        exact congrArg (fun x : ℝ => (Af * Ag) * x)
          (Real.exp_add ((Bf + Bg + 1) * H ^ (mf + mg))
            ((Bf + Bg + 1) * H ^ (mf + mg))).symm
      _ = Af * Ag * Real.exp ((2 * (Bf + Bg + 1)) * H ^ (mf + mg)) := by
        ring
  have htarget_guard :
      Af * Ag * Real.exp ((2 * (Bf + Bg + 1)) * H ^ (mf + mg)) ≤
        Af * Ag * Real.exp ((2 * (Bf + Bg + 1)) * H ^ (mf + mg)) :=
    le_rfl
  exact le_trans hmul (hcollapse ▸ htarget_guard)

/-- A positive polynomial vertical-height bound on the boundary line `re = 1` is an
exponential finite-order bound in the same vertical-height variable. -/
theorem boundaryLine_one_polynomial_growth_bound_to_exponential_growth_bound
    {f : ℂ → ℂ}
    (hpoly :
      ∃ A : ℝ, ∃ m : ℕ,
        0 < A ∧
        ∀ w : ℂ,
          w.re = 1 →
          1 ≤ ‖w.im‖ →
          ‖f w‖ ≤ A * (1 + ‖w.im‖) ^ m) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖f w‖ ≤ A * Real.exp (B * (1 + ‖w.im‖) ^ m) := by
  rcases hpoly with ⟨A, m, hA_pos, hbound⟩
  refine ⟨A, 1, m, hA_pos, zero_lt_one, ?_⟩
  intro w hw_re hw_im
  let H : ℝ := (1 + ‖w.im‖) ^ m
  have hH_nonneg : 0 ≤ H :=
    pow_nonneg
      (le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg w.im)))
      m
  have hH_le_exp : H ≤ Real.exp ((1 : ℝ) * H) := by
    have hone_mul : (1 : ℝ) * H = H := by
      exact one_mul H
    exact Eq.subst
      (motive := fun x : ℝ => H ≤ Real.exp x)
      hone_mul.symm
      (Real.le_exp_self H)
  have hscaled :
      A * H ≤ A * Real.exp ((1 : ℝ) * H) :=
    mul_le_mul_of_nonneg_left hH_le_exp (le_of_lt hA_pos)
  exact le_trans (hbound w hw_re hw_im) hscaled

/-- On the boundary line `re = 1`, the pole-clearing factor has zero real part. -/
theorem boundaryLine_one_sub_one_re_eq_zero
    {w : ℂ}
    (hw_re : w.re = 1) :
    (w - 1).re = 0 := by
  have hone_re : (1 : ℂ).re = 1 :=
    rfl
  calc
    (w - 1).re = w.re - (1 : ℂ).re := by
      exact Complex.sub_re w 1
    _ = 1 - (1 : ℂ).re := by
      exact congrArg (fun x : ℝ => x - (1 : ℂ).re) hw_re
    _ = 1 - 1 := by
      exact congrArg (fun x : ℝ => 1 - x) hone_re
    _ = 0 := by
      exact sub_self 1

/-- On the boundary line `re = 1`, the pole-clearing factor keeps the original
imaginary coordinate. -/
theorem boundaryLine_one_sub_one_im_eq
    (w : ℂ) :
    (w - 1).im = w.im := by
  have hone_im : (1 : ℂ).im = 0 :=
    rfl
  calc
    (w - 1).im = w.im - (1 : ℂ).im := by
      exact Complex.sub_im w 1
    _ = w.im - 0 := by
      exact congrArg (fun x : ℝ => w.im - x) hone_im
    _ = w.im := by
      exact sub_zero w.im

/-- On the boundary line `re = 1`, the pole-clearing factor has exactly the vertical
height as norm. -/
theorem boundaryLine_one_sub_one_norm_eq_vertical_height
    {w : ℂ}
    (hw_re : w.re = 1) :
    ‖w - 1‖ = ‖w.im‖ := by
  have hre_zero : (w - 1).re = 0 :=
    boundaryLine_one_sub_one_re_eq_zero hw_re
  have him_eq : (w - 1).im = w.im :=
    boundaryLine_one_sub_one_im_eq w
  have habs_eq_im :
      Complex.abs (w - 1) = |(w - 1).im| :=
    (Complex.abs_im_eq_abs.mpr hre_zero).symm
  have him_abs_eq_norm : |(w - 1).im| = ‖w.im‖ := by
    calc
      |(w - 1).im| = |w.im| := by
        exact congrArg abs him_eq
      _ = ‖w.im‖ := (Real.norm_eq_abs w.im).symm
  calc
    ‖w - 1‖ = Complex.abs (w - 1) := by
      exact Complex.norm_eq_abs (w - 1)
    _ = |(w - 1).im| := habs_eq_im
    _ = ‖w.im‖ := him_abs_eq_norm

/-- On the boundary line `re = 1`, the pole-clearing factor has norm controlled by the
vertical height. -/
theorem boundaryLine_one_sub_one_norm_le_vertical_height
    {w : ℂ}
    (hw_re : w.re = 1) :
    ‖w - 1‖ ≤ 1 + ‖w.im‖ := by
  have hnorm_eq :
      ‖w - 1‖ = ‖w.im‖ :=
    boundaryLine_one_sub_one_norm_eq_vertical_height hw_re
  exact le_trans (le_of_eq hnorm_eq)
    (le_add_of_nonneg_left zero_le_one)

/-- A logarithmic zeta estimate on `re = 1` gives the log-linear estimate for the
pole-cleared product `(s - 1)ζ(s)`. -/
theorem boundaryLine_one_zeta_log_growth_bound_to_poleCleared_log_linear_growth_bound
    (hzeta :
      ∃ A : ℝ,
        0 < A ∧
        ∀ w : ℂ,
          w.re = 1 →
          1 ≤ ‖w.im‖ →
          ‖riemannZeta w‖ ≤ A * Real.log (2 + ‖w.im‖)) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
  rcases hzeta with ⟨A, hA_pos, hzeta_bound⟩
  refine ⟨A, hA_pos, ?_⟩
  intro w hw_re hw_im
  have hpole_norm :
      ‖w - 1‖ ≤ 1 + ‖w.im‖ :=
    boundaryLine_one_sub_one_norm_le_vertical_height hw_re
  have hzeta_norm :
      ‖riemannZeta w‖ ≤ A * Real.log (2 + ‖w.im‖) :=
    hzeta_bound w hw_re hw_im
  have hzeta_rhs_nonneg :
      0 ≤ A * Real.log (2 + ‖w.im‖) :=
    le_trans (norm_nonneg (riemannZeta w)) hzeta_norm
  have hheight_nonneg : 0 ≤ 1 + ‖w.im‖ :=
    le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg w.im))
  have hmul :
      ‖w - 1‖ * ‖riemannZeta w‖ ≤
        (1 + ‖w.im‖) * (A * Real.log (2 + ‖w.im‖)) :=
    mul_le_mul hpole_norm hzeta_norm hzeta_rhs_nonneg hheight_nonneg
  have htarget_eq :
      (1 + ‖w.im‖) * (A * Real.log (2 + ‖w.im‖)) =
        A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
    calc
      (1 + ‖w.im‖) * (A * Real.log (2 + ‖w.im‖)) =
          ((1 + ‖w.im‖) * A) * Real.log (2 + ‖w.im‖) := by
        exact mul_assoc (1 + ‖w.im‖) A (Real.log (2 + ‖w.im‖))
      _ =
          (A * (1 + ‖w.im‖)) * Real.log (2 + ‖w.im‖) := by
        exact congrArg
          (fun x : ℝ => x * Real.log (2 + ‖w.im‖))
          (mul_comm (1 + ‖w.im‖) A)
      _ =
          A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
        exact rfl
  have hnorm_eq :
      ‖(w - 1) * riemannZeta w‖ = ‖w - 1‖ * ‖riemannZeta w‖ :=
    norm_mul (w - 1) (riemannZeta w)
  exact Eq.subst
    (motive := fun x : ℝ =>
      ‖(w - 1) * riemannZeta w‖ ≤ x)
    htarget_eq
    (Eq.subst
      (motive := fun x : ℝ => x ≤
        (1 + ‖w.im‖) * (A * Real.log (2 + ‖w.im‖)))
      hnorm_eq.symm
      hmul)

/-- Classical logarithmic vertical growth of zeta on the boundary line `re = 1`, proved
by Euler-Maclaurin/Abel truncation.

This is the exact analytic number-theory input: truncate the Dirichlet series at
height comparable to `|t|`, control the tail by Abel summation or Euler-Maclaurin,
and obtain the standard `O(log (2 + |t|))` boundary-line bound. -/
theorem classicalZeta_boundaryLine_one_vertical_log_growth_bound_from_EulerMaclaurin_truncation :
    ∃ A : ℝ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖riemannZeta w‖ ≤ A * Real.log (2 + ‖w.im‖) := by
  sorry

/-- Classical logarithmic vertical growth of zeta on the boundary line `re = 1`, in the
standard partial-summation/truncation form. -/
theorem classicalZeta_boundaryLine_one_vertical_log_growth_bound_from_truncation :
    ∃ A : ℝ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖riemannZeta w‖ ≤ A * Real.log (2 + ‖w.im‖) := by
  exact
    classicalZeta_boundaryLine_one_vertical_log_growth_bound_from_EulerMaclaurin_truncation

/-- Classical log-linear vertical growth of the pole-cleared zeta factor on the boundary
line `re = 1`, obtained from the raw boundary-line zeta estimate and the elementary
pole-clearing factor. -/
theorem classicalZeta_poleCleared_boundaryLine_one_vertical_log_linear_growth_bound_from_truncation :
    ∃ A : ℝ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
  exact boundaryLine_one_zeta_log_growth_bound_to_poleCleared_log_linear_growth_bound
    classicalZeta_boundaryLine_one_vertical_log_growth_bound_from_truncation

/-- The logarithmic boundary-line zeta estimate gives the log-linear estimate for the
pole-cleared product `(s - 1)ζ(s)`. -/
theorem classicalZeta_poleCleared_boundaryLine_one_vertical_log_linear_growth_bound_of_zeta_log
    (hzeta :
      ∃ A : ℝ,
        0 < A ∧
        ∀ w : ℂ,
          w.re = 1 →
          1 ≤ ‖w.im‖ →
          ‖riemannZeta w‖ ≤ A * Real.log (2 + ‖w.im‖)) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
  exact boundaryLine_one_zeta_log_growth_bound_to_poleCleared_log_linear_growth_bound hzeta

/-- Classical log-linear vertical growth of the pole-cleared zeta factor on the boundary
line `re = 1`.  This is the standard boundary-line zeta estimate in the form needed before
coarsening to a finite polynomial envelope. -/
theorem classicalZeta_poleCleared_boundaryLine_one_vertical_log_linear_growth_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖) := by
  exact classicalZeta_poleCleared_boundaryLine_one_vertical_log_linear_growth_bound_from_truncation

/-- A log-linear vertical-height boundary estimate gives the coarser polynomial envelope
used by the normalization chain. -/
theorem boundaryLine_one_log_linear_growth_bound_to_polynomial_growth_bound
    {f : ℂ → ℂ}
    (hlog :
      ∃ A : ℝ,
        0 < A ∧
        ∀ w : ℂ,
          w.re = 1 →
          1 ≤ ‖w.im‖ →
          ‖f w‖ ≤ A * (1 + ‖w.im‖) * Real.log (2 + ‖w.im‖)) :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖f w‖ ≤ A * (1 + ‖w.im‖) ^ m := by
  rcases hlog with ⟨A, hA_pos, hbound⟩
  refine ⟨2 * A, 2, ?_, ?_⟩
  · exact mul_pos two_pos hA_pos
  intro w hw_re hw_im
  let H : ℝ := 1 + ‖w.im‖
  have hH_nonneg : 0 ≤ H :=
    le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg w.im))
  have hH_ge_one : (1 : ℝ) ≤ H :=
    le_add_of_nonneg_right (norm_nonneg w.im)
  have hlog_arg_pos : 0 < 2 + ‖w.im‖ := by
    exact add_pos_of_pos_of_nonneg (by norm_num : (0 : ℝ) < 2) (norm_nonneg w.im)
  have hlog_le_arg :
      Real.log (2 + ‖w.im‖) ≤ 2 + ‖w.im‖ :=
    Real.log_le_self hlog_arg_pos.le
  have harg_eq : 2 + ‖w.im‖ = H + 1 := by
    change 2 + ‖w.im‖ = (1 + ‖w.im‖) + 1
    ring
  have harg_le_twoH : 2 + ‖w.im‖ ≤ 2 * H := by
    rw [harg_eq]
    nlinarith
  have hlog_le_twoH :
      Real.log (2 + ‖w.im‖) ≤ 2 * H :=
    le_trans hlog_le_arg harg_le_twoH
  have hleft_nonneg : 0 ≤ A * H :=
    mul_nonneg (le_of_lt hA_pos) hH_nonneg
  have hmul_log_le :
      A * H * Real.log (2 + ‖w.im‖) ≤ A * H * (2 * H) :=
    mul_le_mul_of_nonneg_left hlog_le_twoH hleft_nonneg
  have htarget_eq :
      A * H * (2 * H) = (2 * A) * H ^ (2 : ℕ) := by
    ring
  exact le_trans (hbound w hw_re hw_im)
    (Eq.subst
      (motive := fun x : ℝ =>
        A * H * Real.log (2 + ‖w.im‖) ≤ x)
      htarget_eq
      hmul_log_le)

/-- Standard polynomial vertical growth of the pole-cleared zeta factor on the boundary
line `re = 1`.

This is the classical boundary-line estimate for the removable meromorphic factor
`(s - 1)ζ(s)`, stated before conversion to the coarser finite-order envelope. -/
theorem riemannZeta_poleCleared_boundaryLine_one_vertical_polynomial_growth_bound_standard :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * (1 + ‖w.im‖) ^ m := by
  exact boundaryLine_one_log_linear_growth_bound_to_polynomial_growth_bound
    classicalZeta_poleCleared_boundaryLine_one_vertical_log_linear_growth_bound

/-- Standard finite-order vertical growth of the pole-cleared zeta factor on the boundary
line `re = 1`, converted from the polynomial boundary-line estimate.

This is the zeta-side finite-order theorem that must come from boundary-line estimates
for the pole-cleared meromorphic zeta function, not from the false far-right `re = 2`
Dirichlet-series route. -/
theorem riemannZeta_poleCleared_boundaryLine_one_vertical_growth_bound_standard :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w.im‖) ^ m) := by
  exact boundaryLine_one_polynomial_growth_bound_to_exponential_growth_bound
    riemannZeta_poleCleared_boundaryLine_one_vertical_polynomial_growth_bound_standard

/-- The standard vertical-height finite-order estimate for `(s - 1)ζ(s)` on `re = 1`
implies the complex-height envelope consumed by the strip-normalization chain. -/
theorem riemannZeta_poleCleared_boundaryLine_one_growth_bound_of_vertical_growth
    (hvertical :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ w : ℂ,
          w.re = 1 →
          1 ≤ ‖w.im‖ →
          ‖(w - 1) * riemannZeta w‖ ≤
            A * Real.exp (B * (1 + ‖w.im‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  rcases hvertical with ⟨A, B, m, hA, hB, hbound⟩
  refine ⟨A, B, m, hA, hB, ?_⟩
  intro w hw_re hw_im
  exact le_trans (hbound w hw_re hw_im)
    (finiteOrder_vertical_envelope_le_complex_envelope
      (le_of_lt hA)
      (le_of_lt hB))

/-- Standard finite-order vertical growth of the pole-cleared zeta factor on the boundary
line `re = 1`, in the complex-height envelope used downstream. -/
theorem riemannZeta_poleCleared_boundaryLine_one_growth_bound_standard :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  exact riemannZeta_poleCleared_boundaryLine_one_growth_bound_of_vertical_growth
    riemannZeta_poleCleared_boundaryLine_one_vertical_growth_bound_standard

/-- The removable pole-cleared boundary-line estimate implies the raw
`(s - 1)ζ(s)` boundary-line estimate on the vertical tail.

The vertical-tail hypothesis excludes the removable point `1`, so the raw product and
`poleClearedRiemannZeta` agree there. -/
theorem riemannZeta_boundaryLine_one_raw_growth_bound_of_poleCleared_growth_bound
    (hpole :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ w : ℂ,
          w.re = 1 →
          1 ≤ ‖w.im‖ →
          ‖poleClearedRiemannZeta w‖ ≤
            A * Real.exp (B * (1 + ‖w‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  rcases hpole with ⟨A, B, m, hA, hB, hpole_bound⟩
  refine ⟨A, B, m, hA, hB, ?_⟩
  intro w hw_re hw_im
  have hw_ne_one : w ≠ 1 := by
    intro hw
    have him_zero : w.im = 0 := by
      calc
        w.im = (1 : ℂ).im := by
          exact congrArg Complex.im hw
        _ = 0 := by
          exact Complex.one_im
    have him_norm_zero : ‖w.im‖ = 0 := by
      calc
        ‖w.im‖ = ‖(0 : ℝ)‖ := by
          exact congrArg norm him_zero
        _ = 0 := by
          exact norm_zero
    have hone_le_zero : (1 : ℝ) ≤ 0 :=
      Eq.subst
        (motive := fun x : ℝ => (1 : ℝ) ≤ x)
        him_norm_zero
        hw_im
    exact not_lt_of_ge hone_le_zero zero_lt_one
  have hpole_eq :
      poleClearedRiemannZeta w = (w - 1) * riemannZeta w :=
    poleClearedRiemannZeta_eq_of_ne_one hw_ne_one
  exact Eq.subst
    (motive := fun x : ℂ =>
      ‖x‖ ≤ A * Real.exp (B * (1 + ‖w‖) ^ m))
    hpole_eq
    (hpole_bound w hw_re hw_im)

/-- Pole-cleared zeta has finite-order vertical growth on the boundary line `re = 1`.

This is the smallest zeta-side analytic primitive needed on the reflected left boundary:
reflection sends `re z = 0` to `re (1 - z) = 1`, not to the `re = 2`
Dirichlet-series boundary. -/
theorem riemannZeta_poleCleared_boundaryLine_one_growth_bound_ownerPrimitive :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        w.re = 1 →
        1 ≤ ‖w.im‖ →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  exact riemannZeta_poleCleared_boundaryLine_one_growth_bound_standard

/-- The reflected `re = 1` pole-cleared zeta factor has finite-order vertical growth.

This is the exact analytic input left after unfolding the completed functional equation in
the raw zeta variable.  The map `z ↦ 1-z` sends `re z = 0` to `re = 1`, so this is not a
consequence of the already-proved far-right Dirichlet-series boundary theorem at `re = 2`.
-/
theorem riemannZeta_reflected_leftBoundary_poleCleared_growth_bound_ownerPrimitive :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖(((1 : ℂ) - z) - 1) * riemannZeta ((1 : ℂ) - z)‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases riemannZeta_poleCleared_boundaryLine_one_growth_bound_ownerPrimitive with
    ⟨A, B, m, hA, hB, hbound⟩
  refine ⟨A, B, 2 * m, hA, hB, ?_⟩
  intro z hz_re hz_im
  let w : ℂ := (1 : ℂ) - z
  have hw_re : w.re = 1 :=
    one_sub_leftBoundary_re_eq_one hz_re
  have hw_im_norm : ‖w.im‖ = ‖z.im‖ := by
    have him_eq : w.im = -z.im := by
      calc
        w.im = (1 : ℂ).im - z.im := by
          exact Complex.sub_im (1 : ℂ) z
        _ = 0 - z.im := by
          exact congrArg (fun x : ℝ => x - z.im) Complex.one_im
        _ = -z.im := by
          exact zero_sub z.im
    calc
      ‖w.im‖ = ‖-z.im‖ := by exact congrArg norm him_eq
      _ = ‖z.im‖ := norm_neg z.im
  have hw_im : 1 ≤ ‖w.im‖ :=
    Eq.subst (motive := fun x : ℝ => 1 ≤ x) hw_im_norm.symm hz_im
  have hw_norm_le : ‖w‖ ≤ 1 + ‖z‖ := by
    calc
      ‖w‖ = ‖(1 : ℂ) - z‖ := rfl
      _ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le (1 : ℂ) z
      _ = 1 + ‖z‖ := by
        exact congrArg (fun x : ℝ => x + ‖z‖) (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
  have hbase_le : 1 + ‖w‖ ≤ (1 + ‖z‖) ^ (2 : ℕ) := by
    let H : ℝ := 1 + ‖z‖
    have hH_ge_one : (1 : ℝ) ≤ H :=
      le_add_of_nonneg_right (norm_nonneg z)
    have hleft_le : 1 + ‖w‖ ≤ 1 + (1 + ‖z‖) :=
      add_le_add_left hw_norm_le 1
    have htwoH_le_Hsq : 1 + (1 + ‖z‖) ≤ H ^ (2 : ℕ) := by
      calc
        1 + (1 + ‖z‖) = 1 + H := rfl
        _ ≤ H * H := by
          nlinarith [hH_ge_one]
        _ = H ^ (2 : ℕ) := by ring
    exact le_trans hleft_le htwoH_le_Hsq
  have hpow_le : (1 + ‖w‖) ^ m ≤ (1 + ‖z‖) ^ (2 * m) := by
    have hleft_nonneg : 0 ≤ 1 + ‖w‖ :=
      le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg w))
    have hpow_base :
        (1 + ‖w‖) ^ m ≤ ((1 + ‖z‖) ^ (2 : ℕ)) ^ m :=
      pow_le_pow_right₀ hleft_nonneg hbase_le m
    have htarget_ge :
        ((1 + ‖z‖) ^ (2 : ℕ)) ^ m = (1 + ‖z‖) ^ (2 * m) := by
      exact pow_mul (1 + ‖z‖) 2 m
    exact hpow_base.trans_eq htarget_ge
  have hexp_le :
      Real.exp (B * (1 + ‖w‖) ^ m) ≤
        Real.exp (B * (1 + ‖z‖) ^ (2 * m)) := by
    exact Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left hpow_le (le_of_lt hB))
  exact le_trans (hbound w hw_re hw_im)
    (mul_le_mul_of_nonneg_left hexp_le (le_of_lt hA))

/-- Functional-equation algebra for the left-edge pole-cleared zeta factor. -/
theorem riemannZeta_leftBoundary_completedFunctionalEquation_factorization
    {z : ℂ}
    (hz_re : z.re = 0)
    (hz_im : 1 ≤ ‖z.im‖) :
    (z - 1) * riemannZeta z =
      (((z - 1) / (((1 : ℂ) - z) - 1)) *
          (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
        ((((1 : ℂ) - z) - 1) * riemannZeta ((1 : ℂ) - z)) := by
  rcases Gammaℝ_leftBoundary_nonzero_of_verticalTail hz_re hz_im with
    ⟨hz_ne_zero, hone_sub_ne_zero, hGamma_ne, hGamma_reflected_ne⟩
  have hw_ne_zero : ((1 : ℂ) - z) ≠ 0 := hone_sub_ne_zero
  have hw_minus_one_ne_zero : ((1 : ℂ) - z) - 1 ≠ 0 := by
    intro h
    have hz_zero : z = 0 := by
      calc
        z = -(((1 : ℂ) - z) - 1) := by ring
        _ = -0 := by exact congrArg Neg.neg h
        _ = 0 := by exact neg_zero
    exact hz_ne_zero hz_zero
  have hGamma_factor :
      completedRiemannZeta z = riemannZeta z * Complex.Gammaℝ z := by
    have hζ := riemannZeta_def_of_ne_zero (s := z) hz_ne_zero
    have hmul := congrArg (fun x : ℂ => x * Complex.Gammaℝ z) hζ
    have hcancel :
        (completedRiemannZeta z / Complex.Gammaℝ z) * Complex.Gammaℝ z =
          completedRiemannZeta z := by
      exact div_mul_cancel₀ _ hGamma_ne
    exact (hmul.trans hcancel).symm
  have hcompleted_symm :
      completedRiemannZeta z = completedRiemannZeta ((1 : ℂ) - z) := by
    exact (completedRiemannZeta_one_sub z).symm
  have hzeta_z :
      riemannZeta z =
        riemannZeta ((1 : ℂ) - z) *
          Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z := by
    have hζw := riemannZeta_def_of_ne_zero (s := ((1 : ℂ) - z)) hw_ne_zero
    calc
      riemannZeta z =
          completedRiemannZeta z / Complex.Gammaℝ z := by
        exact riemannZeta_def_of_ne_zero hz_ne_zero
      _ = completedRiemannZeta ((1 : ℂ) - z) / Complex.Gammaℝ z := by
        exact congrArg (fun x : ℂ => x / Complex.Gammaℝ z) hcompleted_symm
      _ = (riemannZeta ((1 : ℂ) - z) * Complex.Gammaℝ ((1 : ℂ) - z)) /
          Complex.Gammaℝ z := by
        have hζw_mul := congrArg
          (fun x : ℂ => x * Complex.Gammaℝ ((1 : ℂ) - z)) hζw
        have hζw_completed :
            riemannZeta ((1 : ℂ) - z) * Complex.Gammaℝ ((1 : ℂ) - z) =
              completedRiemannZeta ((1 : ℂ) - z) := by
          exact hζw_mul.trans (div_mul_cancel₀ _ hGamma_reflected_ne)
        exact congrArg (fun x : ℂ => x / Complex.Gammaℝ z) hζw_completed.symm
      _ = riemannZeta ((1 : ℂ) - z) *
          Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z := by
        rfl
  calc
    (z - 1) * riemannZeta z =
        (z - 1) *
          (riemannZeta ((1 : ℂ) - z) *
            Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z) := by
      exact congrArg (fun x : ℂ => (z - 1) * x) hzeta_z
    _ = (((z - 1) / (((1 : ℂ) - z) - 1)) *
          (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
        ((((1 : ℂ) - z) - 1) * riemannZeta ((1 : ℂ) - z)) := by
      field_simp [hw_minus_one_ne_zero, hGamma_ne]
      ring

/-- Left-edge transport for the pole-cleared zeta factor through the completed functional
equation before the removable-pole normalization is applied.

This is the remaining analytic component: reflect by
`completedRiemannZeta_one_sub`, use the peeled vertical-growth input on the reflected
line `re (1 - z) = 1`, and control the resulting Gamma/reflection multiplier by the
left-boundary Stirling-ratio estimate. -/
theorem riemannZeta_leftBoundary_completedFunctionalEquation_stirling_transport_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖(z - 1) * riemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases leftBoundary_finiteOrder_product_growth_bound
      Gammaℝ_leftBoundary_completedFunctionalEquation_multiplier_stirling_growth_bound
      riemannZeta_reflected_leftBoundary_poleCleared_growth_bound_ownerPrimitive with
    ⟨A, B, m, hA, hB, hproduct⟩
  refine ⟨A, B, m, hA, hB, ?_⟩
  intro z hz_re hz_im
  have hfactor :
      (z - 1) * riemannZeta z =
        (((z - 1) / (((1 : ℂ) - z) - 1)) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)) *
          ((((1 : ℂ) - z) - 1) * riemannZeta ((1 : ℂ) - z)) :=
    riemannZeta_leftBoundary_completedFunctionalEquation_factorization hz_re hz_im
  have hnorm_factor :
      ‖(z - 1) * riemannZeta z‖ =
        ‖((z - 1) / (((1 : ℂ) - z) - 1)) *
            (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)‖ *
          ‖(((1 : ℂ) - z) - 1) * riemannZeta ((1 : ℂ) - z)‖ := by
    have hnorm_raw := congrArg norm hfactor
    simpa [norm_mul] using hnorm_raw
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    hnorm_factor.symm
    (hproduct z hz_re hz_im)

/-- Left-edge transport for the pole-cleared zeta factor through the completed functional
equation and the available vertical-tail Gamma/Stirling control. -/
theorem poleClearedRiemannZeta_leftBoundary_completedFunctionalEquation_stirling_transport_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases riemannZeta_leftBoundary_completedFunctionalEquation_stirling_transport_growth_bound with
    ⟨A, B, m, hA, hB, hbound⟩
  refine ⟨A, B, m, hA, hB, ?_⟩
  intro z hz_re hz_im
  have hz_ne_one : z ≠ 1 := by
    intro hz_eq
    have hz_re_one : z.re = 1 := by
      calc
        z.re = (1 : ℂ).re := by
          exact congrArg Complex.re hz_eq
        _ = 1 := by
          norm_num
    have hzero_eq_one : (0 : ℝ) = 1 := by
      calc
        (0 : ℝ) = z.re := hz_re.symm
        _ = 1 := hz_re_one
    norm_num at hzero_eq_one
  have hpole :
      poleClearedRiemannZeta z = (z - 1) * riemannZeta z :=
    poleClearedRiemannZeta_eq_of_ne_one hz_ne_one
  exact Eq.subst
    (motive := fun w : ℂ =>
      ‖w‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    hpole.symm
    (hbound z hz_re hz_im)

/-- Exact two-edge boundary-growth input for the pole-cleared zeta strip theorem.

This is the boundary-growth layer separated from the vertical-strip Phragmen-Lindelöf
application: the left edge is the functional-equation/Gamma side, and the right edge is
the Dirichlet-series side. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_leftBoundary_functionalEquation_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact poleClearedRiemannZeta_leftBoundary_completedFunctionalEquation_stirling_transport_growth_bound

/-- On `2 ≤ re z`, subtracting the leading Dirichlet coefficient identifies `ζ z - 1`
with the honest Dirichlet tail starting at `n = 2`. -/
theorem riemannZeta_sub_one_eq_dirichletSeries_tail
    {z : ℂ}
    (hz : 2 ≤ z.re) :
    riemannZeta z - 1 =
      ∑' n : ℕ, 1 / (((n + 2 : ℕ) : ℂ) ^ z) := by
  have h_one_lt_re : 1 < z.re :=
    lt_of_lt_of_le one_lt_two hz
  let f : ℕ → ℂ := fun n : ℕ => 1 / ((n : ℂ) ^ z)
  have hsum : Summable f :=
    (Complex.summable_one_div_nat_cpow (p := z)).mpr h_one_lt_re
  have hzeta :
      riemannZeta z = ∑' n : ℕ, f n :=
    zeta_eq_tsum_one_div_nat_cpow h_one_lt_re
  have hsplit :
      (∑ n ∈ Finset.range 2, f n) + (∑' n : ℕ, f (n + 2)) =
        ∑' n : ℕ, f n :=
    sum_add_tsum_nat_add 2 hsum
  have hprefix :
      ∑ n ∈ Finset.range 2, f n = 1 := by
    dsimp [f]
    simp [zero_cpow (Complex.ne_zero_of_one_lt_re h_one_lt_re)]
  have hone_add_tail_eq_zeta :
      1 + (∑' n : ℕ, f (n + 2)) = riemannZeta z := by
    calc
      1 + (∑' n : ℕ, f (n + 2)) =
          (∑ n ∈ Finset.range 2, f n) + (∑' n : ℕ, f (n + 2)) := by
            exact congrArg (fun x : ℂ => x + (∑' n : ℕ, f (n + 2))) hprefix.symm
      _ = ∑' n : ℕ, f n := hsplit
      _ = riemannZeta z := hzeta.symm
  have hzeta_eq_one_add_tail :
      riemannZeta z = 1 + (∑' n : ℕ, f (n + 2)) :=
    hone_add_tail_eq_zeta.symm
  calc
    riemannZeta z - 1 =
        (1 + (∑' n : ℕ, f (n + 2))) - 1 := by
          exact congrArg (fun w : ℂ => w - 1) hzeta_eq_one_add_tail
    _ = ∑' n : ℕ, f (n + 2) := by
          ring
    _ = ∑' n : ℕ, 1 / (((n + 2 : ℕ) : ℂ) ^ z) := by
          rfl

/-- Uniform boundedness of the far-right Dirichlet-series tail.

This far-right standard analytic primitive is the zeta-side input for finite-order control
of the completed zero packet; analytically it is the comparison of
`∑_{n≥2} n^{-z}` with the convergent real p-series at exponent `2`. -/
theorem riemannZeta_farRightHalfPlane_dirichletSeries_tsum_tail_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ z : ℂ,
        2 ≤ z.re →
        ‖(∑' n : ℕ, 1 / (((n + 2 : ℕ) : ℂ) ^ z))‖ ≤ A := by
  let g : ℕ → ℝ := fun n : ℕ => 1 / (((n + 2 : ℕ) : ℝ) ^ (2 : ℕ))
  have hg_summable : Summable g := by
    have hfull : Summable (fun n : ℕ => 1 / ((n : ℝ) ^ (2 : ℕ))) :=
      Real.summable_one_div_nat_pow.mpr one_lt_two
    exact (summable_nat_add_iff 2).mpr hfull
  refine ⟨(∑' n : ℕ, g n) + 1, ?_, ?_⟩
  · have hg_nonneg : ∀ n : ℕ, 0 ≤ g n := by
      intro n
      exact div_nonneg zero_le_one (pow_nonneg (Nat.cast_nonneg (n + 2)) 2)
    exact add_pos_of_nonneg_of_pos (tsum_nonneg hg_nonneg) zero_lt_one
  intro z hz
  let f : ℕ → ℂ := fun n : ℕ => 1 / (((n + 2 : ℕ) : ℂ) ^ z)
  have hz_one_lt : 1 < z.re :=
    lt_of_lt_of_le one_lt_two hz
  have hf_summable : Summable (fun n : ℕ => ‖f n‖) := by
    have hfull : Summable (fun n : ℕ => 1 / ((n : ℂ) ^ z)) :=
      (Complex.summable_one_div_nat_cpow (p := z)).mpr hz_one_lt
    have htail : Summable (fun n : ℕ => 1 / (((n + 2 : ℕ) : ℂ) ^ z)) :=
      (summable_nat_add_iff 2).mpr hfull
    exact htail.norm
  have hterm_le : ∀ n : ℕ, ‖f n‖ ≤ g n := by
    intro n
    have hn_nat_pos : 0 < n + 2 :=
      Nat.succ_pos (n + 1)
    have hn_real_pos : 0 < ((n + 2 : ℕ) : ℝ) :=
      Nat.cast_pos.mpr hn_nat_pos
    have hn_real_one_le : 1 ≤ ((n + 2 : ℕ) : ℝ) := by
      exact_mod_cast Nat.succ_le_iff.mpr (Nat.succ_pos (n + 1))
    have hnorm_cpow :
        ‖(((n + 2 : ℕ) : ℂ) ^ z)‖ =
          ((n + 2 : ℕ) : ℝ) ^ z.re :=
      Complex.norm_natCast_cpow_of_pos hn_nat_pos z
    have hnorm_term :
        ‖f n‖ = 1 / (((n + 2 : ℕ) : ℝ) ^ z.re) := by
      calc
        ‖f n‖ = ‖(1 : ℂ)‖ / ‖(((n + 2 : ℕ) : ℂ) ^ z)‖ := by
          exact norm_div (1 : ℂ) ((((n + 2 : ℕ) : ℂ) ^ z))
        _ = 1 / ‖(((n + 2 : ℕ) : ℂ) ^ z)‖ := by
          exact congrArg
            (fun x : ℝ => x / ‖(((n + 2 : ℕ) : ℂ) ^ z)‖)
            (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
        _ = 1 / (((n + 2 : ℕ) : ℝ) ^ z.re) := by
          exact congrArg (fun x : ℝ => 1 / x) hnorm_cpow
    have hpow_mono :
        ((n + 2 : ℕ) : ℝ) ^ (2 : ℝ) ≤
          ((n + 2 : ℕ) : ℝ) ^ z.re :=
      Real.rpow_le_rpow_of_exponent_le hn_real_one_le hz
    have hpow_two_pos : 0 < ((n + 2 : ℕ) : ℝ) ^ (2 : ℝ) :=
      Real.rpow_pos_of_pos hn_real_pos 2
    have hdiv_le :
        1 / (((n + 2 : ℕ) : ℝ) ^ z.re) ≤
          1 / (((n + 2 : ℕ) : ℝ) ^ (2 : ℝ)) :=
      one_div_le_one_div_of_le hpow_two_pos hpow_mono
    have hg_eq :
        g n = 1 / (((n + 2 : ℕ) : ℝ) ^ (2 : ℝ)) := by
      calc
        g n = 1 / (((n + 2 : ℕ) : ℝ) ^ (2 : ℕ)) := rfl
        _ = 1 / (((n + 2 : ℕ) : ℝ) ^ (2 : ℝ)) := by
          exact congrArg
            (fun x : ℝ => 1 / x)
            (Real.rpow_natCast (((n + 2 : ℕ) : ℝ)) 2).symm
    exact Eq.subst
      (motive := fun x : ℝ => ‖f n‖ ≤ x)
      hg_eq.symm
      (Eq.subst
        (motive := fun x : ℝ => x ≤ 1 / (((n + 2 : ℕ) : ℝ) ^ (2 : ℝ)))
        hnorm_term.symm
        hdiv_le)
  have hnorm_tail :
      ‖∑' n : ℕ, f n‖ ≤ ∑' n : ℕ, ‖f n‖ :=
    norm_tsum_le_tsum_norm hf_summable
  have hnorms_le_g :
      (∑' n : ℕ, ‖f n‖) ≤ ∑' n : ℕ, g n :=
    tsum_le_tsum hterm_le hf_summable hg_summable
  have htail_le_g :
      ‖∑' n : ℕ, f n‖ ≤ ∑' n : ℕ, g n :=
    le_trans hnorm_tail hnorms_le_g
  exact le_trans htail_le_g (le_add_of_nonneg_right zero_le_one)

/-- The Dirichlet series tail for `ζ` is uniformly bounded on `2 ≤ re z`. -/
theorem riemannZeta_farRightHalfPlane_dirichletSeries_tail_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ z : ℂ,
        2 ≤ z.re →
        ‖riemannZeta z - 1‖ ≤ A := by
  rcases riemannZeta_farRightHalfPlane_dirichletSeries_tsum_tail_bound with
    ⟨A, hA, htail⟩
  refine ⟨A, hA, ?_⟩
  intro z hz
  have hidentity :
      riemannZeta z - 1 =
        ∑' n : ℕ, 1 / (((n + 2 : ℕ) : ℂ) ^ z) :=
    riemannZeta_sub_one_eq_dirichletSeries_tail hz
  exact Eq.subst
    (motive := fun w : ℂ => ‖w‖ ≤ A)
    hidentity.symm
    (htail z hz)

/-- Adding back the leading `1` preserves far-right boundedness of `ζ`. -/
theorem riemannZeta_farRightHalfPlane_dirichletSeries_bound_of_tail_bound
    (htail :
      ∃ A : ℝ,
        0 < A ∧
        ∀ z : ℂ,
          2 ≤ z.re →
          ‖riemannZeta z - 1‖ ≤ A) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ z : ℂ,
        2 ≤ z.re →
        ‖riemannZeta z‖ ≤ A := by
  rcases htail with ⟨A, hA, htail_bound⟩
  refine ⟨A + 1, add_pos hA zero_lt_one, ?_⟩
  intro z hz
  have hdecomp : riemannZeta z = (riemannZeta z - 1) + 1 := by
    exact (sub_add_cancel (riemannZeta z) 1).symm
  have htriangle :
      ‖riemannZeta z‖ ≤ ‖riemannZeta z - 1‖ + ‖(1 : ℂ)‖ := by
    exact Eq.subst
      (motive := fun w : ℂ => ‖w‖ ≤ ‖riemannZeta z - 1‖ + ‖(1 : ℂ)‖)
      hdecomp.symm
      (norm_add_le (riemannZeta z - 1) (1 : ℂ))
  have hone_norm : ‖(1 : ℂ)‖ = (1 : ℝ) := by
    norm_num
  have hsum :
      ‖riemannZeta z - 1‖ + ‖(1 : ℂ)‖ ≤ A + 1 := by
    exact Eq.subst
      (motive := fun x : ℝ => ‖riemannZeta z - 1‖ + x ≤ A + 1)
      hone_norm.symm
      (add_le_add_right (htail_bound z hz) 1)
  exact le_trans htriangle hsum

/-- The far-right half-plane Dirichlet-series bound for `ζ`. -/
theorem riemannZeta_farRightHalfPlane_dirichletSeries_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ z : ℂ,
        2 ≤ z.re →
        ‖riemannZeta z‖ ≤ A := by
  exact riemannZeta_farRightHalfPlane_dirichletSeries_bound_of_tail_bound
    riemannZeta_farRightHalfPlane_dirichletSeries_tail_bound

/-- On the right edge `re z = 2` of the critical strip, the pole-cleared zeta factor
has finite-order growth by the far-right Dirichlet-series bound. -/
theorem riemannZeta_rightCriticalStrip_poleCleared_rightBoundary_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 2 →
        1 ≤ ‖z.im‖ →
        ‖(z - 1) * riemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases riemannZeta_farRightHalfPlane_dirichletSeries_bound with
    ⟨A, hA, hzeta_bound⟩
  refine ⟨A, 1, 1, hA, zero_lt_one, ?_⟩
  intro z hz_re _hz_im
  let H : ℝ := 1 + ‖z‖
  have hH_ge_one : (1 : ℝ) ≤ H :=
    le_add_of_nonneg_right (norm_nonneg z)
  have hH_nonneg : 0 ≤ H :=
    le_trans zero_le_one hH_ge_one
  have hz_far : 2 ≤ z.re :=
    le_of_eq hz_re.symm
  have hzeta : ‖riemannZeta z‖ ≤ A :=
    hzeta_bound z hz_far
  have hsub_norm : ‖z - 1‖ ≤ H := by
    calc
      ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le z (1 : ℂ)
      _ = ‖z‖ + 1 := by
        exact congrArg (fun x : ℝ => ‖z‖ + x) (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
      _ = H := by
        exact (add_comm ‖z‖ 1)
  have hproduct :
      ‖(z - 1) * riemannZeta z‖ ≤ H * A := by
    calc
      ‖(z - 1) * riemannZeta z‖ =
          ‖z - 1‖ * ‖riemannZeta z‖ := by
        exact norm_mul (z - 1) (riemannZeta z)
      _ ≤ H * A :=
        mul_le_mul hsub_norm hzeta (norm_nonneg (riemannZeta z)) hH_nonneg
  have hH_le_expH : H ≤ Real.exp H := by
    exact le_trans (le_add_of_nonneg_right zero_le_one) (add_one_le_exp H)
  have hscaled :
      H * A ≤ A * Real.exp H := by
    calc
      H * A = A * H := by
        exact mul_comm H A
      _ ≤ A * Real.exp H :=
        mul_le_mul_of_nonneg_left hH_le_expH (le_of_lt hA)
  have hexponent :
      (1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ) = H := by
    calc
      (1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ) = (1 + ‖z‖) ^ (1 : ℕ) := by
        exact one_mul ((1 + ‖z‖) ^ (1 : ℕ))
      _ = 1 + ‖z‖ := by
        exact pow_one (1 + ‖z‖)
      _ = H := rfl
  exact le_trans hproduct
    (Eq.subst
      (motive := fun x : ℝ => H * A ≤ A * Real.exp x)
      hexponent.symm
      hscaled)

/-- The right-edge estimate transfers to the removable pole-cleared zeta normalization.

The vertical edge `re z = 2` is disjoint from the pole face, so this is only the
definition-level transport from `(s - 1) ζ(s)` to `poleClearedRiemannZeta`. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_rightBoundary_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases riemannZeta_rightCriticalStrip_poleCleared_rightBoundary_growth_bound with
    ⟨A, B, m, hA, hB, hbound⟩
  refine ⟨A, B, m, hA, hB, ?_⟩
  intro z hz_re hz_im
  have hz_ne_one : z ≠ 1 := by
    intro hz_eq
    have hone_re : z.re = 1 := by
      calc
        z.re = (1 : ℂ).re := by
          exact congrArg Complex.re hz_eq
        _ = 1 := by
          norm_num
    have htwo_eq_one : (2 : ℝ) = 1 := by
      calc
        (2 : ℝ) = z.re := hz_re.symm
        _ = 1 := hone_re
    norm_num at htwo_eq_one
  have hpc :
      poleClearedRiemannZeta z = (z - 1) * riemannZeta z :=
    poleClearedRiemannZeta_eq_of_ne_one hz_ne_one
  exact Eq.subst
    (motive := fun w : ℂ =>
      ‖w‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    hpc.symm
    (hbound z hz_re hz_im)

/-- Right-edge boundary growth for the pole-cleared zeta factor from the far-right
Dirichlet-series estimate. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_rightBoundary_dirichletSeries_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact poleClearedRiemannZeta_rightCriticalStrip_rightBoundary_growth_bound

/-- Exact two-edge boundary-growth input for the pole-cleared zeta strip theorem.

This public owner theorem is a thin wrapper over the two mathematically distinct vertical
edge inputs: the left edge comes from the functional equation and Gamma control, while the
right edge comes from the Dirichlet-series estimate. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_verticalBoundary_growth_bound :
    (∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 0 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m)) ∧
    (∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re = 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m)) := by
  exact
    ⟨poleClearedRiemannZeta_rightCriticalStrip_leftBoundary_functionalEquation_growth_bound,
      poleClearedRiemannZeta_rightCriticalStrip_rightBoundary_dirichletSeries_growth_bound⟩

/-- Vertical-tail strip estimate for the removable pole-cleared zeta factor.

This is the zeta-side consumer of the generic strip Phragmen-Lindelöf theorem before
transporting away from the pole face to `(s - 1) ζ(s)`. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_verticalTail_growth_bound_of_strip_inputs
    (hhol :
      DiffContOnCl ℂ poleClearedRiemannZeta
        (Complex.re ⁻¹' Set.Ioo 0 2))
    (hfinite :
      ∃ c : ℝ,
        c < Real.pi / (2 - 0) ∧
        ∃ D : ℝ,
          poleClearedRiemannZeta =O[
              Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
                𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)))
    (hleft :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 0 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hright :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re = 2 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact strip_growth_bound_of_holomorphic_boundary_growth_and_finite_order
    poleClearedRiemannZeta 0 2 zero_lt_two hhol hfinite hleft hright

/-- Vertical-tail strip estimate for the removable pole-cleared zeta factor.

This theorem is now reduced to the immediate strip inputs for the pole-cleared
normalization: strip holomorphy, admissible strip growth, and the two vertical-edge
finite-order estimates. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_verticalTail_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases poleClearedRiemannZeta_rightCriticalStrip_verticalBoundary_growth_bound with
    ⟨hleft, hright⟩
  exact strip_growth_bound_of_holomorphic_boundary_growth_and_finite_order
    poleClearedRiemannZeta 0 2 zero_lt_two hhol hfinite hleft hright

/-- Vertical-tail pole-cleared zeta strip estimate.

This is the final zeta-specific consumer of the generic strip Phragmen-Lindelöf
pillar `strip_growth_bound_of_holomorphic_boundary_growth_and_finite_order`.
The remaining zeta inputs are exactly the classical ones: holomorphicity after pole
clearing, right-boundary growth from the Dirichlet-series estimate, and left-boundary
growth from the functional equation/completed normalization with Gamma control. -/
theorem riemannZeta_rightCriticalStrip_poleCleared_verticalTail_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖(z - 1) * riemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases poleClearedRiemannZeta_rightCriticalStrip_verticalTail_growth_bound with
    ⟨A, B, m, hA, hB, hbound⟩
  refine ⟨A, B, m, hA, hB, ?_⟩
  intro z hz0 hz2 hzim
  have hz_ne_one : z ≠ 1 := by
    intro hz_eq
    have him_zero : z.im = 0 := by
      calc
        z.im = (1 : ℂ).im := by
          exact congrArg Complex.im hz_eq
        _ = 0 := by
          norm_num
    have hnorm_im_zero : ‖z.im‖ = 0 := by
      rw [him_zero]
      exact norm_zero
    have hle_zero : (1 : ℝ) ≤ 0 :=
      hzim.trans_eq hnorm_im_zero
    norm_num at hle_zero
  have hpc :
      poleClearedRiemannZeta z = (z - 1) * riemannZeta z :=
    poleClearedRiemannZeta_eq_of_ne_one hz_ne_one
  exact Eq.subst
    (motive := fun w : ℂ =>
      ‖w‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    hpc
    (hbound z hz0 hz2 hzim)

/-- Compact and vertical-tail estimates combine to the right-critical-strip pole-cleared
zeta bound. -/
theorem riemannZeta_rightCriticalStrip_poleCleared_boundedWidth_growth_bound_of_compact_and_tail
    (hcompact :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖z.im‖ ≤ 1 →
          ‖(z - 1) * riemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (htail :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          1 ≤ ‖z.im‖ →
          ‖(z - 1) * riemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖(z - 1) * riemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hcompact with ⟨Ac, Bc, mc, hAc, hBc, hc⟩
  rcases htail with ⟨At, Bt, mt, hAt, hBt, ht⟩
  refine ⟨Ac + At, Bc + Bt, mc + mt, add_pos hAc hAt, add_pos hBc hBt, ?_⟩
  intro z hz0 hz2
  have hAc_nonneg : 0 ≤ Ac := le_of_lt hAc
  have hAt_nonneg : 0 ≤ At := le_of_lt hAt
  have hBc_nonneg : 0 ≤ Bc := le_of_lt hBc
  have hBt_nonneg : 0 ≤ Bt := le_of_lt hBt
  match le_total ‖z.im‖ 1 with
  | Or.inl hcompact_im =>
      exact le_trans (hc z hz0 hz2 hcompact_im)
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
      exact le_trans (ht z hz0 hz2 htail_im)
        (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
          hAt_nonneg
          (le_add_of_nonneg_left hAc_nonneg)
          (le_add_of_nonneg_left hBc_nonneg)
          hBt_nonneg
          hdegree)

/-- Pole-cleared finite-order growth for `ζ` in the bounded-width right critical strip. -/
theorem riemannZeta_rightCriticalStrip_poleCleared_boundedWidth_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖(z - 1) * riemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact riemannZeta_rightCriticalStrip_poleCleared_boundedWidth_growth_bound_of_compact_and_tail
    riemannZeta_rightCriticalStrip_poleCleared_compact_growth_bound
    riemannZeta_rightCriticalStrip_poleCleared_verticalTail_growth_bound

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
  rcases completedRiemannZeta₀_rightCriticalStrip_compact_norm_bound with
    ⟨C, hC, hbound⟩
  refine ⟨C, 1, 0, hC, zero_lt_one, ?_⟩
  intro z hz0 hz2 hz_im
  have hz_mem : z ∈ completedRiemannZeta₀_rightCriticalStripCompactSet :=
    ⟨hz0, hz2, hz_im⟩
  have hraw : ‖completedRiemannZeta₀ z‖ ≤ C :=
    hbound z hz_mem
  have hfactor_ge_one : (1 : ℝ) ≤ Real.exp (1 * (1 + ‖z‖) ^ 0) := by
    have hone : (1 : ℝ) * (1 + ‖z‖) ^ 0 = 1 := by
      ring
    exact Eq.subst
      (motive := fun x : ℝ => (1 : ℝ) ≤ Real.exp x)
      hone.symm
      (Real.one_le_exp_iff.mpr zero_le_one)
  have hC_nonneg : 0 ≤ C :=
    le_of_lt hC
  have hC_le_scaled :
      C ≤ C * Real.exp (1 * (1 + ‖z‖) ^ 0) :=
    le_mul_of_one_le_right hC_nonneg hfactor_ge_one
  exact le_trans hraw hC_le_scaled

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
  refine ⟨3, zero_lt_three, ?_⟩
  intro z _hz0 _hz2 hz_im
  have hz_ne_zero : z ≠ 0 := by
    intro hz
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
    exact not_lt_of_ge hone_le_zero zero_lt_one
  have hone_sub_ne_zero : (1 : ℂ) - z ≠ 0 := by
    intro hsub
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
    exact not_lt_of_ge hone_le_zero zero_lt_one
  have hz_minus_one_ne_zero : z - 1 ≠ 0 := by
    intro hsub
    have hone_sub_zero : (1 : ℂ) - z = 0 := by
      calc
        (1 : ℂ) - z = -(z - 1) := by
          ring
        _ = -0 := by
          exact congrArg Neg.neg hsub
        _ = 0 := by
          exact neg_zero
    exact hone_sub_ne_zero hone_sub_zero
  have hGamma_ne : Complex.Gammaℝ z ≠ 0 := by
    intro hGamma
    have hzero_index : ∃ n : ℕ, z = -(2 * (n : ℂ)) :=
      Complex.Gammaℝ_eq_zero_iff.mp hGamma
    rcases hzero_index with ⟨n, hn⟩
    have him_zero : z.im = 0 := by
      calc
        z.im = (-(2 * (n : ℂ))).im := by
          exact congrArg Complex.im hn
        _ = 0 := by
          norm_num
    have him_norm_zero : ‖z.im‖ = 0 :=
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
        ring
      _ = completedRiemannZeta z + 1 / z + 1 / (1 - z) := by
        exact congrArg (fun w : ℂ => w + 1 / z + 1 / (1 - z)) hformula.symm
  have hz_norm_ge_one : (1 : ℝ) ≤ ‖z‖ := by
    exact le_trans hz_im (Complex.abs_im_le_abs z)
  have hone_sub_norm_ge_one : (1 : ℝ) ≤ ‖1 - z‖ := by
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
  have hz_minus_one_norm_ge_one : (1 : ℝ) ≤ ‖z - 1‖ := by
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
  have hinv_z_le_one : ‖1 / z‖ ≤ (1 : ℝ) := by
    have hz_norm_pos : 0 < ‖z‖ :=
      lt_of_lt_of_le zero_lt_one hz_norm_ge_one
    calc
      ‖1 / z‖ = ‖(1 : ℂ)‖ / ‖z‖ := by
        exact norm_div (1 : ℂ) z
      _ = 1 / ‖z‖ := by
        exact congrArg (fun x : ℝ => x / ‖z‖) (by norm_num : ‖(1 : ℂ)‖ = (1 : ℝ))
      _ ≤ 1 := by
        exact div_le_one_of_le₀ hz_norm_pos hz_norm_ge_one
  have hinv_one_sub_le_one : ‖1 / (1 - z)‖ ≤ (1 : ℝ) := by
    have hnorm_pos : 0 < ‖1 - z‖ :=
      lt_of_lt_of_le zero_lt_one hone_sub_norm_ge_one
    calc
      ‖1 / (1 - z)‖ = ‖(1 : ℂ)‖ / ‖1 - z‖ := by
        exact norm_div (1 : ℂ) (1 - z)
      _ = 1 / ‖1 - z‖ := by
        exact congrArg (fun x : ℝ => x / ‖1 - z‖) (by norm_num : ‖(1 : ℂ)‖ = (1 : ℝ))
      _ ≤ 1 := by
        exact div_le_one_of_le₀ hnorm_pos hone_sub_norm_ge_one
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
        exact add_assoc ‖completedRiemannZeta z‖ ‖1 / z‖ ‖1 / (1 - z)‖
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
        ring
  have hP_two_le_three :
      P + 2 ≤ 3 * (P + 1) := by
    nlinarith [hP_nonneg]
  exact le_trans hnorm_decomp (le_trans hsum_bound hP_two_le_three)

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
          0 ≤ z.re →
          z.re ≤ 2 →
          1 ≤ ‖z.im‖ →
          ‖Complex.Gammaℝ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖(z - 1) * riemannZeta z‖ * ‖Complex.Gammaℝ z‖ + 1 ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hzeta with ⟨Az, Bz, mz, hAz, hBz, hzeta_bound⟩
  rcases hGamma with ⟨Ag, Bg, mg, hAg, hBg, hGamma_bound⟩
  refine ⟨Az * Ag + 1, 2 * (Bz + Bg + 1), mz + mg,
    add_pos (mul_pos hAz hAg) zero_lt_one,
    mul_pos zero_lt_two (add_pos (add_pos hBz hBg) zero_lt_one), ?_⟩
  intro z hz0 hz2 hz_im
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
      le_trans (hzeta_bound z hz0 hz2 hz_im) hzeta_enlarge
    have hGamma_to_target :
        ‖Complex.Gammaℝ z‖ ≤
          Ag * Real.exp ((Bz + Bg + 1) * H ^ (mz + mg)) :=
      le_trans (hGamma_bound z hz0 hz2 hz_im) hGamma_enlarge
    have hmul :
        ‖(z - 1) * riemannZeta z‖ * ‖Complex.Gammaℝ z‖ ≤
          (Az * Real.exp ((Bz + Bg + 1) * H ^ (mz + mg))) *
            (Ag * Real.exp ((Bz + Bg + 1) * H ^ (mz + mg))) :=
      mul_le_mul hzeta_to_target hGamma_to_target (norm_nonneg _)
        (mul_nonneg (le_of_lt hAg)
          (le_of_lt (Real.exp_pos ((Bz + Bg + 1) * H ^ (mz + mg)))))
    have hcollapse :
        (Az * Real.exp ((Bz + Bg + 1) * H ^ (mz + mg))) *
            (Ag * Real.exp ((Bz + Bg + 1) * H ^ (mz + mg))) =
          (Az * Ag) * Real.exp (2 * (Bz + Bg + 1) * H ^ (mz + mg)) := by
      calc
        (Az * Real.exp ((Bz + Bg + 1) * H ^ (mz + mg))) *
            (Ag * Real.exp ((Bz + Bg + 1) * H ^ (mz + mg))) =
          (Az * Ag) *
            (Real.exp ((Bz + Bg + 1) * H ^ (mz + mg)) *
              Real.exp ((Bz + Bg + 1) * H ^ (mz + mg))) := by
          ring
        _ = (Az * Ag) *
            Real.exp (((Bz + Bg + 1) * H ^ (mz + mg)) +
              ((Bz + Bg + 1) * H ^ (mz + mg))) := by
          exact congrArg (fun x : ℝ => (Az * Ag) * x)
            (Real.exp_add ((Bz + Bg + 1) * H ^ (mz + mg))
              ((Bz + Bg + 1) * H ^ (mz + mg))).symm
        _ = (Az * Ag) * Real.exp (2 * (Bz + Bg + 1) * H ^ (mz + mg)) := by
          ring
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
      ring
    exact hleft.trans_eq hright
  exact hsum_bound

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
          0 ≤ z.re →
          z.re ≤ 2 →
          1 ≤ ‖z.im‖ →
          ‖Complex.Gammaℝ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases poleCleared_zeta_gamma_rightCriticalStrip_verticalTail_product_plus_one_growth_bound
      hzeta hGamma with
    ⟨Apg, Bpg, mpg, hApg, hBpg, hproduct_plus_one_bound⟩
  rcases completedRiemannZeta₀_rightCriticalStrip_verticalTail_norm_le_poleCleared_zeta_gamma_plus_one with
    ⟨D, hD, hnorm_bound⟩
  refine ⟨D * Apg, Bpg, mpg, mul_pos hD hApg, hBpg, ?_⟩
  intro z hz0 hz2 hz_im
  have hscaled :
      D * (‖(z - 1) * riemannZeta z‖ * ‖Complex.Gammaℝ z‖ + 1) ≤
        D * (Apg * Real.exp (Bpg * (1 + ‖z‖) ^ mpg)) :=
    mul_le_mul_of_nonneg_left (hproduct_plus_one_bound z hz0 hz2 hz_im) (le_of_lt hD)
  have htarget :
      D * (Apg * Real.exp (Bpg * (1 + ‖z‖) ^ mpg)) =
        D * Apg * Real.exp (Bpg * (1 + ‖z‖) ^ mpg) := by
    ring
  exact le_trans (hnorm_bound z hz0 hz2 hz_im) (hscaled.trans_eq htarget)

/-- Vertical-tail bound for the pole-cleared completed-zeta entire part in the
right-critical strip. -/
theorem completedRiemannZeta₀_rightCriticalStrip_verticalTail_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact completedRiemannZeta₀_rightCriticalStrip_verticalTail_growth_bound_of_zeta_and_gamma
    riemannZeta_rightCriticalStrip_poleCleared_verticalTail_growth_bound
    Gammaℝ_rightCriticalStrip_verticalTail_stirling_growth_bound

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
          0 ≤ z.re →
          z.re ≤ 2 →
          1 ≤ ‖z.im‖ →
          ‖completedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hcompact with ⟨Ac, Bc, mc, hAc, hBc, hc⟩
  rcases htail with ⟨At, Bt, mt, hAt, hBt, ht⟩
  refine ⟨Ac + At, Bc + Bt, mc + mt, add_pos hAc hAt, add_pos hBc hBt, ?_⟩
  intro z hz0 hz2
  have hAc_nonneg : 0 ≤ Ac := le_of_lt hAc
  have hAt_nonneg : 0 ≤ At := le_of_lt hAt
  have hBc_nonneg : 0 ≤ Bc := le_of_lt hBc
  have hBt_nonneg : 0 ≤ Bt := le_of_lt hBt
  match le_total ‖z.im‖ 1 with
  | Or.inl hcompact_im =>
      exact le_trans (hc z hz0 hz2 hcompact_im)
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
      exact le_trans (ht z hz0 hz2 htail_im)
        (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
          hAt_nonneg
          (le_add_of_nonneg_left hAc_nonneg)
          (le_add_of_nonneg_left hBc_nonneg)
          hBt_nonneg
          hdegree)

/-- Finite-order growth in the right critical strip for the uncentered entire completed-zeta
part. -/
theorem completedRiemannZeta₀_rightCriticalStrip_finiteOrder_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact completedRiemannZeta₀_rightCriticalStrip_finiteOrder_growth_bound_of_compact_and_tail
    completedRiemannZeta₀_rightCriticalStrip_compact_growth_bound
    completedRiemannZeta₀_rightCriticalStrip_verticalTail_growth_bound

/-- Far-right logarithmic Stirling bound for the archimedean factor.

This far-right standard analytic primitive is the Gamma-side input for finite-order control
of the completed zero packet. -/
theorem Gammaℝ_farRightHalfPlane_stirling_log_growth_bound :
    ∃ C : ℝ, ∃ m : ℕ,
      ∀ z : ℂ,
        2 ≤ z.re →
        Real.log ‖Complex.Gammaℝ z‖ ≤
          C * (1 + ‖z‖) ^ m := by
  rcases Gammaℝ_rightHalfPlane_stirling_log_growth_bound with
    ⟨C, m, hC⟩
  refine ⟨C, m, ?_⟩
  intro z hz
  exact hC z (le_trans zero_le_two hz) (one_le_norm_of_two_le_re hz)

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
theorem Gammaℝ_farRightHalfPlane_stirling_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        2 ≤ z.re →
        ‖Complex.Gammaℝ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact Gammaℝ_farRightHalfPlane_stirling_growth_bound_of_log_growth
    Gammaℝ_farRightHalfPlane_stirling_log_growth_bound

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
  refine ⟨3, zero_lt_three, ?_⟩
  intro z hz_re
  have hz_re_pos : 0 < z.re :=
    lt_of_lt_of_le zero_lt_two hz_re
  have hz_ne_zero : z ≠ 0 := by
    intro hz
    have hre_zero : z.re = 0 :=
      congrArg Complex.re hz
    have hzero_lt_zero : (0 : ℝ) < 0 :=
      Eq.subst
        (motive := fun x : ℝ => (0 : ℝ) < x)
        hre_zero
        hz_re_pos
    exact (not_lt_of_ge (le_refl (0 : ℝ))) hzero_lt_zero
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
        ring
      _ = completedRiemannZeta z + 1 / z + 1 / (1 - z) := by
        exact congrArg (fun w : ℂ => w + 1 / z + 1 / (1 - z)) hformula.symm
  have hz_norm_ge_one : (1 : ℝ) ≤ ‖z‖ := by
    have hre_abs_le_norm : |z.re| ≤ ‖z‖ :=
      Complex.abs_re_le_abs z
    have hone_le_re_abs : (1 : ℝ) ≤ |z.re| := by
      exact le_trans
        (by norm_num : (1 : ℝ) ≤ 2)
        (le_trans hz_re (le_abs_self z.re))
    exact le_trans hone_le_re_abs hre_abs_le_norm
  have hone_sub_norm_ge_one : (1 : ℝ) ≤ ‖1 - z‖ := by
    have hre_abs_le_norm : |(1 - z).re| ≤ ‖1 - z‖ :=
      Complex.abs_re_le_abs (1 - z)
    have hre_eq : (1 - z).re = 1 - z.re := by
      exact Complex.sub_re 1 z
    have hone_le_abs : (1 : ℝ) ≤ |(1 - z).re| := by
      have hle : (1 - z.re) ≤ -1 := by
        linarith
      have habs_eq : |1 - z.re| = -(1 - z.re) :=
        abs_of_nonpos hle
      have hone_le : (1 : ℝ) ≤ -(1 - z.re) := by
        linarith
      exact Eq.subst
        (motive := fun x : ℝ => (1 : ℝ) ≤ |x|)
        hre_eq.symm
        (Eq.subst
          (motive := fun x : ℝ => (1 : ℝ) ≤ x)
          habs_eq.symm
          hone_le)
    exact le_trans hone_le_abs hre_abs_le_norm
  have hinv_z_le_one : ‖1 / z‖ ≤ (1 : ℝ) := by
    have hz_norm_pos : 0 < ‖z‖ :=
      lt_of_lt_of_le zero_lt_one hz_norm_ge_one
    calc
      ‖1 / z‖ = ‖(1 : ℂ)‖ / ‖z‖ := by
        exact norm_div (1 : ℂ) z
      _ = 1 / ‖z‖ := by
        exact congrArg (fun x : ℝ => x / ‖z‖) (by norm_num : ‖(1 : ℂ)‖ = (1 : ℝ))
      _ ≤ 1 := by
        exact div_le_one_of_le₀ hz_norm_pos hz_norm_ge_one
  have hinv_one_sub_le_one : ‖1 / (1 - z)‖ ≤ (1 : ℝ) := by
    have hnorm_pos : 0 < ‖1 - z‖ :=
      lt_of_lt_of_le zero_lt_one hone_sub_norm_ge_one
    calc
      ‖1 / (1 - z)‖ = ‖(1 : ℂ)‖ / ‖1 - z‖ := by
        exact norm_div (1 : ℂ) (1 - z)
      _ = 1 / ‖1 - z‖ := by
        exact congrArg (fun x : ℝ => x / ‖1 - z‖) (by norm_num : ‖(1 : ℂ)‖ = (1 : ℝ))
      _ ≤ 1 := by
        exact div_le_one_of_le₀ hnorm_pos hone_sub_norm_ge_one
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
        exact add_assoc ‖completedRiemannZeta z‖ ‖1 / z‖ ‖1 / (1 - z)‖
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
        ring
  have hP_two_le_three :
      P + 2 ≤ 3 * (P + 1) := by
    nlinarith [hP_nonneg]
  exact le_trans hnorm_decomp (le_trans hsum_bound hP_two_le_three)

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
  rcases hzeta with ⟨Az, hAz, hzeta_bound⟩
  rcases hGamma with ⟨Ag, Bg, mg, hAg, hBg, hGamma_bound⟩
  rcases completedRiemannZeta₀_farRightHalfPlane_norm_le_zeta_gamma_plus_one with
    ⟨D, hD, hnorm_bound⟩
  refine ⟨D * (Az * Ag + 1), Bg, mg, ?_, hBg, ?_⟩
  · exact mul_pos hD (add_pos (mul_pos hAz hAg) zero_lt_one)
  intro z hz
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
  have hzeta_nonneg : 0 ≤ Az :=
    le_of_lt hAz
  have hgamma_target_nonneg : 0 ≤ Ag * Real.exp (Bg * H ^ mg) :=
    mul_nonneg (le_of_lt hAg) (le_of_lt (Real.exp_pos (Bg * H ^ mg)))
  have hproduct_bound :
      ‖riemannZeta z‖ * ‖Complex.Gammaℝ z‖ ≤
        Az * (Ag * Real.exp (Bg * H ^ mg)) :=
    mul_le_mul (hzeta_bound z hz) (hGamma_bound z hz) (norm_nonneg _) hgamma_target_nonneg
  have hproduct_reassoc :
      Az * (Ag * Real.exp (Bg * H ^ mg)) =
        (Az * Ag) * Real.exp (Bg * H ^ mg) := by
    exact (mul_assoc Az Ag (Real.exp (Bg * H ^ mg))).symm
  have hone_scaled :
      (1 : ℝ) ≤ Real.exp (Bg * H ^ mg) :=
    hone_le_exp
  have hsum_bound :
      ‖riemannZeta z‖ * ‖Complex.Gammaℝ z‖ + 1 ≤
        (Az * Ag + 1) * Real.exp (Bg * H ^ mg) := by
    have hleft :
        ‖riemannZeta z‖ * ‖Complex.Gammaℝ z‖ + 1 ≤
          (Az * Ag) * Real.exp (Bg * H ^ mg) +
            Real.exp (Bg * H ^ mg) := by
      exact add_le_add (hproduct_bound.trans_eq hproduct_reassoc) hone_scaled
    have hright :
        (Az * Ag) * Real.exp (Bg * H ^ mg) +
            Real.exp (Bg * H ^ mg) =
          (Az * Ag + 1) * Real.exp (Bg * H ^ mg) := by
      ring
    exact hleft.trans_eq hright
  have hscaled :
      D * (‖riemannZeta z‖ * ‖Complex.Gammaℝ z‖ + 1) ≤
        D * ((Az * Ag + 1) * Real.exp (Bg * H ^ mg)) :=
    mul_le_mul_of_nonneg_left hsum_bound (le_of_lt hD)
  have htarget :
      D * ((Az * Ag + 1) * Real.exp (Bg * H ^ mg)) =
        D * (Az * Ag + 1) * Real.exp (Bg * H ^ mg) := by
    exact mul_assoc D (Az * Ag + 1) (Real.exp (Bg * H ^ mg))
  exact le_trans (hnorm_bound z hz) (hscaled.trans_eq htarget)

/-- Finite-order growth in the far-right half-plane for the uncentered entire
completed-zeta part. -/
theorem completedRiemannZeta₀_farRightHalfPlane_finiteOrder_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        2 ≤ z.re →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact completedRiemannZeta₀_farRightHalfPlane_poleCleared_growth_bound
    riemannZeta_farRightHalfPlane_dirichletSeries_bound
    Gammaℝ_farRightHalfPlane_stirling_growth_bound

/-- A finite-order estimate can be enlarged in constants and exponent. -/
theorem exponentialFiniteOrder_bound_le_of_le_constants_and_exponent
    {A B A' B' : ℝ} {m d : ℕ} {z : ℂ}
    (hA : 0 ≤ A)
    (hAle : A ≤ A')
    (hBle : B ≤ B')
    (hBnonneg : 0 ≤ B)
    (hmd : m ≤ d) :
    A * Real.exp (B * (1 + ‖z‖) ^ m) ≤
      A' * Real.exp (B' * (1 + ‖z‖) ^ d) := by
  let H : ℝ := 1 + ‖z‖
  have hH_ge_one : (1 : ℝ) ≤ H :=
    le_add_of_nonneg_right (norm_nonneg z)
  have hH_nonneg : 0 ≤ H :=
    le_trans zero_le_one hH_ge_one
  have hpow_le : H ^ m ≤ H ^ d :=
    pow_le_pow_right₀ hH_ge_one hmd
  have hB_pow_le : B * H ^ m ≤ B * H ^ d :=
    mul_le_mul_of_nonneg_left hpow_le hBnonneg
  have hB_le_B'pow : B * H ^ d ≤ B' * H ^ d :=
    mul_le_mul_of_nonneg_right hBle (pow_nonneg hH_nonneg d)
  have hexponent_le : B * H ^ m ≤ B' * H ^ d :=
    le_trans hB_pow_le hB_le_B'pow
  have hexp_le :
      Real.exp (B * H ^ m) ≤ Real.exp (B' * H ^ d) :=
    Real.exp_le_exp.mpr hexponent_le
  have hexp_nonneg : 0 ≤ Real.exp (B * H ^ m) :=
    le_of_lt (Real.exp_pos (B * H ^ m))
  have hA'nonneg : 0 ≤ A' :=
    le_trans hA hAle
  exact mul_le_mul hAle hexp_le hexp_nonneg hA'nonneg

/-- Strip and far-right estimates combine to a right-half-plane finite-order estimate. -/
theorem completedRiemannZeta₀_rightHalfPlane_finiteOrder_growth_bound_of_strip_and_farRight
    (hstrip :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖completedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hfar :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          2 ≤ z.re →
          ‖completedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hstrip with ⟨As, Bs, ms, hAs, hBs, hstrip_bound⟩
  rcases hfar with ⟨Af, Bf, mf, hAf, hBf, hfar_bound⟩
  refine ⟨As + Af, Bs + Bf, ms + mf, add_pos hAs hAf, add_pos hBs hBf, ?_⟩
  intro z hz_re_nonneg
  have hAs_nonneg : 0 ≤ As := le_of_lt hAs
  have hAf_nonneg : 0 ≤ Af := le_of_lt hAf
  have hBs_nonneg : 0 ≤ Bs := le_of_lt hBs
  have hBf_nonneg : 0 ≤ Bf := le_of_lt hBf
  have hA_strip_le : As ≤ As + Af :=
    le_add_of_nonneg_right hAf_nonneg
  have hA_far_le : Af ≤ As + Af :=
    le_add_of_nonneg_left hAs_nonneg
  have hB_strip_le : Bs ≤ Bs + Bf :=
    le_add_of_nonneg_right hBf_nonneg
  have hB_far_le : Bf ≤ Bs + Bf :=
    le_add_of_nonneg_left hBs_nonneg
  match le_total z.re 2 with
  | Or.inl hz_re_le_two =>
      exact le_trans (hstrip_bound z hz_re_nonneg hz_re_le_two)
        (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent
          hAs_nonneg
          hA_strip_le
          hB_strip_le
          hBs_nonneg
          (Nat.le_add_right ms mf))
  | Or.inr htwo_le_re =>
      have hdegree : mf ≤ ms + mf := by
        exact Eq.subst
          (motive := fun d : ℕ => mf ≤ d)
          (Nat.add_comm mf ms)
          (Nat.le_add_right mf ms)
      exact le_trans (hfar_bound z htwo_le_re)
        (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent
          hAf_nonneg
          hA_far_le
          hB_far_le
          hBf_nonneg
          hdegree)

/-- Right half-plane finite-order growth for the uncentered entire completed-zeta part. -/
theorem completedRiemannZeta₀_rightHalfPlane_finiteOrder_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact completedRiemannZeta₀_rightHalfPlane_finiteOrder_growth_bound_of_strip_and_farRight
    completedRiemannZeta₀_rightCriticalStrip_finiteOrder_growth_bound
    completedRiemannZeta₀_farRightHalfPlane_finiteOrder_growth_bound

/-- The reflected point `1 - z` lies in the right half-plane when `z` lies in the left
half-plane. -/
theorem completedRiemannZeta₀_reflected_re_nonnegative_of_leftHalfPlane
    {z : ℂ}
    (hz : z.re ≤ 0) :
    0 ≤ (1 - z).re := by
  have hone_re : (1 : ℂ).re = (1 : ℝ) := by
    norm_num
  calc
    0 ≤ 1 - z.re := by
      exact sub_nonneg.mpr (le_trans hz zero_le_one)
    _ = (1 : ℂ).re - z.re := by
      exact congrArg (fun x : ℝ => x - z.re) hone_re.symm
    _ = (1 - z).re := by
      exact (Complex.sub_re 1 z).symm

/-- The reflected affine height is controlled by twice the original affine height. -/
theorem completedRiemannZeta₀_reflected_basicHeight_le
    (z : ℂ) :
    1 + ‖1 - z‖ ≤ 2 * (1 + ‖z‖) := by
  have htriangle : ‖(1 : ℂ) - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ :=
    norm_sub_le (1 : ℂ) z
  have hone_norm : ‖(1 : ℂ)‖ = (1 : ℝ) := by
    norm_num
  have hbound : ‖(1 : ℂ) - z‖ ≤ 1 + ‖z‖ := by
    exact Eq.subst
      (motive := fun x : ℝ => ‖(1 : ℂ) - z‖ ≤ x + ‖z‖)
      hone_norm
      htriangle
  have hnorm_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
  calc
    1 + ‖1 - z‖ ≤ 1 + (1 + ‖z‖) := by
      exact add_le_add_left hbound 1
    _ = 2 + ‖z‖ := by
      ring
    _ ≤ 2 + 2 * ‖z‖ := by
      have hsingle_le_double : ‖z‖ ≤ 2 * ‖z‖ := by
        nlinarith [hnorm_nonneg]
      exact add_le_add_left hsingle_le_double 2
    _ = 2 * (1 + ‖z‖) := by
      ring

/-- Right half-plane finite-order growth transports to the left half-plane by the
functional equation for the pole-cleared entire completed-zeta part. -/
theorem completedRiemannZeta₀_leftHalfPlane_finiteOrder_growth_bound_of_rightHalfPlane
    (hright :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          ‖completedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hright with ⟨A, B, m, hApos, hBpos, hbound⟩
  refine ⟨A, B * (2 : ℝ) ^ m, m, hApos, ?_, ?_⟩
  · exact mul_pos hBpos (pow_pos zero_lt_two m)
  intro z hz_left
  let w : ℂ := 1 - z
  let H : ℝ := 1 + ‖z‖
  have hw_right : 0 ≤ w.re :=
    completedRiemannZeta₀_reflected_re_nonnegative_of_leftHalfPlane hz_left
  have hreflect_norm :
      ‖completedRiemannZeta₀ z‖ = ‖completedRiemannZeta₀ w‖ := by
    have hsymm : completedRiemannZeta₀ (1 - z) = completedRiemannZeta₀ z :=
      completedRiemannZeta₀_one_sub z
    exact congrArg (fun x : ℂ => ‖x‖) hsymm.symm
  have hraw :
      ‖completedRiemannZeta₀ w‖ ≤
        A * Real.exp (B * (1 + ‖w‖) ^ m) :=
    hbound w hw_right
  have hheight_nonneg : 0 ≤ 1 + ‖w‖ := by
    exact le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg w))
  have hheight_le :
      1 + ‖w‖ ≤ 2 * H :=
    completedRiemannZeta₀_reflected_basicHeight_le z
  have hpow_le :
      (1 + ‖w‖) ^ m ≤ (2 * H) ^ m :=
    pow_le_pow_left₀ hheight_nonneg hheight_le m
  have hscale :
      B * (1 + ‖w‖) ^ m ≤ B * (2 * H) ^ m :=
    mul_le_mul_of_nonneg_left hpow_le (le_of_lt hBpos)
  have hmul_pow :
      (2 * H) ^ m = (2 : ℝ) ^ m * H ^ m :=
    mul_pow 2 H m
  have htarget :
      B * (2 * H) ^ m = (B * (2 : ℝ) ^ m) * H ^ m := by
    calc
      B * (2 * H) ^ m = B * ((2 : ℝ) ^ m * H ^ m) := by
        exact congrArg (fun x : ℝ => B * x) hmul_pow
      _ = (B * (2 : ℝ) ^ m) * H ^ m := by
        exact (mul_assoc B ((2 : ℝ) ^ m) (H ^ m)).symm
  have hexp_le :
      Real.exp (B * (1 + ‖w‖) ^ m) ≤
        Real.exp ((B * (2 : ℝ) ^ m) * H ^ m) :=
    Real.exp_le_exp.mpr (hscale.trans_eq htarget)
  have hscaled :
      A * Real.exp (B * (1 + ‖w‖) ^ m) ≤
        A * Real.exp ((B * (2 : ℝ) ^ m) * H ^ m) :=
    mul_le_mul_of_nonneg_left hexp_le (le_of_lt hApos)
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ A * Real.exp ((B * (2 : ℝ) ^ m) * H ^ m))
    hreflect_norm.symm
    (hraw.trans hscaled)

/-- Left half-plane finite-order growth for the uncentered entire completed-zeta part. -/
theorem completedRiemannZeta₀_leftHalfPlane_finiteOrder_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact completedRiemannZeta₀_leftHalfPlane_finiteOrder_growth_bound_of_rightHalfPlane
    completedRiemannZeta₀_rightHalfPlane_finiteOrder_growth_bound

/-- Half-plane finite-order estimates combine to a global finite-order estimate. -/
theorem completedRiemannZeta₀_global_finiteOrder_growth_bound_of_halfPlanes
    (hright :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          ‖completedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hleft :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re ≤ 0 →
          ‖completedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hright with ⟨Ar, Br, mr, hAr, hBr, hright_bound⟩
  rcases hleft with ⟨Al, Bl, ml, hAl, hBl, hleft_bound⟩
  refine ⟨Ar + Al, Br + Bl, mr + ml, add_pos hAr hAl, add_pos hBr hBl, ?_⟩
  intro z
  have hAr_nonneg : 0 ≤ Ar := le_of_lt hAr
  have hAl_nonneg : 0 ≤ Al := le_of_lt hAl
  have hBr_nonneg : 0 ≤ Br := le_of_lt hBr
  have hBl_nonneg : 0 ≤ Bl := le_of_lt hBl
  have hA_right_le : Ar ≤ Ar + Al :=
    le_add_of_nonneg_right hAl_nonneg
  have hA_left_le : Al ≤ Ar + Al :=
    le_add_of_nonneg_left hAr_nonneg
  have hB_right_le : Br ≤ Br + Bl :=
    le_add_of_nonneg_right hBl_nonneg
  have hB_left_le : Bl ≤ Br + Bl :=
    le_add_of_nonneg_left hBr_nonneg
  match le_total 0 z.re with
  | Or.inl hright_re =>
      exact le_trans (hright_bound z hright_re)
        (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent
          hAr_nonneg
          hA_right_le
          hB_right_le
          hBr_nonneg
          (Nat.le_add_right mr ml))
  | Or.inr hleft_re =>
      have hdegree : ml ≤ mr + ml := by
        exact Eq.subst
          (motive := fun d : ℕ => ml ≤ d)
          (Nat.add_comm ml mr)
          (Nat.le_add_right ml mr)
      exact le_trans (hleft_bound z hleft_re)
        (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent
          hAl_nonneg
          hA_left_le
          hB_left_le
          hBl_nonneg
          hdegree)

/-- Owner finite-order growth for the uncentered entire completed-zeta part.

This is the analytic finite-order input actually used by completed-zeta zero counting in
the RH lane.  A more general Hurwitz finite-order theorem may imply it, but the zeta
normalization layer only needs this specialization. -/
theorem completedRiemannZeta₀_finiteOrder_growth_bound_ownerZeta :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact completedRiemannZeta₀_global_finiteOrder_growth_bound_of_halfPlanes
    completedRiemannZeta₀_rightHalfPlane_finiteOrder_growth_bound
    completedRiemannZeta₀_leftHalfPlane_finiteOrder_growth_bound

/-- Finite-order growth for the uncentered entire completed-zeta part. -/
theorem completedRiemannZeta₀_finiteOrder_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
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

/-- Finite-order growth is preserved by centering the entire completed-zeta part. -/
theorem centeredCompletedRiemannZeta₀_finiteOrder_growth_bound_of_uncentered
    (huncentered :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          ‖completedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        ‖centeredCompletedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases huncentered with ⟨A, B, m, hApos, hBpos, hbound⟩
  refine ⟨A, B * (2 : ℝ) ^ m, m, hApos, ?_, ?_⟩
  · exact mul_pos hBpos (pow_pos zero_lt_two m)
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
        A * Real.exp (B * (1 + ‖(1 / 2 : ℂ) + z‖) ^ m) :=
    hbound ((1 / 2 : ℂ) + z)
  have hscale :
      B * (1 + ‖(1 / 2 : ℂ) + z‖) ^ m ≤
        B * (2 * H) ^ m :=
    mul_le_mul_of_nonneg_left hpow_le (le_of_lt hBpos)
  have hmul_pow :
      (2 * H) ^ m = (2 : ℝ) ^ m * H ^ m :=
    mul_pow 2 H m
  have htarget :
      B * (2 * H) ^ m =
        (B * (2 : ℝ) ^ m) * H ^ m := by
    calc
      B * (2 * H) ^ m = B * ((2 : ℝ) ^ m * H ^ m) := by
        exact congrArg (fun x : ℝ => B * x) hmul_pow
      _ = (B * (2 : ℝ) ^ m) * H ^ m := by
        exact (mul_assoc B ((2 : ℝ) ^ m) (H ^ m)).symm
  have hexp_le :
      Real.exp (B * (1 + ‖(1 / 2 : ℂ) + z‖) ^ m) ≤
        Real.exp ((B * (2 : ℝ) ^ m) * H ^ m) :=
    Real.exp_le_exp.mpr (hscale.trans_eq htarget)
  have hscale_exp :
      A * Real.exp (B * (1 + ‖(1 / 2 : ℂ) + z‖) ^ m) ≤
        A * Real.exp ((B * (2 : ℝ) ^ m) * H ^ m) :=
    mul_le_mul_of_nonneg_left hexp_le (le_of_lt hApos)
  exact Eq.subst
    (motive := fun x : ℂ =>
      ‖x‖ ≤ A * Real.exp ((B * (2 : ℝ) ^ m) * H ^ m))
    hcenter.symm
    (hraw.trans hscale_exp)

/-- Finite-order growth for the centered entire completed-zeta part. -/
theorem centeredCompletedRiemannZeta₀_finiteOrder_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        ‖centeredCompletedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact centeredCompletedRiemannZeta₀_finiteOrder_growth_bound_of_uncentered
    completedRiemannZeta₀_finiteOrder_growth_bound

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

/-- The basic centered height is nonnegative. -/
theorem centeredCompletedRiemannZeta_basicHeight_nonnegative
    (z : ℂ) :
    0 ≤ 1 + ‖z‖ := by
  exact le_trans zero_le_one (centeredCompletedRiemannZeta_basicHeight_ge_one z)

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
    exact centeredCompletedRiemannZeta_basicHeight_nonnegative z
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

/-- A nonnegative real exponent has exponential at least one. -/
theorem one_le_exp_of_nonnegative_exponent
    {x : ℝ} (hx : 0 ≤ x) :
    (1 : ℝ) ≤ Real.exp x := by
  calc
    (1 : ℝ) ≤ x + 1 := by
      exact le_add_of_nonneg_left hx
    _ ≤ Real.exp x := by
      exact Real.add_one_le_exp x

/-- Polynomial powers of the basic centered height are dominated by an exponential of a
higher basic-height power. -/
theorem centeredCompletedRiemannZeta_basicHeight_pow_le_exp_pow_add
    (z : ℂ) (m n : ℕ) :
    (1 + ‖z‖) ^ m ≤ Real.exp ((1 + ‖z‖) ^ (m + n)) := by
  let H : ℝ := 1 + ‖z‖
  have hH_ge_one : (1 : ℝ) ≤ H :=
    centeredCompletedRiemannZeta_basicHeight_ge_one z
  have hH_nonneg : 0 ≤ H :=
    centeredCompletedRiemannZeta_basicHeight_nonnegative z
  have hpow_le :
      H ^ m ≤ H ^ (m + n) :=
    pow_le_pow_right₀ hH_ge_one (Nat.le_add_right m n)
  have hpow_nonneg : 0 ≤ H ^ (m + n) :=
    pow_nonneg hH_nonneg (m + n)
  have hle_exp :
      H ^ (m + n) ≤ Real.exp (H ^ (m + n)) :=
    le_trans
      (centeredCompletedRiemannZeta_basicHeight_pow_ge_one z (m + n))
      (one_le_exp_of_nonnegative_exponent hpow_nonneg)
  exact le_trans hpow_le hle_exp

/-- Multiplying an exponential finite-order function by a polynomial-growth function
preserves exponential finite-order growth. -/
theorem exponentialFiniteOrder_mul_polynomialGrowth
    {u v : ℂ → ℂ}
    (hu :
      ∃ A : ℝ, ∃ m : ℕ,
        0 < A ∧
        ∀ z : ℂ, ‖u z‖ ≤ A * (1 + ‖z‖) ^ m)
    (hv :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ, ‖v z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ, ‖u z * v z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hu with ⟨A, m, hA_pos, hA_bound⟩
  rcases hv with ⟨B, C, n, hB_pos, hC_pos, hB_bound⟩
  refine ⟨A * B, C + 1, m + n, mul_pos hA_pos hB_pos, add_pos hC_pos zero_lt_one, ?_⟩
  intro z
  let H : ℝ := 1 + ‖z‖
  have hH_ge_one : (1 : ℝ) ≤ H :=
    centeredCompletedRiemannZeta_basicHeight_ge_one z
  have hH_nonneg : 0 ≤ H :=
    centeredCompletedRiemannZeta_basicHeight_nonnegative z
  have hpoly_exp :
      H ^ m ≤ Real.exp (H ^ (m + n)) :=
    centeredCompletedRiemannZeta_basicHeight_pow_le_exp_pow_add z m n
  have hn_pow_le_sum_pow :
      H ^ n ≤ H ^ (m + n) := by
    have hrewrite : m + n = n + m := by
      exact Nat.add_comm m n
    exact Eq.subst
      (motive := fun k : ℕ => H ^ n ≤ H ^ k)
      hrewrite.symm
      (pow_le_pow_right₀ hH_ge_one (Nat.le_add_right n m))
  have hC_scaled :
      C * H ^ n ≤ C * H ^ (m + n) :=
    mul_le_mul_of_nonneg_left hn_pow_le_sum_pow (le_of_lt hC_pos)
  have hexponent_sum :
      H ^ (m + n) + C * H ^ n ≤ (C + 1) * H ^ (m + n) := by
    have hright :
        H ^ (m + n) + C * H ^ (m + n) =
          (C + 1) * H ^ (m + n) := by
      ring
    exact (add_le_add_left hC_scaled (H ^ (m + n))).trans_eq hright
  have hexp_bound :
      Real.exp (H ^ (m + n)) * Real.exp (C * H ^ n) ≤
        Real.exp ((C + 1) * H ^ (m + n)) := by
    have hmul_exp :
        Real.exp (H ^ (m + n)) * Real.exp (C * H ^ n) =
          Real.exp (H ^ (m + n) + C * H ^ n) := by
      exact (Real.exp_add (H ^ (m + n)) (C * H ^ n)).symm
    exact hmul_exp.trans_le (Real.exp_le_exp.mpr hexponent_sum)
  have hright_nonneg :
      0 ≤ B * Real.exp (C * H ^ n) :=
    mul_nonneg (le_of_lt hB_pos) (le_of_lt (Real.exp_pos (C * H ^ n)))
  have hnorm_mul :
      ‖u z * v z‖ = ‖u z‖ * ‖v z‖ :=
    norm_mul (u z) (v z)
  have hproduct_bound :
      ‖u z‖ * ‖v z‖ ≤
        (A * H ^ m) * (B * Real.exp (C * H ^ n)) :=
    mul_le_mul (hA_bound z) (hB_bound z) (norm_nonneg _) hright_nonneg
  have hconstant_power :
      (A * H ^ m) * (B * Real.exp (C * H ^ n)) =
        (A * B) * (H ^ m * Real.exp (C * H ^ n)) := by
    ring
  have hpower_exp :
      H ^ m * Real.exp (C * H ^ n) ≤
        Real.exp (H ^ (m + n)) * Real.exp (C * H ^ n) :=
    mul_le_mul_of_nonneg_right hpoly_exp (le_of_lt (Real.exp_pos (C * H ^ n)))
  have hinner :
      H ^ m * Real.exp (C * H ^ n) ≤
        Real.exp ((C + 1) * H ^ (m + n)) :=
    hpower_exp.trans hexp_bound
  have hscaled :
      (A * B) * (H ^ m * Real.exp (C * H ^ n)) ≤
        (A * B) * Real.exp ((C + 1) * H ^ (m + n)) :=
    mul_le_mul_of_nonneg_left hinner (le_of_lt (mul_pos hA_pos hB_pos))
  exact hnorm_mul.trans_le
    (hproduct_bound.trans
      ((le_of_eq hconstant_power).trans hscaled))

/-- Subtracting the constant `1` from an exponential finite-order function preserves
exponential finite-order growth. -/
theorem exponentialFiniteOrder_sub_one
    {u : ℂ → ℂ}
    (hu :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ, ‖u z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ, ‖u z - 1‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hu with ⟨A, B, m, hA_pos, hB_pos, hbound⟩
  refine ⟨A + 1, B, m, add_pos hA_pos zero_lt_one, hB_pos, ?_⟩
  intro z
  let H : ℝ := 1 + ‖z‖
  have hH_ge_one : (1 : ℝ) ≤ H :=
    centeredCompletedRiemannZeta_basicHeight_ge_one z
  have hH_nonneg : 0 ≤ H :=
    centeredCompletedRiemannZeta_basicHeight_nonnegative z
  have hexponent_nonneg : 0 ≤ B * H ^ m :=
    mul_nonneg (le_of_lt hB_pos) (pow_nonneg hH_nonneg m)
  have hone_le_exp :
      (1 : ℝ) ≤ Real.exp (B * H ^ m) :=
    one_le_exp_of_nonnegative_exponent hexponent_nonneg
  have htriangle :
      ‖u z - 1‖ ≤ ‖u z‖ + ‖(1 : ℂ)‖ :=
    norm_sub_le (u z) (1 : ℂ)
  have hone_norm : ‖(1 : ℂ)‖ = (1 : ℝ) := by
    norm_num
  have hsum_bound :
      ‖u z‖ + ‖(1 : ℂ)‖ ≤
        A * Real.exp (B * H ^ m) + Real.exp (B * H ^ m) := by
    rw [hone_norm]
    exact add_le_add (hbound z) hone_le_exp
  have halg :
      A * Real.exp (B * H ^ m) + Real.exp (B * H ^ m) =
        (A + 1) * Real.exp (B * H ^ m) := by
    ring
  exact htriangle.trans (hsum_bound.trans_eq halg)

/-- Multiplying a finite-order entire part by the quadratic clearing factor and subtracting
`1` preserves exponential finite-order growth. -/
theorem centeredCompletedRiemannZetaZeroCarrier_growth_bound_of_factor_and_entirePart
    (hfactor :
      ∃ A : ℝ, ∃ m : ℕ,
        0 < A ∧
        ∀ z : ℂ,
          ‖centeredCompletedRiemannZetaZeroCarrierClearingFactor z‖ ≤
            A * (1 + ‖z‖) ^ m)
    (hentire :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          ‖centeredCompletedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        ‖centeredCompletedRiemannZetaZeroCarrier z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  have hproduct :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          ‖centeredCompletedRiemannZetaZeroCarrierClearingFactor z *
              centeredCompletedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m) :=
    exponentialFiniteOrder_mul_polynomialGrowth hfactor hentire
  have hproduct_sub_one :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          ‖centeredCompletedRiemannZetaZeroCarrierClearingFactor z *
              centeredCompletedRiemannZeta₀ z - 1‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m) :=
    exponentialFiniteOrder_sub_one hproduct
  rcases hproduct_sub_one with ⟨A, B, m, hA_pos, hB_pos, hbound⟩
  refine ⟨A, B, m, hA_pos, hB_pos, ?_⟩
  intro z
  have hcarrier :
      centeredCompletedRiemannZetaZeroCarrier z =
        centeredCompletedRiemannZetaZeroCarrierClearingFactor z *
          centeredCompletedRiemannZeta₀ z - 1 :=
    centeredCompletedRiemannZetaZeroCarrier_eq_factor_mul_entirePart_sub_one z
  exact Eq.subst
    (motive := fun w : ℂ =>
      ‖w‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m))
    hcarrier.symm
    (hbound z)

/-- Finite-order growth is preserved by the completed zero-carrier normalization.

The zero-carrier is obtained from the centered entire part by multiplying by the quadratic
clearing factor `((1 / 2) + z) * (1 - ((1 / 2) + z))` and subtracting `1`. -/
theorem centeredCompletedRiemannZetaZeroCarrier_finiteOrder_growth_bound_of_entirePart
    (hentire :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          ‖centeredCompletedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        ‖centeredCompletedRiemannZetaZeroCarrier z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    centeredCompletedRiemannZetaZeroCarrier_growth_bound_of_factor_and_entirePart
      centeredCompletedRiemannZetaZeroCarrierClearingFactor_growth_bound
      hentire

/-- Finite-order growth of the uncentered entire completed-zeta part gives finite-order
growth of the centered entire zero-carrier. -/
theorem centeredCompletedRiemannZetaZeroCarrier_finiteOrder_growth_bound_of_uncentered
    (huncentered :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          ‖completedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        ‖centeredCompletedRiemannZetaZeroCarrier z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact centeredCompletedRiemannZetaZeroCarrier_finiteOrder_growth_bound_of_entirePart
    (centeredCompletedRiemannZeta₀_finiteOrder_growth_bound_of_uncentered huncentered)

/-- Finite-order growth for the centered entire completed-zeta zero-carrier.

This is the normalization-side entire-function input used by Jensen counting. The
zero-carrier is the cleared entire divisor
`((1 / 2) + s) * (1 - ((1 / 2) + s)) * centeredCompletedRiemannZeta₀ s - 1`,
so this theorem is owned by the completed normalization layer rather than by the
downstream zero-counting file. -/
theorem centeredCompletedRiemannZetaZeroCarrier_finiteOrder_growth_bound :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        ‖centeredCompletedRiemannZetaZeroCarrier z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    centeredCompletedRiemannZetaZeroCarrier_finiteOrder_growth_bound_of_uncentered
      completedRiemannZeta₀_finiteOrder_growth_bound

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
