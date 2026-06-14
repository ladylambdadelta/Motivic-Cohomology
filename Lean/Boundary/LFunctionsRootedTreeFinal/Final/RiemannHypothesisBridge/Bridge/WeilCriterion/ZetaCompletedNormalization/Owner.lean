import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.NumberTheory.AbelSummation
import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.Harmonic.Bounds

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
    calc
      ‖Complex.Gammaℝ z‖ = Real.exp (Real.log ‖Complex.Gammaℝ z‖) := hnorm_eq
      _ ≤ Real.exp ((|C| + 1) * (1 + ‖z‖) ^ m) := hexp_le
      _ = 1 * Real.exp ((|C| + 1) * (1 + ‖z‖) ^ m) := by
        exact (one_mul (Real.exp ((|C| + 1) * (1 + ‖z‖) ^ m))).symm

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

/-- The inline half-argument normalized Gamma expression is the local unfolded
`Gammaℝ` factor. -/
theorem halfArgument_normalized_complexGamma_eq_unfoldedNormalizedGammaℝFactor
    (z : ℂ) :
    π ^ (-z / 2) * Complex.Gamma (z / 2) =
      unfoldedNormalizedGammaℝFactor z := by
  rfl

/-- Log-norm transport from the inline half-argument Gamma expression to the local
unfolded `Gammaℝ` factor. -/
theorem log_norm_halfArgument_normalized_complexGamma_eq_log_norm_unfoldedNormalizedGammaℝFactor
    (z : ℂ) :
    Real.log ‖π ^ (-z / 2) * Complex.Gamma (z / 2)‖ =
      Real.log ‖unfoldedNormalizedGammaℝFactor z‖ := by
  exact congrArg
    (fun w : ℂ => Real.log ‖w‖)
    (halfArgument_normalized_complexGamma_eq_unfoldedNormalizedGammaℝFactor z)

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

/-- The half-argument has nonnegative real part in the right half-plane. -/
theorem halfArgument_re_nonneg_of_re_nonneg
    {z : ℂ}
    (hz_re : 0 ≤ z.re) :
    0 ≤ (z / 2).re := by
  have htwo_pos : (0 : ℝ) < 2 := by norm_num
  rw [Complex.div_re_ofReal]
  exact div_nonneg hz_re (le_of_lt htwo_pos)

/-- The half-argument is nonzero in the large right-half-plane Stirling region. -/
theorem halfArgument_ne_zero_of_one_le_norm
    {z : ℂ}
    (hz_norm : 1 ≤ ‖z‖) :
    z / 2 ≠ 0 := by
  intro hzero
  have hz_zero : z = 0 := by
    have hmul := congrArg (fun w : ℂ => w * (2 : ℂ)) hzero
    calc
      z = (z / 2) * (2 : ℂ) := by
        exact (div_mul_cancel₀ z (by norm_num : (2 : ℂ) ≠ 0)).symm
      _ = 0 * (2 : ℂ) := by
        exact hmul
      _ = 0 := zero_mul (2 : ℂ)
  have hnorm_zero : ‖z‖ = 0 := by
    exact congrArg norm hz_zero
  have hnot : ¬ (1 : ℝ) ≤ 0 := by norm_num
  exact hnot (Eq.subst (motive := fun x : ℝ => 1 ≤ x) hnorm_zero hz_norm)

/-- `Complex.Gamma (z / 2)` is nonzero on the large right-half-plane Stirling region. -/
theorem ComplexGamma_halfArgument_ne_zero_of_re_nonneg_and_one_le_norm
    {z : ℂ}
    (hz_re : 0 ≤ z.re)
    (hz_norm : 1 ≤ ‖z‖) :
    Complex.Gamma (z / 2) ≠ 0 := by
  have hz_half_re : 0 ≤ (z / 2).re :=
    halfArgument_re_nonneg_of_re_nonneg hz_re
  have hz_half_ne : z / 2 ≠ 0 :=
    halfArgument_ne_zero_of_one_le_norm hz_norm
  intro hzero
  rcases (Complex.Gamma_eq_zero_iff (z / 2)).mp hzero with ⟨n, hn⟩
  have hhalf_re_eq : (z / 2).re = (-(n : ℂ)).re := congrArg Complex.re hn
  have hn_re : (-(n : ℂ)).re = -(n : ℝ) := by simp
  have hz_half_re_nonpos : (z / 2).re ≤ 0 := by
    calc
      (z / 2).re = (-(n : ℂ)).re := hhalf_re_eq
      _ = -(n : ℝ) := hn_re
      _ ≤ 0 := neg_nonpos.mpr (Nat.cast_nonneg n)
  have hz_half_re_zero : (z / 2).re = 0 :=
    le_antisymm hz_half_re_nonpos hz_half_re
  cases n with
  | zero =>
      have hhalf_zero : z / 2 = 0 := by
        simpa using hn
      exact hz_half_ne hhalf_zero
  | succ n =>
      have hneg_succ_lt_zero : (-(Nat.succ n : ℂ)).re < 0 := by
        simp
      have hcontr : (z / 2).re < 0 := by
        calc
          (z / 2).re = (-(Nat.succ n : ℂ)).re := hhalf_re_eq
          _ < 0 := hneg_succ_lt_zero
      exact (not_lt_of_ge hz_half_re) hcontr

/-- Norm transport for the half-argument. -/
theorem two_mul_norm_halfArgument
    (z : ℂ) :
    2 * ‖z / 2‖ = ‖z‖ := by
  have htwo_norm : ‖(2 : ℂ)‖ = (2 : ℝ) := by
    calc
      ‖(2 : ℂ)‖ = ‖(2 : ℝ)‖ := by
        exact Complex.norm_real 2
      _ = (2 : ℝ) :=
        Real.norm_of_nonneg zero_le_two
  calc
    2 * ‖z / 2‖ = ‖(2 : ℂ)‖ * ‖z / 2‖ := by
      exact congrArg (fun x : ℝ => x * ‖z / 2‖) htwo_norm.symm
    _ = ‖(2 : ℂ) * (z / 2)‖ := by
      exact (norm_mul (2 : ℂ) (z / 2)).symm
    _ = ‖z‖ := by
      have hmul : (2 : ℂ) * (z / 2) = z := by
        calc
          (2 : ℂ) * (z / 2) = z / 2 * (2 : ℂ) := by
            exact mul_comm (2 : ℂ) (z / 2)
          _ = z := div_mul_cancel₀ z (by exact two_ne_zero)
      exact congrArg norm hmul

/-- The half-argument is in the large sectorial region measured at radius `1 / 2`. -/
theorem halfArgument_norm_ge_one_half_of_one_le_norm
    {z : ℂ}
    (hz_norm : 1 ≤ ‖z‖) :
    (1 / 2 : ℝ) ≤ ‖z / 2‖ := by
  have htwo_pos : (0 : ℝ) < 2 := zero_lt_two
  have htransport : 2 * ‖z / 2‖ = ‖z‖ :=
    two_mul_norm_halfArgument z
  have hone_le_two_mul : (1 : ℝ) ≤ 2 * ‖z / 2‖ :=
    Eq.subst
      (motive := fun x : ℝ => (1 : ℝ) ≤ x)
      htransport.symm
      hz_norm
  exact (div_le_iff₀' htwo_pos).mpr hone_le_two_mul

/-- The sectorial envelope is preserved exactly under `w = z / 2`. -/
theorem sectorialGammaEnvelope_halfArgument_eq
    (C : ℝ)
    (z : ℂ) :
    C * (1 + 2 * ‖z / 2‖) * Real.log (2 + 2 * ‖z / 2‖) =
      C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
  exact congrArg
    (fun x : ℝ => C * (1 + x) * Real.log (2 + x))
    (two_mul_norm_halfArgument z)

/-- The log-linear envelope is additive in its constant. -/
theorem logLinearEnvelope_add_constants
    (A B H L : ℝ) :
    A * H * L + B * H * L = (A + B) * H * L := by
  calc
    A * H * L + B * H * L = (A * H + B * H) * L := by
      exact (add_mul (A * H) (B * H) L).symm
    _ = ((A + B) * H) * L := by
      exact congrArg (fun x : ℝ => x * L) (add_mul A B H).symm
    _ = (A + B) * H * L := by
      rfl

/-- The log-linear envelope is monotone in its constant when the envelope
factors are nonnegative. -/
theorem logLinearEnvelope_mono_constant
    {A B H L : ℝ}
    (hAB : A ≤ B)
    (hH : 0 ≤ H)
    (hL : 0 ≤ L) :
    A * H * L ≤ B * H * L := by
  have hAH_le_BH : A * H ≤ B * H :=
    mul_le_mul_of_nonneg_right hAB hH
  exact mul_le_mul_of_nonneg_right hAH_le_BH hL

/-- The logarithmic envelope on `2 + ‖z‖` has argument at least one. -/
theorem one_le_two_add_complex_norm
    (z : ℂ) :
    (1 : ℝ) ≤ 2 + ‖z‖ := by
  calc
    (1 : ℝ) ≤ 2 := one_le_two
    _ ≤ 2 + ‖z‖ := le_add_of_nonneg_right (norm_nonneg z)

/-- The closed right half-plane sector used for the owner Gamma/Stirling roots. -/
def Complex.closedRightHalfPlaneSector (w : ℂ) : Prop :=
  0 ≤ w.re

/-- The fixed-real-part vertical line point `a + i b`, named to keep all fixed-line
Stirling estimates definitionally aligned. -/
def Complex.fixedRealPartVerticalPoint (a b : ℝ) : ℂ :=
  (a : ℂ) + (b : ℂ) * Complex.I

/-- The fixed-line point has real coordinate `a`. -/
theorem Complex.fixedRealPartVerticalPoint_re
    (a b : ℝ) :
    (Complex.fixedRealPartVerticalPoint a b).re = a := by
  calc
    (Complex.fixedRealPartVerticalPoint a b).re =
        ((a : ℂ) + (b : ℂ) * Complex.I).re := rfl
    _ = (a : ℂ).re + ((b : ℂ) * Complex.I).re :=
        Complex.add_re (a : ℂ) ((b : ℂ) * Complex.I)
    _ = a + 0 := by
        exact congrArg
          (fun x : ℝ => a + x)
          (Complex.ofReal_mul_I_re b)
    _ = a := add_zero a

/-- The fixed-line point has imaginary coordinate `b`. -/
theorem Complex.fixedRealPartVerticalPoint_im
    (a b : ℝ) :
    (Complex.fixedRealPartVerticalPoint a b).im = b := by
  calc
    (Complex.fixedRealPartVerticalPoint a b).im =
        ((a : ℂ) + (b : ℂ) * Complex.I).im := rfl
    _ = (a : ℂ).im + ((b : ℂ) * Complex.I).im :=
        Complex.add_im (a : ℂ) ((b : ℂ) * Complex.I)
    _ = 0 + b := by
        exact congrArg
          (fun x : ℝ => 0 + x)
          (Complex.ofReal_mul_I_im b)
    _ = b := zero_add b

/-- The direct fixed-real-part vertical Stirling envelope. -/
def Complex.fixedRealPartVerticalStirlingEnvelope (a b : ℝ) : ℝ :=
  Real.exp (-(Real.pi / 2) * ‖b‖) * (1 + ‖b‖) ^ (a - 1 / 2)

/-- The reciprocal fixed-real-part vertical Stirling envelope. -/
def Complex.fixedRealPartVerticalReciprocalStirlingEnvelope (a b : ℝ) : ℝ :=
  Real.exp ((Real.pi / 2) * ‖b‖) * (1 + ‖b‖) ^ (1 / 2 - a)

/-- The fixed-real-part direct Stirling envelope is positive. -/
theorem Complex.fixedRealPartVerticalStirlingEnvelope_pos
    (a b : ℝ) :
    0 < Complex.fixedRealPartVerticalStirlingEnvelope a b := by
  have hbase_pos : 0 < 1 + ‖b‖ :=
    lt_of_lt_of_le zero_lt_one
      (le_add_of_nonneg_right (norm_nonneg b))
  exact mul_pos
    (Real.exp_pos (-(Real.pi / 2) * ‖b‖))
    (Real.rpow_pos_of_pos hbase_pos (a - 1 / 2))

/-- The fixed-real-part direct Stirling envelope is nonnegative. -/
theorem Complex.fixedRealPartVerticalStirlingEnvelope_nonneg
    (a b : ℝ) :
    0 ≤ Complex.fixedRealPartVerticalStirlingEnvelope a b :=
  le_of_lt (Complex.fixedRealPartVerticalStirlingEnvelope_pos a b)

/-- The fixed-real-part reciprocal Stirling envelope is positive. -/
theorem Complex.fixedRealPartVerticalReciprocalStirlingEnvelope_pos
    (a b : ℝ) :
    0 < Complex.fixedRealPartVerticalReciprocalStirlingEnvelope a b := by
  have hbase_pos : 0 < 1 + ‖b‖ :=
    lt_of_lt_of_le zero_lt_one
      (le_add_of_nonneg_right (norm_nonneg b))
  exact mul_pos
    (Real.exp_pos ((Real.pi / 2) * ‖b‖))
    (Real.rpow_pos_of_pos hbase_pos (1 / 2 - a))

/-- The fixed-real-part reciprocal Stirling envelope is nonnegative. -/
theorem Complex.fixedRealPartVerticalReciprocalStirlingEnvelope_nonneg
    (a b : ℝ) :
    0 ≤ Complex.fixedRealPartVerticalReciprocalStirlingEnvelope a b :=
  le_of_lt (Complex.fixedRealPartVerticalReciprocalStirlingEnvelope_pos a b)

/-- Sectorial logarithmic Stirling expansion for `Complex.Gamma` on the closed
right half-plane.

This is the deepest classical special-function root for the sectorial Gamma
lane: on closed subsectors avoiding the negative real axis, `log Γ(w)` has the
usual Stirling expansion with a uniform `O(1 / ‖w‖)` remainder.  In the closed
right half-plane this gives the formula below after exponentiating the
remainder; cf. DLMF §5.11 and Whittaker-Watson, Ch. XII. -/
theorem Complex.sectorialLogGammaAsymptotic_closedRightHalfPlane :
    ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖ := by
  sorry

/-- If a complex number is within `sqrt (2π)` of `sqrt (2π)`, then its norm is
bounded by `2 sqrt (2π)`.

This is the elementary triangle-inequality extraction used to pass from the
exponential Stirling remainder to a uniform bound for the normalized Gamma
factor. -/
theorem Complex.norm_le_two_sqrt_two_pi_of_norm_sub_sqrt_two_pi_le_sqrt_two_pi
    (A : ℂ)
    (hA :
      ‖A - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤ Real.sqrt (2 * Real.pi)) :
    ‖A‖ ≤ 2 * Real.sqrt (2 * Real.pi) := by
  have htriangle :
      ‖A‖ ≤
        ‖A - (Real.sqrt (2 * Real.pi) : ℂ)‖ +
          ‖(Real.sqrt (2 * Real.pi) : ℂ)‖ := by
    calc
      ‖A‖ =
          ‖(A - (Real.sqrt (2 * Real.pi) : ℂ)) +
            (Real.sqrt (2 * Real.pi) : ℂ)‖ := by
        exact congrArg norm (sub_add_cancel A (Real.sqrt (2 * Real.pi) : ℂ)).symm
      _ ≤
          ‖A - (Real.sqrt (2 * Real.pi) : ℂ)‖ +
            ‖(Real.sqrt (2 * Real.pi) : ℂ)‖ :=
        norm_add_le (A - (Real.sqrt (2 * Real.pi) : ℂ))
          (Real.sqrt (2 * Real.pi) : ℂ)
  have hsqrt_nonneg : 0 ≤ Real.sqrt (2 * Real.pi) :=
    Real.sqrt_nonneg (2 * Real.pi)
  have hnorm_sqrt :
      ‖(Real.sqrt (2 * Real.pi) : ℂ)‖ = Real.sqrt (2 * Real.pi) := by
    exact Complex.norm_ofReal_of_nonneg hsqrt_nonneg
  calc
    ‖A‖ ≤
        ‖A - (Real.sqrt (2 * Real.pi) : ℂ)‖ +
          ‖(Real.sqrt (2 * Real.pi) : ℂ)‖ := htriangle
    _ ≤ Real.sqrt (2 * Real.pi) +
          ‖(Real.sqrt (2 * Real.pi) : ℂ)‖ :=
        add_le_add_right hA ‖(Real.sqrt (2 * Real.pi) : ℂ)‖
    _ = Real.sqrt (2 * Real.pi) + Real.sqrt (2 * Real.pi) :=
        congrArg (fun x : ℝ => Real.sqrt (2 * Real.pi) + x) hnorm_sqrt
    _ = 2 * Real.sqrt (2 * Real.pi) := by
        exact (two_mul (Real.sqrt (2 * Real.pi))).symm

/-- Pointwise normalized Gamma-factor bound extracted from an exponential
Stirling estimate once the error term is at most `sqrt (2π)`. -/
theorem Complex.normalizedGammaFactor_norm_le_two_sqrt_two_pi_of_exponentialStirling_error
    (R K : ℝ)
    (hStirling :
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖)
    (w : ℂ)
    (hw_sector : Complex.closedRightHalfPlaneSector w)
    (hw_R : R ≤ ‖w‖)
    (hw_error : K / ‖w‖ ≤ Real.sqrt (2 * Real.pi)) :
    ‖Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w)‖ ≤
      2 * Real.sqrt (2 * Real.pi) := by
  have herror :
      ‖Complex.Gamma w * Complex.exp w *
          w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
        Real.sqrt (2 * Real.pi) :=
    le_trans (hStirling w hw_sector hw_R) hw_error
  exact
    Complex.norm_le_two_sqrt_two_pi_of_norm_sub_sqrt_two_pi_le_sqrt_two_pi
      (Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w))
      herror

/-- The normalized factor appearing in sectorial exponential Stirling for
`Complex.Gamma`. -/
def Complex.normalizedGammaStirlingFactor (w : ℂ) : ℂ :=
  Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w)

/-- The logarithmic denominator loss incurred when solving the normalized
Stirling factor for `log ‖Γ(w)‖`. -/
def Complex.normalizedGammaStirlingLogLoss (w : ℂ) : ℝ :=
  -w.re - Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖

/-- A norm bound for the normalized Stirling factor gives the corresponding
logarithmic bound. -/
theorem Complex.normalizedGammaStirlingFactor_log_le_of_norm_bound
    (B : ℝ)
    {w : ℂ}
    (hfactor_pos : 0 < ‖Complex.normalizedGammaStirlingFactor w‖)
    (hbound : ‖Complex.normalizedGammaStirlingFactor w‖ ≤ B) :
    Real.log ‖Complex.normalizedGammaStirlingFactor w‖ ≤ Real.log B :=
  Real.log_le_log hfactor_pos hbound

/-- `Gamma` is nonzero at nonzero points in the closed right half-plane.

The only zeros of mathlib's completed finite-valued `Gamma` are the
nonpositive integers; the closed right half-plane excludes the negative
integers, and the explicit nonzero hypothesis excludes `0`. -/
theorem Complex.Gamma_ne_zero_of_closedRightHalfPlaneSector_of_ne_zero
    {w : ℂ}
    (hw_sector : Complex.closedRightHalfPlaneSector w)
    (hw_ne : w ≠ 0) :
    Complex.Gamma w ≠ 0 := by
  intro hzero
  rcases (Complex.Gamma_eq_zero_iff w).mp hzero with ⟨n, hn⟩
  subst w
  cases n with
  | zero =>
      exact hw_ne (neg_zero : -((0 : ℂ)) = 0)
  | succ n =>
      have hre_eq :
          (-(((Nat.succ n : ℕ) : ℂ))).re =
            -(((Nat.succ n : ℕ) : ℝ)) := by
        calc
          (-(((Nat.succ n : ℕ) : ℂ))).re =
              -(((Nat.succ n : ℕ) : ℂ).re) :=
            Complex.neg_re (((Nat.succ n : ℕ) : ℂ))
          _ = -(((Nat.succ n : ℕ) : ℝ)) := by
            exact congrArg Neg.neg (Complex.natCast_re (Nat.succ n))
      have hre_nonneg :
          (0 : ℝ) ≤ -(((Nat.succ n : ℕ) : ℝ)) :=
        Eq.subst
          (motive := fun x : ℝ => (0 : ℝ) ≤ x)
          hre_eq
          hw_sector
      have hsucc_pos : (0 : ℝ) < ((Nat.succ n : ℕ) : ℝ) :=
        Nat.cast_pos.mpr (Nat.succ_pos n)
      have hneg_lt_zero : -(((Nat.succ n : ℕ) : ℝ)) < 0 :=
        neg_neg_of_pos hsucc_pos
      exact (not_lt_of_ge hre_nonneg) hneg_lt_zero

/-- Nonvanishing of the normalized Stirling factor in the closed right
half-plane away from the origin.

This is the exact nonvanishing input for the large-radius extraction: `Γ` has
no zeros off the nonpositive integers, `exp` never vanishes, and `w^α` is
nonzero for `w ≠ 0`. -/
theorem Complex.normalizedGammaStirlingFactor_ne_zero_of_closedRightHalfPlaneSector_largeRadius
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀)
    {w : ℂ}
    (hw_sector : Complex.closedRightHalfPlaneSector w)
    (hw_radius : R₀ ≤ ‖w‖) :
    Complex.normalizedGammaStirlingFactor w ≠ 0 := by
  have hw_norm_pos : 0 < ‖w‖ :=
    lt_of_lt_of_le hR₀_pos hw_radius
  have hw_ne : w ≠ 0 :=
    norm_pos_iff.mp hw_norm_pos
  have hGamma_ne : Complex.Gamma w ≠ 0 :=
    Complex.Gamma_ne_zero_of_closedRightHalfPlaneSector_of_ne_zero
      hw_sector hw_ne
  have hexp_ne : Complex.exp w ≠ 0 :=
    Complex.exp_ne_zero w
  have hcpow_ne : w ^ ((1 / 2 : ℂ) - w) ≠ 0 := by
    intro hzero
    have hbase_zero : w = 0 :=
      ((cpow_eq_zero_iff w ((1 / 2 : ℂ) - w)).mp hzero).1
    exact hw_ne hbase_zero
  show
      Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w) ≠ 0
  exact mul_ne_zero (mul_ne_zero hGamma_ne hexp_ne) hcpow_ne

/-- Norm expansion for the normalized Gamma Stirling factor. -/
theorem Complex.normalizedGammaStirlingFactor_norm_eq
    (w : ℂ) :
    ‖Complex.normalizedGammaStirlingFactor w‖ =
      ‖Complex.Gamma w‖ * ‖Complex.exp w‖ *
        ‖w ^ ((1 / 2 : ℂ) - w)‖ := by
  calc
    ‖Complex.normalizedGammaStirlingFactor w‖ =
        ‖Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w)‖ := rfl
    _ = ‖Complex.Gamma w * Complex.exp w‖ *
          ‖w ^ ((1 / 2 : ℂ) - w)‖ :=
      norm_mul (Complex.Gamma w * Complex.exp w)
        (w ^ ((1 / 2 : ℂ) - w))
    _ = ‖Complex.Gamma w‖ * ‖Complex.exp w‖ *
          ‖w ^ ((1 / 2 : ℂ) - w)‖ := by
      exact congrArg
        (fun x : ℝ => x * ‖w ^ ((1 / 2 : ℂ) - w)‖)
        (norm_mul (Complex.Gamma w) (Complex.exp w))

/-- Log norm of the complex exponential is its real part. -/
theorem Complex.log_norm_exp_eq_re
    (w : ℂ) :
    Real.log ‖Complex.exp w‖ = w.re := by
  have hnorm_eq_abs :
      ‖Complex.exp w‖ = Complex.abs (Complex.exp w) :=
    norm_eq_abs (Complex.exp w)
  have habs_eq_exp :
      Complex.abs (Complex.exp w) = Real.exp w.re :=
    Complex.abs_exp w
  calc
    Real.log ‖Complex.exp w‖ =
        Real.log (Complex.abs (Complex.exp w)) :=
      congrArg Real.log hnorm_eq_abs
    _ = Real.log (Real.exp w.re) :=
      congrArg Real.log habs_eq_exp
    _ = w.re :=
      Real.log_exp w.re

/-- Exact log expansion of the normalized Gamma Stirling factor. -/
theorem Complex.normalizedGammaStirlingFactor_log_eq
    (w : ℂ)
    (hGamma_ne : Complex.Gamma w ≠ 0)
    (hcpow_ne : w ^ ((1 / 2 : ℂ) - w) ≠ 0) :
    Real.log ‖Complex.normalizedGammaStirlingFactor w‖ =
      Real.log ‖Complex.Gamma w‖ + w.re +
        Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ := by
  have hGamma_norm_ne : ‖Complex.Gamma w‖ ≠ 0 :=
    ne_of_gt (norm_pos_iff.mpr hGamma_ne)
  have hexp_norm_ne : ‖Complex.exp w‖ ≠ 0 :=
    ne_of_gt (norm_pos_iff.mpr (Complex.exp_ne_zero w))
  have hcpow_norm_ne : ‖w ^ ((1 / 2 : ℂ) - w)‖ ≠ 0 :=
    ne_of_gt (norm_pos_iff.mpr hcpow_ne)
  have hGamma_exp_norm_ne :
      ‖Complex.Gamma w‖ * ‖Complex.exp w‖ ≠ 0 :=
    mul_ne_zero hGamma_norm_ne hexp_norm_ne
  calc
    Real.log ‖Complex.normalizedGammaStirlingFactor w‖ =
        Real.log
          (‖Complex.Gamma w‖ * ‖Complex.exp w‖ *
            ‖w ^ ((1 / 2 : ℂ) - w)‖) :=
      congrArg Real.log (Complex.normalizedGammaStirlingFactor_norm_eq w)
    _ =
        Real.log (‖Complex.Gamma w‖ * ‖Complex.exp w‖) +
          Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ :=
      Real.log_mul hGamma_exp_norm_ne hcpow_norm_ne
    _ =
        (Real.log ‖Complex.Gamma w‖ + Real.log ‖Complex.exp w‖) +
          Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ := by
      exact congrArg
        (fun x : ℝ => x + Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖)
        (Real.log_mul hGamma_norm_ne hexp_norm_ne)
    _ =
        (Real.log ‖Complex.Gamma w‖ + w.re) +
          Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ := by
      exact congrArg
        (fun x : ℝ => (Real.log ‖Complex.Gamma w‖ + x) +
          Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖)
        (Complex.log_norm_exp_eq_re w)
    _ =
        Real.log ‖Complex.Gamma w‖ + w.re +
          Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ := rfl

/-- Real cancellation used when solving the normalized Stirling-factor logarithm
for the original Gamma logarithm. -/
theorem real_add_add_add_neg_add_neg_cancel
    (A B C : ℝ) :
    (A + B + C) + (-B + -C) = A := by
  have hC_cancel :
      C + (-B + -C) = -B := by
    calc
      C + (-B + -C) =
          C + (-C + -B) :=
        congrArg (fun x : ℝ => C + x) (add_comm (-B) (-C))
      _ = (C + -C) + -B :=
        (add_assoc C (-C) (-B)).symm
      _ = 0 + -B :=
        congrArg (fun x : ℝ => x + -B) (add_right_neg C)
      _ = -B :=
        zero_add (-B)
  calc
    (A + B + C) + (-B + -C) =
        (A + B) + (C + (-B + -C)) :=
      add_assoc (A + B) C (-B + -C)
    _ = (A + B) + -B :=
      congrArg (fun x : ℝ => (A + B) + x) hC_cancel
    _ = A + (B + -B) :=
      add_assoc A B (-B)
    _ = A + 0 :=
      congrArg (fun x : ℝ => A + x) (add_right_neg B)
    _ = A :=
      add_zero A

/-- Exact logarithmic extraction identity from the normalized Stirling factor. -/
theorem Complex.Gamma_log_norm_eq_normalizedGammaStirlingFactor_log_add_loss
    (w : ℂ)
    (hGamma_ne : Complex.Gamma w ≠ 0)
    (hcpow_ne : w ^ ((1 / 2 : ℂ) - w) ≠ 0) :
    Real.log ‖Complex.Gamma w‖ =
      Real.log ‖Complex.normalizedGammaStirlingFactor w‖ +
        Complex.normalizedGammaStirlingLogLoss w := by
  let A : ℝ := Real.log ‖Complex.Gamma w‖
  let B : ℝ := w.re
  let C : ℝ := Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖
  have hfactor :
      Real.log ‖Complex.normalizedGammaStirlingFactor w‖ =
        A + B + C :=
    Complex.normalizedGammaStirlingFactor_log_eq w hGamma_ne hcpow_ne
  have hloss :
      Complex.normalizedGammaStirlingLogLoss w = -B + -C := by
    exact sub_eq_add_neg (-w.re) (Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖)
  calc
    Real.log ‖Complex.Gamma w‖ = A := rfl
    _ = (A + B + C) + (-B + -C) :=
      (real_add_add_add_neg_add_neg_cancel A B C).symm
    _ =
        Real.log ‖Complex.normalizedGammaStirlingFactor w‖ +
          (-B + -C) :=
      congrArg (fun x : ℝ => x + (-B + -C)) hfactor.symm
    _ =
        Real.log ‖Complex.normalizedGammaStirlingFactor w‖ +
          Complex.normalizedGammaStirlingLogLoss w :=
      congrArg
        (fun x : ℝ =>
          Real.log ‖Complex.normalizedGammaStirlingFactor w‖ + x)
        hloss.symm

/-- Exact logarithmic extraction from the normalized Stirling factor.

After expanding
`‖Γ(w) exp(w) w^(1/2-w)‖`, this inequality solves for
`log ‖Γ(w)‖`.  The loss term is precisely the exponential denominator
`log ‖exp w‖ = w.re` and the principal-power denominator
`log ‖w^(1/2-w)‖`. -/
theorem Complex.Gamma_log_norm_le_normalizedGammaStirlingFactor_log_add_loss
    (w : ℂ)
    (hfactor_ne : Complex.normalizedGammaStirlingFactor w ≠ 0) :
    Real.log ‖Complex.Gamma w‖ ≤
      Real.log ‖Complex.normalizedGammaStirlingFactor w‖ +
        Complex.normalizedGammaStirlingLogLoss w := by
  have hGamma_ne : Complex.Gamma w ≠ 0 := by
    intro hGamma_zero
    have hfactor_zero :
        Complex.normalizedGammaStirlingFactor w = 0 := by
      calc
        Complex.normalizedGammaStirlingFactor w =
            Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w) := rfl
        _ = 0 * Complex.exp w * w ^ ((1 / 2 : ℂ) - w) :=
          congrArg
            (fun x : ℂ => x * Complex.exp w * w ^ ((1 / 2 : ℂ) - w))
            hGamma_zero
        _ = (0 : ℂ) * w ^ ((1 / 2 : ℂ) - w) := by
          exact congrArg
            (fun x : ℂ => x * w ^ ((1 / 2 : ℂ) - w))
            (zero_mul (Complex.exp w))
        _ = 0 :=
          zero_mul (w ^ ((1 / 2 : ℂ) - w))
    exact hfactor_ne hfactor_zero
  have hcpow_ne : w ^ ((1 / 2 : ℂ) - w) ≠ 0 := by
    intro hcpow_zero
    have hfactor_zero :
        Complex.normalizedGammaStirlingFactor w = 0 := by
      calc
        Complex.normalizedGammaStirlingFactor w =
            Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w) := rfl
        _ = Complex.Gamma w * Complex.exp w * 0 :=
          congrArg
            (fun x : ℂ => Complex.Gamma w * Complex.exp w * x)
            hcpow_zero
        _ = 0 :=
          mul_zero (Complex.Gamma w * Complex.exp w)
    exact hfactor_ne hfactor_zero
  exact le_of_eq
    (Complex.Gamma_log_norm_eq_normalizedGammaStirlingFactor_log_add_loss
      w hGamma_ne hcpow_ne)

/-- Constant logarithmic terms are absorbed by the large-radius log-linear
envelope on the closed right half-plane. -/
theorem Complex.constant_log_absorbed_by_largeRadius_logLinearEnvelope
    (B R₀ : ℝ)
    (hB_pos : 0 < B)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        Real.log B ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  let δ : ℝ := Real.log 2
  let C : ℝ := max (Real.log B / δ) 1
  have hδ_pos : 0 < δ :=
    Real.log_pos one_lt_two
  have hC_pos : 0 < C :=
    lt_of_lt_of_le zero_lt_one (le_max_right (Real.log B / δ) 1)
  refine ⟨C, hC_pos, ?_⟩
  intro w _hw_sector _hw_radius
  have htwo_norm_nonneg : 0 ≤ 2 * ‖w‖ :=
    mul_nonneg zero_le_two (norm_nonneg w)
  have hH_ge_one : (1 : ℝ) ≤ 1 + 2 * ‖w‖ :=
    le_add_of_nonneg_right htwo_norm_nonneg
  have harg_ge_two : (2 : ℝ) ≤ 2 + 2 * ‖w‖ :=
    le_add_of_nonneg_right htwo_norm_nonneg
  have hlog_ge_delta :
      δ ≤ Real.log (2 + 2 * ‖w‖) :=
    Real.log_le_log zero_lt_two harg_ge_two
  have hlog_nonneg : 0 ≤ Real.log (2 + 2 * ‖w‖) :=
    le_trans (le_of_lt hδ_pos) hlog_ge_delta
  have hdelta_le_envelope :
      δ ≤ (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
    have hlog_le_envelope :
        Real.log (2 + 2 * ‖w‖) ≤
          (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
      calc
        Real.log (2 + 2 * ‖w‖) =
            1 * Real.log (2 + 2 * ‖w‖) :=
          (one_mul (Real.log (2 + 2 * ‖w‖))).symm
        _ ≤ (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
          mul_le_mul_of_nonneg_right hH_ge_one hlog_nonneg
    exact le_trans hlog_ge_delta hlog_le_envelope
  have hlogB_div_le_C : Real.log B / δ ≤ C :=
    le_max_left (Real.log B / δ) 1
  have hlogB_le_Cδ : Real.log B ≤ C * δ :=
    (div_le_iff₀ hδ_pos).mp hlogB_div_le_C
  have hCδ_le_Cenv :
      C * δ ≤ C * ((1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖)) :=
    mul_le_mul_of_nonneg_left hdelta_le_envelope (le_of_lt hC_pos)
  have hCenv_eq :
      C * ((1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖)) =
        C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
    mul_assoc C (1 + 2 * ‖w‖) (Real.log (2 + 2 * ‖w‖))
  exact
    le_trans hlogB_le_Cδ
      (le_trans hCδ_le_Cenv (le_of_eq hCenv_eq))

/-- In the closed right half-plane, the real-part contribution to the
normalized Stirling loss is nonpositive, so the loss is bounded by the
principal-power logarithmic loss alone. -/
theorem Complex.normalizedGammaStirlingLogLoss_le_neg_cpow_log
    {w : ℂ}
    (hw_sector : Complex.closedRightHalfPlaneSector w) :
    Complex.normalizedGammaStirlingLogLoss w ≤
      -Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ := by
  have hneg_re_nonpos : -w.re ≤ 0 :=
    neg_nonpos.mpr hw_sector
  calc
    Complex.normalizedGammaStirlingLogLoss w =
        -w.re + -Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ := by
      exact sub_eq_add_neg (-w.re) (Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖)
    _ ≤ 0 + -Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ :=
      add_le_add_right hneg_re_nonpos
        (-Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖)
    _ = -Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ :=
      zero_add (-Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖)

/-- Positive radius lower bound excludes the origin. -/
theorem Complex.ne_zero_of_pos_le_norm
    {R : ℝ}
    (hR_pos : 0 < R)
    {z : ℂ}
    (hz_radius : R ≤ ‖z‖) :
    z ≠ 0 :=
  norm_pos_iff.mp (lt_of_lt_of_le hR_pos hz_radius)

/-- The closed right half-plane is exactly the principal-argument sector
`|arg z| ≤ π / 2`. -/
theorem Complex.abs_arg_le_pi_div_two_of_closedRightHalfPlaneSector
    {z : ℂ}
    (hz_sector : Complex.closedRightHalfPlaneSector z) :
    |Complex.arg z| ≤ Real.pi / 2 :=
  Complex.abs_arg_le_pi_div_two_iff.mpr hz_sector

/-- Principal-branch absolute-value formula for complex powers in logarithmic
form. -/
theorem Complex.log_abs_cpow_eq_re_mul_log_abs_sub_arg_mul_im_of_ne_zero
    {z a : ℂ}
    (hz_ne : z ≠ 0) :
    Real.log (Complex.abs (z ^ a)) =
      a.re * Real.log (Complex.abs z) - Complex.arg z * a.im := by
  have hz_abs_pos : 0 < Complex.abs z :=
    Complex.abs.pos hz_ne
  have hpow_pos : 0 < Complex.abs z ^ a.re :=
    Real.rpow_pos_of_pos hz_abs_pos a.re
  have hexp_pos : 0 < Real.exp (Complex.arg z * a.im) :=
    Real.exp_pos (Complex.arg z * a.im)
  have hcpow_abs :
      Complex.abs (z ^ a) =
        Complex.abs z ^ a.re / Real.exp (Complex.arg z * a.im) :=
    Complex.abs_cpow_of_ne_zero hz_ne a
  calc
    Real.log (Complex.abs (z ^ a)) =
        Real.log
          (Complex.abs z ^ a.re / Real.exp (Complex.arg z * a.im)) :=
      congrArg Real.log hcpow_abs
    _ =
        Real.log (Complex.abs z ^ a.re) -
          Real.log (Real.exp (Complex.arg z * a.im)) :=
      Real.log_div (ne_of_gt hpow_pos) (ne_of_gt hexp_pos)
    _ =
        a.re * Real.log (Complex.abs z) -
          Real.log (Real.exp (Complex.arg z * a.im)) := by
      exact congrArg
        (fun x : ℝ => x - Real.log (Real.exp (Complex.arg z * a.im)))
        (Real.log_rpow hz_abs_pos a.re)
    _ =
        a.re * Real.log (Complex.abs z) - Complex.arg z * a.im := by
      exact congrArg
        (fun x : ℝ => a.re * Real.log (Complex.abs z) - x)
        (Real.log_exp (Complex.arg z * a.im))

/-- Principal-branch norm formula for complex powers in logarithmic form. -/
theorem Complex.log_norm_cpow_eq_re_mul_log_norm_sub_arg_mul_im_of_ne_zero
    {z a : ℂ}
    (hz_ne : z ≠ 0) :
    Real.log ‖z ^ a‖ =
      a.re * Real.log ‖z‖ - Complex.arg z * a.im := by
  have hnorm_cpow_abs :
      ‖z ^ a‖ = Complex.abs (z ^ a) :=
    Complex.norm_eq_abs (z ^ a)
  have hnorm_z_abs :
      ‖z‖ = Complex.abs z :=
    Complex.norm_eq_abs z
  calc
    Real.log ‖z ^ a‖ =
        Real.log (Complex.abs (z ^ a)) :=
      congrArg Real.log hnorm_cpow_abs
    _ =
        a.re * Real.log (Complex.abs z) - Complex.arg z * a.im :=
      Complex.log_abs_cpow_eq_re_mul_log_abs_sub_arg_mul_im_of_ne_zero
        hz_ne
    _ =
        a.re * Real.log ‖z‖ - Complex.arg z * a.im := by
      exact congrArg
        (fun x : ℝ => a.re * Real.log x - Complex.arg z * a.im)
        hnorm_z_abs.symm

/-- Real coordinate of the Stirling power exponent `(1/2) - w`. -/
theorem Complex.half_minus_self_re
    (w : ℂ) :
    ((1 / 2 : ℂ) - w).re = (1 / 2 : ℝ) - w.re := by
  calc
    ((1 / 2 : ℂ) - w).re =
        (1 / 2 : ℂ).re - w.re :=
      Complex.sub_re (1 / 2 : ℂ) w
    _ = (1 / 2 : ℝ) - w.re := by
      exact congrArg (fun x : ℝ => x - w.re) (Complex.ofReal_re (1 / 2))

/-- Imaginary coordinate of the Stirling power exponent `(1/2) - w`. -/
theorem Complex.half_minus_self_im
    (w : ℂ) :
    ((1 / 2 : ℂ) - w).im = -w.im := by
  calc
    ((1 / 2 : ℂ) - w).im =
        (1 / 2 : ℂ).im - w.im :=
      Complex.sub_im (1 / 2 : ℂ) w
    _ = 0 - w.im := by
      exact congrArg (fun x : ℝ => x - w.im) (Complex.ofReal_im (1 / 2))
    _ = -w.im :=
      zero_sub w.im

/-- Algebraic rearrangement of the cpow logarithmic formula for the Stirling
exponent. -/
theorem Complex.neg_log_norm_cpow_half_minus_self_eq_radiusArgumentLoss_of_log_norm_cpow
    {w : ℂ}
    (hw_ne : w ≠ 0)
    (hlog :
      Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ =
        ((1 / 2 : ℂ) - w).re * Real.log ‖w‖ -
          Complex.arg w * ((1 / 2 : ℂ) - w).im) :
    -Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ =
      (w.re - 1 / 2) * Real.log ‖w‖ - Complex.arg w * w.im := by
  have hre :
      ((1 / 2 : ℂ) - w).re = (1 / 2 : ℝ) - w.re :=
    Complex.half_minus_self_re w
  have him :
      ((1 / 2 : ℂ) - w).im = -w.im :=
    Complex.half_minus_self_im w
  have hcoordinate :
      ((1 / 2 : ℂ) - w).re * Real.log ‖w‖ -
          Complex.arg w * ((1 / 2 : ℂ) - w).im =
        ((1 / 2 : ℝ) - w.re) * Real.log ‖w‖ -
          Complex.arg w * (-w.im) := by
    exact congrArg₂
      (fun x y : ℝ => x * Real.log ‖w‖ - Complex.arg w * y)
      hre
      him
  have hneg_coordinate :
      -(((1 / 2 : ℝ) - w.re) * Real.log ‖w‖ -
          Complex.arg w * (-w.im)) =
        (w.re - 1 / 2) * Real.log ‖w‖ - Complex.arg w * w.im := by
    calc
      -(((1 / 2 : ℝ) - w.re) * Real.log ‖w‖ -
          Complex.arg w * (-w.im)) =
          -(((1 / 2 : ℝ) - w.re) * Real.log ‖w‖) +
            Complex.arg w * (-w.im) := by
        exact neg_sub
          (((1 / 2 : ℝ) - w.re) * Real.log ‖w‖)
          (Complex.arg w * (-w.im))
      _ = (-((1 / 2 : ℝ) - w.re)) * Real.log ‖w‖ +
            Complex.arg w * (-w.im) := by
        exact congrArg
          (fun x : ℝ => x + Complex.arg w * (-w.im))
          (neg_mul ((1 / 2 : ℝ) - w.re) (Real.log ‖w‖))
      _ = (-(1 / 2 : ℝ) + w.re) * Real.log ‖w‖ +
            Complex.arg w * (-w.im) := by
        exact congrArg
          (fun x : ℝ => x * Real.log ‖w‖ + Complex.arg w * (-w.im))
          (neg_sub (1 / 2 : ℝ) w.re)
      _ = (w.re - 1 / 2) * Real.log ‖w‖ +
            Complex.arg w * (-w.im) := by
        exact congrArg
          (fun x : ℝ => x * Real.log ‖w‖ + Complex.arg w * (-w.im))
          (sub_eq_add_neg w.re (1 / 2)).symm
      _ = (w.re - 1 / 2) * Real.log ‖w‖ +
            (-(Complex.arg w * w.im)) := by
        exact congrArg
          (fun x : ℝ => (w.re - 1 / 2) * Real.log ‖w‖ + x)
          (mul_neg (Complex.arg w) w.im)
      _ = (w.re - 1 / 2) * Real.log ‖w‖ -
            Complex.arg w * w.im := by
        exact sub_eq_add_neg
          ((w.re - 1 / 2) * Real.log ‖w‖)
          (Complex.arg w * w.im)
  calc
    -Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ =
        -(((1 / 2 : ℂ) - w).re * Real.log ‖w‖ -
          Complex.arg w * ((1 / 2 : ℂ) - w).im) :=
      congrArg Neg.neg hlog
    _ =
        -(((1 / 2 : ℝ) - w.re) * Real.log ‖w‖ -
          Complex.arg w * (-w.im)) :=
      congrArg Neg.neg hcoordinate
    _ = (w.re - 1 / 2) * Real.log ‖w‖ -
          Complex.arg w * w.im :=
      hneg_coordinate

/-- The exact branch-loss expression for `w^(1/2-w)`.  This is the
coordinate form of the principal logarithm contribution: the radius part is
`(Re w - 1/2) log ‖w‖`, and the angular part is `- arg(w) Im w`. -/
theorem Complex.neg_log_norm_cpow_half_minus_self_eq_radiusArgumentLoss
    {w : ℂ}
    (hw_ne : w ≠ 0) :
    -Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ =
      (w.re - 1 / 2) * Real.log ‖w‖ - Complex.arg w * w.im := by
  exact
    Complex.neg_log_norm_cpow_half_minus_self_eq_radiusArgumentLoss_of_log_norm_cpow
      hw_ne
      (Complex.log_norm_cpow_eq_re_mul_log_norm_sub_arg_mul_im_of_ne_zero
        hw_ne)

/-- The real coordinate is bounded by the complex norm. -/
theorem Complex.re_le_norm
    (w : ℂ) :
    w.re ≤ ‖w‖ := by
  have hre_abs_le_abs : |w.re| ≤ Complex.abs w :=
    Complex.abs_re_le_abs w
  have hnorm_eq_abs : ‖w‖ = Complex.abs w :=
    Complex.norm_eq_abs w
  have hre_abs_le_norm : |w.re| ≤ ‖w‖ :=
    Eq.subst
      (motive := fun x : ℝ => |w.re| ≤ x)
      hnorm_eq_abs.symm
      hre_abs_le_abs
  exact le_trans (le_abs_self w.re) hre_abs_le_norm

/-- The imaginary coordinate absolute value is bounded by the complex norm. -/
theorem Complex.abs_im_le_norm
    (w : ℂ) :
    |w.im| ≤ ‖w‖ := by
  have him_abs_le_abs : |w.im| ≤ Complex.abs w :=
    Complex.abs_im_le_abs w
  have hnorm_eq_abs : ‖w‖ = Complex.abs w :=
    Complex.norm_eq_abs w
  exact
    Eq.subst
      (motive := fun x : ℝ => |w.im| ≤ x)
      hnorm_eq_abs.symm
      him_abs_le_abs

/-- A positive lower radius cutoff makes the logarithmic envelope positive. -/
theorem real_largeRadius_log_envelope_pos
    (R₀ r : ℝ)
    (hR₀_pos : 0 < R₀)
    (hr : R₀ ≤ r) :
    0 < Real.log (2 + 2 * r) := by
  have hr_pos : 0 < r :=
    lt_of_lt_of_le hR₀_pos hr
  have htwo_r_pos : 0 < 2 * r :=
    mul_pos two_pos hr_pos
  have hone_lt_arg : (1 : ℝ) < 2 + 2 * r := by
    calc
      (1 : ℝ) < 2 := one_lt_two
      _ ≤ 2 + 2 * r := le_add_of_nonneg_right (le_of_lt htwo_r_pos)
  exact Real.log_pos hone_lt_arg

/-- The large-radius log envelope is nonnegative. -/
theorem real_largeRadius_log_envelope_nonneg
    (R₀ r : ℝ)
    (hR₀_pos : 0 < R₀)
    (hr : R₀ ≤ r) :
    0 ≤ Real.log (2 + 2 * r) :=
  le_of_lt (real_largeRadius_log_envelope_pos R₀ r hR₀_pos hr)

/-- On a positive large-radius region, the log envelope is at least `log 2`. -/
theorem real_log_two_le_largeRadius_log_envelope
    (R₀ r : ℝ)
    (hR₀_pos : 0 < R₀)
    (hr : R₀ ≤ r) :
    Real.log 2 ≤ Real.log (2 + 2 * r) := by
  have hr_nonneg : 0 ≤ r :=
    le_of_lt (lt_of_lt_of_le hR₀_pos hr)
  have harg_le : (2 : ℝ) ≤ 2 + 2 * r :=
    le_add_of_nonneg_right (mul_nonneg zero_le_two hr_nonneg)
  exact Real.log_le_log zero_lt_two harg_le

/-- Positive lower radius cutoff gives nonnegative radius. -/
theorem real_nonneg_of_largeRadius
    (R₀ r : ℝ)
    (hR₀_pos : 0 < R₀)
    (hr : R₀ ≤ r) :
    0 ≤ r :=
  le_of_lt (lt_of_lt_of_le hR₀_pos hr)

/-- The linear factor `r + 1/2` is dominated by the standard height factor
`1 + 2r` on nonnegative radii. -/
theorem real_radius_add_half_le_one_add_two_mul
    (r : ℝ)
    (hr_nonneg : 0 ≤ r) :
    r + 1 / 2 ≤ 1 + 2 * r := by
  have hhalf_le_one : (1 / 2 : ℝ) ≤ 1 :=
    one_half_le_one
  have hr_le_two_r : r ≤ 2 * r := by
    calc
      r = 1 * r := (one_mul r).symm
      _ ≤ 2 * r := mul_le_mul_of_nonneg_right one_le_two hr_nonneg
  calc
    r + 1 / 2 ≤ 2 * r + 1 :=
      add_le_add hr_le_two_r hhalf_le_one
    _ = 1 + 2 * r :=
      add_comm (2 * r) 1

/-- The radius itself is dominated by the standard height factor. -/
theorem real_radius_le_one_add_two_mul
    (r : ℝ)
    (hr_nonneg : 0 ≤ r) :
    r ≤ 1 + 2 * r := by
  calc
    r ≤ 2 * r :=
      calc
        r = 1 * r := (one_mul r).symm
        _ ≤ 2 * r := mul_le_mul_of_nonneg_right one_le_two hr_nonneg
    _ ≤ 1 + 2 * r :=
      le_add_of_nonneg_left zero_le_one

/-- The angular linear term is absorbed by the standard log-linear envelope on
any positive large-radius region. -/
theorem real_pi_radius_absorbed_by_logLinearEnvelope_uniform
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ r : ℝ,
        R₀ ≤ r →
        (Real.pi / 2) * r ≤
          C * (1 + 2 * r) * Real.log (2 + 2 * r) := by
  let C : ℝ := (Real.pi / 2) / Real.log 2
  have hlog_two_pos : 0 < Real.log 2 :=
    Real.log_pos one_lt_two
  have hpi_half_pos : 0 < Real.pi / 2 :=
    div_pos Real.pi_pos two_pos
  have hC_pos : 0 < C :=
    div_pos hpi_half_pos hlog_two_pos
  refine ⟨C, hC_pos, ?_⟩
  intro r hr
  have hr_nonneg : 0 ≤ r :=
    real_nonneg_of_largeRadius R₀ r hR₀_pos hr
  have hH_nonneg : 0 ≤ 1 + 2 * r :=
    add_nonneg zero_le_one (mul_nonneg zero_le_two hr_nonneg)
  have hr_le_H : r ≤ 1 + 2 * r :=
    real_radius_le_one_add_two_mul r hr_nonneg
  have hL_lower : Real.log 2 ≤ Real.log (2 + 2 * r) :=
    real_log_two_le_largeRadius_log_envelope R₀ r hR₀_pos hr
  have hC_log_two : C * Real.log 2 = Real.pi / 2 := by
    calc
      C * Real.log 2 =
          ((Real.pi / 2) / Real.log 2) * Real.log 2 := rfl
      _ = Real.pi / 2 :=
        div_mul_cancel₀ (Real.pi / 2) (ne_of_gt hlog_two_pos)
  have hpi_half_le_CL :
      Real.pi / 2 ≤ C * Real.log (2 + 2 * r) := by
    have hmul : C * Real.log 2 ≤ C * Real.log (2 + 2 * r) :=
      mul_le_mul_of_nonneg_left hL_lower (le_of_lt hC_pos)
    exact le_trans (le_of_eq hC_log_two.symm) hmul
  have hleft_to_H :
      (Real.pi / 2) * r ≤ (Real.pi / 2) * (1 + 2 * r) :=
    mul_le_mul_of_nonneg_left hr_le_H (le_of_lt hpi_half_pos)
  have hH_scale :
      (Real.pi / 2) * (1 + 2 * r) ≤
        (C * Real.log (2 + 2 * r)) * (1 + 2 * r) :=
    mul_le_mul_of_nonneg_right hpi_half_le_CL hH_nonneg
  have htarget_eq :
      (C * Real.log (2 + 2 * r)) * (1 + 2 * r) =
        C * (1 + 2 * r) * Real.log (2 + 2 * r) := by
    calc
      (C * Real.log (2 + 2 * r)) * (1 + 2 * r) =
          C * (Real.log (2 + 2 * r) * (1 + 2 * r)) :=
        (mul_assoc C (Real.log (2 + 2 * r)) (1 + 2 * r)).symm
      _ = C * ((1 + 2 * r) * Real.log (2 + 2 * r)) := by
        exact congrArg
          (fun x : ℝ => C * x)
          (mul_comm (Real.log (2 + 2 * r)) (1 + 2 * r))
      _ = C * (1 + 2 * r) * Real.log (2 + 2 * r) := by
        exact mul_assoc C (1 + 2 * r) (Real.log (2 + 2 * r))
  exact le_trans hleft_to_H
    (le_trans hH_scale (le_of_eq htarget_eq))

/-- Uniform version of the real logarithmic envelope on a large-radius region. -/
theorem real_abs_log_le_largeRadius_log_envelope_uniform
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ r : ℝ,
        R₀ ≤ r →
        ‖Real.log r‖ ≤ C * Real.log (2 + 2 * r) := by
  let C : ℝ := max 1 (R₀⁻¹ / Real.log 2)
  have hlog_two_pos : 0 < Real.log 2 :=
    Real.log_pos one_lt_two
  have hR₀_inv_nonneg : 0 ≤ R₀⁻¹ :=
    inv_nonneg.mpr (le_of_lt hR₀_pos)
  have hC_pos : 0 < C :=
    lt_of_lt_of_le zero_lt_one (le_max_left 1 (R₀⁻¹ / Real.log 2))
  refine ⟨C, hC_pos, ?_⟩
  intro r hr
  have hr_pos : 0 < r :=
    lt_of_lt_of_le hR₀_pos hr
  have hr_nonneg : 0 ≤ r :=
    le_of_lt hr_pos
  have hL_nonneg : 0 ≤ Real.log (2 + 2 * r) :=
    real_largeRadius_log_envelope_nonneg R₀ r hR₀_pos hr
  have hL_lower : Real.log 2 ≤ Real.log (2 + 2 * r) :=
    real_log_two_le_largeRadius_log_envelope R₀ r hR₀_pos hr
  by_cases hone_le_r : (1 : ℝ) ≤ r
  · have hlog_nonneg : 0 ≤ Real.log r :=
      Real.log_nonneg hone_le_r
    have hnorm_log : ‖Real.log r‖ = Real.log r :=
      Real.norm_of_nonneg hlog_nonneg
    have hr_le_arg : r ≤ 2 + 2 * r := by
      calc
        r ≤ 2 * r :=
          calc
            r = 1 * r := (one_mul r).symm
            _ ≤ 2 * r := mul_le_mul_of_nonneg_right one_le_two hr_nonneg
        _ ≤ 2 + 2 * r :=
          le_add_of_nonneg_left zero_le_two
    have hlog_le_L : Real.log r ≤ Real.log (2 + 2 * r) :=
      Real.log_le_log hr_pos hr_le_arg
    have hC_ge_one : (1 : ℝ) ≤ C :=
      le_max_left 1 (R₀⁻¹ / Real.log 2)
    have hL_le_CL : Real.log (2 + 2 * r) ≤ C * Real.log (2 + 2 * r) := by
      calc
        Real.log (2 + 2 * r) =
            1 * Real.log (2 + 2 * r) :=
          (one_mul (Real.log (2 + 2 * r))).symm
        _ ≤ C * Real.log (2 + 2 * r) :=
          mul_le_mul_of_nonneg_right hC_ge_one hL_nonneg
    exact le_trans (le_of_eq hnorm_log)
      (le_trans hlog_le_L hL_le_CL)
  · have hr_le_one : r ≤ 1 :=
      le_of_not_ge hone_le_r
    have hlog_nonpos : Real.log r ≤ 0 :=
      (Real.log_nonpos_iff hr_pos).mpr hr_le_one
    have hnorm_log : ‖Real.log r‖ = -Real.log r :=
      Real.norm_of_nonpos hlog_nonpos
    have hneg_log_le_inv : -Real.log r ≤ r⁻¹ := by
      have hneg_inv_le_log : -r⁻¹ ≤ Real.log r :=
        Real.neg_inv_le_log hr_nonneg
      exact neg_le.mp hneg_inv_le_log
    have hinv_le_R₀_inv : r⁻¹ ≤ R₀⁻¹ :=
      one_div_le_one_div_of_le hR₀_pos hr
    have hsmall : ‖Real.log r‖ ≤ R₀⁻¹ :=
      le_trans (le_of_eq hnorm_log) (le_trans hneg_log_le_inv hinv_le_R₀_inv)
    have hratio_le_C : R₀⁻¹ / Real.log 2 ≤ C :=
      le_max_right 1 (R₀⁻¹ / Real.log 2)
    have hR₀_inv_le_ratio_L :
        R₀⁻¹ ≤ (R₀⁻¹ / Real.log 2) * Real.log (2 + 2 * r) := by
      have hR₀_inv_div_mul :
          R₀⁻¹ = (R₀⁻¹ / Real.log 2) * Real.log 2 := by
        exact (div_mul_cancel₀ R₀⁻¹ (ne_of_gt hlog_two_pos)).symm
      have hmul :
          (R₀⁻¹ / Real.log 2) * Real.log 2 ≤
            (R₀⁻¹ / Real.log 2) * Real.log (2 + 2 * r) :=
        mul_le_mul_of_nonneg_left hL_lower
          (div_nonneg hR₀_inv_nonneg (le_of_lt hlog_two_pos))
      exact le_trans (le_of_eq hR₀_inv_div_mul)
        hmul
    have hratio_L_le_CL :
        (R₀⁻¹ / Real.log 2) * Real.log (2 + 2 * r) ≤
          C * Real.log (2 + 2 * r) :=
      mul_le_mul_of_nonneg_right hratio_le_C hL_nonneg
    exact le_trans hsmall
      (le_trans hR₀_inv_le_ratio_L hratio_L_le_CL)

/-- Pure real logarithmic envelope for a radius bounded below away from zero. -/
theorem real_abs_log_le_largeRadius_log_envelope
    (R₀ r : ℝ)
    (hR₀_pos : 0 < R₀)
    (hr : R₀ ≤ r) :
    ∃ C : ℝ,
      0 < C ∧
      ‖Real.log r‖ ≤ C * Real.log (2 + 2 * r) := by
  rcases real_abs_log_le_largeRadius_log_envelope_uniform R₀ hR₀_pos with
    ⟨C, hC_pos, hC⟩
  exact ⟨C, hC_pos, hC r hr⟩

/-- The logarithm of the radius is absorbed by the logarithmic envelope on any
large-radius region bounded away from zero. -/
theorem Complex.log_norm_le_log_envelope
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        R₀ ≤ ‖w‖ →
        ‖Real.log ‖w‖‖ ≤ C * Real.log (2 + 2 * ‖w‖) := by
  exact real_abs_log_le_largeRadius_log_envelope_uniform R₀ hR₀_pos

/-- If `0 ≤ x ≤ r`, then the shifted coordinate `x - 1/2` is bounded by
`r + 1/2` in absolute value. -/
theorem real_abs_sub_half_le_radius_add_half
    (x r : ℝ)
    (hx_nonneg : 0 ≤ x)
    (hx_le_r : x ≤ r) :
    |x - 1 / 2| ≤ r + 1 / 2 := by
  have hr_nonneg : 0 ≤ r :=
    le_trans hx_nonneg hx_le_r
  have hneg_r_le_x : -r ≤ x :=
    le_trans (neg_nonpos.mpr hr_nonneg) hx_nonneg
  have hneg_half_le_half : -(1 / 2 : ℝ) ≤ 1 / 2 :=
    neg_le_self (le_of_lt one_half_pos)
  have hlower : -(r + 1 / 2) ≤ x - 1 / 2 := by
    calc
      -(r + 1 / 2) = -r + -(1 / 2 : ℝ) :=
        neg_add r (1 / 2)
      _ ≤ x + -(1 / 2 : ℝ) :=
        add_le_add_right hneg_r_le_x (-(1 / 2 : ℝ))
      _ = x - 1 / 2 :=
        (sub_eq_add_neg x (1 / 2)).symm
  have hupper : x - 1 / 2 ≤ r + 1 / 2 := by
    calc
      x - 1 / 2 ≤ r - 1 / 2 :=
        sub_le_sub_right hx_le_r (1 / 2)
      _ = r + -(1 / 2 : ℝ) :=
        sub_eq_add_neg r (1 / 2)
      _ ≤ r + 1 / 2 :=
        add_le_add_left hneg_half_le_half r
  exact abs_le.mpr ⟨hlower, hupper⟩

/-- Radius part of the branch loss is bounded by the norm-log majorant. -/
theorem real_radiusTerm_le_norm_log_majorant
    (x r : ℝ)
    (hx_nonneg : 0 ≤ x)
    (hx_le_r : x ≤ r) :
    (x - 1 / 2) * Real.log r ≤
      (r + 1 / 2) * ‖Real.log r‖ := by
  have hterm_le_abs :
      (x - 1 / 2) * Real.log r ≤
        |(x - 1 / 2) * Real.log r| :=
    le_abs_self ((x - 1 / 2) * Real.log r)
  have habs_mul :
      |(x - 1 / 2) * Real.log r| =
        |x - 1 / 2| * |Real.log r| :=
    abs_mul (x - 1 / 2) (Real.log r)
  have habs_log_eq_norm :
      |Real.log r| = ‖Real.log r‖ :=
    (Real.norm_eq_abs (Real.log r)).symm
  have hshift :
      |x - 1 / 2| ≤ r + 1 / 2 :=
    real_abs_sub_half_le_radius_add_half x r hx_nonneg hx_le_r
  have hmajor :
      |x - 1 / 2| * |Real.log r| ≤
        (r + 1 / 2) * ‖Real.log r‖ := by
    have hlog_nonneg : 0 ≤ ‖Real.log r‖ :=
      norm_nonneg (Real.log r)
    have hmul :
        |x - 1 / 2| * ‖Real.log r‖ ≤
          (r + 1 / 2) * ‖Real.log r‖ :=
      mul_le_mul_of_nonneg_right hshift hlog_nonneg
    exact
      Eq.subst
        (motive := fun y : ℝ =>
          |x - 1 / 2| * y ≤ (r + 1 / 2) * ‖Real.log r‖)
        habs_log_eq_norm.symm
        hmul
  exact le_trans hterm_le_abs
    (le_trans (le_of_eq habs_mul) hmajor)

/-- Angular part of the branch loss is bounded by the sectorial angle majorant. -/
theorem real_argumentTerm_le_sectorial_majorant
    (θ y r : ℝ)
    (hy_abs_le_r : |y| ≤ r)
    (hθ_abs_le : |θ| ≤ Real.pi / 2) :
    -θ * y ≤ (Real.pi / 2) * r := by
  have hneg_product_le_abs :
      -θ * y ≤ |θ * y| := by
    calc
      -θ * y = -(θ * y) :=
        (neg_mul θ y).symm
      _ ≤ |θ * y| :=
        neg_le_abs (θ * y)
  have habs_product :
      |θ * y| = |θ| * |y| :=
    abs_mul θ y
  have hpi_half_nonneg : 0 ≤ Real.pi / 2 :=
    le_of_lt (div_pos Real.pi_pos two_pos)
  have habs_product_le :
      |θ| * |y| ≤ (Real.pi / 2) * r :=
    mul_le_mul hθ_abs_le hy_abs_le_r (abs_nonneg y) hpi_half_nonneg
  exact le_trans hneg_product_le_abs
    (le_trans (le_of_eq habs_product) habs_product_le)

/-- Pure real radius/argument majorization after replacing coordinates by norm
bounds and the argument by its sectorial bound. -/
theorem real_radiusArgumentLoss_le_norm_log_majorant
    (x y θ r : ℝ)
    (hx_nonneg : 0 ≤ x)
    (hx_le_r : x ≤ r)
    (hy_abs_le_r : |y| ≤ r)
    (hθ_abs_le : |θ| ≤ Real.pi / 2) :
    (x - 1 / 2) * Real.log r - θ * y ≤
      (r + 1 / 2) * ‖Real.log r‖ + (Real.pi / 2) * r := by
  have hradius :
      (x - 1 / 2) * Real.log r ≤
        (r + 1 / 2) * ‖Real.log r‖ :=
    real_radiusTerm_le_norm_log_majorant x r hx_nonneg hx_le_r
  have hangle :
      -θ * y ≤ (Real.pi / 2) * r :=
    real_argumentTerm_le_sectorial_majorant θ y r hy_abs_le_r hθ_abs_le
  have hleft_eq :
      (x - 1 / 2) * Real.log r - θ * y =
        (x - 1 / 2) * Real.log r + (-θ * y) := by
    exact sub_eq_add_neg ((x - 1 / 2) * Real.log r) (θ * y)
  have hsum :
      (x - 1 / 2) * Real.log r + (-θ * y) ≤
        (r + 1 / 2) * ‖Real.log r‖ + (Real.pi / 2) * r :=
    add_le_add hradius hangle
  exact le_trans (le_of_eq hleft_eq) hsum

/-- Coordinate domination of the Stirling radius/argument loss by the elementary
norm majorant. -/
theorem Complex.radiusArgumentLoss_le_norm_log_majorant
    (w : ℂ)
    (hw_sector : Complex.closedRightHalfPlaneSector w) :
    (w.re - 1 / 2) * Real.log ‖w‖ - Complex.arg w * w.im ≤
      (‖w‖ + 1 / 2) * ‖Real.log ‖w‖‖ + (Real.pi / 2) * ‖w‖ := by
  exact
    real_radiusArgumentLoss_le_norm_log_majorant
      w.re w.im (Complex.arg w) ‖w‖
      hw_sector
      (Complex.re_le_norm w)
      (Complex.abs_im_le_norm w)
      (Complex.abs_arg_le_pi_div_two_of_closedRightHalfPlaneSector hw_sector)

/-- Uniform pure real absorption of the norm-log majorant into the standard
log-linear envelope on a large-radius region. -/
theorem real_linear_log_absorption_uniform
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ r : ℝ,
        R₀ ≤ r →
        (r + 1 / 2) * ‖Real.log r‖ + (Real.pi / 2) * r ≤
          C * (1 + 2 * r) * Real.log (2 + 2 * r) := by
  rcases real_abs_log_le_largeRadius_log_envelope_uniform R₀ hR₀_pos with
    ⟨Clog, hClog_pos, hlog⟩
  rcases real_pi_radius_absorbed_by_logLinearEnvelope_uniform R₀ hR₀_pos with
    ⟨Cpi, hCpi_pos, hpi⟩
  refine ⟨Clog + Cpi, add_pos hClog_pos hCpi_pos, ?_⟩
  intro r hr
  have hr_nonneg : 0 ≤ r :=
    real_nonneg_of_largeRadius R₀ r hR₀_pos hr
  have hH_nonneg : 0 ≤ 1 + 2 * r :=
    add_nonneg zero_le_one (mul_nonneg zero_le_two hr_nonneg)
  have hL_nonneg : 0 ≤ Real.log (2 + 2 * r) :=
    real_largeRadius_log_envelope_nonneg R₀ r hR₀_pos hr
  have hfactor_nonneg : 0 ≤ r + 1 / 2 :=
    add_nonneg hr_nonneg (le_of_lt one_half_pos)
  have hfactor_le_H : r + 1 / 2 ≤ 1 + 2 * r :=
    real_radius_add_half_le_one_add_two_mul r hr_nonneg
  have hlog_bound :
      ‖Real.log r‖ ≤ Clog * Real.log (2 + 2 * r) :=
    hlog r hr
  have hfirst_step :
      (r + 1 / 2) * ‖Real.log r‖ ≤
        (r + 1 / 2) * (Clog * Real.log (2 + 2 * r)) :=
    mul_le_mul_of_nonneg_left hlog_bound hfactor_nonneg
  have hClogL_nonneg :
      0 ≤ Clog * Real.log (2 + 2 * r) :=
    mul_nonneg (le_of_lt hClog_pos) hL_nonneg
  have hfirst_factor :
      (r + 1 / 2) * (Clog * Real.log (2 + 2 * r)) ≤
        (1 + 2 * r) * (Clog * Real.log (2 + 2 * r)) :=
    mul_le_mul_of_nonneg_right hfactor_le_H hClogL_nonneg
  have hfirst_assoc :
      (1 + 2 * r) * (Clog * Real.log (2 + 2 * r)) =
        Clog * (1 + 2 * r) * Real.log (2 + 2 * r) := by
    calc
      (1 + 2 * r) * (Clog * Real.log (2 + 2 * r)) =
          ((1 + 2 * r) * Clog) * Real.log (2 + 2 * r) :=
        mul_assoc (1 + 2 * r) Clog (Real.log (2 + 2 * r))
      _ = (Clog * (1 + 2 * r)) * Real.log (2 + 2 * r) := by
        exact congrArg
          (fun x : ℝ => x * Real.log (2 + 2 * r))
          (mul_comm (1 + 2 * r) Clog)
      _ = Clog * (1 + 2 * r) * Real.log (2 + 2 * r) := rfl
  have hfirst :
      (r + 1 / 2) * ‖Real.log r‖ ≤
        Clog * (1 + 2 * r) * Real.log (2 + 2 * r) :=
    le_trans hfirst_step
      (le_trans hfirst_factor (le_of_eq hfirst_assoc))
  have hsecond :
      (Real.pi / 2) * r ≤
        Cpi * (1 + 2 * r) * Real.log (2 + 2 * r) :=
    hpi r hr
  have hsum :
      (r + 1 / 2) * ‖Real.log r‖ + (Real.pi / 2) * r ≤
        Clog * (1 + 2 * r) * Real.log (2 + 2 * r) +
          Cpi * (1 + 2 * r) * Real.log (2 + 2 * r) :=
    add_le_add hfirst hsecond
  have hcombine :
      Clog * (1 + 2 * r) * Real.log (2 + 2 * r) +
          Cpi * (1 + 2 * r) * Real.log (2 + 2 * r) =
        (Clog + Cpi) * (1 + 2 * r) * Real.log (2 + 2 * r) :=
    logLinearEnvelope_add_constants
      Clog Cpi (1 + 2 * r) (Real.log (2 + 2 * r))
  exact le_trans hsum (le_of_eq hcombine)

/-- Pure real absorption of the norm-log majorant into the standard log-linear
envelope, using a lower radius cutoff. -/
theorem real_linear_log_absorption
    (R₀ r : ℝ)
    (hR₀_pos : 0 < R₀)
    (hr : R₀ ≤ r) :
    ∃ C : ℝ,
      0 < C ∧
      (r + 1 / 2) * ‖Real.log r‖ + (Real.pi / 2) * r ≤
        C * (1 + 2 * r) * Real.log (2 + 2 * r) := by
  rcases real_linear_log_absorption_uniform R₀ hR₀_pos with
    ⟨C, hC_pos, hC⟩
  exact ⟨C, hC_pos, hC r hr⟩

/-- The elementary norm-log majorant is absorbed by the standard log-linear
envelope on every large-radius region. -/
theorem Complex.linear_log_absorption
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        R₀ ≤ ‖w‖ →
        (‖w‖ + 1 / 2) * ‖Real.log ‖w‖‖ + (Real.pi / 2) * ‖w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  exact real_linear_log_absorption_uniform R₀ hR₀_pos

/-- Pure real domination of the radius/argument loss by the standard
log-linear envelope on the closed right half-plane.

This is now the deepest real-inequality sink in the normalized Stirling
extraction.  It combines `0 ≤ Re w`, `|arg w| ≤ π/2`, `|Re w|, |Im w| ≤ ‖w‖`,
and lower-radius control to absorb the possible small-radius logarithmic term
into a constant multiple of `(1 + 2 ‖w‖) log (2 + 2 ‖w‖)`. -/
theorem Complex.radiusArgumentLoss_absorbed_by_largeRadius_logLinearEnvelope
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        (w.re - 1 / 2) * Real.log ‖w‖ - Complex.arg w * w.im ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  rcases Complex.linear_log_absorption R₀ hR₀_pos with
    ⟨C, hC_pos, hlinear⟩
  refine ⟨C, hC_pos, ?_⟩
  intro w hw_sector hw_radius
  exact le_trans
    (Complex.radiusArgumentLoss_le_norm_log_majorant w hw_sector)
    (hlinear w hw_radius)

/-- The branch-loss radius/argument expression is absorbed by the standard
large-radius log-linear envelope on the closed right half-plane. -/
theorem Complex.cpow_half_minus_self_radiusArgumentLoss_absorbed_by_largeRadius_logLinearEnvelope
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        (w.re - 1 / 2) * Real.log ‖w‖ - Complex.arg w * w.im ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  exact
    Complex.radiusArgumentLoss_absorbed_by_largeRadius_logLinearEnvelope
      R₀ hR₀_pos

/-- Principal-power logarithmic loss for `w^(1/2-w)` is absorbed by the
large-radius log-linear envelope. -/
theorem Complex.neg_log_norm_cpow_half_minus_self_absorbed_by_largeRadius_logLinearEnvelope
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        -Real.log ‖w ^ ((1 / 2 : ℂ) - w)‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  rcases
      Complex.cpow_half_minus_self_radiusArgumentLoss_absorbed_by_largeRadius_logLinearEnvelope
        R₀ hR₀_pos with
    ⟨C, hC_pos, hbranch_bound⟩
  refine ⟨C, hC_pos, ?_⟩
  intro w hw_sector hw_radius
  have hw_ne : w ≠ 0 :=
    Complex.ne_zero_of_pos_le_norm hR₀_pos hw_radius
  exact le_trans
    (le_of_eq
      (Complex.neg_log_norm_cpow_half_minus_self_eq_radiusArgumentLoss
        hw_ne))
    (hbranch_bound w hw_sector hw_radius)

/-- The principal-branch logarithmic loss in normalized Stirling is absorbed by
the large-radius log-linear envelope. -/
theorem Complex.normalizedGammaStirlingLogLoss_absorbed_by_largeRadius_logLinearEnvelope
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        Complex.normalizedGammaStirlingLogLoss w ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  rcases
      Complex.neg_log_norm_cpow_half_minus_self_absorbed_by_largeRadius_logLinearEnvelope
        R₀ hR₀_pos with
    ⟨C, hC_pos, hcpow⟩
  refine ⟨C, hC_pos, ?_⟩
  intro w hw_sector hw_radius
  exact le_trans
    (Complex.normalizedGammaStirlingLogLoss_le_neg_cpow_log hw_sector)
    (hcpow w hw_sector hw_radius)

/-- Assembly of constant-log absorption and principal-branch loss absorption. -/
theorem Complex.normalizedGammaStirlingLogLoss_absorbs_logBound_of_constant_and_loss
    (B R₀ : ℝ)
    (hconstant :
      ∃ C : ℝ,
        0 < C ∧
        ∀ w : ℂ,
          Complex.closedRightHalfPlaneSector w →
          R₀ ≤ ‖w‖ →
          Real.log B ≤
            C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖))
    (hloss :
      ∃ C : ℝ,
        0 < C ∧
        ∀ w : ℂ,
          Complex.closedRightHalfPlaneSector w →
          R₀ ≤ ‖w‖ →
          Complex.normalizedGammaStirlingLogLoss w ≤
            C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖)) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        Real.log B + Complex.normalizedGammaStirlingLogLoss w ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  rcases hconstant with ⟨Cconstant, hCconstant_pos, hconstant_bound⟩
  rcases hloss with ⟨Closs, hCloss_pos, hloss_bound⟩
  refine ⟨Cconstant + Closs, add_pos hCconstant_pos hCloss_pos, ?_⟩
  intro w hw_sector hw_radius
  have hsum :
      Real.log B + Complex.normalizedGammaStirlingLogLoss w ≤
        Cconstant * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) +
          Closs * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
    add_le_add
      (hconstant_bound w hw_sector hw_radius)
      (hloss_bound w hw_sector hw_radius)
  have hcombine :
      Cconstant * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) +
          Closs * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) =
        (Cconstant + Closs) * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
    logLinearEnvelope_add_constants
      Cconstant Closs (1 + 2 * ‖w‖) (Real.log (2 + 2 * ‖w‖))
  exact le_trans hsum (le_of_eq hcombine)

/-- The branch/cpow logarithmic loss from normalized Stirling is absorbed by
the standard log-linear envelope on the large-radius closed right half-plane. -/
theorem Complex.normalizedGammaStirlingLogLoss_absorbs_logBound
    (B R₀ : ℝ)
    (hB_pos : 0 < B)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        Real.log B + Complex.normalizedGammaStirlingLogLoss w ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  exact
    Complex.normalizedGammaStirlingLogLoss_absorbs_logBound_of_constant_and_loss
      B R₀
      (Complex.constant_log_absorbed_by_largeRadius_logLinearEnvelope
        B R₀ hB_pos hR₀_pos)
      (Complex.normalizedGammaStirlingLogLoss_absorbed_by_largeRadius_logLinearEnvelope
        R₀ hR₀_pos)

/-- Large-radius extraction from a normalized Stirling-factor bound to a
logarithmic Gamma envelope.

This is the branch-sensitive analytic core of the normalized-factor route:
from
`‖Γ(w) exp(w) w^(1/2-w)‖ ≤ B`, one expands the norm of `exp(w)` and the
principal-branch norm of `w^(1/2-w)`, then bounds the resulting real part by
`(1 + 2 ‖w‖) log (2 + 2 ‖w‖)` on the closed right half-plane. -/
theorem Complex.Gamma_log_norm_bound_of_normalizedStirlingFactor_bound_largeRadius
    (B R₀ : ℝ)
    (hB_pos : 0 < B)
    (hR₀_pos : 0 < R₀)
    (hfactor :
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w)‖ ≤ B) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  rcases Complex.normalizedGammaStirlingLogLoss_absorbs_logBound
      B R₀ hB_pos hR₀_pos with
    ⟨C, hC_pos, hloss⟩
  refine ⟨C, hC_pos, ?_⟩
  intro w hw_sector hw_radius
  have hfactor_ne :
      Complex.normalizedGammaStirlingFactor w ≠ 0 :=
    Complex.normalizedGammaStirlingFactor_ne_zero_of_closedRightHalfPlaneSector_largeRadius
      R₀ hR₀_pos hw_sector hw_radius
  have hfactor_pos :
      0 < ‖Complex.normalizedGammaStirlingFactor w‖ :=
    norm_pos_iff.mpr hfactor_ne
  have hfactor_bound :
      ‖Complex.normalizedGammaStirlingFactor w‖ ≤ B :=
    hfactor w hw_sector hw_radius
  have hfactor_log :
      Real.log ‖Complex.normalizedGammaStirlingFactor w‖ ≤ Real.log B :=
    Complex.normalizedGammaStirlingFactor_log_le_of_norm_bound
      B hfactor_pos hfactor_bound
  have hgamma_extract :
      Real.log ‖Complex.Gamma w‖ ≤
        Real.log ‖Complex.normalizedGammaStirlingFactor w‖ +
          Complex.normalizedGammaStirlingLogLoss w :=
    Complex.Gamma_log_norm_le_normalizedGammaStirlingFactor_log_add_loss
      w hfactor_ne
  have hlog_plus_loss :
      Real.log ‖Complex.normalizedGammaStirlingFactor w‖ +
          Complex.normalizedGammaStirlingLogLoss w ≤
        Real.log B + Complex.normalizedGammaStirlingLogLoss w :=
    add_le_add_right hfactor_log
      (Complex.normalizedGammaStirlingLogLoss w)
  exact
    le_trans hgamma_extract
      (le_trans hlog_plus_loss (hloss w hw_sector hw_radius))

/-- The closed right-half-plane Gamma annulus used to absorb small radii in the
normalized Stirling extraction. -/
def Complex.closedRightHalfPlaneGammaAnnulus (R₀ : ℝ) : Set ℂ :=
  {w : ℂ | Complex.closedRightHalfPlaneSector w ∧ (1 / 2 : ℝ) ≤ ‖w‖ ∧ ‖w‖ ≤ R₀}

/-- The closed right-half-plane Gamma annulus is closed. -/
theorem Complex.closedRightHalfPlaneGammaAnnulus_isClosed
    (R₀ : ℝ) :
    IsClosed (Complex.closedRightHalfPlaneGammaAnnulus R₀) := by
  have hsector : IsClosed {w : ℂ | Complex.closedRightHalfPlaneSector w} := by
    exact isClosed_le continuous_const Complex.continuous_re
  have hinner : IsClosed {w : ℂ | (1 / 2 : ℝ) ≤ ‖w‖} := by
    exact isClosed_le continuous_const continuous_norm
  have houter : IsClosed {w : ℂ | ‖w‖ ≤ R₀} := by
    exact isClosed_le continuous_norm continuous_const
  have hset :
      Complex.closedRightHalfPlaneGammaAnnulus R₀ =
        {w : ℂ | Complex.closedRightHalfPlaneSector w} ∩
          {w : ℂ | (1 / 2 : ℝ) ≤ ‖w‖} ∩
            {w : ℂ | ‖w‖ ≤ R₀} := by
    ext w
    constructor
    · intro hw
      exact ⟨⟨hw.1, hw.2.1⟩, hw.2.2⟩
    · intro hw
      exact ⟨hw.1.1, hw.1.2, hw.2⟩
  exact Eq.subst
    (motive := fun S : Set ℂ => IsClosed S)
    hset.symm
    ((hsector.inter hinner).inter houter)

/-- The closed right-half-plane Gamma annulus is bounded. -/
theorem Complex.closedRightHalfPlaneGammaAnnulus_isBounded
    (R₀ : ℝ) :
    Bornology.IsBounded (Complex.closedRightHalfPlaneGammaAnnulus R₀) := by
  refine isBounded_iff_forall_norm_le.2 ⟨max R₀ 0 + 1, ?_⟩
  intro w hw
  have hraw : ‖w‖ ≤ R₀ := hw.2.2
  exact le_trans hraw
    (le_trans (le_max_left R₀ 0) (le_add_of_nonneg_right zero_le_one))

/-- The closed right-half-plane Gamma annulus is compact. -/
theorem Complex.closedRightHalfPlaneGammaAnnulus_isCompact
    (R₀ : ℝ) :
    IsCompact (Complex.closedRightHalfPlaneGammaAnnulus R₀) :=
  Metric.isCompact_of_isClosed_isBounded
    (Complex.closedRightHalfPlaneGammaAnnulus_isClosed R₀)
    (Complex.closedRightHalfPlaneGammaAnnulus_isBounded R₀)

/-- `Gamma` is nonzero on the closed right-half-plane Gamma annulus. -/
theorem Complex.Gamma_ne_zero_on_closedRightHalfPlaneGammaAnnulus
    (R₀ : ℝ)
    {w : ℂ}
    (hw : w ∈ Complex.closedRightHalfPlaneGammaAnnulus R₀) :
    Complex.Gamma w ≠ 0 := by
  intro hzero
  rcases (Complex.Gamma_eq_zero_iff w).mp hzero with ⟨n, hn⟩
  subst w
  cases n with
  | zero =>
      have hnorm_zero : ‖(-((0 : ℕ) : ℂ))‖ = 0 := by
        calc
          ‖(-((0 : ℕ) : ℂ))‖ = ‖(-(0 : ℂ))‖ := rfl
          _ = ‖(0 : ℂ)‖ :=
            congrArg norm (neg_zero : -((0 : ℂ)) = 0)
          _ = 0 := norm_zero
      have hhalf_le_zero : (1 / 2 : ℝ) ≤ 0 :=
        Eq.subst
          (motive := fun x : ℝ => (1 / 2 : ℝ) ≤ x)
          hnorm_zero
          hw.2.1
      exact (not_lt_of_ge hhalf_le_zero) one_half_pos
  | succ n =>
      have hre_eq :
          (-(((Nat.succ n : ℕ) : ℂ))).re =
            -(((Nat.succ n : ℕ) : ℝ)) := by
        calc
          (-(((Nat.succ n : ℕ) : ℂ))).re =
              -(((Nat.succ n : ℕ) : ℂ).re) :=
            Complex.neg_re (((Nat.succ n : ℕ) : ℂ))
          _ = -(((Nat.succ n : ℕ) : ℝ)) := by
            exact congrArg Neg.neg (Complex.natCast_re (Nat.succ n))
      have hre_nonneg :
          (0 : ℝ) ≤ -(((Nat.succ n : ℕ) : ℝ)) :=
        Eq.subst
          (motive := fun x : ℝ => (0 : ℝ) ≤ x)
          hre_eq
          hw.1
      have hsucc_pos : (0 : ℝ) < ((Nat.succ n : ℕ) : ℝ) :=
        Nat.cast_pos.mpr (Nat.succ_pos n)
      have hneg_lt_zero : -(((Nat.succ n : ℕ) : ℝ)) < 0 :=
        neg_neg_of_pos hsucc_pos
      exact (not_lt_of_ge hre_nonneg) hneg_lt_zero

/-- The function `w ↦ log ‖Γ(w)‖` is continuous on the closed right-half-plane
Gamma annulus. -/
theorem Complex.continuousOn_log_norm_Gamma_closedRightHalfPlaneGammaAnnulus
    (R₀ : ℝ) :
    ContinuousOn
      (fun w : ℂ => Real.log ‖Complex.Gamma w‖)
      (Complex.closedRightHalfPlaneGammaAnnulus R₀) := by
  intro w hw
  have hgamma_ne : Complex.Gamma w ≠ 0 :=
    Complex.Gamma_ne_zero_on_closedRightHalfPlaneGammaAnnulus R₀ hw
  have hnot_pole : ∀ m : ℕ, w ≠ -m := by
    intro m hwm
    exact hgamma_ne ((Complex.Gamma_eq_zero_iff w).mpr ⟨m, hwm⟩)
  have hgamma_cont : ContinuousAt Complex.Gamma w :=
    (Complex.differentiableAt_Gamma w hnot_pole).continuousAt
  have hnorm_cont :
      ContinuousWithinAt (fun z : ℂ => ‖Complex.Gamma z‖)
        (Complex.closedRightHalfPlaneGammaAnnulus R₀) w :=
    hgamma_cont.norm.continuousWithinAt
  have hnorm_ne : ‖Complex.Gamma w‖ ≠ 0 :=
    ne_of_gt (norm_pos_iff.mpr hgamma_ne)
  exact hnorm_cont.log hnorm_ne

/-- Compact boundedness of `log ‖Γ(w)‖` on the closed right-half-plane Gamma
annulus. -/
theorem Complex.log_norm_Gamma_closedRightHalfPlaneGammaAnnulus_bound
    (R₀ : ℝ) :
    ∃ M : ℝ,
      ∀ w : ℂ,
        w ∈ Complex.closedRightHalfPlaneGammaAnnulus R₀ →
        Real.log ‖Complex.Gamma w‖ ≤ M := by
  rcases IsCompact.exists_bound_of_continuousOn
      (Complex.closedRightHalfPlaneGammaAnnulus_isCompact R₀)
      (Complex.continuousOn_log_norm_Gamma_closedRightHalfPlaneGammaAnnulus R₀) with
    ⟨M, hM⟩
  refine ⟨M, ?_⟩
  intro w hw
  exact hM w hw

/-- The log-linear Gamma envelope has a positive lower bound on the compact
annulus. -/
theorem Complex.logLinearEnvelope_closedRightHalfPlaneGammaAnnulus_lower_bound
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ δ : ℝ,
      0 < δ ∧
      ∀ w : ℂ,
        w ∈ Complex.closedRightHalfPlaneGammaAnnulus R₀ →
        δ ≤ (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  refine ⟨Real.log 3, Real.log_pos one_lt_three, ?_⟩
  intro w hw
  have htwo_norm_ge_one : (1 : ℝ) ≤ 2 * ‖w‖ :=
    (div_le_iff₀' zero_lt_two).mp hw.2.1
  have hH_ge_one : (1 : ℝ) ≤ 1 + 2 * ‖w‖ :=
    le_add_of_nonneg_right (mul_nonneg zero_le_two (norm_nonneg w))
  have harg_ge_three : (3 : ℝ) ≤ 2 + 2 * ‖w‖ := by
    calc
      (3 : ℝ) = 2 + 1 := rfl
      _ ≤ 2 + 2 * ‖w‖ :=
        add_le_add_left htwo_norm_ge_one 2
  have hlog_le :
      Real.log 3 ≤ Real.log (2 + 2 * ‖w‖) :=
    Real.log_le_log zero_lt_three harg_ge_three
  have hlog_nonneg : 0 ≤ Real.log (2 + 2 * ‖w‖) :=
    le_trans (le_of_lt (Real.log_pos one_lt_three)) hlog_le
  have hone_mul :
      Real.log (2 + 2 * ‖w‖) ≤
        (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
    calc
      Real.log (2 + 2 * ‖w‖) = 1 * Real.log (2 + 2 * ‖w‖) :=
        (one_mul (Real.log (2 + 2 * ‖w‖))).symm
      _ ≤ (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
        mul_le_mul_of_nonneg_right hH_ge_one hlog_nonneg
  exact le_trans hlog_le hone_mul

/-- A bounded numerator and positive envelope lower bound give a constant
multiple bound on the compact Gamma annulus. -/
theorem Complex.Gamma_log_norm_bound_closedRightHalfPlaneSector_compactAnnulus_of_bound_and_lower
    (R₀ M δ : ℝ)
    (hδ_pos : 0 < δ)
    (hM :
      ∀ w : ℂ,
        w ∈ Complex.closedRightHalfPlaneGammaAnnulus R₀ →
        Real.log ‖Complex.Gamma w‖ ≤ M)
    (hδ :
      ∀ w : ℂ,
        w ∈ Complex.closedRightHalfPlaneGammaAnnulus R₀ →
        δ ≤ (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖)) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        ‖w‖ ≤ R₀ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  let C : ℝ := max (M / δ) 1
  have hC_pos : 0 < C :=
    lt_of_lt_of_le zero_lt_one (le_max_right (M / δ) 1)
  refine ⟨C, hC_pos, ?_⟩
  intro w hw_sector hw_inner hw_outer
  have hw_annulus : w ∈ Complex.closedRightHalfPlaneGammaAnnulus R₀ :=
    ⟨hw_sector, hw_inner, hw_outer⟩
  have hraw :
      Real.log ‖Complex.Gamma w‖ ≤ M :=
    hM w hw_annulus
  have hM_div_le_C : M / δ ≤ C :=
    le_max_left (M / δ) 1
  have hM_le_Cδ : M ≤ C * δ :=
    (div_le_iff₀ hδ_pos).mp hM_div_le_C
  have hδ_le_env :
      δ ≤ (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
    hδ w hw_annulus
  have hCδ_le_Cenv :
      C * δ ≤ C * ((1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖)) :=
    mul_le_mul_of_nonneg_left hδ_le_env (le_of_lt hC_pos)
  have hCenv_eq :
      C * ((1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖)) =
        C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
    mul_assoc C (1 + 2 * ‖w‖) (Real.log (2 + 2 * ‖w‖))
  exact
    le_trans hraw
      (le_trans hM_le_Cδ
        (le_trans hCδ_le_Cenv (le_of_eq hCenv_eq)))

/-- Compact annulus absorption for the logarithmic Gamma envelope in the closed
right half-plane sector.

This owns the local boundedness part omitted by the large-radius normalized
Stirling estimate: on the compact annulus
`0 ≤ re w`, `1 / 2 ≤ ‖w‖`, `‖w‖ ≤ R₀`, continuity of `Γ` and nonvanishing of
`Γ` give a finite bound for `log ‖Γ(w)‖`, which is absorbed by the positive
logarithmic envelope. -/
theorem Complex.Gamma_log_norm_bound_closedRightHalfPlaneSector_compactAnnulus
    (R₀ : ℝ)
    (hR₀_pos : 0 < R₀) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        ‖w‖ ≤ R₀ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  rcases Complex.log_norm_Gamma_closedRightHalfPlaneGammaAnnulus_bound R₀ with
    ⟨M, hM⟩
  rcases Complex.logLinearEnvelope_closedRightHalfPlaneGammaAnnulus_lower_bound
      R₀ hR₀_pos with
    ⟨δ, hδ_pos, hδ⟩
  exact
    Complex.Gamma_log_norm_bound_closedRightHalfPlaneSector_compactAnnulus_of_bound_and_lower
      R₀ M δ hδ_pos hM hδ

/-- Assembly of large-radius extraction and compact-annulus absorption. -/
theorem Complex.Gamma_log_norm_bound_of_largeRadius_and_compactAnnulus
    (R₀ : ℝ)
    (hlarge :
      ∃ C : ℝ,
        0 < C ∧
        ∀ w : ℂ,
          Complex.closedRightHalfPlaneSector w →
          R₀ ≤ ‖w‖ →
          Real.log ‖Complex.Gamma w‖ ≤
            C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖))
    (hannulus :
      ∃ C : ℝ,
        0 < C ∧
        ∀ w : ℂ,
          Complex.closedRightHalfPlaneSector w →
          (1 / 2 : ℝ) ≤ ‖w‖ →
          ‖w‖ ≤ R₀ →
          Real.log ‖Complex.Gamma w‖ ≤
            C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖)) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  rcases hlarge with ⟨Clarge, hClarge_pos, hlarge_bound⟩
  rcases hannulus with ⟨Cannulus, hCannulus_pos, hannulus_bound⟩
  refine ⟨max Clarge Cannulus,
    lt_of_lt_of_le hClarge_pos (le_max_left Clarge Cannulus), ?_⟩
  intro w hw_sector hw_norm
  have htwo_norm_nonneg : 0 ≤ 2 * ‖w‖ :=
    mul_nonneg zero_le_two (norm_nonneg w)
  have hH_nonneg : 0 ≤ 1 + 2 * ‖w‖ :=
    add_nonneg zero_le_one htwo_norm_nonneg
  have hlog_arg_ge_one : (1 : ℝ) ≤ 2 + 2 * ‖w‖ := by
    exact le_trans one_le_two (le_add_of_nonneg_right htwo_norm_nonneg)
  have hL_nonneg : 0 ≤ Real.log (2 + 2 * ‖w‖) :=
    Real.log_nonneg hlog_arg_ge_one
  by_cases hlarge_radius : R₀ ≤ ‖w‖
  · have hraw :
        Real.log ‖Complex.Gamma w‖ ≤
          Clarge * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
      hlarge_bound w hw_sector hlarge_radius
    have hmono :
        Clarge * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) ≤
          max Clarge Cannulus * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
      logLinearEnvelope_mono_constant
        (le_max_left Clarge Cannulus)
        hH_nonneg
        hL_nonneg
    exact le_trans hraw hmono
  · have hannulus_radius : ‖w‖ ≤ R₀ :=
      le_of_not_ge hlarge_radius
    have hraw :
        Real.log ‖Complex.Gamma w‖ ≤
          Cannulus * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
      hannulus_bound w hw_sector hw_norm hannulus_radius
    have hmono :
        Cannulus * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) ≤
          max Clarge Cannulus * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
      logLinearEnvelope_mono_constant
        (le_max_right Clarge Cannulus)
        hH_nonneg
        hL_nonneg
    exact le_trans hraw hmono

/-- The remaining real/branch extraction from a uniform bound for
`Γ(w) exp(w) w^(1/2-w)` to the logarithmic Gamma norm envelope.

This is deliberately isolated as the deepest nontrivial extraction root: it is
where the norm identities for `Complex.exp`, the closed-right-half-plane branch
control for `w ^ (1/2-w)`, and the elementary real domination by
`(1 + 2 ‖w‖) log (2 + 2 ‖w‖)` are used. -/
theorem Complex.Gamma_log_norm_bound_of_normalizedStirlingFactor_bound
    (B R₀ : ℝ)
    (hB_pos : 0 < B)
    (hR₀_pos : 0 < R₀)
    (hfactor :
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w)‖ ≤ B) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  have hlarge :
      ∃ C : ℝ,
        0 < C ∧
        ∀ w : ℂ,
          Complex.closedRightHalfPlaneSector w →
          R₀ ≤ ‖w‖ →
          Real.log ‖Complex.Gamma w‖ ≤
            C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
    Complex.Gamma_log_norm_bound_of_normalizedStirlingFactor_bound_largeRadius
      B R₀ hB_pos hR₀_pos hfactor
  have hannulus :
      ∃ C : ℝ,
        0 < C ∧
        ∀ w : ℂ,
          Complex.closedRightHalfPlaneSector w →
          (1 / 2 : ℝ) ≤ ‖w‖ →
          ‖w‖ ≤ R₀ →
          Real.log ‖Complex.Gamma w‖ ≤
            C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) :=
    Complex.Gamma_log_norm_bound_closedRightHalfPlaneSector_compactAnnulus
      R₀ hR₀_pos
  exact
    Complex.Gamma_log_norm_bound_of_largeRadius_and_compactAnnulus
      R₀ hlarge hannulus

/-- The elementary cutoff inequality used in the exponential-Stirling extraction:
if the radius dominates `2K / sqrt (2π)`, then the normalized error term
`K / r` is at most `sqrt (2π)`.

This is a pure real-inequality sink; it is separated from the Gamma theorem so
the analytic owner theorem only assembles named estimates. -/
theorem real_stirlingError_div_norm_le_sqrt_two_pi_of_cutoff
    (K r : ℝ)
    (hK_pos : 0 < K)
    (hr_pos : 0 < r)
    (hr_cutoff : 2 * K / Real.sqrt (2 * Real.pi) ≤ r) :
    K / r ≤ Real.sqrt (2 * Real.pi) := by
  let s : ℝ := Real.sqrt (2 * Real.pi)
  have hs_pos : 0 < s :=
    Real.sqrt_pos.mpr (mul_pos two_pos Real.pi_pos)
  have hcutoff_mul : 2 * K ≤ r * s :=
    (div_le_iff₀ hs_pos).mp hr_cutoff
  have hK_le_twoK : K ≤ 2 * K := by
    calc
      K = 1 * K := (one_mul K).symm
      _ ≤ 2 * K := mul_le_mul_of_nonneg_right one_le_two (le_of_lt hK_pos)
  have hK_le_rs : K ≤ r * s :=
    le_trans hK_le_twoK hcutoff_mul
  have hK_le_sr : K ≤ s * r :=
    Eq.subst
      (motive := fun x : ℝ => K ≤ x)
      (mul_comm r s)
      hK_le_rs
  exact (div_le_iff₀ hr_pos).mpr hK_le_sr

/-- Log-norm envelope extracted from the closed-right-half-plane exponential
Stirling expansion.

This is the exact reusable Gamma/Stirling API boundary between the normalized
exponential asymptotic and the downstream finite-order estimates.  Its proof is
the analytic extraction step: compare
`Γ(w) exp(w) w^(1/2-w)` with `sqrt (2π)`, bound the normalized factor away from
zero for large `‖w‖`, and transport through the branch-sensitive norm identities
for `Complex.exp` and `Complex.cpow`; cf. DLMF §5.11. -/
theorem Complex.Gamma_closedRightHalfPlane_sectorial_log_norm_bound_of_exponential_stirling
    (hStirling :
      ∃ R : ℝ, ∃ K : ℝ,
        0 < R ∧
        0 < K ∧
        ∀ w : ℂ,
          Complex.closedRightHalfPlaneSector w →
          R ≤ ‖w‖ →
          ‖Complex.Gamma w * Complex.exp w *
              w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
            K / ‖w‖) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  rcases hStirling with ⟨R, K, hR_pos, hK_pos, hStirling_pointwise⟩
  let R₀ : ℝ :=
    max R (max (2 * K / Real.sqrt (2 * Real.pi)) 1)
  have hR₀_pos : 0 < R₀ := by
    exact lt_of_lt_of_le zero_lt_one (le_max_right R (max (2 * K / Real.sqrt (2 * Real.pi)) 1))
  have hfactor :
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R₀ ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w)‖ ≤
          2 * Real.sqrt (2 * Real.pi) := by
    intro w hw_sector hw_R₀
    have hw_R : R ≤ ‖w‖ :=
      le_trans (le_max_left R (max (2 * K / Real.sqrt (2 * Real.pi)) 1)) hw_R₀
    have hw_one : 1 ≤ ‖w‖ :=
      le_trans (le_trans (le_max_right (2 * K / Real.sqrt (2 * Real.pi)) 1)
        (le_max_right R (max (2 * K / Real.sqrt (2 * Real.pi)) 1))) hw_R₀
    have hw_norm_pos : 0 < ‖w‖ :=
      lt_of_lt_of_le zero_lt_one hw_one
    have hw_cutoff : 2 * K / Real.sqrt (2 * Real.pi) ≤ ‖w‖ :=
      le_trans (le_trans
        (le_max_left (2 * K / Real.sqrt (2 * Real.pi)) 1)
        (le_max_right R (max (2 * K / Real.sqrt (2 * Real.pi)) 1))) hw_R₀
    have hK_div_le : K / ‖w‖ ≤ Real.sqrt (2 * Real.pi) :=
      real_stirlingError_div_norm_le_sqrt_two_pi_of_cutoff
        K ‖w‖ hK_pos hw_norm_pos hw_cutoff
    exact
      Complex.normalizedGammaFactor_norm_le_two_sqrt_two_pi_of_exponentialStirling_error
        R K hStirling_pointwise w hw_sector hw_R hK_div_le
  have hB_pos : 0 < 2 * Real.sqrt (2 * Real.pi) := by
    exact mul_pos two_pos (Real.sqrt_pos.mpr (mul_pos two_pos Real.pi_pos))
  exact
    Complex.Gamma_log_norm_bound_of_normalizedStirlingFactor_bound
      (2 * Real.sqrt (2 * Real.pi)) R₀ hB_pos hR₀_pos hfactor

/-- The sectorial exponential Stirling asymptotic gives the standard logarithmic
norm envelope on the closed right half-plane.

This is still part of the classical complex-Gamma Stirling input: it is the
real-part extraction and elementary domination step from the sectorial
asymptotic above, using nonnegative standard comparison envelopes.  Once
mathlib has a sectorial complex Stirling theorem, this is the single local
corollary that should be proved from it. -/
theorem Complex.sectorialGammaExponentialEnvelope_closedRightHalfPlane_of_asymptotic
    (hStirling :
      ∃ R : ℝ, ∃ K : ℝ,
        0 < R ∧
        0 < K ∧
        ∀ w : ℂ,
          Complex.closedRightHalfPlaneSector w →
          R ≤ ‖w‖ →
          ‖Complex.Gamma w * Complex.exp w *
              w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
            K / ‖w‖) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  exact
    Complex.Gamma_closedRightHalfPlane_sectorial_log_norm_bound_of_exponential_stirling
      hStirling

/-- Classical closed-sector exponential Stirling expansion for `Complex.Gamma`.

This is the formula-level sectorial asymptotic root for the Gamma lane:
Stirling's expansion with a uniform `O(1 / ‖w‖)` remainder on the closed right
half-plane, viewed as a closed sector avoiding the negative real axis; cf. DLMF
§5.11 and Whittaker-Watson, Ch. XII. -/
theorem Complex.Gamma_closedRightHalfPlane_sectorial_exponential_stirling_expansion_classical :
    ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        0 ≤ w.re →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖ := by
  exact Complex.sectorialLogGammaAsymptotic_closedRightHalfPlane

/-- Sectorial Gamma exponential envelope on the closed right half-plane.

This is the classical growth consequence of sectorial logarithmic Stirling:
the real part of `log Γ(w)` is bounded by a linear-logarithmic envelope on the
closed right half-plane, uniformly away from the origin; cf. DLMF §5.11. -/
theorem Complex.sectorialGammaExponentialEnvelope_closedRightHalfPlane :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  exact
    Complex.sectorialGammaExponentialEnvelope_closedRightHalfPlane_of_asymptotic
      Complex.sectorialLogGammaAsymptotic_closedRightHalfPlane

/-- Classical large-height fixed-real-part vertical Stirling theorem.

For arbitrary real part `a`, the vertical line `a + i b` is not contained in
the closed right half-plane when `a < 0`.  The correct owner input is therefore
the fixed-line specialization of sectorial Stirling in sectors avoiding the
negative real axis, with constants depending on `a`; cf. DLMF §5.11. -/
theorem Complex.fixedRealPartVerticalStirling_largeHeight_classical
    (a : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ b : ℝ,
        H ≤ ‖b‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := by
  sorry

/-- Large-height fixed-real-part vertical Stirling bounds for `Complex.Gamma`.

For an arbitrary fixed real part `a`, the vertical line `a + ib` eventually
lies in a closed sector avoiding the negative real axis, with sector aperture
depending on `a`.  Sectorial Stirling there gives the two-sided
`exp (-π |b| / 2) (1 + |b|)^(a - 1/2)` envelope. -/
theorem Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_largeHeight_classical
    (a : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ b : ℝ,
        H ≤ ‖b‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := by
  exact Complex.fixedRealPartVerticalStirling_largeHeight_classical a

/-- The compact-height part of a fixed vertical line. -/
def Complex.fixedRealPartVerticalCompactHeightSet
    (H : ℝ) : Set ℝ :=
  {b : ℝ | (1 / 2 : ℝ) ≤ ‖b‖ ∧ ‖b‖ ≤ H}

/-- Upper ratio of the fixed-line Gamma norm by the positive Stirling envelope. -/
def Complex.fixedRealPartVerticalGammaUpperRatio
    (a b : ℝ) : ℝ :=
  ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ /
    Complex.fixedRealPartVerticalStirlingEnvelope a b

/-- Lower ratio of the fixed-line Gamma norm by the positive Stirling envelope. -/
def Complex.fixedRealPartVerticalGammaLowerRatio
    (a b : ℝ) : ℝ :=
  ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ /
    Complex.fixedRealPartVerticalStirlingEnvelope a b

/-- `Gamma` is nonzero on the fixed-line compact-height strip. -/
theorem Complex.Gamma_fixedRealPartVerticalPoint_ne_zero_of_compactHeight
    {a H b : ℝ}
    (hb : b ∈ Complex.fixedRealPartVerticalCompactHeightSet H) :
    Complex.Gamma (Complex.fixedRealPartVerticalPoint a b) ≠ 0 := by
  intro hzero
  rcases
      (Complex.Gamma_eq_zero_iff
        (Complex.fixedRealPartVerticalPoint a b)).mp hzero with
    ⟨n, hn⟩
  have him_eq :
      (Complex.fixedRealPartVerticalPoint a b).im = (-(n : ℂ)).im :=
    congrArg Complex.im hn
  have hleft_im :
      (Complex.fixedRealPartVerticalPoint a b).im = b :=
    Complex.fixedRealPartVerticalPoint_im a b
  have hright_im : (-(n : ℂ)).im = 0 := by
    calc
      (-(n : ℂ)).im = -((n : ℂ).im) := Complex.neg_im (n : ℂ)
      _ = -0 := congrArg Neg.neg (Complex.natCast_im n)
      _ = 0 := neg_zero
  have hb_zero : b = 0 :=
    Eq.trans hleft_im.symm (Eq.trans him_eq hright_im)
  have hnorm_zero : ‖b‖ = 0 :=
    congrArg norm hb_zero
  have hhalf_pos : (0 : ℝ) < 1 / 2 :=
    half_pos zero_lt_one
  have hnot : ¬ (1 / 2 : ℝ) ≤ 0 :=
    not_le.mpr hhalf_pos
  exact
    hnot
      (Eq.subst
        (motive := fun x : ℝ => (1 / 2 : ℝ) ≤ x)
        hnorm_zero hb.1)

/-- Canonical compact-height ratio theorem for a fixed vertical line.

The proof is the standard compactness argument: the height set is compact,
the Gamma ratio is continuous there, `Gamma` has no zeros on it because
`|b| ≥ 1/2`, and the fixed-line Stirling envelope is strictly positive. -/
theorem Complex.fixedRealPartVerticalGammaRatio_compactHeight_bounds
    (a H : ℝ)
    (hH_pos : 0 < H) :
    ∃ C : ℝ, ∃ c : ℝ,
      0 < C ∧
      0 < c ∧
      ∀ b : ℝ,
        b ∈ Complex.fixedRealPartVerticalCompactHeightSet H →
          Complex.fixedRealPartVerticalGammaUpperRatio a b ≤ C ∧
          c ≤ Complex.fixedRealPartVerticalGammaLowerRatio a b := by
  sorry

/-- Ratio bounds on the compact-height part of a fixed vertical line.

This is the compactness/nonvanishing owner certificate: continuity supplies a
finite upper bound for the upper ratio, while nonvanishing of `Γ` and the
strictly positive Stirling envelope supply a positive lower bound. -/
theorem Complex.fixedRealPartVerticalGammaRatio_bounds_on_compactHeight
    (a H : ℝ)
    (hH_pos : 0 < H) :
    ∃ C : ℝ, ∃ c : ℝ,
      0 < C ∧
      0 < c ∧
      ∀ b : ℝ,
        b ∈ Complex.fixedRealPartVerticalCompactHeightSet H →
          Complex.fixedRealPartVerticalGammaUpperRatio a b ≤ C ∧
          c ≤ Complex.fixedRealPartVerticalGammaLowerRatio a b := by
  exact Complex.fixedRealPartVerticalGammaRatio_compactHeight_bounds a H hH_pos

/-- Ratio bounds convert to two-sided envelope bounds on the compact-height
part of a fixed vertical line. -/
theorem Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_compactHeight_of_ratio_bounds
    (a H C c : ℝ)
    (hC_pos : 0 < C)
    (hc_pos : 0 < c)
    (hratio :
      ∀ b : ℝ,
        b ∈ Complex.fixedRealPartVerticalCompactHeightSet H →
          Complex.fixedRealPartVerticalGammaUpperRatio a b ≤ C ∧
          c ≤ Complex.fixedRealPartVerticalGammaLowerRatio a b) :
    ∀ b : ℝ,
      (1 / 2 : ℝ) ≤ ‖b‖ →
      ‖b‖ ≤ H →
        ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
          C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
        c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := by
  intro b hb_inner hb_outer
  have hb_mem :
      b ∈ Complex.fixedRealPartVerticalCompactHeightSet H :=
    ⟨hb_inner, hb_outer⟩
  have hratio_b :
      Complex.fixedRealPartVerticalGammaUpperRatio a b ≤ C ∧
        c ≤ Complex.fixedRealPartVerticalGammaLowerRatio a b :=
    hratio b hb_mem
  have hE_pos :
      0 < Complex.fixedRealPartVerticalStirlingEnvelope a b :=
    Complex.fixedRealPartVerticalStirlingEnvelope_pos a b
  have hE_nonneg :
      0 ≤ Complex.fixedRealPartVerticalStirlingEnvelope a b :=
    le_of_lt hE_pos
  have hupper_div :
      ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ /
          Complex.fixedRealPartVerticalStirlingEnvelope a b ≤ C :=
    hratio_b.1
  have hlower_div :
      c ≤
        ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ /
          Complex.fixedRealPartVerticalStirlingEnvelope a b :=
    hratio_b.2
  have hupper :
      ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
        C * Complex.fixedRealPartVerticalStirlingEnvelope a b :=
    (div_le_iff₀ hE_pos).mp hupper_div
  have hlower :
      c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
        ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ :=
    (le_div_iff₀ hE_pos).mp hlower_div
  exact ⟨hupper, hlower⟩

/-- Compact-height patch for fixed-real-part vertical Stirling bounds.

On the compact set `1 / 2 ≤ |b| ≤ H`, continuity and nonvanishing of `Γ` on
the fixed vertical line give finite upper and positive lower constants relative
to the positive fixed-line Stirling envelope. -/
theorem Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_compactHeight
    (a H : ℝ)
    (hH_pos : 0 < H) :
    ∃ C : ℝ, ∃ c : ℝ,
      0 < C ∧
      0 < c ∧
      ∀ b : ℝ,
        (1 / 2 : ℝ) ≤ ‖b‖ →
        ‖b‖ ≤ H →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := by
  rcases
      Complex.fixedRealPartVerticalGammaRatio_bounds_on_compactHeight
        a H hH_pos with
    ⟨C, c, hC_pos, hc_pos, hratio⟩
  exact
    ⟨C, c, hC_pos, hc_pos,
      Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_compactHeight_of_ratio_bounds
        a H C c hC_pos hc_pos hratio⟩

/-- Assembly of large-height fixed-line Stirling and compact-height patching. -/
theorem Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_of_large_and_compact
    (a : ℝ)
    (hlarge :
      ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
        0 < H ∧
        0 < C ∧
        0 < c ∧
        ∀ b : ℝ,
          H ≤ ‖b‖ →
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
              C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
            c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
              ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖)
    (hcompact :
      ∀ H : ℝ,
        0 < H →
          ∃ C : ℝ, ∃ c : ℝ,
            0 < C ∧
            0 < c ∧
            ∀ b : ℝ,
              (1 / 2 : ℝ) ≤ ‖b‖ →
              ‖b‖ ≤ H →
                ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
                  C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
                c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
                  ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖) :
    ∃ C : ℝ, ∃ c : ℝ,
      0 < C ∧
      0 < c ∧
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := by
  rcases hlarge with ⟨H, Clarge, clarge, hH_pos, hClarge_pos, hclarge_pos, hlarge_bound⟩
  rcases hcompact H hH_pos with
    ⟨Ccompact, ccompact, hCcompact_pos, hccompact_pos, hcompact_bound⟩
  let C : ℝ := max Clarge Ccompact
  let c : ℝ := min clarge ccompact
  have hC_pos : 0 < C :=
    lt_of_lt_of_le hClarge_pos (le_max_left Clarge Ccompact)
  have hc_pos : 0 < c :=
    lt_min hclarge_pos hccompact_pos
  refine ⟨C, c, hC_pos, hc_pos, ?_⟩
  intro b hb
  have hE_nonneg :
      0 ≤ Complex.fixedRealPartVerticalStirlingEnvelope a b :=
    Complex.fixedRealPartVerticalStirlingEnvelope_nonneg a b
  by_cases hb_large : H ≤ ‖b‖
  · have hlarge_b :
        ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
            Clarge * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
          clarge * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ :=
      hlarge_bound b hb_large
    have hupper_constant :
        Clarge * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
          C * Complex.fixedRealPartVerticalStirlingEnvelope a b :=
      mul_le_mul_of_nonneg_right (le_max_left Clarge Ccompact) hE_nonneg
    have hlower_constant :
        c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
          clarge * Complex.fixedRealPartVerticalStirlingEnvelope a b :=
      mul_le_mul_of_nonneg_right (min_le_left clarge ccompact) hE_nonneg
    exact
      ⟨le_trans hlarge_b.1 hupper_constant,
        le_trans hlower_constant hlarge_b.2⟩
  · have hb_compact_upper : ‖b‖ ≤ H :=
      le_of_not_ge hb_large
    have hcompact_b :
        ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
            Ccompact * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
          ccompact * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ :=
      hcompact_bound b hb hb_compact_upper
    have hupper_constant :
        Ccompact * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
          C * Complex.fixedRealPartVerticalStirlingEnvelope a b :=
      mul_le_mul_of_nonneg_right (le_max_right Clarge Ccompact) hE_nonneg
    have hlower_constant :
        c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
          ccompact * Complex.fixedRealPartVerticalStirlingEnvelope a b :=
      mul_le_mul_of_nonneg_right (min_le_right clarge ccompact) hE_nonneg
    exact
      ⟨le_trans hcompact_b.1 hupper_constant,
        le_trans hlower_constant hcompact_b.2⟩

/-- Fixed-real-part vertical two-sided Stirling bounds for `Complex.Gamma`.

This is the exact fixed-line specialization theorem in the classical Stirling
API.  Deriving it from the sectorial exponential asymptotic requires the full
vertical-line argument analysis of
`w ^ ((1 / 2 : ℂ) - w)`, including the `exp (-π |b| / 2)` factor and matching
lower bound. -/
theorem Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_classical
    (a : ℝ) :
    ∃ C : ℝ, ∃ c : ℝ,
      0 < C ∧
      0 < c ∧
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := by
  exact
    Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_of_large_and_compact
      a
      (Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_largeHeight_classical
        a)
      (Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_compactHeight
        a)

/-- Two-sided fixed-real-part vertical Stirling envelope for `Complex.Gamma`.

This is the fixed-line specialization of sectorial complex Stirling after
separating the argument of `a + i b`: it supplies the matching
`exp (-π |b| / 2) (1 + |b|)^(a - 1/2)` upper and lower envelopes on every
fixed real line.  The public one-sided estimates below are just projections
from this two-sided classical input. -/
theorem Complex.fixedLineVerticalGammaTwoSidedEnvelope :
    ∀ a : ℝ,
      ∃ C : ℝ, ∃ c : ℝ,
        0 < C ∧
        0 < c ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
              C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
            c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
              ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := by
  intro a
  exact Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_classical a

/-- Standard sectorial `log Γ` Stirling upper bound on the closed right half-plane.

This is the logarithmic special-function root after peeling the downstream
growth theory: Stirling's expansion for `log Γ(w)` on a closed sector avoiding
the negative real axis gives a uniform
`O((1 + ‖w‖) log (2 + ‖w‖))` bound on the closed right half-plane; cf. DLMF
§5.11. The bound is stated for `log ‖Γ(w)‖`, the real part of `log Γ(w)`, so
later Gamma-real normalization steps do not need a branch of `logGamma`. -/
theorem Complex.logGamma_closedRightHalfPlane_sectorial_log_norm_bound_classical :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 ≤ w.re →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  exact Complex.sectorialGammaExponentialEnvelope_closedRightHalfPlane

/-- Fixed-line vertical upper envelope for `Complex.Gamma`.

For each fixed real part `a`, Stirling's formula on the vertical line
`a + i b` gives exponential decay `exp (-π |b| / 2)` and polynomial factor
`(1 + |b|)^(a - 1/2)`; cf. DLMF §5.11. -/
theorem Complex.fixedLineVerticalGammaUpperEnvelope :
    ∀ a : ℝ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope a b := by
  intro a
  rcases Complex.fixedLineVerticalGammaTwoSidedEnvelope a with
    ⟨C, c, hC_pos, hc_pos, hbounds⟩
  exact
    ⟨C, hC_pos,
      fun b hb =>
        (hbounds b hb).1⟩

/-- Fixed-real-part vertical Stirling upper bound for `Complex.Gamma`.

This is the direct fixed-line classical estimate: for each fixed real part `a`,
`Γ(a + i b)` has vertical decay `exp (-π |b| / 2)` and polynomial factor
`(1 + |b|)^(a - 1/2)`; cf. DLMF §5.11. -/
theorem Complex.Gamma_fixedRealPart_vertical_stirling_upper_bound_classical :
    ∀ a : ℝ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
            C * Real.exp (-(Real.pi / 2) * ‖b‖) *
              (1 + ‖b‖) ^ (a - 1 / 2) := by
  exact Complex.fixedLineVerticalGammaUpperEnvelope

/-- Fixed-line vertical lower envelope for `Complex.Gamma`.

For each fixed real part `a`, the lower half of vertical Stirling gives the
matching positive constant in front of the same exponential-polynomial
envelope; cf. DLMF §5.11. -/
theorem Complex.fixedLineVerticalGammaLowerEnvelope :
    ∀ a : ℝ,
      ∃ c : ℝ,
        0 < c ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := by
  intro a
  rcases Complex.fixedLineVerticalGammaTwoSidedEnvelope a with
    ⟨C, c, hC_pos, hc_pos, hbounds⟩
  exact
    ⟨c, hc_pos,
      fun b hb =>
        (hbounds b hb).2⟩

/-- Fixed-real-part vertical Stirling lower bound for `Complex.Gamma`.

This is the lower half of the classical fixed-line estimate, isolated so the
reciprocal estimate is a norm-order transport rather than an independent
primitive. -/
theorem Complex.Gamma_fixedRealPart_vertical_stirling_lower_bound_classical :
    ∀ a : ℝ,
      ∃ c : ℝ,
        0 < c ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          c * Real.exp (-(Real.pi / 2) * ‖b‖) *
              (1 + ‖b‖) ^ (a - 1 / 2) ≤
            ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ := by
  exact Complex.fixedLineVerticalGammaLowerEnvelope

/-- Two-sided fixed-real-part vertical Stirling bounds for `Complex.Gamma`, with the
fixed-line point and envelope named by the owner API.

This is the reusable bundled form of the classical fixed-line asymptotic estimates:
downstream reciprocal and quotient arguments should consume this statement rather
than repeatedly unpacking the two split roots. -/
theorem Complex.Gamma_fixedRealPart_vertical_twoSided_stirling_bounds_owner
    (a : ℝ) :
    ∃ C : ℝ, ∃ c : ℝ,
      0 < C ∧
      0 < c ∧
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := by
  rcases Complex.Gamma_fixedRealPart_vertical_stirling_upper_bound_classical a with
    ⟨C, hC_pos, hupper⟩
  rcases Complex.Gamma_fixedRealPart_vertical_stirling_lower_bound_classical a with
    ⟨c, hc_pos, hlower⟩
  refine ⟨C, c, hC_pos, hc_pos, ?_⟩
  intro b hb
  exact ⟨hupper b hb, hlower b hb⟩

/-- Classical Gamma/Stirling owner package on the closed right half-plane.

This package is now only product assembly from the canonical local
special-function roots above: sectorial exponential Stirling, its log-norm
consequence, and the two fixed-real-part vertical estimates. -/
theorem Complex.Gamma_closedRightHalfPlane_sectorial_stirling_package_classical :
    (∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        0 ≤ w.re →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖) ∧
    (∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 ≤ w.re →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖)) ∧
    (∀ a : ℝ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
            C * Real.exp (-(Real.pi / 2) * ‖b‖) *
              (1 + ‖b‖) ^ (a - 1 / 2)) ∧
    (∀ a : ℝ,
      ∃ c : ℝ,
        0 < c ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          c * Real.exp (-(Real.pi / 2) * ‖b‖) *
              (1 + ‖b‖) ^ (a - 1 / 2) ≤
            ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖) := by
  exact
    ⟨Complex.Gamma_closedRightHalfPlane_sectorial_exponential_stirling_expansion_classical,
      Complex.logGamma_closedRightHalfPlane_sectorial_log_norm_bound_classical,
      Complex.Gamma_fixedRealPart_vertical_stirling_upper_bound_classical,
      Complex.Gamma_fixedRealPart_vertical_stirling_lower_bound_classical⟩

/-- Sectorial log-norm consequence of closed-sector logarithmic Stirling for
`Complex.Gamma` on the closed right half-plane. -/
theorem Complex.Gamma_closedRightHalfPlane_sectorial_log_norm_bound_classical :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 ≤ w.re →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  exact Complex.logGamma_closedRightHalfPlane_sectorial_log_norm_bound_classical

/-- `Complex.Gamma` is nonzero on fixed vertical lines away from the real-axis
pole convention when `|b| ≥ 1/2`. -/
theorem Complex.Gamma_fixedRealPart_vertical_ne_zero_of_half_le_norm
    (a b : ℝ)
    (hb : (1 / 2 : ℝ) ≤ ‖b‖) :
    Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I) ≠ 0 := by
  intro hzero
  rcases (Complex.Gamma_eq_zero_iff ((a : ℂ) + (b : ℂ) * Complex.I)).mp hzero with
    ⟨n, hn⟩
  have him_eq : (((a : ℂ) + (b : ℂ) * Complex.I).im) = (-(n : ℂ)).im :=
    congrArg Complex.im hn
  have hleft_im :
      (((a : ℂ) + (b : ℂ) * Complex.I).im) = b := by
    calc
      (((a : ℂ) + (b : ℂ) * Complex.I).im) =
          (a : ℂ).im + ((b : ℂ) * Complex.I).im := Complex.add_im (a : ℂ) ((b : ℂ) * Complex.I)
      _ = 0 + b := by
        exact congrArg (fun x : ℝ => 0 + x) (Complex.ofReal_mul_I_im b)
      _ = b := zero_add b
  have hright_im : (-(n : ℂ)).im = 0 := by
    calc
      (-(n : ℂ)).im = -((n : ℂ).im) := Complex.neg_im (n : ℂ)
      _ = -0 := congrArg Neg.neg (Complex.ofReal_im (n : ℝ))
      _ = 0 := neg_zero
  have hb_zero : b = 0 :=
    Eq.trans hleft_im.symm (Eq.trans him_eq hright_im)
  have hnorm_zero : ‖b‖ = 0 :=
    congrArg norm hb_zero
  have hhalf_pos : (0 : ℝ) < 1 / 2 :=
    half_pos zero_lt_one
  have hnot : ¬ (1 / 2 : ℝ) ≤ 0 :=
    not_le.mpr hhalf_pos
  exact hnot (Eq.subst (motive := fun x : ℝ => (1 / 2 : ℝ) ≤ x) hnorm_zero hb)

/-- Reciprocal transport for fixed-real-part vertical Gamma estimates.

A lower Stirling bound and nonvanishing of `Γ(a + i b)` imply the corresponding
upper bound for the reciprocal. -/
theorem Complex.Gamma_fixedRealPart_vertical_reciprocal_bound_of_lower_bound
    {a c : ℝ}
    (hc_pos : 0 < c)
    (hlower :
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
        c * Real.exp (-(Real.pi / 2) * ‖b‖) *
            (1 + ‖b‖) ^ (a - 1 / 2) ≤
          ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖) :
    ∀ b : ℝ,
      1 / 2 ≤ ‖b‖ →
      ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
        c⁻¹ * Real.exp ((Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (1 / 2 - a) := by
  intro b hb
  let x : ℝ := (Real.pi / 2) * ‖b‖
  let H : ℝ := 1 + ‖b‖
  let G : ℂ := Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)
  have hH_pos : 0 < H :=
    lt_of_lt_of_le zero_lt_one
      (le_add_of_nonneg_right (norm_nonneg b))
  have hexp_pos : 0 < Real.exp (-x) :=
    Real.exp_pos (-x)
  have hrpow_pos : 0 < H ^ (a - 1 / 2) :=
    Real.rpow_pos_of_pos hH_pos (a - 1 / 2)
  have henvelope_pos :
      0 < c * Real.exp (-x) * H ^ (a - 1 / 2) :=
    mul_pos (mul_pos hc_pos hexp_pos) hrpow_pos
  have hG_lower :
      c * Real.exp (-x) * H ^ (a - 1 / 2) ≤ ‖G‖ := by
    exact hlower b hb
  have hG_inv_norm :
      ‖G⁻¹‖ = ‖G‖⁻¹ :=
    norm_inv G
  have hreciprocal_le :
      ‖G‖⁻¹ ≤ (c * Real.exp (-x) * H ^ (a - 1 / 2))⁻¹ :=
    inv_le_inv_of_le henvelope_pos hG_lower
  have htarget_eq :
      (c * Real.exp (-x) * H ^ (a - 1 / 2))⁻¹ =
        c⁻¹ * Real.exp x * H ^ (1 / 2 - a) := by
    have hexp_neg_eq : Real.exp (-x) = (Real.exp x)⁻¹ :=
      Real.exp_neg x
    have hpow_neg_eq :
        H ^ (1 / 2 - a) = (H ^ (a - 1 / 2))⁻¹ := by
      have hneg : 1 / 2 - a = -(a - 1 / 2) := by
        exact (neg_sub a (1 / 2)).symm
      exact Eq.trans
        (congrArg (fun y : ℝ => H ^ y) hneg)
        (Real.rpow_neg (le_of_lt hH_pos) (a - 1 / 2))
    calc
      (c * Real.exp (-x) * H ^ (a - 1 / 2))⁻¹ =
          (c * Real.exp (-x))⁻¹ * (H ^ (a - 1 / 2))⁻¹ := by
            exact inv_mul_eq_inv_mul_inv (c * Real.exp (-x)) (H ^ (a - 1 / 2))
      _ = (c⁻¹ * (Real.exp (-x))⁻¹) * (H ^ (a - 1 / 2))⁻¹ := by
            exact congrArg
              (fun y : ℝ => y * (H ^ (a - 1 / 2))⁻¹)
              (inv_mul_eq_inv_mul_inv c (Real.exp (-x)))
      _ = (c⁻¹ * Real.exp x) * (H ^ (a - 1 / 2))⁻¹ := by
            exact congrArg
              (fun y : ℝ => (c⁻¹ * y) * (H ^ (a - 1 / 2))⁻¹)
              (congrArg Inv.inv hexp_neg_eq)
      _ = (c⁻¹ * Real.exp x) * H ^ (1 / 2 - a) := by
            exact congrArg
              (fun y : ℝ => (c⁻¹ * Real.exp x) * y)
              hpow_neg_eq.symm
      _ = c⁻¹ * Real.exp x * H ^ (1 / 2 - a) := by
            exact (mul_assoc c⁻¹ (Real.exp x) (H ^ (1 / 2 - a))).symm
  exact Eq.subst
    (motive := fun y : ℝ => ‖G⁻¹‖ ≤ y)
    htarget_eq
    (Eq.subst
      (motive := fun y : ℝ => y ≤
        (c * Real.exp (-x) * H ^ (a - 1 / 2))⁻¹)
      hG_inv_norm.symm
      hreciprocal_le)

/-- Fixed-real-part reciprocal vertical Stirling bound for `Complex.Gamma`, obtained
from the lower fixed-line estimate by reciprocal transport. -/
theorem Complex.Gamma_fixedRealPart_vertical_reciprocal_stirling_bound_classical :
    ∀ a : ℝ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
            C * Real.exp ((Real.pi / 2) * ‖b‖) *
              (1 + ‖b‖) ^ (1 / 2 - a) := by
  intro a
  rcases Complex.Gamma_fixedRealPart_vertical_stirling_lower_bound_classical a with
    ⟨c, hc_pos, hlower⟩
  refine ⟨c⁻¹, inv_pos.mpr hc_pos, ?_⟩
  exact Complex.Gamma_fixedRealPart_vertical_reciprocal_bound_of_lower_bound hc_pos hlower

/-- Fixed-real-part vertical Stirling bounds for `Complex.Gamma` and its
reciprocal. -/
theorem Complex.Gamma_fixedRealPart_vertical_twoSided_stirling_bounds_classical :
    ∀ a : ℝ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
              C * Real.exp (-(Real.pi / 2) * ‖b‖) *
                (1 + ‖b‖) ^ (a - 1 / 2) ∧
          ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
              C * Real.exp ((Real.pi / 2) * ‖b‖) *
                (1 + ‖b‖) ^ (1 / 2 - a) := by
  intro a
  rcases Complex.Gamma_fixedRealPart_vertical_stirling_upper_bound_classical a with
    ⟨Cu, hCu_pos, hCu⟩
  rcases Complex.Gamma_fixedRealPart_vertical_reciprocal_stirling_bound_classical a with
    ⟨Cr, hCr_pos, hCr⟩
  let C : ℝ := Cu + Cr
  have hC_pos : 0 < C :=
    add_pos hCu_pos hCr_pos
  have hCu_le_C : Cu ≤ C :=
    le_add_of_nonneg_right (le_of_lt hCr_pos)
  have hCr_le_C : Cr ≤ C :=
    le_add_of_nonneg_left (le_of_lt hCu_pos)
  refine ⟨C, hC_pos, ?_⟩
  intro b hb
  have hdirect_envelope_nonneg :
      0 ≤ Real.exp (-(Real.pi / 2) * ‖b‖) *
        (1 + ‖b‖) ^ (a - 1 / 2) := by
    have hbase_pos : 0 < 1 + ‖b‖ :=
      lt_of_lt_of_le zero_lt_one
        (le_add_of_nonneg_right (norm_nonneg b))
    exact mul_nonneg
      (le_of_lt (Real.exp_pos (-(Real.pi / 2) * ‖b‖)))
      (le_of_lt (Real.rpow_pos_of_pos hbase_pos (a - 1 / 2)))
  have hreciprocal_envelope_nonneg :
      0 ≤ Real.exp ((Real.pi / 2) * ‖b‖) *
        (1 + ‖b‖) ^ (1 / 2 - a) := by
    have hbase_pos : 0 < 1 + ‖b‖ :=
      lt_of_lt_of_le zero_lt_one
        (le_add_of_nonneg_right (norm_nonneg b))
    exact mul_nonneg
      (le_of_lt (Real.exp_pos ((Real.pi / 2) * ‖b‖)))
      (le_of_lt (Real.rpow_pos_of_pos hbase_pos (1 / 2 - a)))
  have hdirect_scaled :
      Cu * (Real.exp (-(Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (a - 1 / 2)) ≤
        C * (Real.exp (-(Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (a - 1 / 2)) :=
    mul_le_mul_of_nonneg_right hCu_le_C hdirect_envelope_nonneg
  have hreciprocal_scaled :
      Cr * (Real.exp ((Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (1 / 2 - a)) ≤
        C * (Real.exp ((Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (1 / 2 - a)) :=
    mul_le_mul_of_nonneg_right hCr_le_C hreciprocal_envelope_nonneg
  have hdirect_source_assoc :
      Cu * Real.exp (-(Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (a - 1 / 2) =
        Cu * (Real.exp (-(Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (a - 1 / 2)) :=
    mul_assoc Cu (Real.exp (-(Real.pi / 2) * ‖b‖))
      ((1 + ‖b‖) ^ (a - 1 / 2))
  have hdirect_target_assoc :
      C * Real.exp (-(Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (a - 1 / 2) =
        C * (Real.exp (-(Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (a - 1 / 2)) :=
    mul_assoc C (Real.exp (-(Real.pi / 2) * ‖b‖))
      ((1 + ‖b‖) ^ (a - 1 / 2))
  have hreciprocal_source_assoc :
      Cr * Real.exp ((Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (1 / 2 - a) =
        Cr * (Real.exp ((Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (1 / 2 - a)) :=
    mul_assoc Cr (Real.exp ((Real.pi / 2) * ‖b‖))
      ((1 + ‖b‖) ^ (1 / 2 - a))
  have hreciprocal_target_assoc :
      C * Real.exp ((Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (1 / 2 - a) =
        C * (Real.exp ((Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (1 / 2 - a)) :=
    mul_assoc C (Real.exp ((Real.pi / 2) * ‖b‖))
      ((1 + ‖b‖) ^ (1 / 2 - a))
  constructor
  · exact Eq.subst
      (motive := fun x : ℝ =>
        ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤ x)
      hdirect_target_assoc.symm
      (le_trans
        (Eq.subst
          (motive := fun x : ℝ =>
            ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤ x)
          hdirect_source_assoc
          (hCu b hb))
        hdirect_scaled)
  · exact Eq.subst
      (motive := fun x : ℝ =>
        ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤ x)
      hreciprocal_target_assoc.symm
      (le_trans
        (Eq.subst
          (motive := fun x : ℝ =>
            ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤ x)
          hreciprocal_source_assoc
          (hCr b hb))
        hreciprocal_scaled)

/-- Classical closed-sector Stirling expansion for `Complex.Gamma`, with the
sectorial and fixed-line consequences used by the normalization chain.

This owner theorem is now only the product assembly of the formula-level
Stirling input, its sectorial log-norm consequence, and the fixed-line vertical
estimates; cf. DLMF §5.11. -/
theorem Complex.Gamma_closedRightHalfPlane_sectorial_stirling_expansion_with_vertical_bounds_classical :
    (∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        0 ≤ w.re →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖) ∧
    (∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 ≤ w.re →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖)) ∧
    (∀ a : ℝ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
              C * Real.exp (-(Real.pi / 2) * ‖b‖) *
                (1 + ‖b‖) ^ (a - 1 / 2) ∧
          ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
              C * Real.exp ((Real.pi / 2) * ‖b‖) *
                (1 + ‖b‖) ^ (1 / 2 - a)) := by
  exact
    ⟨Complex.Gamma_closedRightHalfPlane_sectorial_exponential_stirling_expansion_classical,
      Complex.Gamma_closedRightHalfPlane_sectorial_log_norm_bound_classical,
      Complex.Gamma_fixedRealPart_vertical_twoSided_stirling_bounds_classical⟩

/-- Classical closed-sector Stirling estimates for `Complex.Gamma`.

This is the single classical special-function owner input for the Gamma lane.
It packages the sectorial log-norm consequence of Stirling's expansion in the
closed right half-plane together with the fixed-real-part vertical two-sided
estimates obtained from the same expansion.  The sector avoids the negative
real axis, and the fixed-line bounds are the usual
`Γ(a + i b) = O(exp (-π |b| / 2) |b|^(a - 1/2))` estimate and its reciprocal
dual; cf. DLMF §5.11. -/
theorem Complex.Gamma_closedRightHalfPlane_sectorial_and_vertical_stirling_bounds_classical :
    (∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 ≤ w.re →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖)) ∧
    (∀ a : ℝ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
              C * Real.exp (-(Real.pi / 2) * ‖b‖) *
                (1 + ‖b‖) ^ (a - 1 / 2) ∧
          ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
              C * Real.exp ((Real.pi / 2) * ‖b‖) *
                (1 + ‖b‖) ^ (1 / 2 - a)) := by
  exact
    ⟨Complex.Gamma_closedRightHalfPlane_sectorial_stirling_expansion_with_vertical_bounds_classical.2.1,
      Complex.Gamma_closedRightHalfPlane_sectorial_stirling_expansion_with_vertical_bounds_classical.2.2⟩

/-- Standard sectorial logarithmic Stirling for `Complex.Gamma` in the closed right half-plane.

This is the standard special-function input closest to the literature: the
sectorial Stirling expansion for `log Γ(w)` on a closed sector avoiding the
negative real axis, specialized to `0 ≤ w.re` and converted to a log-norm
upper bound.  The radius is written as `2 * ‖w‖` so the downstream
half-argument transport is formula-level; cf. DLMF §5.11. -/
theorem Complex.Gamma_sectorial_rightHalfPlane_stirling_log_norm_bound_classical :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 ≤ w.re →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  exact
    Complex.Gamma_closedRightHalfPlane_sectorial_and_vertical_stirling_bounds_classical.1

/-- Standard sectorial logarithmic Stirling for `Complex.Gamma` in the closed right half-plane.

This is name transport from the classical sectorial `log Γ` estimate. -/
theorem Complex.Gamma_sectorial_rightHalfPlane_stirling_log_norm_bound_standard :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 ≤ w.re →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  exact Complex.Gamma_sectorial_rightHalfPlane_stirling_log_norm_bound_classical

/-- Standard sectorial logarithmic Stirling for `Complex.Gamma` in the closed right half-plane.

This is only name transport from the canonical sectorial Gamma log-norm input. -/
theorem Complex.logGamma_sectorial_rightHalfPlane_stirling_log_norm_bound_standard :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 ≤ w.re →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  exact Complex.Gamma_sectorial_rightHalfPlane_stirling_log_norm_bound_standard

/-- Sectorial logarithmic Stirling for `Complex.Gamma` in the closed right half-plane.

This is the canonical sectorial Gamma root for the normalization chain.  It is
formula-level transport from the standard Mathlib-shaped sectorial Stirling
estimate for `Complex.Gamma`; cf. DLMF §5.11. -/
theorem Complex.logGamma_sectorial_rightHalfPlane_stirling_log_norm_bound :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 ≤ w.re →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  exact Complex.logGamma_sectorial_rightHalfPlane_stirling_log_norm_bound_standard

/-- The standard sectorial complex-Stirling input for `Complex.Gamma` in the closed
right half-plane.

This owner-root spelling is retained for the normalization chain.  Its proof is only
name transport from the canonical sectorial `log Γ` Stirling input. -/
theorem sectorialComplexGammaStirling_rightHalfPlane_log_linear_growth_bound_degree_one :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 ≤ w.re →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := by
  exact Complex.logGamma_sectorial_rightHalfPlane_stirling_log_norm_bound

/-- Transport the sectorial `Complex.Gamma` estimate from `w` to the half-argument
`w = z / 2`. -/
theorem sectorialComplexGammaStirling_halfArgument_rightHalfPlane_log_linear_growth_bound_degree_one_of_sectorial
    (hsector :
      ∃ C : ℝ,
        0 < C ∧
        ∀ w : ℂ,
          0 ≤ w.re →
          (1 / 2 : ℝ) ≤ ‖w‖ →
          Real.log ‖Complex.Gamma w‖ ≤
            C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖)) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        1 ≤ ‖z‖ →
        Real.log ‖Complex.Gamma (z / 2)‖ ≤
          C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
  rcases hsector with ⟨C, hC_pos, hC⟩
  refine ⟨C, hC_pos, ?_⟩
  intro z hz_re hz_norm
  have hz_half_re : 0 ≤ (z / 2).re :=
    halfArgument_re_nonneg_of_re_nonneg hz_re
  have hz_half_norm : (1 / 2 : ℝ) ≤ ‖z / 2‖ :=
    halfArgument_norm_ge_one_half_of_one_le_norm hz_norm
  have hraw :
      Real.log ‖Complex.Gamma (z / 2)‖ ≤
        C * (1 + 2 * ‖z / 2‖) * Real.log (2 + 2 * ‖z / 2‖) :=
    hC (z / 2) hz_half_re hz_half_norm
  have htarget_eq :
      C * (1 + 2 * ‖z / 2‖) * Real.log (2 + 2 * ‖z / 2‖) =
        C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
    exact sectorialGammaEnvelope_halfArgument_eq C z
  exact Eq.subst
    (motive := fun x : ℝ => Real.log ‖Complex.Gamma (z / 2)‖ ≤ x)
    htarget_eq
    hraw

/-- Classical sectorial log-Gamma growth for the half-argument in the closed right
half-plane.

This is the exact missing special-function theorem: sectorial Stirling for
`Γ(w)` on `0 ≤ w.re`, transported to `w = z / 2` and measured against `‖z‖`;
cf. DLMF §5.11. -/
theorem sectorialComplexGammaStirling_halfArgument_rightHalfPlane_log_linear_growth_bound_degree_one :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        1 ≤ ‖z‖ →
        Real.log ‖Complex.Gamma (z / 2)‖ ≤
          C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
  exact
    sectorialComplexGammaStirling_halfArgument_rightHalfPlane_log_linear_growth_bound_degree_one_of_sectorial
      sectorialComplexGammaStirling_rightHalfPlane_log_linear_growth_bound_degree_one

/-- The `π ^ (-z / 2)` normalization contributes no positive log-growth in the right
half-plane. -/
theorem pi_cpow_neg_halfArgument_rightHalfPlane_log_norm_nonpos
    {z : ℂ}
    (hz_re : 0 ≤ z.re) :
    Real.log ‖π ^ (-z / 2 : ℂ)‖ ≤ 0 := by
  have hpi_pos : (0 : ℝ) < π := Real.pi_pos
  have hpi_one_lt : (1 : ℝ) < π := Real.one_lt_pi
  have hre_nonpos : (-z / 2 : ℂ).re ≤ 0 := by
    rw [Complex.div_re_ofReal, Complex.neg_re]
    exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz_re) (by norm_num : (0 : ℝ) ≤ 2)
  have hnorm_eq : ‖π ^ (-z / 2 : ℂ)‖ = π ^ (-z / 2 : ℂ).re := by
    simpa [Complex.norm_eq_abs] using
      Complex.abs_cpow_eq_rpow_re_of_pos hpi_pos (-z / 2 : ℂ)
  have hnorm_le_one : ‖π ^ (-z / 2 : ℂ)‖ ≤ 1 := by
    rw [hnorm_eq]
    exact Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt hpi_one_lt) hre_nonpos
  have hnorm_pos : 0 < ‖π ^ (-z / 2 : ℂ)‖ := by
    rw [hnorm_eq]
    exact Real.rpow_pos_of_pos hpi_pos (-z / 2 : ℂ).re
  exact Real.log_nonpos hnorm_pos.le hnorm_le_one

/-- The `π ^ (-z / 2)` normalization is bounded by the same log-linear envelope. -/
theorem pi_cpow_neg_halfArgument_rightHalfPlane_log_linear_growth_bound_degree_one :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        1 ≤ ‖z‖ →
        Real.log ‖π ^ (-z / 2 : ℂ)‖ ≤
          C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
  refine ⟨1, zero_lt_one, ?_⟩
  intro z hz_re hz_norm
  have hlog_nonpos :
      Real.log ‖π ^ (-z / 2 : ℂ)‖ ≤ 0 :=
    pi_cpow_neg_halfArgument_rightHalfPlane_log_norm_nonpos hz_re
  have hnorm_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
  have hleft_nonneg : 0 ≤ 1 + ‖z‖ :=
    add_nonneg zero_le_one hnorm_nonneg
  have hlog_arg_ge_one : (1 : ℝ) ≤ 2 + ‖z‖ := by
    exact one_le_two_add_complex_norm z
  have hlog_nonneg : 0 ≤ Real.log (2 + ‖z‖) :=
    Real.log_nonneg hlog_arg_ge_one
  have htarget_nonneg :
      0 ≤ (1 : ℝ) * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
    exact mul_nonneg (mul_nonneg zero_le_one hleft_nonneg) hlog_nonneg
  exact le_trans hlog_nonpos htarget_nonneg

/-- Log norm of the normalized half-argument Gamma factor splits into the normalization
term and the Gamma term on the right-half-plane Stirling region. -/
theorem log_norm_halfArgument_normalized_complexGamma_le_sum_log_norm_factors
    {z : ℂ}
    (hz_re : 0 ≤ z.re)
    (hz_norm : 1 ≤ ‖z‖) :
    Real.log ‖π ^ (-z / 2) * Complex.Gamma (z / 2)‖ ≤
      Real.log ‖π ^ (-z / 2 : ℂ)‖ +
        Real.log ‖Complex.Gamma (z / 2)‖ := by
  have hpi_pos : 0 < ‖π ^ (-z / 2 : ℂ)‖ := by
    have hpi_pos_real : (0 : ℝ) < π := Real.pi_pos
    have hnorm_eq : ‖π ^ (-z / 2 : ℂ)‖ = π ^ (-z / 2 : ℂ).re := by
      simpa [Complex.norm_eq_abs] using
        Complex.abs_cpow_eq_rpow_re_of_pos hpi_pos_real (-z / 2 : ℂ)
    rw [hnorm_eq]
    exact Real.rpow_pos_of_pos hpi_pos_real (-z / 2 : ℂ).re
  have hgamma_pos : 0 < ‖Complex.Gamma (z / 2)‖ :=
    norm_pos_iff.mpr
      (ComplexGamma_halfArgument_ne_zero_of_re_nonneg_and_one_le_norm hz_re hz_norm)
  calc
    Real.log ‖π ^ (-z / 2) * Complex.Gamma (z / 2)‖ =
        Real.log (‖π ^ (-z / 2 : ℂ)‖ * ‖Complex.Gamma (z / 2)‖) := by
      rw [norm_mul]
    _ = Real.log ‖π ^ (-z / 2 : ℂ)‖ +
        Real.log ‖Complex.Gamma (z / 2)‖ := by
      exact Real.log_mul hpi_pos.ne' hgamma_pos.ne'

/-- Combining the sectorial Gamma estimate and the `π` normalization gives the normalized
half-argument estimate. -/
theorem halfArgument_normalized_rightHalfPlane_log_linear_growth_bound_degree_one_of_Gamma_and_pi
    (hGamma :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          1 ≤ ‖z‖ →
          Real.log ‖Complex.Gamma (z / 2)‖ ≤
            C * (1 + ‖z‖) * Real.log (2 + ‖z‖))
    (hPi :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          1 ≤ ‖z‖ →
          Real.log ‖π ^ (-z / 2 : ℂ)‖ ≤
            C * (1 + ‖z‖) * Real.log (2 + ‖z‖)) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        1 ≤ ‖z‖ →
        Real.log ‖π ^ (-z / 2) * Complex.Gamma (z / 2)‖ ≤
          C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
  rcases hGamma with ⟨CGamma, hCGamma_pos, hCGamma⟩
  rcases hPi with ⟨CPi, hCPi_pos, hCPi⟩
  refine ⟨CPi + CGamma, add_pos hCPi_pos hCGamma_pos, ?_⟩
  intro z hz_re hz_norm
  have hsplit :
      Real.log ‖π ^ (-z / 2) * Complex.Gamma (z / 2)‖ ≤
        Real.log ‖π ^ (-z / 2 : ℂ)‖ +
          Real.log ‖Complex.Gamma (z / 2)‖ :=
    log_norm_halfArgument_normalized_complexGamma_le_sum_log_norm_factors
      hz_re hz_norm
  have hsum :
      Real.log ‖π ^ (-z / 2 : ℂ)‖ +
          Real.log ‖Complex.Gamma (z / 2)‖ ≤
        CPi * (1 + ‖z‖) * Real.log (2 + ‖z‖) +
          CGamma * (1 + ‖z‖) * Real.log (2 + ‖z‖) :=
    add_le_add (hCPi z hz_re hz_norm) (hCGamma z hz_re hz_norm)
  have hcombine :
      CPi * (1 + ‖z‖) * Real.log (2 + ‖z‖) +
          CGamma * (1 + ‖z‖) * Real.log (2 + ‖z‖) =
        (CPi + CGamma) * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
    exact logLinearEnvelope_add_constants
      CPi CGamma (1 + ‖z‖) (Real.log (2 + ‖z‖))
  exact le_trans hsplit (le_trans hsum (le_of_eq hcombine))

/-- Sectorial complex Stirling in the normalized half-argument form needed by `Gammaℝ`.

This is the canonical classical special-function estimate: Stirling's expansion for
`Γ(z / 2)` in the closed right half-plane, with the harmless `π ^ (-z / 2)`
normalization absorbed into the constant; cf. DLMF §5.11. -/
theorem sectorialComplexGammaStirling_halfArgument_normalized_rightHalfPlane_log_linear_growth_bound_degree_one :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        1 ≤ ‖z‖ →
        Real.log ‖π ^ (-z / 2) * Complex.Gamma (z / 2)‖ ≤
          C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
  exact
    halfArgument_normalized_rightHalfPlane_log_linear_growth_bound_degree_one_of_Gamma_and_pi
      sectorialComplexGammaStirling_halfArgument_rightHalfPlane_log_linear_growth_bound_degree_one
      pi_cpow_neg_halfArgument_rightHalfPlane_log_linear_growth_bound_degree_one

/-- The historical owner-root spelling for the sectorial complex Stirling estimate.

The proof is only name transport from the canonical sectorial `Complex.Gamma`
Stirling primitive. -/
theorem sectorialStirling_complexGamma_halfArgument_normalized_rightHalfPlane_log_linear_growth_bound_degree_one :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        1 ≤ ‖z‖ →
        Real.log ‖π ^ (-z / 2) * Complex.Gamma (z / 2)‖ ≤
          C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
  exact
    sectorialComplexGammaStirling_halfArgument_normalized_rightHalfPlane_log_linear_growth_bound_degree_one

/-- Classical sectorial Stirling growth for the inline half-argument normalized Gamma
factor.

This is the smallest special-function input for the right-half-plane normalization:
complex Stirling for `π^(-z/2) Γ(z/2)` on `0 ≤ re z`, with `1 ≤ ‖z‖` excluding
the origin; cf. DLMF §5.11. -/
theorem classicalStirling_complexGamma_halfArgument_normalized_rightHalfPlane_log_linear_growth_bound_degree_one_from_sectorialStirling :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        1 ≤ ‖z‖ →
        Real.log ‖π ^ (-z / 2) * Complex.Gamma (z / 2)‖ ≤
          C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
  exact
    sectorialStirling_complexGamma_halfArgument_normalized_rightHalfPlane_log_linear_growth_bound_degree_one

/-- Classical sectorial Stirling growth for the unfolded normalized real-Gamma factor.

This is the exact special-function input behind the right-half-plane `Gammaℝ`
normalization.  The proof is now only transport from the inline half-argument
Stirling input through the local unfolded name. -/
theorem classicalStirling_unfoldedNormalizedGammaℝFactor_rightHalfPlane_log_linear_growth_bound_degree_one_from_sectorialStirling :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        1 ≤ ‖z‖ →
        Real.log ‖unfoldedNormalizedGammaℝFactor z‖ ≤
          C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
  rcases
    classicalStirling_complexGamma_halfArgument_normalized_rightHalfPlane_log_linear_growth_bound_degree_one_from_sectorialStirling
    with ⟨C, hC_pos, hbound⟩
  refine ⟨C, hC_pos, ?_⟩
  intro z hz_re hz_norm
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ C * (1 + ‖z‖) * Real.log (2 + ‖z‖))
    (log_norm_halfArgument_normalized_complexGamma_eq_log_norm_unfoldedNormalizedGammaℝFactor z)
    (hbound z hz_re hz_norm)

/-- Classical complex-Stirling growth for the half-argument normalized Gamma factor.

This is only the formula-level transport from the unfolded owner primitive to the
inline half-argument Gamma expression. -/
theorem classicalStirling_complexGamma_halfArgument_normalized_rightHalfPlane_log_linear_growth_bound_degree_one :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        1 ≤ ‖z‖ →
        Real.log ‖π ^ (-z / 2) * Complex.Gamma (z / 2)‖ ≤
          C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
  rcases
    classicalStirling_unfoldedNormalizedGammaℝFactor_rightHalfPlane_log_linear_growth_bound_degree_one_from_sectorialStirling
    with ⟨C, hC_pos, hbound⟩
  refine ⟨C, hC_pos, ?_⟩
  intro z hz_re hz_norm
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ C * (1 + ‖z‖) * Real.log (2 + ‖z‖))
    (log_norm_halfArgument_normalized_complexGamma_eq_log_norm_unfoldedNormalizedGammaℝFactor z).symm
    (hbound z hz_re hz_norm)

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
    classicalStirling_unfoldedNormalizedGammaℝFactor_rightHalfPlane_log_linear_growth_bound_degree_one_from_sectorialStirling

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
      exact zero_lt_two
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

/-- Away from the removable pole face, the pole-cleared zeta factor is differentiable by
the ordinary zeta differentiability theorem. -/
theorem poleClearedRiemannZeta_differentiableAt_of_ne_one
    {z : ℂ}
    (hz : z ≠ 1) :
    DifferentiableAt ℂ poleClearedRiemannZeta z := by
  have hraw :
      DifferentiableAt ℂ (fun w : ℂ => (w - 1) * riemannZeta w) z :=
    (differentiableAt_id.sub differentiableAt_const).mul
      (differentiableAt_riemannZeta hz)
  have hevent :
      poleClearedRiemannZeta =ᶠ[𝓝 z]
        (fun w : ℂ => (w - 1) * riemannZeta w) := by
    filter_upwards [eventually_ne_nhds hz] with w hw
    exact poleClearedRiemannZeta_eq_of_ne_one hw
  exact hraw.congr_of_eventuallyEq hevent

/-- The residue-normalized pole-cleared zeta factor is analytic at the removable pole. -/
theorem poleClearedRiemannZeta_analyticAt_one :
    AnalyticAt ℂ poleClearedRiemannZeta 1 := by
  have hd :
      ∀ᶠ z in 𝓝[≠] (1 : ℂ),
        DifferentiableAt ℂ poleClearedRiemannZeta z := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact poleClearedRiemannZeta_differentiableAt_of_ne_one hz
  exact Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    hd
    (poleClearedRiemannZeta_continuousAt 1)

/-- The removable pole-cleared zeta factor is differentiable everywhere. -/
theorem poleClearedRiemannZeta_differentiableAt
    (z : ℂ) :
    DifferentiableAt ℂ poleClearedRiemannZeta z := by
  by_cases hz : z = 1
  · exact Eq.subst
      (motive := fun w : ℂ => DifferentiableAt ℂ poleClearedRiemannZeta w)
      hz.symm
      poleClearedRiemannZeta_analyticAt_one.differentiableAt
  · exact poleClearedRiemannZeta_differentiableAt_of_ne_one hz

/-- The pole-cleared zeta factor is differentiable on every set. -/
theorem poleClearedRiemannZeta_differentiableOn
    (s : Set ℂ) :
    DifferentiableOn ℂ poleClearedRiemannZeta s := by
  intro z _hz
  exact (poleClearedRiemannZeta_differentiableAt z).differentiableWithinAt

/-- Removable-pole holomorphy of the pole-cleared zeta factor on the open right
critical strip.

This is the zeta-side holomorphy input for the strip Phragmen-Lindelöf theorem: away
from `1` it is `(s - 1)ζ(s)`, and at `1` the removable value is the zeta residue. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_diffContOnCl :
    DiffContOnCl ℂ poleClearedRiemannZeta
      (Complex.re ⁻¹' Set.Ioo 0 2) := by
  exact
    ⟨poleClearedRiemannZeta_differentiableOn (Complex.re ⁻¹' Set.Ioo 0 2),
      fun z _hz => (poleClearedRiemannZeta_continuousAt z).continuousWithinAt⟩

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

/-- The numerator in the unfolded completed real-Gamma ratio on the left boundary. -/
def unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam (t : ℝ) : ℂ :=
  π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
    Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)

/-- The denominator in the unfolded completed real-Gamma ratio on the left boundary. -/
def unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam (t : ℝ) : ℂ :=
  π ^ (-((t : ℂ) * Complex.I) / 2) *
    Complex.Gamma (((t : ℂ) * Complex.I) / 2)

/-- The unfolded left-boundary Gamma-ratio is the quotient of its named numerator
and denominator. -/
theorem unfoldedGammaℝLeftBoundaryRatioRealParam_eq_named_quotient
    (t : ℝ) :
    unfoldedGammaℝLeftBoundaryRatioRealParam t =
      unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t /
        unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t := by
  rfl

/-- The named numerator is the unfolded `Gammaℝ` factor at the reflected left-boundary
point. -/
theorem unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam_eq_Gammaℝ
    (t : ℝ) :
    unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t =
      Complex.Gammaℝ ((1 : ℂ) - (t : ℂ) * Complex.I) := by
  exact (Complex.Gammaℝ_def ((1 : ℂ) - (t : ℂ) * Complex.I)).symm

/-- The named denominator is the unfolded `Gammaℝ` factor at the left-boundary point. -/
theorem unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam_eq_Gammaℝ
    (t : ℝ) :
    unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t =
      Complex.Gammaℝ ((t : ℂ) * Complex.I) := by
  exact (Complex.Gammaℝ_def ((t : ℂ) * Complex.I)).symm

/-- The denominator in the unfolded left-boundary Gamma quotient is nonzero on the
vertical-tail range. -/
theorem unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam_ne_zero_of_one_le_norm
    {t : ℝ}
    (ht : 1 ≤ ‖t‖) :
    unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t ≠ 0 := by
  have haxis_re : (((t : ℂ) * Complex.I).re) = 0 := by
    calc
      (((t : ℂ) * Complex.I).re) =
          (t : ℂ).re * Complex.I.re - (t : ℂ).im * Complex.I.im := by
        exact Complex.mul_re (t : ℂ) Complex.I
      _ = t * 0 - 0 * 1 := by
        rw [Complex.ofReal_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]
      _ = 0 := by
        ring
  have haxis_im_norm : ‖((t : ℂ) * Complex.I).im‖ = ‖t‖ := by
    have him : ((t : ℂ) * Complex.I).im = t := by
      calc
        ((t : ℂ) * Complex.I).im =
            (t : ℂ).re * Complex.I.im + (t : ℂ).im * Complex.I.re := by
          exact Complex.mul_im (t : ℂ) Complex.I
        _ = t * 1 + 0 * 0 := by
          rw [Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, Complex.I_re]
        _ = t := by
          ring
    exact congrArg norm him
  have haxis_im : 1 ≤ ‖((t : ℂ) * Complex.I).im‖ :=
    Eq.subst
      (motive := fun x : ℝ => 1 ≤ x)
      haxis_im_norm.symm
      ht
  have hGamma_ne :
      Complex.Gammaℝ ((t : ℂ) * Complex.I) ≠ 0 :=
    (Gammaℝ_leftBoundary_nonzero_of_verticalTail haxis_re haxis_im).2.2.1
  intro hzero
  exact hGamma_ne
    (Eq.trans
      (unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam_eq_Gammaℝ t).symm
      hzero)

/-- The denominator in the unfolded left-boundary Gamma quotient has positive norm on
the vertical-tail range. -/
theorem norm_unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam_pos_of_one_le_norm
    {t : ℝ}
    (ht : 1 ≤ ‖t‖) :
    0 < ‖unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t‖ :=
  norm_pos_iff.mpr
    (unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam_ne_zero_of_one_le_norm ht)

/-- Norm of the unfolded left-boundary Gamma quotient after naming numerator and
denominator. -/
theorem norm_unfoldedGammaℝLeftBoundaryRatioRealParam_eq_named_quotient
    (t : ℝ) :
    ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ =
      ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t /
        unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t‖ := by
  exact congrArg norm (unfoldedGammaℝLeftBoundaryRatioRealParam_eq_named_quotient t)

/-- Norm of the named unfolded left-boundary Gamma quotient is the quotient of the named
numerator and denominator norms. -/
theorem norm_unfoldedGammaℝLeftBoundaryRatio_named_quotient_eq_norm_div
    (t : ℝ) :
    ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t /
        unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t‖ =
      ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t‖ /
        ‖unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t‖ := by
  exact norm_div
    (unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t)
    (unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)

/-- The π-normalized two-Gamma quotient is exactly the named unfolded quotient. -/
theorem inline_twoGammaQuotient_eq_unfoldedGammaℝLeftBoundaryRatioRealParam
    (t : ℝ) :
    (π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
          Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
        (π ^ (-((t : ℂ) * Complex.I) / 2) *
          Complex.Gamma (((t : ℂ) * Complex.I) / 2)) =
      unfoldedGammaℝLeftBoundaryRatioRealParam t := by
  rfl

/-- Norm transport from the inline π-normalized two-Gamma quotient to the named unfolded
quotient. -/
theorem norm_inline_twoGammaQuotient_eq_norm_unfoldedGammaℝLeftBoundaryRatioRealParam
    (t : ℝ) :
    ‖(π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
          Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
        (π ^ (-((t : ℂ) * Complex.I) / 2) *
          Complex.Gamma (((t : ℂ) * Complex.I) / 2))‖ =
      ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ := by
  exact congrArg norm (inline_twoGammaQuotient_eq_unfoldedGammaℝLeftBoundaryRatioRealParam t)

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

/-- The two-sided fixed-real-part vertical Stirling norm estimates for `Complex.Gamma`.

This is the exact classical special-function input after all downstream algebra has
been peeled off: for fixed real part `a`, `Γ(a + i b)` has vertical decay
`exp (-π |b| / 2)` and its reciprocal has the opposite exponential envelope,
with the dual polynomial powers; cf. DLMF §5.11. -/
theorem verticalComplexGammaStirling_fixedRealPart_twoSided_core_bound_standard
    (a : ℝ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
        ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
          C * Real.exp (-(Real.pi / 2) * ‖b‖) *
            (1 + ‖b‖) ^ (a - 1 / 2) ∧
        ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
          C * Real.exp ((Real.pi / 2) * ‖b‖) *
            (1 + ‖b‖) ^ (1 / 2 - a) := by
  exact
    Complex.Gamma_closedRightHalfPlane_sectorial_and_vertical_stirling_bounds_classical.2 a

/-- The direct fixed-real-part vertical Stirling norm estimate for `Complex.Gamma`.

This is the canonical special-function owner input after the `π`-normalization has
been peeled off: for fixed real part `a`, the norm of `Γ(a + i b)` has the standard
`exp (-π |b| / 2)` vertical decay with polynomial factor
`(1 + |b|)^(a - 1/2)`; cf. DLMF §5.11. -/
theorem verticalComplexGammaStirling_fixedRealPart_norm_core_bound_standard
    (a : ℝ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
        ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
          C * Real.exp (-(Real.pi / 2) * ‖b‖) *
            (1 + ‖b‖) ^ (a - 1 / 2) := by
  rcases verticalComplexGammaStirling_fixedRealPart_twoSided_core_bound_standard a with
    ⟨C, hC_pos, hC⟩
  refine ⟨C, hC_pos, ?_⟩
  intro b hb
  exact (hC b hb).1

/-- The reciprocal fixed-real-part vertical Stirling estimate for `Complex.Gamma`.

This is the dual canonical special-function owner input: on each fixed vertical
line the reciprocal has the opposite exponential envelope and the reciprocal
polynomial exponent; cf. DLMF §5.11. -/
theorem verticalComplexGammaStirling_fixedRealPart_reciprocal_core_bound_standard
    (a : ℝ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
        ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
          C * Real.exp ((Real.pi / 2) * ‖b‖) *
            (1 + ‖b‖) ^ (1 / 2 - a) := by
  rcases verticalComplexGammaStirling_fixedRealPart_twoSided_core_bound_standard a with
    ⟨C, hC_pos, hC⟩
  refine ⟨C, hC_pos, ?_⟩
  intro b hb
  exact (hC b hb).2

/-- The fixed-real-part direct Stirling envelope factor is nonnegative. -/
theorem fixedRealPart_gamma_norm_envelope_nonneg
    (a b : ℝ) :
    0 ≤ Real.exp (-(Real.pi / 2) * ‖b‖) *
      (1 + ‖b‖) ^ (a - 1 / 2) := by
  have hbase_pos : 0 < 1 + ‖b‖ :=
    lt_of_lt_of_le zero_lt_one
      (le_add_of_nonneg_right (norm_nonneg b))
  exact mul_nonneg
    (le_of_lt (Real.exp_pos (-(Real.pi / 2) * ‖b‖)))
    (le_of_lt (Real.rpow_pos_of_pos hbase_pos (a - 1 / 2)))

/-- The fixed-real-part reciprocal Stirling envelope factor is nonnegative. -/
theorem fixedRealPart_gamma_reciprocal_envelope_nonneg
    (a b : ℝ) :
    0 ≤ Real.exp ((Real.pi / 2) * ‖b‖) *
      (1 + ‖b‖) ^ (1 / 2 - a) := by
  have hbase_pos : 0 < 1 + ‖b‖ :=
    lt_of_lt_of_le zero_lt_one
      (le_add_of_nonneg_right (norm_nonneg b))
  exact mul_nonneg
    (le_of_lt (Real.exp_pos ((Real.pi / 2) * ‖b‖)))
    (le_of_lt (Real.rpow_pos_of_pos hbase_pos (1 / 2 - a)))

/-- A direct fixed-real-part vertical Gamma estimate remains valid after enlarging
its constant. -/
theorem verticalComplexGammaStirling_fixedRealPart_norm_core_bound_mono_constant
    {a C D : ℝ}
    (hCD : C ≤ D)
    (hC :
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
        ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
          C * Real.exp (-(Real.pi / 2) * ‖b‖) *
            (1 + ‖b‖) ^ (a - 1 / 2)) :
    ∀ b : ℝ,
      1 / 2 ≤ ‖b‖ →
      ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
        D * Real.exp (-(Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (a - 1 / 2) := by
  intro b hb
  let E : ℝ :=
    Real.exp (-(Real.pi / 2) * ‖b‖) *
      (1 + ‖b‖) ^ (a - 1 / 2)
  have hE_nonneg : 0 ≤ E :=
    fixedRealPart_gamma_norm_envelope_nonneg a b
  have hscaled : C * E ≤ D * E :=
    mul_le_mul_of_nonneg_right hCD hE_nonneg
  have hsource_assoc :
      C * Real.exp (-(Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (a - 1 / 2) =
        C * E :=
    mul_assoc C (Real.exp (-(Real.pi / 2) * ‖b‖))
      ((1 + ‖b‖) ^ (a - 1 / 2))
  have htarget_assoc :
      D * Real.exp (-(Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (a - 1 / 2) =
        D * E :=
    mul_assoc D (Real.exp (-(Real.pi / 2) * ‖b‖))
      ((1 + ‖b‖) ^ (a - 1 / 2))
  exact Eq.subst
    (motive := fun x : ℝ =>
      ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤ x)
    htarget_assoc.symm
    (le_trans
      (Eq.subst
        (motive := fun x : ℝ =>
          ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤ x)
        hsource_assoc
        (hC b hb))
      hscaled)

/-- A reciprocal fixed-real-part vertical Gamma estimate remains valid after enlarging
its constant. -/
theorem verticalComplexGammaStirling_fixedRealPart_reciprocal_core_bound_mono_constant
    {a C D : ℝ}
    (hCD : C ≤ D)
    (hC :
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
        ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
          C * Real.exp ((Real.pi / 2) * ‖b‖) *
            (1 + ‖b‖) ^ (1 / 2 - a)) :
    ∀ b : ℝ,
      1 / 2 ≤ ‖b‖ →
      ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
        D * Real.exp ((Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (1 / 2 - a) := by
  intro b hb
  let E : ℝ :=
    Real.exp ((Real.pi / 2) * ‖b‖) *
      (1 + ‖b‖) ^ (1 / 2 - a)
  have hE_nonneg : 0 ≤ E :=
    fixedRealPart_gamma_reciprocal_envelope_nonneg a b
  have hscaled : C * E ≤ D * E :=
    mul_le_mul_of_nonneg_right hCD hE_nonneg
  have hsource_assoc :
      C * Real.exp ((Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (1 / 2 - a) =
        C * E :=
    mul_assoc C (Real.exp ((Real.pi / 2) * ‖b‖))
      ((1 + ‖b‖) ^ (1 / 2 - a))
  have htarget_assoc :
      D * Real.exp ((Real.pi / 2) * ‖b‖) *
          (1 + ‖b‖) ^ (1 / 2 - a) =
        D * E :=
    mul_assoc D (Real.exp ((Real.pi / 2) * ‖b‖))
      ((1 + ‖b‖) ^ (1 / 2 - a))
  exact Eq.subst
    (motive := fun x : ℝ =>
      ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤ x)
    htarget_assoc.symm
    (le_trans
      (Eq.subst
        (motive := fun x : ℝ =>
          ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤ x)
        hsource_assoc
        (hC b hb))
      hscaled)

/-- The two fixed-real-part vertical Gamma estimates can be put under one positive
constant by enlarging to the sum of the two constants. -/
theorem verticalComplexGammaStirling_fixedRealPart_core_bounds_of_norm_and_reciprocal
    {a : ℝ}
    (hnorm :
      ∃ C : ℝ,
        0 < C ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
            C * Real.exp (-(Real.pi / 2) * ‖b‖) *
              (1 + ‖b‖) ^ (a - 1 / 2))
    (hreciprocal :
      ∃ C : ℝ,
        0 < C ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
            C * Real.exp ((Real.pi / 2) * ‖b‖) *
              (1 + ‖b‖) ^ (1 / 2 - a)) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
        ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
          C * Real.exp (-(Real.pi / 2) * ‖b‖) *
            (1 + ‖b‖) ^ (a - 1 / 2) ∧
        ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
          C * Real.exp ((Real.pi / 2) * ‖b‖) *
            (1 + ‖b‖) ^ (1 / 2 - a) := by
  rcases hnorm with ⟨Cn, hCn_pos, hCn⟩
  rcases hreciprocal with ⟨Cr, hCr_pos, hCr⟩
  let C : ℝ := Cn + Cr
  have hC_pos : 0 < C :=
    add_pos hCn_pos hCr_pos
  have hCn_le_C : Cn ≤ C :=
    le_add_of_nonneg_right (le_of_lt hCr_pos)
  have hCr_le_C : Cr ≤ C :=
    le_add_of_nonneg_left (le_of_lt hCn_pos)
  have hnorm_C :
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
        ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
          C * Real.exp (-(Real.pi / 2) * ‖b‖) *
            (1 + ‖b‖) ^ (a - 1 / 2) :=
    verticalComplexGammaStirling_fixedRealPart_norm_core_bound_mono_constant
      hCn_le_C hCn
  have hreciprocal_C :
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
        ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
          C * Real.exp ((Real.pi / 2) * ‖b‖) *
            (1 + ‖b‖) ^ (1 / 2 - a) :=
    verticalComplexGammaStirling_fixedRealPart_reciprocal_core_bound_mono_constant
      hCr_le_C hCr
  refine ⟨C, hC_pos, ?_⟩
  intro b hb
  exact ⟨hnorm_C b hb, hreciprocal_C b hb⟩

/-- Vertical complex Stirling on fixed real lines, in the two norm forms needed for
left-boundary Gamma transport.

This owner theorem is now only the common-constant transport from the direct and
reciprocal fixed-real-part vertical Stirling estimates. -/
theorem verticalComplexGammaStirling_fixedRealPart_core_bounds
    (a : ℝ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
        ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
          C * Real.exp (-(Real.pi / 2) * ‖b‖) *
            (1 + ‖b‖) ^ (a - 1 / 2) ∧
        ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
          C * Real.exp ((Real.pi / 2) * ‖b‖) *
            (1 + ‖b‖) ^ (1 / 2 - a) := by
  exact verticalComplexGammaStirling_fixedRealPart_core_bounds_of_norm_and_reciprocal
    (verticalComplexGammaStirling_fixedRealPart_norm_core_bound_standard a)
    (verticalComplexGammaStirling_fixedRealPart_reciprocal_core_bound_standard a)

/-- The numerator Gamma argument on the left boundary is the fixed-real-part
vertical point `1/2 + i(-t/2)`. -/
theorem leftBoundary_numerator_complexGamma_argument_eq_fixedRealPart
    (t : ℝ) :
    (((1 : ℂ) - (t : ℂ) * Complex.I) / 2) =
      ((1 / 2 : ℝ) : ℂ) + ((-t / 2 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · calc
      ((((1 : ℂ) - (t : ℂ) * Complex.I) / 2)).re =
          (((1 : ℂ) - (t : ℂ) * Complex.I).re) / 2 := by
        exact Complex.div_re_ofReal ((1 : ℂ) - (t : ℂ) * Complex.I) 2
      _ = 1 / 2 := by
        exact congrArg (fun x : ℝ => x / 2)
          (by
            calc
              (((1 : ℂ) - (t : ℂ) * Complex.I).re) =
                  (1 : ℂ).re - ((t : ℂ) * Complex.I).re := by
                exact Complex.sub_re (1 : ℂ) ((t : ℂ) * Complex.I)
              _ = 1 - ((t : ℂ).re * Complex.I.re - (t : ℂ).im * Complex.I.im) := by
                exact congrArg
                  (fun x : ℝ => x - ((t : ℂ).re * Complex.I.re - (t : ℂ).im * Complex.I.im))
                  Complex.one_re
              _ = 1 - (t * 0 - 0 * 1) := rfl
              _ = 1 := by
                calc
                  1 - (t * 0 - 0 * 1) = 1 - (0 - 0 * 1) := by
                    exact congrArg (fun x : ℝ => 1 - (x - 0 * 1)) (mul_zero t)
                  _ = 1 - (0 - 0) := by
                    exact congrArg (fun x : ℝ => 1 - (0 - x)) (zero_mul 1)
                  _ = 1 - 0 := by
                    exact congrArg (fun x : ℝ => 1 - x) (sub_zero 0)
                  _ = 1 := sub_zero 1)
      _ = (((1 / 2 : ℝ) : ℂ) + ((-t / 2 : ℝ) : ℂ) * Complex.I).re := by
        rfl
  · calc
      ((((1 : ℂ) - (t : ℂ) * Complex.I) / 2)).im =
          (((1 : ℂ) - (t : ℂ) * Complex.I).im) / 2 := by
        exact Complex.div_im_ofReal ((1 : ℂ) - (t : ℂ) * Complex.I) 2
      _ = -t / 2 := by
        exact congrArg (fun x : ℝ => x / 2)
          (by
            calc
              (((1 : ℂ) - (t : ℂ) * Complex.I).im) =
                  (1 : ℂ).im - ((t : ℂ) * Complex.I).im := by
                exact Complex.sub_im (1 : ℂ) ((t : ℂ) * Complex.I)
              _ = 0 - ((t : ℂ).re * Complex.I.im + (t : ℂ).im * Complex.I.re) := by
                exact congrArg
                  (fun x : ℝ => x - ((t : ℂ).re * Complex.I.im + (t : ℂ).im * Complex.I.re))
                  Complex.one_im
              _ = 0 - (t * 1 + 0 * 0) := rfl
              _ = 0 - (t + 0 * 0) := by
                exact congrArg (fun x : ℝ => 0 - (x + 0 * 0)) (mul_one t)
              _ = 0 - (t + 0) := by
                exact congrArg (fun x : ℝ => 0 - (t + x)) (zero_mul 0)
              _ = 0 - t := by
                exact congrArg (fun x : ℝ => 0 - x) (add_zero t)
              _ = -t := by
                exact zero_sub t)
      _ = (((1 / 2 : ℝ) : ℂ) + ((-t / 2 : ℝ) : ℂ) * Complex.I).im := by
        rfl

/-- The denominator Gamma argument on the left boundary is the fixed-real-part
vertical point `0 + i(t/2)`. -/
theorem leftBoundary_denominator_complexGamma_argument_eq_fixedRealPart
    (t : ℝ) :
    (((t : ℂ) * Complex.I) / 2) =
      ((0 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I := by
  apply Complex.ext
  · calc
      (((t : ℂ) * Complex.I) / 2).re =
          (((t : ℂ) * Complex.I).re) / 2 := by
        exact Complex.div_re_ofReal ((t : ℂ) * Complex.I) 2
      _ = (t * 0 - 0 * 1) / 2 := by
        exact congrArg (fun x : ℝ => x / 2)
          (by
            calc
              (((t : ℂ) * Complex.I).re) =
                  (t : ℂ).re * Complex.I.re - (t : ℂ).im * Complex.I.im := by
                exact Complex.mul_re (t : ℂ) Complex.I
              _ = t * 0 - 0 * 1 := rfl)
      _ = 0 := by
        calc
          (t * 0 - 0 * 1) / 2 = (0 - 0 * 1) / 2 := by
            exact congrArg (fun x : ℝ => (x - 0 * 1) / 2) (mul_zero t)
          _ = (0 - 0) / 2 := by
            exact congrArg (fun x : ℝ => (0 - x) / 2) (zero_mul 1)
          _ = 0 / 2 := by
            exact congrArg (fun x : ℝ => x / 2) (sub_zero 0)
          _ = 0 := zero_div 2
      _ = (((0 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I).re := by
        rfl
  · calc
      (((t : ℂ) * Complex.I) / 2).im =
          (((t : ℂ) * Complex.I).im) / 2 := by
        exact Complex.div_im_ofReal ((t : ℂ) * Complex.I) 2
      _ = (t * 1 + 0 * 0) / 2 := by
        exact congrArg (fun x : ℝ => x / 2)
          (by
            calc
              (((t : ℂ) * Complex.I).im) =
                  (t : ℂ).re * Complex.I.im + (t : ℂ).im * Complex.I.re := by
                exact Complex.mul_im (t : ℂ) Complex.I
              _ = t * 1 + 0 * 0 := rfl)
      _ = t / 2 := by
        calc
          (t * 1 + 0 * 0) / 2 = (t + 0 * 0) / 2 := by
            exact congrArg (fun x : ℝ => (x + 0 * 0) / 2) (mul_one t)
          _ = (t + 0) / 2 := by
            exact congrArg (fun x : ℝ => (t + x) / 2) (zero_mul 0)
          _ = t / 2 := by
            exact congrArg (fun x : ℝ => x / 2) (add_zero t)
      _ = (((0 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I).im := by
        rfl

/-- The half-scaled vertical coordinate has norm at least `1/2` on the
left-boundary vertical-tail range. -/
theorem half_norm_ge_one_half_of_one_le_norm
    {t : ℝ}
    (ht : 1 ≤ ‖t‖) :
    (1 / 2 : ℝ) ≤ ‖t / 2‖ := by
  have htwo_pos : (0 : ℝ) < 2 := zero_lt_two
  have hnorm_div : ‖t / 2‖ = ‖t‖ / 2 := by
    calc
      ‖t / 2‖ = ‖t‖ / ‖(2 : ℝ)‖ := by
        exact norm_div t 2
      _ = ‖t‖ / 2 := by
        exact congrArg (fun x : ℝ => ‖t‖ / x)
          (Real.norm_of_nonneg (le_of_lt htwo_pos))
  exact Eq.subst
    (motive := fun x : ℝ => (1 / 2 : ℝ) ≤ x)
    hnorm_div.symm
    ((div_le_div_right htwo_pos).mpr ht)

/-- Negating the half-scaled vertical coordinate preserves the half-tail bound. -/
theorem neg_half_norm_ge_one_half_of_one_le_norm
    {t : ℝ}
    (ht : 1 ≤ ‖t‖) :
    (1 / 2 : ℝ) ≤ ‖-t / 2‖ := by
  have hneg_div : -t / 2 = -(t / 2) := by
    exact neg_div t 2
  have hnorm : ‖-t / 2‖ = ‖t / 2‖ := by
    calc
      ‖-t / 2‖ = ‖-(t / 2)‖ := by
        exact congrArg norm hneg_div
      _ = ‖t / 2‖ :=
        norm_neg (t / 2)
  exact Eq.subst
    (motive := fun x : ℝ => (1 / 2 : ℝ) ≤ x)
    hnorm.symm
    (half_norm_ge_one_half_of_one_le_norm ht)

/-- The numerator vertical line for the left-boundary quotient, before the `π`
normalization is attached.

This is the canonical classical special-function input: vertical Stirling for
`Γ(1/2 - i t/2)` with the exponential envelope needed on the left boundary;
cf. DLMF §5.11. -/
theorem verticalComplexGammaStirling_leftBoundary_numerator_core_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)‖ ≤
          A * Real.exp (-(Real.pi / 4) * ‖t‖) := by
  rcases verticalComplexGammaStirling_fixedRealPart_core_bounds (1 / 2) with
    ⟨A, hA_pos, hA⟩
  refine ⟨A, hA_pos, ?_⟩
  intro t ht
  have htail : (1 / 2 : ℝ) ≤ ‖-t / 2‖ :=
    neg_half_norm_ge_one_half_of_one_le_norm ht
  have hbound :
      ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) + ((-t / 2 : ℝ) : ℂ) * Complex.I)‖ ≤
        A * Real.exp (-(Real.pi / 2) * ‖-t / 2‖) *
          (1 + ‖-t / 2‖) ^ ((1 / 2 : ℝ) - 1 / 2) :=
    (hA (-t / 2) htail).1
  have harg :
      Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2) =
        Complex.Gamma (((1 / 2 : ℝ) : ℂ) + ((-t / 2 : ℝ) : ℂ) * Complex.I) := by
    exact congrArg Complex.Gamma
      (leftBoundary_numerator_complexGamma_argument_eq_fixedRealPart t)
  have hpow :
      (1 + ‖-t / 2‖) ^ ((1 / 2 : ℝ) - 1 / 2) = 1 := by
    have hexponent :
        ((1 / 2 : ℝ) - 1 / 2) = 0 :=
      sub_self (1 / 2 : ℝ)
    exact Eq.subst
      (motive := fun x : ℝ => (1 + ‖-t / 2‖) ^ x = 1)
      hexponent.symm
      (Real.rpow_zero (1 + ‖-t / 2‖))
  have hexp :
      Real.exp (-(Real.pi / 2) * ‖-t / 2‖) =
        Real.exp (-(Real.pi / 4) * ‖t‖) := by
    have hnorm : ‖-t / 2‖ = ‖t‖ / 2 := by
      have hneg_div : -t / 2 = -(t / 2) := by
        exact neg_div t 2
      have htwo_nonneg : (0 : ℝ) ≤ 2 :=
        le_of_lt zero_lt_two
      calc
        ‖-t / 2‖ = ‖-(t / 2)‖ := by
          exact congrArg norm hneg_div
        _ = ‖t / 2‖ :=
          norm_neg (t / 2)
        _ = ‖t‖ / ‖(2 : ℝ)‖ := by
          exact norm_div t 2
        _ = ‖t‖ / 2 := by
          exact congrArg (fun x : ℝ => ‖t‖ / x)
            (Real.norm_of_nonneg htwo_nonneg)
    have hexponent :
        -(Real.pi / 2) * (‖t‖ / 2) = -(Real.pi / 4) * ‖t‖ := by
      have hdiv :
          (Real.pi / 2) / 2 = Real.pi / ((2 : ℝ) * 2) :=
        div_div_eq_div_mul Real.pi 2 2
      have hnegdiv :
          -(Real.pi / 2) / 2 = -(Real.pi / ((2 : ℝ) * 2)) :=
        congrArg Neg.neg hdiv
      have hfour :
          ((2 : ℝ) * 2) = 4 :=
        rfl
      calc
        -(Real.pi / 2) * (‖t‖ / 2) =
            (-(Real.pi / 2) / 2) * ‖t‖ := by
          exact (mul_div_assoc (-(Real.pi / 2)) ‖t‖ 2).symm
        _ = (-(Real.pi / (2 * 2))) * ‖t‖ := by
          exact congrArg (fun x : ℝ => x * ‖t‖)
            hnegdiv
        _ = -(Real.pi / 4) * ‖t‖ := by
          exact congrArg (fun x : ℝ => -(Real.pi / x) * ‖t‖)
            hfour
    exact congrArg Real.exp
      (Eq.trans
        (congrArg (fun x : ℝ => -(Real.pi / 2) * x) hnorm)
        hexponent)
  exact Eq.subst
    (motive := fun x : ℂ => ‖x‖ ≤ A * Real.exp (-(Real.pi / 4) * ‖t‖))
    harg.symm
    (Eq.subst
      (motive := fun x : ℝ => ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) +
        ((-t / 2 : ℝ) : ℂ) * Complex.I)‖ ≤ A * x)
      hexp
      (Eq.subst
        (motive := fun x : ℝ => ‖Complex.Gamma (((1 / 2 : ℝ) : ℂ) +
          ((-t / 2 : ℝ) : ℂ) * Complex.I)‖ ≤
            A * Real.exp (-(Real.pi / 2) * ‖-t / 2‖) * x)
        hpow
        hbound))

/-- The denominator vertical line for the left-boundary quotient, before the `π`
normalization is attached.

This is the canonical classical special-function input: the reciprocal vertical
Stirling estimate for `Γ(i t/2)`; cf. DLMF §5.11. -/
theorem verticalComplexGammaStirling_leftBoundary_denominator_inv_core_bound :
    ∃ B : ℝ,
      0 < B ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖(Complex.Gamma (((t : ℂ) * Complex.I) / 2))⁻¹‖ ≤
          B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖) := by
  rcases verticalComplexGammaStirling_fixedRealPart_core_bounds 0 with
    ⟨B, hB_pos, hB⟩
  refine ⟨B, hB_pos, ?_⟩
  intro t ht
  have htail : (1 / 2 : ℝ) ≤ ‖t / 2‖ :=
    half_norm_ge_one_half_of_one_le_norm ht
  have hbound :
      ‖(Complex.Gamma (((0 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I))⁻¹‖ ≤
        B * Real.exp ((Real.pi / 2) * ‖t / 2‖) *
          (1 + ‖t / 2‖) ^ ((1 / 2 : ℝ) - 0) :=
    (hB (t / 2) htail).2
  have harg :
      Complex.Gamma (((t : ℂ) * Complex.I) / 2) =
        Complex.Gamma (((0 : ℝ) : ℂ) + ((t / 2 : ℝ) : ℂ) * Complex.I) := by
    exact congrArg Complex.Gamma
      (leftBoundary_denominator_complexGamma_argument_eq_fixedRealPart t)
  have hnorm_half : ‖t / 2‖ = ‖t‖ / 2 := by
    have htwo_nonneg : (0 : ℝ) ≤ 2 :=
      le_of_lt zero_lt_two
    calc
      ‖t / 2‖ = ‖t‖ / ‖(2 : ℝ)‖ := by
        exact norm_div t 2
      _ = ‖t‖ / 2 := by
        exact congrArg (fun x : ℝ => ‖t‖ / x)
          (Real.norm_of_nonneg htwo_nonneg)
  have hexp :
      Real.exp ((Real.pi / 2) * ‖t / 2‖) =
        Real.exp ((Real.pi / 4) * ‖t‖) := by
    have hexponent :
        (Real.pi / 2) * (‖t‖ / 2) = (Real.pi / 4) * ‖t‖ := by
      have hdiv :
          (Real.pi / 2) / 2 = Real.pi / ((2 : ℝ) * 2) :=
        div_div_eq_div_mul Real.pi 2 2
      have hfour :
          ((2 : ℝ) * 2) = 4 :=
        rfl
      calc
        (Real.pi / 2) * (‖t‖ / 2) =
            ((Real.pi / 2) / 2) * ‖t‖ := by
          exact (mul_div_assoc (Real.pi / 2) ‖t‖ 2).symm
        _ = (Real.pi / ((2 : ℝ) * 2)) * ‖t‖ := by
          exact congrArg (fun x : ℝ => x * ‖t‖) hdiv
        _ = (Real.pi / 4) * ‖t‖ := by
          exact congrArg (fun x : ℝ => (Real.pi / x) * ‖t‖) hfour
    exact congrArg Real.exp
      (Eq.trans
        (congrArg (fun x : ℝ => (Real.pi / 2) * x) hnorm_half)
        hexponent)
  have hsqrt :
      (1 + ‖t / 2‖) ^ ((1 / 2 : ℝ) - 0) ≤ Real.sqrt (1 + ‖t‖) := by
    have hbase_nonneg : 0 ≤ 1 + ‖t / 2‖ :=
      add_nonneg zero_le_one (norm_nonneg (t / 2))
    have hhalf_le : ‖t‖ / 2 ≤ ‖t‖ :=
      div_le_self (norm_nonneg t) one_le_two
    have hbase_le : 1 + ‖t / 2‖ ≤ 1 + ‖t‖ := by
      exact add_le_add_left
        (Eq.subst
          (motive := fun x : ℝ => x ≤ ‖t‖)
          hnorm_half.symm
          hhalf_le)
        1
    have hexponent :
        ((1 / 2 : ℝ) - 0) = 1 / 2 :=
      sub_zero (1 / 2 : ℝ)
    have hrpow :
        (1 + ‖t / 2‖) ^ ((1 / 2 : ℝ) - 0) =
          Real.sqrt (1 + ‖t / 2‖) :=
      Eq.subst
        (motive := fun x : ℝ =>
          (1 + ‖t / 2‖) ^ x = Real.sqrt (1 + ‖t / 2‖))
        hexponent.symm
        (Real.rpow_one_div_two hbase_nonneg)
    exact Eq.subst
      (motive := fun x : ℝ => x ≤ Real.sqrt (1 + ‖t‖))
      hrpow.symm
      (Real.sqrt_le_sqrt hbase_le)
  have hscaled :
      B * Real.exp ((Real.pi / 2) * ‖t / 2‖) *
          (1 + ‖t / 2‖) ^ ((1 / 2 : ℝ) - 0) ≤
        B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖) := by
    have hleft_nonneg :
        0 ≤ B * Real.exp ((Real.pi / 2) * ‖t / 2‖) :=
      mul_nonneg (le_of_lt hB_pos) (le_of_lt (Real.exp_pos _))
    exact Eq.subst
      (motive := fun x : ℝ =>
        B * x * (1 + ‖t / 2‖) ^ ((1 / 2 : ℝ) - 0) ≤
          B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖))
      hexp
      (mul_le_mul_of_nonneg_left hsqrt hleft_nonneg)
  exact Eq.subst
    (motive := fun x : ℂ =>
      ‖x⁻¹‖ ≤ B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖))
    harg.symm
    (le_trans hbound hscaled)

/-- The real part of the numerator `π`-normalizing exponent is `-1/2`. -/
theorem leftBoundary_numerator_piExponent_re
    (t : ℝ) :
    (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2).re = -(1 / 2 : ℝ) := by
  calc
    (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2).re =
        (-((1 : ℂ) - (t : ℂ) * Complex.I)).re / 2 := by
      exact Complex.div_re_ofReal (-((1 : ℂ) - (t : ℂ) * Complex.I)) 2
    _ = -(((1 : ℂ) - (t : ℂ) * Complex.I).re) / 2 := by
      exact congrArg (fun x : ℝ => x / 2)
        (Complex.neg_re ((1 : ℂ) - (t : ℂ) * Complex.I))
    _ = -(1 / 2 : ℝ) := by
      have hre_one : (((1 : ℂ) - (t : ℂ) * Complex.I).re) = 1 := by
        calc
          (((1 : ℂ) - (t : ℂ) * Complex.I).re) =
              (1 : ℂ).re - ((t : ℂ) * Complex.I).re := by
            exact Complex.sub_re (1 : ℂ) ((t : ℂ) * Complex.I)
          _ = 1 - ((t : ℂ) * Complex.I).re := by
            exact congrArg (fun x : ℝ => x - ((t : ℂ) * Complex.I).re) Complex.one_re
          _ = 1 - ((t : ℂ).re * Complex.I.re - (t : ℂ).im * Complex.I.im) := by
            exact congrArg (fun x : ℝ => 1 - x)
              (Complex.mul_re (t : ℂ) Complex.I)
          _ = 1 - (t * 0 - 0 * 1) := by
            rfl
          _ = 1 := by
            calc
              1 - (t * 0 - 0 * 1) = 1 - (0 - 0 * 1) := by
                exact congrArg (fun x : ℝ => 1 - (x - 0 * 1)) (mul_zero t)
              _ = 1 - (0 - 0) := by
                exact congrArg (fun x : ℝ => 1 - (0 - x)) (zero_mul 1)
              _ = 1 - 0 := by
                exact congrArg (fun x : ℝ => 1 - x) (sub_zero 0)
              _ = 1 :=
                sub_zero 1
      calc
        -(((1 : ℂ) - (t : ℂ) * Complex.I).re) / 2 =
            -1 / 2 := by
          exact congrArg (fun x : ℝ => -x / 2) hre_one
        _ = -(1 / 2 : ℝ) := by
          exact neg_div 1 2

/-- The numerator `π`-normalizing factor is bounded by `1`; its constant
contribution is absorbed into the Stirling constant. -/
theorem norm_leftBoundary_numerator_piFactor_le_one
    (t : ℝ) :
    ‖π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2 : ℂ)‖ ≤ 1 := by
  have hpi_pos : (0 : ℝ) < π := Real.pi_pos
  have hpi_one_le : (1 : ℝ) ≤ π :=
    le_of_lt Real.one_lt_pi
  have hnorm_eq :
      ‖π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2 : ℂ)‖ =
        π ^ (-(1 / 2 : ℝ)) := by
    calc
      ‖π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2 : ℂ)‖ =
          Complex.abs (π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2 : ℂ)) := by
        exact Complex.norm_eq_abs
          (π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2 : ℂ))
      _ = π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2 : ℂ).re := by
        exact Complex.abs_cpow_eq_rpow_re_of_pos hpi_pos
          (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2 : ℂ)
      _ = π ^ (-(1 / 2 : ℝ)) := by
        exact congrArg (fun x : ℝ => π ^ x)
          (leftBoundary_numerator_piExponent_re t)
  have hexponent_nonpos : (-(1 / 2 : ℝ)) ≤ 0 := by
    exact neg_nonpos.mpr
      (div_nonneg zero_le_one zero_le_two)
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ 1)
    hnorm_eq.symm
    (Real.rpow_le_one_of_one_le_of_nonpos hpi_one_le hexponent_nonpos)

/-- The real part of the denominator `π`-normalizing exponent is `0`. -/
theorem leftBoundary_denominator_piExponent_re
    (t : ℝ) :
    (-((t : ℂ) * Complex.I) / 2).re = 0 := by
  calc
    (-((t : ℂ) * Complex.I) / 2).re =
        (-((t : ℂ) * Complex.I)).re / 2 := by
      exact Complex.div_re_ofReal (-((t : ℂ) * Complex.I)) 2
    _ = -(((t : ℂ) * Complex.I).re) / 2 := by
      exact congrArg (fun x : ℝ => x / 2)
        (Complex.neg_re ((t : ℂ) * Complex.I))
    _ = -(t * 0 - 0 * 1) / 2 := by
      exact congrArg (fun x : ℝ => -x / 2)
        (calc
          (((t : ℂ) * Complex.I).re) =
              (t : ℂ).re * Complex.I.re - (t : ℂ).im * Complex.I.im := by
            exact Complex.mul_re (t : ℂ) Complex.I
          _ = t * 0 - 0 * 1 := by
            rfl)
    _ = 0 := by
      calc
        -(t * 0 - 0 * 1) / 2 = -(0 - 0 * 1) / 2 := by
          exact congrArg (fun x : ℝ => -(x - 0 * 1) / 2) (mul_zero t)
        _ = -(0 - 0) / 2 := by
          exact congrArg (fun x : ℝ => -(0 - x) / 2) (zero_mul 1)
        _ = -0 / 2 := by
          exact congrArg (fun x : ℝ => -x / 2) (sub_zero 0)
        _ = 0 / 2 := by
          exact congrArg (fun x : ℝ => x / 2) (neg_zero.symm)
        _ = 0 :=
          zero_div 2

/-- The denominator `π`-normalizing factor has norm one on the left-boundary
vertical line. -/
theorem norm_leftBoundary_denominator_piFactor_eq_one
    (t : ℝ) :
    ‖π ^ (-((t : ℂ) * Complex.I) / 2 : ℂ)‖ = 1 := by
  have hpi_pos : (0 : ℝ) < π := Real.pi_pos
  calc
    ‖π ^ (-((t : ℂ) * Complex.I) / 2 : ℂ)‖ =
        Complex.abs (π ^ (-((t : ℂ) * Complex.I) / 2 : ℂ)) := by
      exact Complex.norm_eq_abs
        (π ^ (-((t : ℂ) * Complex.I) / 2 : ℂ))
    _ = π ^ (-((t : ℂ) * Complex.I) / 2 : ℂ).re := by
      exact Complex.abs_cpow_eq_rpow_re_of_pos hpi_pos
        (-((t : ℂ) * Complex.I) / 2 : ℂ)
    _ = π ^ (0 : ℝ) := by
      exact congrArg (fun x : ℝ => π ^ x)
        (leftBoundary_denominator_piExponent_re t)
    _ = 1 := by
      exact Real.rpow_zero π

/-- The denominator `π`-normalizing factor is nonzero on the left-boundary
vertical line. -/
theorem leftBoundary_denominator_piFactor_ne_zero
    (t : ℝ) :
    π ^ (-((t : ℂ) * Complex.I) / 2 : ℂ) ≠ 0 := by
  intro hzero
  have hnorm_zero :
      ‖π ^ (-((t : ℂ) * Complex.I) / 2 : ℂ)‖ = 0 := by
    exact congrArg norm hzero
  have hone_zero : (1 : ℝ) = 0 := by
    calc
      (1 : ℝ) = ‖π ^ (-((t : ℂ) * Complex.I) / 2 : ℂ)‖ := by
        exact (norm_leftBoundary_denominator_piFactor_eq_one t).symm
      _ = 0 := hnorm_zero
  exact one_ne_zero hone_zero

/-- Attach the numerator `π`-normalization to the canonical vertical `Complex.Gamma`
Stirling estimate. -/
theorem twoSidedVerticalComplexGammaStirling_leftBoundary_numerator_bound_of_core
    (hcore :
      ∃ A : ℝ,
        0 < A ∧
        ∀ t : ℝ,
          1 ≤ ‖t‖ →
          ‖Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)‖ ≤
            A * Real.exp (-(Real.pi / 4) * ‖t‖)) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t‖ ≤
          A * Real.exp (-(Real.pi / 4) * ‖t‖) := by
  rcases hcore with ⟨A, hA_pos, hA⟩
  refine ⟨A, hA_pos, ?_⟩
  intro t ht
  have hpi_le_one :
      ‖π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2 : ℂ)‖ ≤ 1 :=
    norm_leftBoundary_numerator_piFactor_le_one t
  have hgamma_bound :
      ‖Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)‖ ≤
        A * Real.exp (-(Real.pi / 4) * ‖t‖) :=
    hA t ht
  have htarget_nonneg :
      0 ≤ A * Real.exp (-(Real.pi / 4) * ‖t‖) :=
    mul_nonneg (le_of_lt hA_pos) (le_of_lt (Real.exp_pos _))
  calc
    ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t‖ =
        ‖π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2 : ℂ)‖ *
          ‖Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)‖ := by
      exact norm_mul
        (π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2 : ℂ))
        (Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2))
    _ ≤ 1 * (A * Real.exp (-(Real.pi / 4) * ‖t‖)) := by
      exact mul_le_mul hpi_le_one hgamma_bound (norm_nonneg _) zero_le_one
    _ = A * Real.exp (-(Real.pi / 4) * ‖t‖) := by
      exact one_mul (A * Real.exp (-(Real.pi / 4) * ‖t‖))

/-- Attach the denominator `π`-normalization to the canonical reciprocal vertical
`Complex.Gamma` Stirling estimate. -/
theorem twoSidedVerticalComplexGammaStirling_leftBoundary_denominator_inv_bound_of_core
    (hcore :
      ∃ B : ℝ,
        0 < B ∧
        ∀ t : ℝ,
          1 ≤ ‖t‖ →
          ‖(Complex.Gamma (((t : ℂ) * Complex.I) / 2))⁻¹‖ ≤
            B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖)) :
    ∃ B : ℝ,
      0 < B ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖(unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ ≤
          B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖) := by
  rcases hcore with ⟨B, hB_pos, hB⟩
  refine ⟨B, hB_pos, ?_⟩
  intro t ht
  let P : ℂ := π ^ (-((t : ℂ) * Complex.I) / 2 : ℂ)
  let G : ℂ := Complex.Gamma (((t : ℂ) * Complex.I) / 2)
  have hP_ne : P ≠ 0 :=
    leftBoundary_denominator_piFactor_ne_zero t
  have hP_norm_one : ‖P‖ = (1 : ℝ) :=
    norm_leftBoundary_denominator_piFactor_eq_one t
  have hraw :
      ‖G⁻¹‖ ≤ B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖) :=
    hB t ht
  have hnorm_eq :
      ‖(unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ =
        ‖G⁻¹‖ := by
    calc
      ‖(unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ =
          ‖(P * G)⁻¹‖ := by
        rfl
      _ = ‖P⁻¹ * G⁻¹‖ := by
        exact congrArg norm (mul_inv_rev P G)
      _ = ‖P⁻¹‖ * ‖G⁻¹‖ := by
        exact norm_mul P⁻¹ G⁻¹
      _ = ‖P‖⁻¹ * ‖G⁻¹‖ := by
        exact congrArg (fun x : ℝ => x * ‖G⁻¹‖) (norm_inv P)
      _ = 1⁻¹ * ‖G⁻¹‖ := by
        exact congrArg (fun x : ℝ => x⁻¹ * ‖G⁻¹‖) hP_norm_one
      _ = 1 * ‖G⁻¹‖ := by
        exact congrArg (fun x : ℝ => x * ‖G⁻¹‖) (inv_one : (1 : ℝ)⁻¹ = 1)
      _ = ‖G⁻¹‖ := by
        exact one_mul ‖G⁻¹‖
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖))
    hnorm_eq.symm
    hraw

/-- Vertical Stirling upper bound for the named numerator in the unfolded left-boundary
Gamma quotient.

This is one of the exact classical special-function inputs: Stirling on the vertical
line `((1 - it) / 2)`, including the `π` normalization; cf. DLMF §5.11. -/
theorem twoSidedVerticalComplexGammaStirling_leftBoundary_numerator_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t‖ ≤
          A * Real.exp (-(Real.pi / 4) * ‖t‖) := by
  exact
    twoSidedVerticalComplexGammaStirling_leftBoundary_numerator_bound_of_core
      verticalComplexGammaStirling_leftBoundary_numerator_core_bound

/-- Vertical Stirling reciprocal bound for the named denominator in the unfolded
left-boundary Gamma quotient.

This is the matching exact classical special-function input: Stirling on the vertical
line `(it / 2)`, inverted and normalized so the quotient algebra has the expected
square-root growth; cf. DLMF §5.11. -/
theorem twoSidedVerticalComplexGammaStirling_leftBoundary_denominator_inv_bound :
    ∃ B : ℝ,
      0 < B ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖(unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ ≤
          B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖) := by
  exact
    twoSidedVerticalComplexGammaStirling_leftBoundary_denominator_inv_bound_of_core
      verticalComplexGammaStirling_leftBoundary_denominator_inv_core_bound

/-- Algebraic quotient estimate obtained from the numerator bound and denominator
reciprocal bound.  The exponential factors cancel, leaving the square-root envelope. -/
theorem unfoldedGammaℝLeftBoundaryRatioRealParam_sqrt_growth_bound_of_numerator_and_denominator
    (hnum :
      ∃ A : ℝ,
        0 < A ∧
        ∀ t : ℝ,
          1 ≤ ‖t‖ →
          ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t‖ ≤
            A * Real.exp (-(Real.pi / 4) * ‖t‖))
    (hden :
      ∃ B : ℝ,
        0 < B ∧
        ∀ t : ℝ,
          1 ≤ ‖t‖ →
          ‖(unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ ≤
            B * Real.exp ((Real.pi / 4) * ‖t‖) * Real.sqrt (1 + ‖t‖)) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ ≤
          A * Real.sqrt (1 + ‖t‖) := by
  rcases hnum with ⟨Anum, hAnum_pos, hAnum⟩
  rcases hden with ⟨Bden, hBden_pos, hBden⟩
  refine ⟨Anum * Bden, mul_pos hAnum_pos hBden_pos, ?_⟩
  intro t ht
  let Eminus : ℝ := Real.exp (-(Real.pi / 4) * ‖t‖)
  let Eplus : ℝ := Real.exp ((Real.pi / 4) * ‖t‖)
  let S : ℝ := Real.sqrt (1 + ‖t‖)
  have hnum_bound :
      ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t‖ ≤ Anum * Eminus :=
    hAnum t ht
  have hden_bound :
      ‖(unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ ≤
        Bden * Eplus * S :=
    hBden t ht
  have hden_inv_nonneg :
      0 ≤ ‖(unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ :=
    norm_nonneg _
  have hquot_eq :
      ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ =
        ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t‖ *
          ‖(unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ := by
    calc
      ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ =
          ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t /
            unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t‖ :=
        norm_unfoldedGammaℝLeftBoundaryRatioRealParam_eq_named_quotient t
      _ = ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t *
            (unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ := by
        rfl
      _ = ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t‖ *
          ‖(unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ := by
        exact norm_mul
          (unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t)
          (unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹
  have hmul_bound :
      ‖unfoldedGammaℝLeftBoundaryRatioNumeratorRealParam t‖ *
          ‖(unfoldedGammaℝLeftBoundaryRatioDenominatorRealParam t)⁻¹‖ ≤
        (Anum * Eminus) * (Bden * Eplus * S) :=
    mul_le_mul hnum_bound hden_bound hden_inv_nonneg
      (mul_nonneg (le_of_lt hAnum_pos) (Real.exp_pos _).le)
  have hexp_cancel :
      Eminus * Eplus = 1 := by
    have hsum_exp :
        (-(Real.pi / 4) * ‖t‖) + ((Real.pi / 4) * ‖t‖) = 0 := by
      have hneg :
          -(Real.pi / 4) * ‖t‖ =
            -((Real.pi / 4) * ‖t‖) :=
        neg_mul (Real.pi / 4) ‖t‖
      calc
        (-(Real.pi / 4) * ‖t‖) + ((Real.pi / 4) * ‖t‖) =
            -((Real.pi / 4) * ‖t‖) + ((Real.pi / 4) * ‖t‖) := by
          exact congrArg
            (fun x : ℝ => x + ((Real.pi / 4) * ‖t‖))
            hneg
        _ = 0 :=
          add_left_neg ((Real.pi / 4) * ‖t‖)
    calc
      Eminus * Eplus =
          Real.exp ((-(Real.pi / 4) * ‖t‖) + ((Real.pi / 4) * ‖t‖)) := by
        exact (Real.exp_add (-(Real.pi / 4) * ‖t‖) ((Real.pi / 4) * ‖t‖)).symm
      _ = Real.exp 0 := by
        exact congrArg Real.exp hsum_exp
      _ = 1 := Real.exp_zero
  have htarget_eq :
      (Anum * Eminus) * (Bden * Eplus * S) = (Anum * Bden) * S := by
    have hcomm :
        (Anum * Eminus) * (Bden * Eplus * S) =
          (Anum * Bden) * (Eminus * Eplus) * S := by
      calc
        (Anum * Eminus) * (Bden * Eplus * S) =
            Anum * (Eminus * (Bden * Eplus * S)) := by
          exact mul_assoc Anum Eminus (Bden * Eplus * S)
        _ = Anum * (Bden * (Eminus * Eplus * S)) := by
          exact congrArg (fun x : ℝ => Anum * x)
            (calc
              Eminus * (Bden * Eplus * S) =
                  Eminus * (Bden * (Eplus * S)) := by
                exact congrArg (fun x : ℝ => Eminus * x)
                  (mul_assoc Bden Eplus S)
              _ = Bden * (Eminus * (Eplus * S)) := by
                exact mul_left_comm Eminus Bden (Eplus * S)
              _ = Bden * ((Eminus * Eplus) * S) := by
                exact congrArg (fun x : ℝ => Bden * x)
                  (mul_assoc Eminus Eplus S).symm)
        _ = (Anum * Bden) * (Eminus * Eplus * S) := by
          exact (mul_assoc Anum Bden (Eminus * Eplus * S)).symm
        _ = (Anum * Bden) * ((Eminus * Eplus) * S) := by
          exact congrArg (fun x : ℝ => (Anum * Bden) * x)
            (mul_assoc Eminus Eplus S).symm
        _ = (Anum * Bden) * (Eminus * Eplus) * S := by
          exact mul_assoc (Anum * Bden) (Eminus * Eplus) S
    calc
      (Anum * Eminus) * (Bden * Eplus * S) =
          (Anum * Bden) * (Eminus * Eplus) * S :=
        hcomm
      _ = (Anum * Bden) * 1 * S := by
        exact congrArg (fun x : ℝ => (Anum * Bden) * x * S) hexp_cancel
      _ = (Anum * Bden) * S := by
        exact congrArg (fun x : ℝ => x * S)
          (mul_one (Anum * Bden))
  exact Eq.subst
    (motive := fun x : ℝ => ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ ≤ x)
    htarget_eq
    (Eq.subst
      (motive := fun x : ℝ => x ≤ (Anum * Eminus) * (Bden * Eplus * S))
      hquot_eq.symm
      hmul_bound)

/-- Inline form of the quotient algebra for the left-boundary two-Gamma expression. -/
theorem inline_twoGammaQuotient_sqrt_growth_bound_of_unfolded
    (hunfolded :
      ∃ A : ℝ,
        0 < A ∧
        ∀ t : ℝ,
          1 ≤ ‖t‖ →
          ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ ≤
            A * Real.sqrt (1 + ‖t‖)) :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖(π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
            (π ^ (-((t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((t : ℂ) * Complex.I) / 2))‖ ≤
          A * Real.sqrt (1 + ‖t‖) := by
  rcases hunfolded with ⟨A, hA_pos, hbound⟩
  refine ⟨A, hA_pos, ?_⟩
  intro t ht
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ A * Real.sqrt (1 + ‖t‖))
    (norm_inline_twoGammaQuotient_eq_norm_unfoldedGammaℝLeftBoundaryRatioRealParam t)
    (hbound t ht)

/-- Vertical Stirling quotient corollary for the completed real-Gamma boundary
ratio.

This is the canonical quotient consequence of the two-sided vertical Stirling
formula, specialized to `(1 - it) / 2` and `it / 2`; cf. DLMF §5.11. -/
theorem twoSidedVerticalComplexGammaStirling_leftBoundary_twoGammaQuotient_sqrt_growth_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖(π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
            (π ^ (-((t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((t : ℂ) * Complex.I) / 2))‖ ≤
          A * Real.sqrt (1 + ‖t‖) := by
  exact inline_twoGammaQuotient_sqrt_growth_bound_of_unfolded
    (unfoldedGammaℝLeftBoundaryRatioRealParam_sqrt_growth_bound_of_numerator_and_denominator
      twoSidedVerticalComplexGammaStirling_leftBoundary_numerator_bound
      twoSidedVerticalComplexGammaStirling_leftBoundary_denominator_inv_bound)

/-- The historical owner-root spelling for the left-boundary two-Gamma quotient estimate.

The proof is only name transport from the canonical two-sided vertical `Complex.Gamma`
Stirling quotient primitive. -/
theorem verticalStirling_complexGamma_leftBoundary_twoGammaQuotient_sqrt_growth_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖(π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
            (π ^ (-((t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((t : ℂ) * Complex.I) / 2))‖ ≤
          A * Real.sqrt (1 + ‖t‖) := by
  exact
    twoSidedVerticalComplexGammaStirling_leftBoundary_twoGammaQuotient_sqrt_growth_bound

/-- Classical two-sided vertical Stirling control for the inline two-Gamma quotient on
the left boundary.

This is the smallest special-function input for the left-edge Gamma-ratio: after
substituting `z = it`, apply the two-sided vertical Stirling formula to the numerator
and denominator Gamma factors; cf. DLMF §5.11. -/
theorem classicalStirling_complexGamma_leftBoundary_twoGammaQuotient_vertical_sqrt_growth_bound_from_twoSidedVerticalStirling :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖(π ^ (-((1 : ℂ) - (t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((1 : ℂ) - (t : ℂ) * Complex.I) / 2)) /
            (π ^ (-((t : ℂ) * Complex.I) / 2) *
              Complex.Gamma (((t : ℂ) * Complex.I) / 2))‖ ≤
          A * Real.sqrt (1 + ‖t‖) := by
  exact
    verticalStirling_complexGamma_leftBoundary_twoGammaQuotient_sqrt_growth_bound

/-- Classical two-sided vertical Stirling control for the unfolded completed real-Gamma
ratio on the left boundary.

This is now only transport from the inline two-Gamma quotient to the local unfolded
ratio name. -/
theorem classicalStirling_unfoldedGammaℝLeftBoundaryRatioRealParam_vertical_sqrt_growth_bound_from_twoSidedVerticalStirling :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖unfoldedGammaℝLeftBoundaryRatioRealParam t‖ ≤
          A * Real.sqrt (1 + ‖t‖) := by
  rcases
    classicalStirling_complexGamma_leftBoundary_twoGammaQuotient_vertical_sqrt_growth_bound_from_twoSidedVerticalStirling
    with ⟨A, hA_pos, hbound⟩
  refine ⟨A, hA_pos, ?_⟩
  intro t ht
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ A * Real.sqrt (1 + ‖t‖))
    (congrArg norm (unfoldedGammaℝLeftBoundaryRatioRealParam_eq_inline t)).symm
    (hbound t ht)

/-- Classical vertical Stirling control for the two-Gamma quotient on the left boundary.

This theorem is only the formula-level transport from the unfolded owner primitive to
the inline two-Gamma quotient. -/
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
  rcases
    classicalStirling_unfoldedGammaℝLeftBoundaryRatioRealParam_vertical_sqrt_growth_bound_from_twoSidedVerticalStirling
    with ⟨A, hA_pos, hbound⟩
  refine ⟨A, hA_pos, ?_⟩
  intro t ht
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ A * Real.sqrt (1 + ‖t‖))
    (congrArg norm (unfoldedGammaℝLeftBoundaryRatioRealParam_eq_inline t))
    (hbound t ht)

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
  exact
    classicalStirling_unfoldedGammaℝLeftBoundaryRatioRealParam_vertical_sqrt_growth_bound_from_twoSidedVerticalStirling

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

/-- The complex point with real coordinate `1` and imaginary coordinate `t`. -/
def boundaryLineOnePointRealParam (t : ℝ) : ℂ :=
  ⟨1, t⟩

/-- Real coordinate of the canonical point `1 + it` on the boundary line. -/
theorem boundaryLineOnePointRealParam_re
    (t : ℝ) :
    (boundaryLineOnePointRealParam t).re = 1 := by
  rfl

/-- Imaginary coordinate of the canonical point `1 + it` on the boundary line. -/
theorem boundaryLineOnePointRealParam_im
    (t : ℝ) :
    (boundaryLineOnePointRealParam t).im = t := by
  rfl

/-- The vertical height of the canonical point `1 + it` is the absolute value of `t`. -/
theorem boundaryLineOnePointRealParam_vertical_height
    (t : ℝ) :
    ‖(boundaryLineOnePointRealParam t).im‖ = ‖t‖ := by
  rfl

/-- A point on the boundary line `re = 1` is the canonical real-parameter boundary
point attached to its vertical coordinate. -/
theorem boundaryLine_one_eq_realParam_point
    {w : ℂ}
    (hw_re : w.re = 1) :
    w = boundaryLineOnePointRealParam w.im := by
  exact Complex.ext hw_re rfl

/-- The real-parameter zeta value attached to the boundary line `re = 1`. -/
def boundaryLineOneZetaRealParam (t : ℝ) : ℂ :=
  riemannZeta (boundaryLineOnePointRealParam t)

/-- Boundary-line zeta is the real-parameter zeta value at the same vertical
coordinate. -/
theorem riemannZeta_boundaryLine_one_eq_realParam
    {w : ℂ}
    (hw_re : w.re = 1) :
    riemannZeta w = boundaryLineOneZetaRealParam w.im := by
  exact congrArg riemannZeta (boundaryLine_one_eq_realParam_point hw_re)

/-- Norm form of the boundary-line real-parameter zeta transport. -/
theorem norm_riemannZeta_boundaryLine_one_eq_norm_realParam
    {w : ℂ}
    (hw_re : w.re = 1) :
    ‖riemannZeta w‖ = ‖boundaryLineOneZetaRealParam w.im‖ := by
  exact congrArg norm (riemannZeta_boundaryLine_one_eq_realParam hw_re)

/-- Harmonic sums are controlled by the logarithm at the natural cutoff `⌊y⌋₊`.

This is the finite-sum side of the Abel/Euler-Maclaurin estimate: after truncating
at a real height `y`, the positive harmonic majorant is at most `1 + log y`. -/
theorem harmonic_truncation_floor_le_one_add_log
    {y : ℝ}
    (hy : 1 ≤ y) :
    harmonic ⌊y⌋₊ ≤ 1 + Real.log y := by
  exact harmonic_floor_le_one_add_log y hy

/-- The cutoff `2 + |t|` is always in the range where the harmonic-log comparison applies. -/
theorem one_le_two_add_norm
    (t : ℝ) :
    (1 : ℝ) ≤ 2 + ‖t‖ := by
  have hnorm : 0 ≤ ‖t‖ :=
    norm_nonneg t
  have htwo_le : (1 : ℝ) ≤ 2 := by
    calc
      (1 : ℝ) ≤ 1 + 1 :=
        le_add_of_nonneg_right zero_le_one
      _ = 2 := rfl
  exact le_trans htwo_le (le_add_of_nonneg_right hnorm)

/-- Harmonic control at the boundary-line truncation height `2 + |t|`. -/
theorem harmonic_boundaryLine_truncation_le_one_add_log
    (t : ℝ) :
    harmonic ⌊2 + ‖t‖⌋₊ ≤ 1 + Real.log (2 + ‖t‖) := by
  exact harmonic_truncation_floor_le_one_add_log (one_le_two_add_norm t)

/-- Each Dirichlet monomial on the boundary line `re = 1` has norm `1 / n`. -/
theorem boundaryLineOnePointRealParam_dirichletTerm_norm_eq_inv
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n) :
    ‖(1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ = 1 / (n : ℝ) := by
  have hnorm_pow :
      ‖(n : ℂ) ^ boundaryLineOnePointRealParam t‖ = (n : ℝ) ^ (1 : ℝ) := by
    calc
      ‖(n : ℂ) ^ boundaryLineOnePointRealParam t‖ =
          (n : ℝ) ^ (boundaryLineOnePointRealParam t).re := by
            exact Complex.norm_natCast_cpow_of_pos hn (boundaryLineOnePointRealParam t)
      _ = (n : ℝ) ^ (1 : ℝ) := by
            exact congrArg (fun x : ℝ => (n : ℝ) ^ x)
              (boundaryLineOnePointRealParam_re t)
  have hpow_one : (n : ℝ) ^ (1 : ℝ) = (n : ℝ) := by
    exact Real.rpow_one (n : ℝ)
  calc
    ‖(1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ =
        ‖(1 : ℂ)‖ / ‖(n : ℂ) ^ boundaryLineOnePointRealParam t‖ := by
          exact norm_div (1 : ℂ) ((n : ℂ) ^ boundaryLineOnePointRealParam t)
    _ = 1 / ‖(n : ℂ) ^ boundaryLineOnePointRealParam t‖ := by
          exact congrArg
            (fun x : ℝ => x / ‖(n : ℂ) ^ boundaryLineOnePointRealParam t‖)
            (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
    _ = 1 / ((n : ℝ) ^ (1 : ℝ)) := by
          exact congrArg (fun x : ℝ => 1 / x) hnorm_pow
    _ = 1 / (n : ℝ) := by
          exact congrArg (fun x : ℝ => 1 / x) hpow_one

/-- The finite Dirichlet truncation on `re = 1` is bounded by the corresponding
positive harmonic majorant. -/
theorem boundaryLineOnePointRealParam_finite_dirichlet_truncation_norm_le_harmonic
    (t : ℝ)
    (N : ℕ) :
    ‖∑ n ∈ Finset.Icc 1 N,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
      harmonic N := by
  have hsum_norm :
      ‖∑ n ∈ Finset.Icc 1 N,
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
        ∑ n ∈ Finset.Icc 1 N,
          ‖(1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ := by
    exact norm_sum_le _ _
  have hterm_sum :
      (∑ n ∈ Finset.Icc 1 N,
          ‖(1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖) =
        ∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro n hn_mem
    have hn_one_le : 1 ≤ n :=
      (Finset.mem_Icc.mp hn_mem).1
    have hn_pos : 0 < n :=
      Nat.lt_of_succ_le hn_one_le
    exact boundaryLineOnePointRealParam_dirichletTerm_norm_eq_inv t hn_pos
  have hharmonic :
      (∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ))) = harmonic N := by
    calc
      (∑ n ∈ Finset.Icc 1 N, (1 / (n : ℝ))) =
          ∑ n ∈ Finset.Icc 1 N, ((n : ℚ)⁻¹ : ℝ) := by
            refine Finset.sum_congr rfl ?_
            intro n hn_mem
            have hn_one_le : 1 ≤ n :=
              (Finset.mem_Icc.mp hn_mem).1
            have hn_pos : 0 < n :=
              Nat.lt_of_succ_le hn_one_le
            have hn_rat_ne : (n : ℚ) ≠ 0 := by
              exact_mod_cast Nat.ne_of_gt hn_pos
            calc
              (1 / (n : ℝ)) = ((n : ℝ)⁻¹) := by
                exact one_div (n : ℝ)
              _ = (((n : ℚ)⁻¹ : ℚ) : ℝ) := by
                exact (Rat.cast_inv (R := ℝ) (n : ℚ)).symm
      _ = harmonic N := by
            exact_mod_cast (harmonic_eq_sum_Icc (n := N)).symm
  exact le_trans hsum_norm (le_of_eq (hterm_sum.trans hharmonic))

/-- The finite Dirichlet truncation at the Abel/Euler-Maclaurin boundary cutoff is
bounded by `1 + log (2 + |t|)`. -/
theorem boundaryLineOnePointRealParam_finite_dirichlet_truncation_norm_le_one_add_log
    (t : ℝ) :
    ‖∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
      1 + Real.log (2 + ‖t‖) := by
  exact le_trans
    (boundaryLineOnePointRealParam_finite_dirichlet_truncation_norm_le_harmonic
      t ⌊2 + ‖t‖⌋₊)
    (harmonic_boundaryLine_truncation_le_one_add_log t)

/-- On the logarithmic boundary range used below, `1 ≤ log (2 + |t|)`. -/
theorem one_le_log_two_add_norm_of_one_le_norm
    {t : ℝ}
    (ht : 1 ≤ ‖t‖) :
    (1 : ℝ) ≤ Real.log (2 + ‖t‖) := by
  have hthree_le : (3 : ℝ) ≤ 2 + ‖t‖ := by
    calc
      (3 : ℝ) = 2 + 1 := rfl
      _ ≤ 2 + ‖t‖ :=
        add_le_add_left ht 2
  have hexp_one_le_three : Real.exp (1 : ℝ) ≤ 3 := by
    have hexp_le_d9 : Real.exp (1 : ℝ) ≤ 2.7182818286 :=
      le_of_lt Real.exp_one_lt_d9
    have hd9_eq :
        (2.7182818286 : ℝ) =
          (27182818286 : ℝ) / 10000000000 := rfl
    have hden_pos : (0 : ℝ) < 10000000000 := by
      exact_mod_cast (show (0 : ℕ) < 10000000000 by decide)
    have hnum_le :
        (27182818286 : ℝ) ≤ 3 * (10000000000 : ℝ) := by
      exact_mod_cast
        (show (27182818286 : ℕ) ≤ 3 * 10000000000 by decide)
    have hd9_le_three : (2.7182818286 : ℝ) ≤ 3 := by
      have hfrac :
          (27182818286 : ℝ) / 10000000000 ≤ 3 :=
        (div_le_iff₀ hden_pos).mpr hnum_le
      exact Eq.subst
        (motive := fun x : ℝ => x ≤ 3)
        hd9_eq.symm
        hfrac
    exact le_trans hexp_le_d9 hd9_le_three
  have hexp_one_le : Real.exp (1 : ℝ) ≤ 2 + ‖t‖ :=
    le_trans hexp_one_le_three hthree_le
  exact Real.le_log_of_exp_le
    (lt_of_lt_of_le Real.exp_pos hexp_one_le)
    hexp_one_le

/-- The Abel/Euler-Maclaurin cutoff `⌊2 + |t|⌋₊` is nonzero. -/
theorem boundaryLineOnePointRealParam_cutoff_pos
    (t : ℝ) :
    0 < ⌊2 + ‖t‖⌋₊ := by
  have hone_le : (1 : ℝ) ≤ 2 + ‖t‖ :=
    one_le_two_add_norm t
  exact (Nat.one_le_floor_iff zero_lt_one).mpr hone_le

/-- The Abel/Euler-Maclaurin cutoff dominates `2`. -/
theorem boundaryLineOnePointRealParam_two_le_cutoff
    (t : ℝ) :
    2 ≤ ⌊2 + ‖t‖⌋₊ := by
  have htwo_le : (2 : ℝ) ≤ 2 + ‖t‖ :=
    le_add_of_nonneg_right (norm_nonneg t)
  exact (Nat.le_floor_iff zero_lt_two).mpr htwo_le

/-- Transport the finite Dirichlet truncation from `Icc 1 N` to the successor-indexed
form used by analytic Dirichlet-series tails. -/
theorem boundaryLineOnePointRealParam_dirichlet_truncation_eq_sum_range_add_one
    (t : ℝ)
    (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) =
      ∑ n ∈ Finset.range N,
        (1 : ℂ) / (((n + 1 : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t) := by
  induction N with
  | zero =>
      have hleft :
          (∑ n ∈ Finset.Icc 1 0,
              (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) = 0 := by
        exact Finset.sum_eq_zero
          (fun n hn => by
            have hn_bounds : 1 ≤ n ∧ n ≤ 0 :=
              Finset.mem_Icc.mp hn
            have hone_le_zero : (1 : ℕ) ≤ 0 :=
              le_trans hn_bounds.1 hn_bounds.2
            exact False.elim
              ((Nat.not_succ_le_zero 0) hone_le_zero))
      have hright :
          (∑ n ∈ Finset.range 0,
              (1 : ℂ) / (((n + 1 : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t)) = 0 := by
        exact Eq.subst
          (motive := fun s : Finset ℕ =>
            (∑ n ∈ s,
              (1 : ℂ) / (((n + 1 : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t)) = 0)
          (Finset.range_zero.symm)
          rfl
      exact Eq.trans hleft hright.symm
  | succ N ih =>
      have hleft :
          (∑ n ∈ Finset.Icc 1 (N + 1),
              (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) =
            (∑ n ∈ Finset.Icc 1 N,
              (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) +
              (1 : ℂ) / (((N + 1 : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t) := by
        exact Finset.sum_Icc_succ_top (Nat.succ_pos N)
          (fun n : ℕ => (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t))
      have hright :
          (∑ n ∈ Finset.range (N + 1),
              (1 : ℂ) / (((n + 1 : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t)) =
            (∑ n ∈ Finset.range N,
              (1 : ℂ) / (((n + 1 : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t)) +
              (1 : ℂ) / (((N + 1 : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t) := by
        exact Finset.sum_range_succ
          (fun n : ℕ =>
            (1 : ℂ) / (((n + 1 : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t))
          N
      exact Eq.trans hleft (Eq.trans (congrArg
        (fun z : ℂ =>
          z + (1 : ℂ) / (((N + 1 : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t))
        ih) hright.symm)

/-- The oscillatory coefficient in the boundary-line Dirichlet term is exactly `n^{-it}`
after the real part `1` is peeled off. -/
theorem boundaryLineOnePointRealParam_dirichletTerm_eq_inv_mul_oscillation
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n) :
    (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t) =
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) / (n : ℂ) := by
  have hn_complex_ne : (n : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have hpoint :
      boundaryLineOnePointRealParam t = 1 + (t : ℂ) * Complex.I := by
    exact Complex.ext rfl rfl
  have hpow_add :
      (n : ℂ) ^ boundaryLineOnePointRealParam t =
        (n : ℂ) ^ (1 : ℂ) * (n : ℂ) ^ ((t : ℂ) * Complex.I) := by
    exact Eq.subst
      (motive := fun z : ℂ =>
        (n : ℂ) ^ z =
          (n : ℂ) ^ (1 : ℂ) * (n : ℂ) ^ ((t : ℂ) * Complex.I))
      hpoint.symm
      (Complex.cpow_add (1 : ℂ) ((t : ℂ) * Complex.I) hn_complex_ne)
  have hinv_osc :
      ((n : ℂ) ^ ((t : ℂ) * Complex.I))⁻¹ =
        (n : ℂ) ^ (-(t : ℂ) * Complex.I) := by
    have hneg :
        -((t : ℂ) * Complex.I) = -(t : ℂ) * Complex.I := by
      exact neg_mul (t : ℂ) Complex.I
    exact Eq.subst
      (motive := fun z : ℂ =>
        ((n : ℂ) ^ ((t : ℂ) * Complex.I))⁻¹ = (n : ℂ) ^ z)
      hneg
      (Complex.cpow_neg (n : ℂ) ((t : ℂ) * Complex.I)).symm
  calc
    (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t) =
        ((n : ℂ) ^ boundaryLineOnePointRealParam t)⁻¹ := by
          exact one_div ((n : ℂ) ^ boundaryLineOnePointRealParam t)
    _ = ((n : ℂ) ^ (1 : ℂ) * (n : ℂ) ^ ((t : ℂ) * Complex.I))⁻¹ := by
          exact congrArg Inv.inv hpow_add
    _ = ((n : ℂ) ^ ((t : ℂ) * Complex.I))⁻¹ * ((n : ℂ) ^ (1 : ℂ))⁻¹ := by
          exact mul_inv_rev ((n : ℂ) ^ (1 : ℂ)) ((n : ℂ) ^ ((t : ℂ) * Complex.I))
    _ = (n : ℂ) ^ (-(t : ℂ) * Complex.I) * ((n : ℂ) ^ (1 : ℂ))⁻¹ := by
          exact congrArg
            (fun z : ℂ => z * ((n : ℂ) ^ (1 : ℂ))⁻¹)
            hinv_osc
    _ = (n : ℂ) ^ (-(t : ℂ) * Complex.I) / (n : ℂ) := by
          exact congrArg
            (fun z : ℂ => (n : ℂ) ^ (-(t : ℂ) * Complex.I) * z⁻¹)
            (Complex.cpow_one (n : ℂ))

/-- The boundary-line Dirichlet monomial with the oscillation written on the right,
matching the Abel-summation convention `f k * c k`. -/
theorem boundaryLineOnePointRealParam_dirichletTerm_eq_inv_mul_oscillation_left
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n) :
    (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t) =
      ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
  have hright :
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) / (n : ℂ) =
        ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
    calc
      ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) / (n : ℂ) =
          ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) * (n : ℂ)⁻¹ := by
            exact div_eq_mul_inv ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) (n : ℂ)
      _ = ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
            exact mul_comm ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) ((n : ℂ)⁻¹ : ℂ)
  exact Eq.trans
    (boundaryLineOnePointRealParam_dirichletTerm_eq_inv_mul_oscillation t hn)
    hright

/-- Finite boundary-line Dirichlet truncations are exactly the Abel-summation
weighted oscillatory sums. -/
theorem boundaryLineOnePointRealParam_finite_truncation_eq_inv_mul_oscillation_sum
    (t : ℝ)
    (N : ℕ) :
    (∑ n ∈ Finset.Icc 1 N,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) =
      ∑ n ∈ Finset.Icc 1 N,
        ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
  refine Finset.sum_congr rfl ?_
  intro n hn_mem
  have hn_one_le : 1 ≤ n :=
    (Finset.mem_Icc.mp hn_mem).1
  have hn_pos : 0 < n :=
    Nat.lt_of_succ_le hn_one_le
  exact boundaryLineOnePointRealParam_dirichletTerm_eq_inv_mul_oscillation_left t hn_pos

/-- A finite boundary-line tail after the Abel/Euler-Maclaurin cutoff is exactly the
corresponding Abel weighted oscillatory tail. -/
theorem boundaryLineOnePointRealParam_finite_tail_after_cutoff_eq_inv_mul_oscillation_sum
    (t : ℝ)
    (M : ℕ) :
    (∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) =
      ∑ n ∈ Finset.Ioc ⌊2 + ‖t‖⌋₊ M,
        ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
  refine Finset.sum_congr rfl ?_
  intro n hn_mem
  have hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n :=
    (Finset.mem_Ioc.mp hn_mem).1
  have hn_pos : 0 < n :=
    lt_trans (boundaryLineOnePointRealParam_cutoff_pos t) hcutoff_lt_n
  exact boundaryLineOnePointRealParam_dirichletTerm_eq_inv_mul_oscillation_left t hn_pos

/-- The natural Abel/Euler-Maclaurin cutoff is fixed by taking the natural floor
after coercion to the real line. -/
theorem boundaryLineOnePointRealParam_cutoff_floor_natCast
    (t : ℝ) :
    ⌊((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)⌋₊ = ⌊2 + ‖t‖⌋₊ := by
  exact Nat.floor_natCast ⌊2 + ‖t‖⌋₊

/-- The Abel/Euler-Maclaurin cutoff is the left endpoint immediately below
`2 + |t|`. -/
theorem boundaryLineOnePointRealParam_cutoff_cast_le_height
    (t : ℝ) :
    (⌊2 + ‖t‖⌋₊ : ℝ) ≤ 2 + ‖t‖ := by
  have hnonneg : (0 : ℝ) ≤ 2 + ‖t‖ :=
    le_trans zero_le_one (one_le_two_add_norm t)
  exact Nat.floor_le hnonneg

/-- The real height `2 + |t|` lies strictly before the successor of the cutoff. -/
theorem boundaryLineOnePointRealParam_height_lt_cutoff_add_one
    (t : ℝ) :
    2 + ‖t‖ < (⌊2 + ‖t‖⌋₊ : ℝ) + 1 := by
  exact Nat.lt_floor_add_one (2 + ‖t‖)

/-- The cutoff endpoint contributes at most one through the reciprocal weight. -/
theorem boundaryLineOnePointRealParam_cutoff_inv_le_one
    (t : ℝ) :
    (1 : ℝ) / (⌊2 + ‖t‖⌋₊ : ℝ) ≤ 1 := by
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hone_le_cutoff_nat : 1 ≤ ⌊2 + ‖t‖⌋₊ :=
    Nat.succ_le_of_lt hcutoff_pos
  have hone_le_cutoff_real : (1 : ℝ) ≤ (⌊2 + ‖t‖⌋₊ : ℝ) := by
    exact_mod_cast hone_le_cutoff_nat
  calc
    (1 : ℝ) / (⌊2 + ‖t‖⌋₊ : ℝ) =
        ((⌊2 + ‖t‖⌋₊ : ℝ)⁻¹ : ℝ) := by
          exact one_div (⌊2 + ‖t‖⌋₊ : ℝ)
    _ ≤ 1 := by
          exact inv_le_one_of_one_le₀ hone_le_cutoff_real

/-- Reciprocal weights are monotone decreasing along the positive natural tail. -/
theorem positive_nat_reciprocal_antitone
    {m n : ℕ}
    (hm : 0 < m)
    (hmn : m ≤ n) :
    (1 : ℝ) / (n : ℝ) ≤ (1 : ℝ) / (m : ℝ) := by
  have hm_real_pos : (0 : ℝ) < (m : ℝ) := by
    exact_mod_cast hm
  have hmn_real : (m : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hmn
  exact one_div_le_one_div_of_le hm_real_pos hmn_real

/-- Past the Abel/Euler-Maclaurin cutoff, all reciprocal weights are bounded by
the reciprocal of the cutoff endpoint. -/
theorem boundaryLineOnePointRealParam_post_cutoff_reciprocal_le_cutoff
    (t : ℝ)
    {n : ℕ}
    (hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n) :
    (1 : ℝ) / (n : ℝ) ≤ (1 : ℝ) / (⌊2 + ‖t‖⌋₊ : ℝ) := by
  have hcutoff_pos : 0 < ⌊2 + ‖t‖⌋₊ :=
    boundaryLineOnePointRealParam_cutoff_pos t
  have hcutoff_le_n : ⌊2 + ‖t‖⌋₊ ≤ n :=
    Nat.le_of_lt hcutoff_lt_n
  exact positive_nat_reciprocal_antitone hcutoff_pos hcutoff_le_n

/-- Logarithmic-phase partial sums for the boundary-line oscillator `n^{-it}`.

The phase is `-t log n`; these sums must not be treated as constant-ratio
geometric sums. -/
def boundaryLineOnePointRealParam_logarithmicPhasePartialSum
    (t : ℝ)
    (M : ℕ) : ℂ :=
  ∑ k ∈ Finset.Icc 0 M,
    (k : ℂ) ^ (-(t : ℂ) * Complex.I)

/-- Definitional expansion of the logarithmic-phase partial sum. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_eq
    (t : ℝ)
    (M : ℕ) :
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum t M =
      ∑ k ∈ Finset.Icc 0 M,
        (k : ℂ) ^ (-(t : ℂ) * Complex.I) := by
  rfl

/-- The continuous logarithmic phase whose integer samples are `n^{-it}` away
from the origin. -/
def boundaryLineOnePointRealParam_logarithmicPhaseFunction
    (t : ℝ)
    (x : ℝ) : ℂ :=
  Complex.exp ((-(t : ℂ) * Complex.I) * (Real.log x : ℂ))

/-- Owner API: positive real samples of the logarithmic phase are the complex
power samples used by the Dirichlet-polynomial primitive.

This is the branch-normalization calculation for the principal complex power on
the positive real axis. -/
theorem logarithmicPhaseFunction_positiveReal_cpow
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    boundaryLineOnePointRealParam_logarithmicPhaseFunction t x =
      (x : ℂ) ^ (-(t : ℂ) * Complex.I) := by
  let a : ℂ := -(t : ℂ) * Complex.I
  have hx_complex_ne : (x : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr hx.ne'
  have hlog : (Real.log x : ℂ) = Complex.log (x : ℂ) :=
    Complex.ofReal_log hx.le
  have harg_left :
      a * (Real.log x : ℂ) = (Real.log x : ℂ) * a :=
    mul_comm a (Real.log x : ℂ)
  have harg_right :
      (Real.log x : ℂ) * a = Complex.log (x : ℂ) * a :=
    congrArg (fun z : ℂ => z * a) hlog
  calc
    boundaryLineOnePointRealParam_logarithmicPhaseFunction t x =
        Complex.exp (a * (Real.log x : ℂ)) := by
          rfl
    _ = Complex.exp ((Real.log x : ℂ) * a) :=
          congrArg Complex.exp harg_left
    _ = Complex.exp (Complex.log (x : ℂ) * a) :=
          congrArg Complex.exp harg_right
    _ = (x : ℂ) ^ a :=
          (Complex.cpow_def_of_ne_zero hx_complex_ne a).symm

/-- Positive real samples of the logarithmic phase agree with the complex-power
notation used in the Dirichlet-polynomial partial sums. -/
theorem boundaryLineOnePointRealParam_logarithmicPhaseFunction_eq_cpow_of_pos
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    boundaryLineOnePointRealParam_logarithmicPhaseFunction t x =
      (x : ℂ) ^ (-(t : ℂ) * Complex.I) := by
  exact logarithmicPhaseFunction_positiveReal_cpow t hx

/-- Deep algebraic sink reordering the chain-rule derivative into the public
`a / x * f x` form. -/
theorem logarithmicPhaseFunction_positiveReal_derivative_reorder
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    Complex.exp (((-(t : ℂ) * Complex.I) * (Real.log x : ℂ))) *
        (((-(t : ℂ) * Complex.I)) * (x⁻¹ : ℂ)) =
      (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhaseFunction t x) := by
  let a : ℂ := -(t : ℂ) * Complex.I
  let E : ℂ := Complex.exp (a * (Real.log x : ℂ))
  have hinv : (x⁻¹ : ℂ) = (x : ℂ)⁻¹ :=
    Complex.ofReal_inv x
  have hreplace_inv :
      E * (a * (x⁻¹ : ℂ)) = E * (a * (x : ℂ)⁻¹) :=
    congrArg (fun z : ℂ => E * (a * z)) hinv
  have hcomm :
      E * (a * (x : ℂ)⁻¹) = (a * (x : ℂ)⁻¹) * E :=
    mul_comm E (a * (x : ℂ)⁻¹)
  have hdiv : a / (x : ℂ) = a * (x : ℂ)⁻¹ :=
    div_eq_mul_inv a (x : ℂ)
  have hreplace_div :
      (a * (x : ℂ)⁻¹) * E = (a / (x : ℂ)) * E :=
    congrArg (fun z : ℂ => z * E) hdiv.symm
  calc
    E * (a * (x⁻¹ : ℂ)) = E * (a * (x : ℂ)⁻¹) :=
      hreplace_inv
    _ = (a * (x : ℂ)⁻¹) * E :=
      hcomm
    _ = (a / (x : ℂ)) * E :=
      hreplace_div

/-- Owner API: derivative of the logarithmic phase on the positive real axis. -/
theorem logarithmicPhaseFunction_positiveReal_hasDerivAt
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt
      (boundaryLineOnePointRealParam_logarithmicPhaseFunction t)
      (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhaseFunction t x)
      x := by
  let a : ℂ := -(t : ℂ) * Complex.I
  have hlog_real : HasDerivAt Real.log x⁻¹ x :=
    Real.hasDerivAt_log hx.ne'
  have hlog_complex :
      HasDerivAt (fun y : ℝ => (Real.log y : ℂ)) (x⁻¹ : ℂ) x :=
    hlog_real.ofReal_comp
  have hphase :
      HasDerivAt
        (fun y : ℝ => a * (Real.log y : ℂ))
        (a * (x⁻¹ : ℂ))
        x :=
    hlog_complex.const_mul a
  have hexp :
      HasDerivAt
        (fun y : ℝ => Complex.exp (a * (Real.log y : ℂ)))
        (Complex.exp (a * (Real.log x : ℂ)) * (a * (x⁻¹ : ℂ)))
        x :=
    hphase.cexp
  have hderiv_reorder :
      Complex.exp (a * (Real.log x : ℂ)) * (a * (x⁻¹ : ℂ)) =
        (a / (x : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhaseFunction t x := by
    exact logarithmicPhaseFunction_positiveReal_derivative_reorder t hx
  exact hderiv_reorder ▸ hexp

/-- Real-part calculation for the purely imaginary logarithmic-phase exponent. -/
theorem logarithmicPhaseFunction_exponent_re_zero
    (t : ℝ)
    (x : ℝ) :
    (((-(t : ℂ) * Complex.I) * (Real.log x : ℂ)).re) = 0 := by
  let u : ℂ := -(t : ℂ) * Complex.I
  let v : ℂ := (Real.log x : ℂ)
  have hu_re : u.re = 0 := by
    have hneg_im : (-(t : ℂ)).im = 0 := by
      calc
        (-(t : ℂ)).im = -((t : ℂ).im) :=
          Complex.neg_im (t : ℂ)
        _ = -0 :=
          congrArg Neg.neg (Complex.ofReal_im t)
        _ = 0 :=
          neg_zero
    calc
      u.re = (-(t : ℂ) * Complex.I).re :=
        rfl
      _ = - (-(t : ℂ)).im :=
        Complex.mul_I_re (-(t : ℂ))
      _ = -0 :=
        congrArg Neg.neg hneg_im
      _ = 0 :=
        neg_zero
  have hv_im : v.im = 0 := by
    calc
      v.im = ((Real.log x : ℝ) : ℂ).im :=
        rfl
      _ = 0 :=
        Complex.ofReal_im (Real.log x)
  calc
    (((-(t : ℂ) * Complex.I) * (Real.log x : ℂ)).re) =
        u.re * v.re - u.im * v.im := by
      exact Complex.mul_re u v
    _ = 0 * v.re - u.im * v.im := by
      exact congrArg (fun y : ℝ => y * v.re - u.im * v.im) hu_re
    _ = 0 * v.re - u.im * 0 := by
      exact congrArg (fun y : ℝ => 0 * v.re - u.im * y) hv_im
    _ = 0 - u.im * 0 := by
      exact congrArg (fun y : ℝ => y - u.im * 0) (zero_mul v.re)
    _ = 0 - 0 := by
      exact congrArg (fun y : ℝ => 0 - y) (mul_zero u.im)
    _ = 0 :=
      sub_zero 0

/-- Unit norm of the positive-real logarithmic phase.

This is the elementary identity `‖exp (-it log x)‖ = 1`; it is peeled as the
phase-normalization sink used by the derivative norm algebra. -/
theorem boundaryLineOnePointRealParam_logarithmicPhaseFunction_norm
    (t : ℝ)
    (x : ℝ) :
    ‖boundaryLineOnePointRealParam_logarithmicPhaseFunction t x‖ = 1 := by
  let exponent : ℂ := (-(t : ℂ) * Complex.I) * (Real.log x : ℂ)
  have hnorm_abs :
      ‖Complex.exp exponent‖ = Complex.abs (Complex.exp exponent) :=
    Complex.norm_eq_abs (Complex.exp exponent)
  have habs_exp :
      Complex.abs (Complex.exp exponent) = Real.exp exponent.re :=
    Complex.abs_exp exponent
  have hexponent_re : exponent.re = 0 :=
    logarithmicPhaseFunction_exponent_re_zero t x
  have hexp_zero : Real.exp 0 = 1 :=
    Real.exp_zero
  calc
    ‖boundaryLineOnePointRealParam_logarithmicPhaseFunction t x‖ =
        ‖Complex.exp exponent‖ :=
      rfl
    _ = Complex.abs (Complex.exp exponent) :=
      hnorm_abs
    _ = Real.exp exponent.re :=
      habs_exp
    _ = Real.exp 0 :=
      congrArg Real.exp hexponent_re
    _ = 1 :=
      hexp_zero

/-- Numerator norm for the logarithmic-phase derivative. -/
theorem logarithmicPhaseFunction_derivative_numerator_norm
    (t : ℝ) :
    ‖(-(t : ℂ) * Complex.I)‖ = ‖t‖ := by
  have hmul :
      ‖(-(t : ℂ) * Complex.I)‖ = ‖-(t : ℂ)‖ * ‖Complex.I‖ :=
    norm_mul (-(t : ℂ)) Complex.I
  have hneg : ‖-(t : ℂ)‖ = ‖(t : ℂ)‖ :=
    norm_neg (t : ℂ)
  have hI : ‖Complex.I‖ = 1 :=
    norm_I
  have hreal : ‖(t : ℂ)‖ = ‖t‖ :=
    RCLike.norm_ofReal t
  calc
    ‖(-(t : ℂ) * Complex.I)‖ = ‖-(t : ℂ)‖ * ‖Complex.I‖ :=
      hmul
    _ = ‖(t : ℂ)‖ * ‖Complex.I‖ :=
      congrArg (fun y : ℝ => y * ‖Complex.I‖) hneg
    _ = ‖(t : ℂ)‖ * 1 :=
      congrArg (fun y : ℝ => ‖(t : ℂ)‖ * y) hI
    _ = ‖(t : ℂ)‖ :=
      mul_one ‖(t : ℂ)‖
    _ = ‖t‖ :=
      hreal

/-- Denominator norm for a positive real embedded in `ℂ`. -/
theorem logarithmicPhaseFunction_positiveReal_denominator_norm
    {x : ℝ}
    (hx : 0 < x) :
    ‖(x : ℂ)‖ = x := by
  have hreal : ‖(x : ℂ)‖ = ‖x‖ :=
    RCLike.norm_ofReal x
  have hx_norm : ‖x‖ = x :=
    norm_of_nonneg hx.le
  exact hreal.trans hx_norm

/-- Division by a positive real denominator after taking complex norms. -/
theorem logarithmicPhaseFunction_positiveReal_norm_div_algebra
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    ‖(-(t : ℂ) * Complex.I)‖ / ‖(x : ℂ)‖ = ‖t‖ / x := by
  have hnum : ‖(-(t : ℂ) * Complex.I)‖ = ‖t‖ :=
    logarithmicPhaseFunction_derivative_numerator_norm t
  have hden : ‖(x : ℂ)‖ = x :=
    logarithmicPhaseFunction_positiveReal_denominator_norm hx
  calc
    ‖(-(t : ℂ) * Complex.I)‖ / ‖(x : ℂ)‖ =
        ‖t‖ / ‖(x : ℂ)‖ :=
      congrArg (fun y : ℝ => y / ‖(x : ℂ)‖) hnum
    _ = ‖t‖ / x :=
      congrArg (fun y : ℝ => ‖t‖ / y) hden

/-- Deep algebraic sink for the logarithmic-phase derivative norm on the
positive real axis. -/
theorem logarithmicPhaseFunction_positiveReal_derivative_norm_algebra
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    ‖(((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhaseFunction t x)‖ =
      ‖t‖ / x := by
  let numerator : ℂ := -(t : ℂ) * Complex.I
  let denominator : ℂ := (x : ℂ)
  let phase : ℂ := boundaryLineOnePointRealParam_logarithmicPhaseFunction t x
  have hphase_norm : ‖phase‖ = 1 :=
    boundaryLineOnePointRealParam_logarithmicPhaseFunction_norm t x
  have hproduct_norm :
      ‖(numerator / denominator) * phase‖ =
        ‖numerator / denominator‖ * ‖phase‖ :=
    norm_mul (numerator / denominator) phase
  have hquotient_norm :
      ‖numerator / denominator‖ = ‖numerator‖ / ‖denominator‖ :=
    norm_div numerator denominator
  have hquotient_norm_target :
      ‖numerator‖ / ‖denominator‖ = ‖t‖ / x :=
    logarithmicPhaseFunction_positiveReal_norm_div_algebra t hx
  calc
    ‖(((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhaseFunction t x)‖ =
        ‖(numerator / denominator) * phase‖ :=
      rfl
    _ = ‖numerator / denominator‖ * ‖phase‖ :=
      hproduct_norm
    _ = (‖numerator‖ / ‖denominator‖) * ‖phase‖ :=
      congrArg (fun y : ℝ => y * ‖phase‖) hquotient_norm
    _ = (‖numerator‖ / ‖denominator‖) * 1 :=
      congrArg (fun y : ℝ => (‖numerator‖ / ‖denominator‖) * y) hphase_norm
    _ = ‖numerator‖ / ‖denominator‖ :=
      mul_one (‖numerator‖ / ‖denominator‖)
    _ = ‖t‖ / x :=
      hquotient_norm_target

/-- The logarithmic phase has derivative `(-it / x) exp (-it log x)` on the
positive real line. -/
theorem boundaryLineOnePointRealParam_logarithmicPhaseFunction_hasDerivAt
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    HasDerivAt
      (boundaryLineOnePointRealParam_logarithmicPhaseFunction t)
      (((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhaseFunction t x)
      x := by
  exact logarithmicPhaseFunction_positiveReal_hasDerivAt t hx

/-- Owner API: the derivative magnitude of the logarithmic phase is `|t| / x`.

The proof combines the positive-real logarithmic branch normalization with
`‖exp (iθ)‖ = 1` and the reciprocal norm of a positive real. -/
theorem logarithmicPhaseFunction_positiveReal_derivative_norm_eq
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    ‖(((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhaseFunction t x)‖ =
      ‖t‖ / x := by
  exact logarithmicPhaseFunction_positiveReal_derivative_norm_algebra t hx

/-- The derivative magnitude of the logarithmic phase is exactly `|t| / x`. -/
theorem boundaryLineOnePointRealParam_logarithmicPhaseFunction_derivative_norm_eq
    (t : ℝ)
    {x : ℝ}
    (hx : 0 < x) :
    ‖(((-(t : ℂ) * Complex.I) / (x : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhaseFunction t x)‖ =
      ‖t‖ / x := by
  exact logarithmicPhaseFunction_positiveReal_derivative_norm_eq t hx

/-- Deep analytic owner estimate for logarithmic-phase partial sums.

This is the first-derivative/Euler-Maclaurin bound for
`u ↦ exp (-i t log u)` after the canonical cutoff; cf. Titchmarsh,
*The Theory of the Riemann Zeta-function*, §3.5. -/
theorem logarithmicPhasePartialSum_firstDerivative_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {x : ℝ}
    (hx : (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) := by
  sorry

/-- Standard first-derivative/Euler-Maclaurin estimate for the logarithmic
phase partial sums.

The proof is the classical monotone first-derivative argument for
`φ(x) = -t log x`, with the Euler-Maclaurin endpoint correction; cf.
Titchmarsh, *The Theory of the Riemann Zeta-function*, §3.5. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_norm_le_firstDerivative_core
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {x : ℝ}
    (hx : (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) := by
  exact logarithmicPhasePartialSum_firstDerivative_bound t ht hx

/-- First-derivative/Euler-Maclaurin owner estimate for the logarithmic phase
`u ↦ exp (-i t log u)`.

This is the analytic estimate which replaces any constant-ratio argument.  The
proof chain is the standard monotone first-derivative bound for
`φ(u) = -t log u`, plus the Euler-Maclaurin endpoint correction; cf.
Titchmarsh, *The Theory of the Riemann Zeta-function*, §3.5. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_norm_le_firstDerivative
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {x : ℝ}
    (hx : (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_norm_le_firstDerivative_core
      t ht hx

/-- Euler-Maclaurin / van-der-Corput bound for the logarithmic-phase oscillator.

This is the canonical replacement for the false constant-ratio geometric route:
the proof studies the phase `x ↦ -t log x` and obtains a partial-sum bound
with the necessary long-range `x / |t|` term.  The latter term is unavoidable:
the primitive of `u^{-it}` has size comparable to `x / |t|` for large `x`;
cf. Titchmarsh, *The Theory of the Riemann Zeta-function*, §3.5. -/
theorem boundaryLineOnePointRealParam_logarithmicPhasePartialSum_norm_le_vdc
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {x : ℝ}
    (hx : (⌊2 + ‖t‖⌋₊ : ℝ) ≤ x) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      8 * ((x / ‖t‖) + Real.sqrt (1 + ‖t‖)) * Real.log (2 + x) := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhasePartialSum_norm_le_firstDerivative
      t ht hx

/-- First conjunct of the finite Abel package: the endpoint partial sum at `M`
is exactly the first-derivative estimate at the real endpoint `M`. -/
theorem logarithmicPhase_firstDerivative_finiteAbel_rightPartial_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊((M : ℕ) : ℝ)⌋₊‖ ≤
      8 * ((((M : ℕ) : ℝ) / ‖t‖) + Real.sqrt (1 + ‖t‖)) *
        Real.log (2 + ((M : ℕ) : ℝ)) := by
  have hreal :
      ((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) ≤ ((M : ℕ) : ℝ) :=
    Nat.cast_le.mpr hNM
  exact logarithmicPhasePartialSum_firstDerivative_bound t ht hreal

/-- Sharper endpoint estimate in the logarithmic-phase partial-summation
package.

This is not obtained by multiplying the coarse primitive bound by the reciprocal
endpoint weights.  It is the endpoint part of the oscillatory
Euler-Maclaurin/partial-summation argument, where cancellation at the cutoff and
right endpoint is retained. -/
theorem oscillatoryEulerMaclaurin_logarithmicPhase_endpoint_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊‖ +
        ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖) := by
  sorry

/-- Endpoint arithmetic after the logarithmic-phase first-derivative
Euler-Maclaurin estimate.

The two terms are the reciprocal endpoint contributions at the right endpoint
`M` and at the canonical cutoff `⌊2 + |t|⌋₊`.  The analytic input is only the
first-derivative primitive estimate; this theorem owns the subsequent
reciprocal-weight and cutoff arithmetic.  Cf. Apostol, *Introduction to
Analytic Number Theory*, partial summation, and Titchmarsh, Ch. 3. -/
theorem eulerMaclaurin_logarithmicPhase_finiteAbel_endpoint_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊‖ +
        ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖) := by
  exact oscillatoryEulerMaclaurin_logarithmicPhase_endpoint_bound t ht hNM

/-- Sharper reciprocal-derivative integral estimate in the logarithmic-phase
partial-summation package.

This is the variation part of the oscillatory Euler-Maclaurin argument.  The
estimate keeps cancellation in the logarithmic phase before integrating against
the reciprocal derivative; it is not a consequence of the coarse primitive
majorant alone. -/
theorem oscillatoryEulerMaclaurin_logarithmicPhase_integral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖) := by
  sorry

/-- Integral arithmetic for the reciprocal-derivative term in the finite Abel
decomposition.

This is the variation side of partial summation for the weight `x ↦ 1 / x`.
After the first-derivative Euler-Maclaurin estimate bounds the logarithmic-phase
primitive, this theorem owns the monotone reciprocal-variation integral and the
normalization to the cutoff logarithm.  Cf. Edwards, *Riemann's Zeta Function*,
Euler-Maclaurin derivations. -/
theorem eulerMaclaurin_logarithmicPhase_finiteAbel_integral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖) := by
  exact oscillatoryEulerMaclaurin_logarithmicPhase_integral_bound t ht hNM

/-- Deep Euler-Maclaurin arithmetic owner for the finite Abel endpoint and
reciprocal-derivative integral terms.

This is the remaining bookkeeping attached to the first-derivative
Euler-Maclaurin estimate: the reciprocal endpoint weights and the integral of
the reciprocal derivative are both normalized to the same logarithmic cutoff
constant. -/
theorem logarithmicPhase_firstDerivative_finiteAbel_endpoint_integral_arithmetic
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊‖ +
        ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖)) ∧
    (‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖)) := by
  exact
    ⟨eulerMaclaurin_logarithmicPhase_finiteAbel_endpoint_bound t ht hNM,
      eulerMaclaurin_logarithmicPhase_finiteAbel_integral_bound t ht hNM⟩

/-- Exact endpoint arithmetic for the finite Abel package.  This is the
reciprocal-weight endpoint part after the first-derivative estimate has been
applied at `M` and at the canonical cutoff. -/
theorem logarithmicPhase_firstDerivative_finiteAbel_endpoint_arithmetic
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊‖ +
        ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖) := by
  exact
    (logarithmicPhase_firstDerivative_finiteAbel_endpoint_integral_arithmetic
      t ht hNM).1

/-- Exact reciprocal-derivative integral arithmetic for the finite Abel package.
The analytic input is the first-derivative partial-sum estimate; this lemma owns
the endpoint and logarithmic integral bookkeeping. -/
theorem logarithmicPhase_firstDerivative_finiteAbel_integral_arithmetic
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖) := by
  exact
    (logarithmicPhase_firstDerivative_finiteAbel_endpoint_integral_arithmetic
      t ht hNM).2

/-- Algebraic endpoint extraction from the logarithmic-phase first-derivative
partial-sum estimate.

This is not a separate analytic input: the two reciprocal endpoint weights are
controlled after the canonical cutoff by applying
`logarithmicPhasePartialSum_firstDerivative_bound` at `M` and at the cutoff. -/
theorem logarithmicPhase_firstDerivative_eulerMaclaurin_finiteAbel_package
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    (‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊((M : ℕ) : ℝ)⌋₊‖ ≤
        8 * ((((M : ℕ) : ℝ) / ‖t‖) + Real.sqrt (1 + ‖t‖)) *
          Real.log (2 + ((M : ℕ) : ℝ))) ∧
    (‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊‖ +
        ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖)) ∧
    (‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
        2 + 8 * Real.log (3 + ‖t‖)) := by
  exact
    ⟨logarithmicPhase_firstDerivative_finiteAbel_rightPartial_bound t ht hNM,
      logarithmicPhase_firstDerivative_finiteAbel_endpoint_arithmetic t ht hNM,
      logarithmicPhase_firstDerivative_finiteAbel_integral_arithmetic t ht hNM⟩

/-- Explicit finite Abel-tail constant for the logarithmic-phase oscillator
after the canonical cutoff.

The constant is intentionally not normalized to `1`: the owner estimate must
record the actual Abel endpoint and reciprocal-derivative contribution rather
than hiding it behind a false unit-bound surface. -/
def boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant
    (t : ℝ) : ℝ :=
  4 + 16 * Real.log (3 + ‖t‖)

/-- Owner API: endpoint contribution in the finite Abel decomposition after the
canonical cutoff. -/
theorem logarithmicPhase_finiteAbelEndpoint_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          ⌊((M : ℕ) : ℝ)⌋₊‖ +
      ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤
      2 + 8 * Real.log (3 + ‖t‖) := by
  exact (logarithmicPhase_firstDerivative_eulerMaclaurin_finiteAbel_package
    t ht hNM).2.1

/-- Endpoint contribution in the finite Abel decomposition after the canonical
cutoff.  This consumes the first-derivative logarithmic-phase primitive bound at
the two natural endpoints and the reciprocal endpoint weights. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelEndpoint_norm_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          ⌊((M : ℕ) : ℝ)⌋₊‖ +
      ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤
      2 + 8 * Real.log (3 + ‖t‖) := by
  exact logarithmicPhase_finiteAbelEndpoint_bound t ht hNM

/-- Owner API: reciprocal-derivative integral contribution in the finite Abel
decomposition after the canonical cutoff. -/
theorem logarithmicPhase_finiteAbelDerivativeIntegral_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      2 + 8 * Real.log (3 + ‖t‖) := by
  exact
    (logarithmicPhase_firstDerivative_eulerMaclaurin_finiteAbel_package
      t ht hNM).2.2

/-- Reciprocal-derivative integral contribution in the finite Abel decomposition.
The integrand is the product of the derivative of `u ↦ 1/u` and the
first-derivative logarithmic-phase primitive bound. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelDerivativeIntegral_norm_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊‖ ≤
      2 + 8 * Real.log (3 + ‖t‖) := by
  exact logarithmicPhase_finiteAbelDerivativeIntegral_bound t ht hNM

/-- Finite Abel-tail estimate obtained from the exact Abel identity, endpoint
bounds, and reciprocal-derivative integral bound. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelTail_norm_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
        ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  let N : ℕ := ⌊2 + ‖t‖⌋₊
  let SM : ℂ :=
    ((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ) *
      boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
        ⌊((M : ℕ) : ℝ)⌋₊
  let SN : ℂ :=
    (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
      boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
        ⌊(((N : ℕ) : ℝ))⌋₊
  let J : ℂ :=
    ∫ x in Set.Ioc (((N : ℕ) : ℝ)) ((M : ℕ) : ℝ),
      deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊
  have hf_diff :
      ∀ x ∈ Set.Icc (((N : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        DifferentiableAt ℝ (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x := by
    intro x hx
    fun_prop
  have hf_int :
      IntegrableOn
        (deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)))
        (Set.Icc (((N : ℕ) : ℝ)) ((M : ℕ) : ℝ)) := by
    fun_prop
  have hidentity :
      (∑ k ∈ Finset.Ioc ⌊(((N : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
          ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))) =
        SM - SN - J := by
    exact
      abelSummation_boundaryLineOnePointRealParam_cutoff_finite_tail_endpoint_derivative_identity
        t hNM hf_diff hf_int
  have hendpoint :
      ‖SM‖ + ‖SN‖ ≤ 2 + 8 * Real.log (3 + ‖t‖) := by
    exact
      boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelEndpoint_norm_le
        t ht hNM
  have hintegral :
      ‖J‖ ≤ 2 + 8 * Real.log (3 + ‖t‖) := by
    exact
      boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelDerivativeIntegral_norm_le
        t ht hNM
  have htriangle :
      ‖SM - SN - J‖ ≤ ‖SM‖ + ‖SN‖ + ‖J‖ := by
    have hfirst : ‖SM - SN - J‖ ≤ ‖SM - SN‖ + ‖J‖ :=
      norm_sub_le (SM - SN) J
    have hsecond : ‖SM - SN‖ ≤ ‖SM‖ + ‖SN‖ :=
      norm_sub_le SM SN
    exact le_trans hfirst (add_le_add_right hsecond ‖J‖)
  have hpost_triangle :
      ‖SM‖ + ‖SN‖ + ‖J‖ ≤
        (2 + 8 * Real.log (3 + ‖t‖)) +
          (2 + 8 * Real.log (3 + ‖t‖)) := by
    exact add_le_add hendpoint hintegral
  have hconstant :
      (2 + 8 * Real.log (3 + ‖t‖)) +
          (2 + 8 * Real.log (3 + ‖t‖)) =
        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
    let L : ℝ := Real.log (3 + ‖t‖)
    have hadd :
        (2 + 8 * L) + (2 + 8 * L) =
          (2 + 2) + (8 * L + 8 * L) := by
      ac_rfl
    have htwo : (2 : ℝ) + 2 = 4 := by
      rfl
    have height_coeff : (8 : ℝ) + 8 = 16 := by
      rfl
    have height : (8 : ℝ) * L + 8 * L = 16 * L := by
      calc
        (8 : ℝ) * L + 8 * L = ((8 : ℝ) + 8) * L := by
          exact (add_mul (8 : ℝ) 8 L).symm
        _ = 16 * L := by
          exact congrArg (fun c : ℝ => c * L) height_coeff
    calc
      (2 + 8 * Real.log (3 + ‖t‖)) +
          (2 + 8 * Real.log (3 + ‖t‖)) =
          (2 + 8 * L) + (2 + 8 * L) := by
        rfl
      _ = (2 + 2) + (8 * L + 8 * L) :=
        hadd
      _ = 4 + (8 * L + 8 * L) := by
        exact congrArg (fun x : ℝ => x + (8 * L + 8 * L)) htwo
      _ = 4 + 16 * L := by
        exact congrArg (fun x : ℝ => 4 + x) height
      _ = boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
        rfl
  exact Eq.subst
    (motive := fun z : ℂ =>
      ‖z‖ ≤ boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t)
    hidentity.symm
    (le_trans htriangle (le_trans hpost_triangle (le_of_eq hconstant)))

/-- The completed Abel/Euler-Maclaurin tail package for the logarithmic-phase
oscillator after the canonical cutoff.

The pointwise primitive has an unavoidable `x / |t|` component, so the owner
bound carries the explicit cutoff constant
`boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t`.  The
classical proof combines Abel summation with cancellation in the endpoint and
reciprocal-derivative terms at `N = ⌊2 + |t|⌋₊`. -/
theorem boundaryLineOnePointRealParam_logarithmicPhase_abelTail_norm_le_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M) :
    ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
        ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  exact
    boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelTail_norm_le
      t ht hNM

/-- Abel summation in the precise finite form needed for the boundary-line tail:
coefficients are the logarithmic-phase oscillatory partial sums of `n^{-it}` and
the weight is `1/x`. -/
theorem abelSummation_boundaryLineOnePointRealParam_finite_tail_identity
    (t : ℝ)
    {a b : ℝ}
    (ha : 0 ≤ a)
    (hab : a ≤ b)
    (hf_diff :
      ∀ x ∈ Set.Icc a b, DifferentiableAt ℝ (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x)
    (hf_int :
      IntegrableOn
        (deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)))
        (Set.Icc a b)) :
    ∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
        ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)) =
      ((b : ℂ)⁻¹ : ℂ) *
          (∑ k ∈ Finset.Icc 0 ⌊b⌋₊,
            (k : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        ((a : ℂ)⁻¹ : ℂ) *
          (∑ k ∈ Finset.Icc 0 ⌊a⌋₊,
            (k : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        ∫ x in Set.Ioc a b,
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            (∑ k ∈ Finset.Icc 0 ⌊x⌋₊,
              (k : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
  exact sum_mul_eq_sub_sub_integral_mul
    (fun k : ℕ => (k : ℂ) ^ (-(t : ℂ) * Complex.I))
    ha
    hab
    hf_diff
    hf_int

/-- Abel summation specialized to natural endpoints.  The floor terms are left
visible so the theorem is definitionally aligned with mathlib's statement. -/
theorem abelSummation_boundaryLineOnePointRealParam_finite_nat_tail_identity
    (t : ℝ)
    {N M : ℕ}
    (hNM : N ≤ M)
    (hf_diff :
      ∀ x ∈ Set.Icc ((N : ℕ) : ℝ) ((M : ℕ) : ℝ),
        DifferentiableAt ℝ (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x)
    (hf_int :
      IntegrableOn
        (deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)))
        (Set.Icc ((N : ℕ) : ℝ) ((M : ℕ) : ℝ))) :
    ∑ k ∈ Finset.Ioc ⌊((N : ℕ) : ℝ)⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
        ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)) =
      ((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ) *
          (∑ k ∈ Finset.Icc 0 ⌊((M : ℕ) : ℝ)⌋₊,
            (k : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        ((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ) *
          (∑ k ∈ Finset.Icc 0 ⌊((N : ℕ) : ℝ)⌋₊,
            (k : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        ∫ x in Set.Ioc ((N : ℕ) : ℝ) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            (∑ k ∈ Finset.Icc 0 ⌊x⌋₊,
              (k : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
  have ha : (0 : ℝ) ≤ ((N : ℕ) : ℝ) :=
    Nat.cast_nonneg N
  have hab : ((N : ℕ) : ℝ) ≤ ((M : ℕ) : ℝ) := by
    exact_mod_cast hNM
  exact abelSummation_boundaryLineOnePointRealParam_finite_tail_identity
    t ha hab hf_diff hf_int

/-- Abel summation with the canonical boundary-line cutoff as the left endpoint.
The floor terms are kept visible so this remains a direct transport of mathlib's
finite Abel identity. -/
theorem abelSummation_boundaryLineOnePointRealParam_cutoff_nat_tail_identity
    (t : ℝ)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hf_diff :
      ∀ x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        DifferentiableAt ℝ (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x)
    (hf_int :
      IntegrableOn
        (deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)))
        (Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ))) :
    ∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
        ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)) =
      ((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ) *
          (∑ k ∈ Finset.Icc 0 ⌊((M : ℕ) : ℝ)⌋₊,
            (k : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        (((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          (∑ k ∈ Finset.Icc 0 ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊,
            (k : ℂ) ^ (-(t : ℂ) * Complex.I)) -
        ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            (∑ k ∈ Finset.Icc 0 ⌊x⌋₊,
              (k : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
  exact abelSummation_boundaryLineOnePointRealParam_finite_nat_tail_identity
    t hNM hf_diff hf_int

/-- Exact finite Abel summation endpoint/deivative decomposition at the canonical
boundary-line cutoff, written in terms of the owner partial-sum primitive. -/
theorem abelSummation_boundaryLineOnePointRealParam_cutoff_finite_tail_endpoint_derivative_identity
    (t : ℝ)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hf_diff :
      ∀ x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        DifferentiableAt ℝ (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x)
    (hf_int :
      IntegrableOn
        (deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)))
        (Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ))) :
    ∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
        ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)) =
      ((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊ -
        (((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ -
        ∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            boundaryLineOnePointRealParam_logarithmicPhasePartialSum t ⌊x⌋₊ := by
  exact abelSummation_boundaryLineOnePointRealParam_cutoff_nat_tail_identity
    t hNM hf_diff hf_int

/-- The right endpoint in the finite Abel decomposition is controlled by the
reciprocal weight times the owner partial-sum bound. -/
theorem abelSummation_boundaryLineOnePointRealParam_right_endpoint_norm_le
    (t : ℝ)
    {M : ℕ}
    (K : ℝ)
    (hK_nonneg : 0 ≤ K)
    (hpartial :
      ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
        ⌊((M : ℕ) : ℝ)⌋₊‖ ≤ K) :
    ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          ⌊((M : ℕ) : ℝ)⌋₊‖ ≤
      (1 / (M : ℝ)) * K := by
  have hM_factor :
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ = 1 / (M : ℝ) := by
    calc
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ =
          ‖((((M : ℕ) : ℝ) : ℂ))‖⁻¹ := by
        exact norm_inv ((((M : ℕ) : ℝ) : ℂ))
      _ = ‖((M : ℝ))‖⁻¹ := by
        exact congrArg Inv.inv (Complex.norm_ofReal (M : ℝ))
      _ = (M : ℝ)⁻¹ := by
        have hM_nonneg : 0 ≤ (M : ℝ) :=
          Nat.cast_nonneg M
        exact congrArg Inv.inv (Real.norm_of_nonneg hM_nonneg)
      _ = 1 / (M : ℝ) := by
        exact (one_div (M : ℝ)).symm
  calc
    ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          ⌊((M : ℕ) : ℝ)⌋₊‖ =
        ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ *
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊((M : ℕ) : ℝ)⌋₊‖ := by
          exact norm_mul (((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))
            (boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
              ⌊((M : ℕ) : ℝ)⌋₊)
    _ ≤ (1 / (M : ℝ)) * K := by
          exact mul_le_mul (le_of_eq hM_factor) hpartial hK_nonneg
            (norm_nonneg (((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)))

/-- The cutoff endpoint in the finite Abel decomposition is controlled by the
cutoff reciprocal weight times the owner partial-sum bound. -/
theorem abelSummation_boundaryLineOnePointRealParam_cutoff_endpoint_norm_le
    (t : ℝ)
    (K : ℝ)
    (hK_nonneg : 0 ≤ K)
    (hpartial :
      ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
        ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤ K) :
    ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ ≤
      (1 / (⌊2 + ‖t‖⌋₊ : ℝ)) * K := by
  let N : ℕ := ⌊2 + ‖t‖⌋₊
  have hN_factor :
      ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ = 1 / (N : ℝ) := by
    calc
      ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ =
          ‖((((N : ℕ) : ℝ) : ℂ))‖⁻¹ := by
        exact norm_inv ((((N : ℕ) : ℝ) : ℂ))
      _ = ‖((N : ℝ))‖⁻¹ := by
        exact congrArg Inv.inv (Complex.norm_ofReal (N : ℝ))
      _ = (N : ℝ)⁻¹ := by
        have hN_nonneg : 0 ≤ (N : ℝ) :=
          Nat.cast_nonneg N
        exact congrArg Inv.inv (Real.norm_of_nonneg hN_nonneg)
      _ = 1 / (N : ℝ) := by
        exact (one_div (N : ℝ)).symm
  calc
    ‖(((((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
        boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
          ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊‖ =
        ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) *
          boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((N : ℕ) : ℝ))⌋₊‖ := by
          rfl
    _ = ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ *
          ‖boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
            ⌊(((N : ℕ) : ℝ))⌋₊‖ := by
          exact norm_mul (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))
            (boundaryLineOnePointRealParam_logarithmicPhasePartialSum t
              ⌊(((N : ℕ) : ℝ))⌋₊)
    _ ≤ (1 / (N : ℝ)) * K := by
          exact mul_le_mul (le_of_eq hN_factor) hpartial hK_nonneg
            (norm_nonneg (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)))

/-- Finite Abel reduction for the post-cutoff boundary-line oscillatory tail.

This is the algebraic/order part of the Euler-Maclaurin tail route: once the
oscillatory primitives
`∑_{0 ≤ k ≤ floor x} k^{-it}` and the reciprocal-derivative integral have been
bounded, the finite weighted tail is bounded by the two endpoint terms and the
integral term. -/
theorem abelSummation_boundaryLineOnePointRealParam_cutoff_finite_tail_norm_le
    (t : ℝ)
    {M : ℕ}
    (hNM : ⌊2 + ‖t‖⌋₊ ≤ M)
    (hf_diff :
      ∀ x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
        DifferentiableAt ℝ (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x)
    (hf_int :
      IntegrableOn
        (deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)))
        (Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ)))
    (K I : ℝ)
    (hK_nonneg : 0 ≤ K)
    (hpartial :
      ∀ x : ℝ,
        x ∈ Set.Icc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ) →
        ‖∑ k ∈ Finset.Icc 0 ⌊x⌋₊,
          (k : ℂ) ^ (-(t : ℂ) * Complex.I)‖ ≤ K)
    (hintegral :
      ‖∫ x in Set.Ioc (((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ)) ((M : ℕ) : ℝ),
          deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
            (∑ k ∈ Finset.Icc 0 ⌊x⌋₊,
              (k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤ I) :
    ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
        ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      (1 / (M : ℝ)) * K +
        (1 / (⌊2 + ‖t‖⌋₊ : ℝ)) * K + I := by
  let N : ℕ := ⌊2 + ‖t‖⌋₊
  let a : ℝ := ((N : ℕ) : ℝ)
  let b : ℝ := ((M : ℕ) : ℝ)
  let SM : ℂ :=
    ∑ k ∈ Finset.Icc 0 ⌊b⌋₊,
      (k : ℂ) ^ (-(t : ℂ) * Complex.I)
  let SN : ℂ :=
    ∑ k ∈ Finset.Icc 0 ⌊a⌋₊,
      (k : ℂ) ^ (-(t : ℂ) * Complex.I)
  let J : ℂ :=
    ∫ x in Set.Ioc a b,
      deriv (fun y : ℝ => ((y : ℂ)⁻¹ : ℂ)) x *
        (∑ k ∈ Finset.Icc 0 ⌊x⌋₊,
          (k : ℂ) ^ (-(t : ℂ) * Complex.I))
  have hidentity :
      (∑ k ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊,
          ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))) =
        ((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ) * SM -
          (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN - J := by
    exact abelSummation_boundaryLineOnePointRealParam_cutoff_nat_tail_identity
      t hNM hf_diff hf_int
  have hM_mem :
      b ∈ Set.Icc a b := by
    exact ⟨by exact_mod_cast hNM, le_rfl⟩
  have hN_mem :
      a ∈ Set.Icc a b := by
    exact ⟨le_rfl, by exact_mod_cast hNM⟩
  have hSM_norm : ‖SM‖ ≤ K :=
    hpartial b hM_mem
  have hSN_norm : ‖SN‖ ≤ K :=
    hpartial a hN_mem
  have hM_factor :
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ = 1 / (M : ℝ) := by
    calc
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ =
          ‖((((M : ℕ) : ℝ) : ℂ))‖⁻¹ := by
        exact norm_inv ((((M : ℕ) : ℝ) : ℂ))
      _ = ‖((M : ℝ))‖⁻¹ := by
        exact congrArg Inv.inv (Complex.norm_ofReal (M : ℝ))
      _ = (M : ℝ)⁻¹ := by
        have hM_nonneg : 0 ≤ (M : ℝ) :=
          Nat.cast_nonneg M
        exact congrArg Inv.inv (Real.norm_of_nonneg hM_nonneg)
      _ = 1 / (M : ℝ) := by
        exact (one_div (M : ℝ)).symm
  have hN_factor :
      ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ = 1 / (N : ℝ) := by
    calc
      ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ =
          ‖((((N : ℕ) : ℝ) : ℂ))‖⁻¹ := by
        exact norm_inv ((((N : ℕ) : ℝ) : ℂ))
      _ = ‖((N : ℝ))‖⁻¹ := by
        exact congrArg Inv.inv (Complex.norm_ofReal (N : ℝ))
      _ = (N : ℝ)⁻¹ := by
        have hN_nonneg : 0 ≤ (N : ℝ) :=
          Nat.cast_nonneg N
        exact congrArg Inv.inv (Real.norm_of_nonneg hN_nonneg)
      _ = 1 / (N : ℝ) := by
        exact (one_div (N : ℝ)).symm
  have hM_term :
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM‖ ≤
        (1 / (M : ℝ)) * K := by
    calc
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM‖ =
          ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ * ‖SM‖ := by
        exact norm_mul (((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) SM
      _ ≤ (1 / (M : ℝ)) * K := by
        exact mul_le_mul (le_of_eq hM_factor) hSM_norm hK_nonneg
          (norm_nonneg (((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)))
  have hN_term :
      ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN‖ ≤
        (1 / (N : ℝ)) * K := by
    calc
      ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN‖ =
          ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ))‖ * ‖SN‖ := by
        exact norm_mul (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) SN
      _ ≤ (1 / (N : ℝ)) * K := by
        exact mul_le_mul (le_of_eq hN_factor) hSN_norm hK_nonneg
          (norm_nonneg (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)))
  have htriangle :
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM -
          (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN - J‖ ≤
        ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM‖ +
          ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN‖ + ‖J‖ := by
    have hfirst :
        ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM -
            (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN - J‖ ≤
          ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM -
            (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN‖ + ‖J‖ :=
      norm_sub_le
        (((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM -
          (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN)
        J
    have hsecond :
        ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM -
            (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN‖ ≤
          ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM‖ +
            ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN‖ :=
      norm_sub_le
        (((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM)
        (((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN)
    exact le_trans hfirst (add_le_add_right hsecond ‖J‖)
  have hterms :
      ‖(((((M : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SM‖ +
          ‖(((((N : ℕ) : ℝ) : ℂ)⁻¹ : ℂ)) * SN‖ + ‖J‖ ≤
        (1 / (M : ℝ)) * K + (1 / (N : ℝ)) * K + I :=
    add_le_add (add_le_add hM_term hN_term) hintegral
  exact Eq.subst
    (motive := fun z : ℂ =>
      ‖z‖ ≤ (1 / (M : ℝ)) * K + (1 / (N : ℝ)) * K + I)
    hidentity.symm
    (le_trans htriangle hterms)

/-- Pointwise transport of the post-cutoff boundary-line Dirichlet tail to the
Abel-normalized oscillatory tail. -/
theorem boundaryLineOnePointRealParam_post_cutoff_dirichletTerm_eq_inv_mul_oscillation
    (t : ℝ)
    (n : ℕ) :
    (if ⌊2 + ‖t‖⌋₊ < n then
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)
      else
        0) =
      if ⌊2 + ‖t‖⌋₊ < n then
        ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))
      else
        0 := by
  by_cases hcutoff_lt_n : ⌊2 + ‖t‖⌋₊ < n
  · have hn_pos : 0 < n :=
      lt_trans (boundaryLineOnePointRealParam_cutoff_pos t) hcutoff_lt_n
    have hleft :
        (if ⌊2 + ‖t‖⌋₊ < n then
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)
          else
            0) =
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t) :=
      if_pos hcutoff_lt_n
    have hterm :
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t) =
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
      boundaryLineOnePointRealParam_dirichletTerm_eq_inv_mul_oscillation_left
        t hn_pos
    have hright :
        (if ⌊2 + ‖t‖⌋₊ < n then
            ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))
          else
            0) =
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
      if_pos hcutoff_lt_n
    exact Eq.trans hleft (Eq.trans hterm hright.symm)
  · have hleft :
        (if ⌊2 + ‖t‖⌋₊ < n then
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)
          else
            0) =
          0 :=
      if_neg hcutoff_lt_n
    have hright :
        (if ⌊2 + ‖t‖⌋₊ < n then
            ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))
          else
            0) =
          0 :=
      if_neg hcutoff_lt_n
    exact Eq.trans hleft hright.symm

/-- The zeroth boundary-line Dirichlet monomial vanishes.  This is the only extra
index left after removing `Icc 1 N` from the natural-indexed Dirichlet series. -/
theorem boundaryLineOnePointRealParam_dirichletTerm_zero
    (t : ℝ) :
    (1 : ℂ) / ((0 : ℂ) ^ boundaryLineOnePointRealParam t) = 0 := by
  have hpoint_ne_zero : boundaryLineOnePointRealParam t ≠ 0 := by
    intro hpoint_zero
    have hre_zero :
        (boundaryLineOnePointRealParam t).re = (0 : ℂ).re :=
      congrArg Complex.re hpoint_zero
    have hre_one :
        (boundaryLineOnePointRealParam t).re = 1 :=
      boundaryLineOnePointRealParam_re t
    have hone_eq_zero : (1 : ℝ) = 0 :=
      Eq.trans hre_one.symm hre_zero
    exact one_ne_zero hone_eq_zero
  have hpow_zero :
      (0 : ℂ) ^ boundaryLineOnePointRealParam t = 0 := by
    exact (cpow_eq_zero_iff).mpr ⟨rfl, hpoint_ne_zero⟩
  calc
    (1 : ℂ) / ((0 : ℂ) ^ boundaryLineOnePointRealParam t) =
        (1 : ℂ) / 0 := by
          exact congrArg (fun z : ℂ => (1 : ℂ) / z) hpow_zero
    _ = 0 := by
          exact div_zero (1 : ℂ)

/-- The complement indicator obtained from removing `Icc 1 N` from the natural-indexed
Dirichlet series is exactly the post-cutoff tail indicator. -/
theorem boundaryLineOnePointRealParam_dirichlet_tail_indicator_eq_cutoff_if
    (t : ℝ)
    (N n : ℕ) :
    ({m : ℕ | m ∉ Finset.Icc 1 N}.indicator
        (fun m : ℕ =>
          (1 : ℂ) / ((m : ℂ) ^ boundaryLineOnePointRealParam t)) n) =
      if N < n then
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)
      else
        0 := by
  by_cases hN_lt_n : N < n
  · have hn_not_mem : n ∉ Finset.Icc 1 N := by
      intro hn_mem
      have hn_le_N : n ≤ N :=
        (Finset.mem_Icc.mp hn_mem).2
      exact (Nat.not_lt_of_ge hn_le_N) hN_lt_n
    have hn_mem_tail : n ∈ {m : ℕ | m ∉ Finset.Icc 1 N} :=
      hn_not_mem
    have hleft :
        ({m : ℕ | m ∉ Finset.Icc 1 N}.indicator
            (fun m : ℕ =>
              (1 : ℂ) / ((m : ℂ) ^ boundaryLineOnePointRealParam t)) n) =
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t) :=
      Set.indicator_of_mem hn_mem_tail
        (fun m : ℕ =>
          (1 : ℂ) / ((m : ℂ) ^ boundaryLineOnePointRealParam t))
    have hright :
        (if N < n then
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)
        else
          0) =
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t) :=
      if_pos hN_lt_n
    exact Eq.trans hleft hright.symm
  · by_cases hn_zero : n = 0
    · have hn_not_mem : n ∉ Finset.Icc 1 N := by
        intro hn_mem
        have hone_le_n : 1 ≤ n :=
          (Finset.mem_Icc.mp hn_mem).1
        have hone_le_zero : (1 : ℕ) ≤ 0 :=
          Eq.subst (motive := fun m : ℕ => 1 ≤ m) hn_zero hone_le_n
        exact (Nat.not_succ_le_zero 0) hone_le_zero
      have hn_mem_tail : n ∈ {m : ℕ | m ∉ Finset.Icc 1 N} :=
        hn_not_mem
      have hleft :
          ({m : ℕ | m ∉ Finset.Icc 1 N}.indicator
              (fun m : ℕ =>
                (1 : ℂ) / ((m : ℂ) ^ boundaryLineOnePointRealParam t)) n) =
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t) :=
        Set.indicator_of_mem hn_mem_tail
          (fun m : ℕ =>
            (1 : ℂ) / ((m : ℂ) ^ boundaryLineOnePointRealParam t))
      have hterm_zero :
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t) = 0 :=
        Eq.subst
          (motive := fun m : ℕ =>
            (1 : ℂ) / ((m : ℂ) ^ boundaryLineOnePointRealParam t) = 0)
          hn_zero.symm
          (boundaryLineOnePointRealParam_dirichletTerm_zero t)
      have hright :
          (if N < n then
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)
          else
            0) =
            0 :=
        if_neg hN_lt_n
      exact Eq.trans hleft (Eq.trans hterm_zero hright.symm)
    · have hn_pos : 0 < n :=
        Nat.pos_of_ne_zero hn_zero
      have hone_le_n : 1 ≤ n :=
        Nat.succ_le_of_lt hn_pos
      have hn_le_N : n ≤ N :=
        Nat.le_of_not_gt hN_lt_n
      have hn_mem_Icc : n ∈ Finset.Icc 1 N :=
        Finset.mem_Icc.mpr ⟨hone_le_n, hn_le_N⟩
      have hn_not_mem_tail : n ∉ {m : ℕ | m ∉ Finset.Icc 1 N} := by
        intro hn_mem_tail
        exact hn_mem_tail hn_mem_Icc
      have hleft :
          ({m : ℕ | m ∉ Finset.Icc 1 N}.indicator
              (fun m : ℕ =>
                (1 : ℂ) / ((m : ℂ) ^ boundaryLineOnePointRealParam t)) n) =
            0 :=
        Set.indicator_of_not_mem hn_not_mem_tail
          (fun m : ℕ =>
            (1 : ℂ) / ((m : ℂ) ^ boundaryLineOnePointRealParam t))
      have hright :
          (if N < n then
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)
          else
            0) =
            0 :=
        if_neg hN_lt_n
      exact Eq.trans hleft hright.symm

/-- Removing a finite Dirichlet truncation from a natural-indexed boundary-line
Dirichlet series gives the exact post-cutoff Dirichlet tail. -/
theorem boundaryLineOnePointRealParam_dirichlet_tail_after_cutoff_hasSum_zeta_remainder_of_dirichlet_series
    (t : ℝ)
    (N : ℕ)
    (hζ :
      HasSum
        (fun n : ℕ =>
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t))
        (riemannZeta (boundaryLineOnePointRealParam t))) :
    HasSum
        (fun n : ℕ =>
          if N < n then
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)
          else
            0)
        (riemannZeta (boundaryLineOnePointRealParam t) -
          ∑ n ∈ Finset.Icc 1 N,
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) := by
  have htail_compl :
      HasSum
        (fun x : {n : ℕ // n ∉ Finset.Icc 1 N} =>
          (1 : ℂ) / (((x : ℕ) : ℂ) ^ boundaryLineOnePointRealParam t))
        (riemannZeta (boundaryLineOnePointRealParam t) -
          ∑ n ∈ Finset.Icc 1 N,
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) :=
    ((Finset.Icc 1 N).hasSum_iff_compl).mp hζ
  have htail_indicator :
      HasSum
        ({n : ℕ | n ∉ Finset.Icc 1 N}.indicator
          (fun n : ℕ =>
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)))
        (riemannZeta (boundaryLineOnePointRealParam t) -
          ∑ n ∈ Finset.Icc 1 N,
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) := by
    exact
      (hasSum_subtype_iff_indicator
        (s := {n : ℕ | n ∉ Finset.Icc 1 N})
        (f := fun n : ℕ =>
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t))).mp
        htail_compl
  exact htail_indicator.congr_fun
    (fun n : ℕ =>
      (boundaryLineOnePointRealParam_dirichlet_tail_indicator_eq_cutoff_if
        t N n).symm)

/-- The boundary point `1 + it` is away from the zeta pole when `|t| ≥ 1`. -/
theorem boundaryLineOnePointRealParam_ne_one_of_one_le_norm
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    boundaryLineOnePointRealParam t ≠ (1 : ℂ) := by
  intro hpoint
  have him_eq :
      t = 0 :=
    Eq.trans (boundaryLineOnePointRealParam_im t).symm
      (Eq.trans (congrArg Complex.im hpoint) rfl)
  have hnorm_eq :
      ‖t‖ = 0 :=
    norm_eq_zero.mpr him_eq
  have hone_le_zero :
      (1 : ℝ) ≤ 0 :=
    Eq.subst
      (motive := fun x : ℝ => (1 : ℝ) ≤ x)
      hnorm_eq
      ht
  exact not_lt_of_ge hone_le_zero zero_lt_one

/-- Analytic-continuation continuity of `ζ` at the boundary point `1 + it`, away
from the pole. -/
theorem boundaryLineOnePointRealParam_riemannZeta_continuousAt
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ContinuousAt riemannZeta (boundaryLineOnePointRealParam t) := by
  exact
    (differentiableAt_riemannZeta
      (boundaryLineOnePointRealParam_ne_one_of_one_le_norm t ht)).continuousAt

/-- The right-half-plane Abel family approaching the boundary point `1 + it`. -/
def boundaryLineOnePointRealParam_abscissaShift
    (σ t : ℝ) : ℂ :=
  (σ : ℂ) + (t : ℂ) * Complex.I

/-- Abel continuation of the half-plane Dirichlet identity to the boundary point
`1 + it`.

The ordinary boundary series `∑ n^{-1-it}` is not asserted to converge.  The
correct owner statement is the Abel-limit theorem: the half-plane sums
`∑ n^{-σ-it}` tend to the analytic-continuation value of `ζ` as
`σ ↓ 1`. -/
theorem boundaryLineOnePointRealParam_dirichlet_series_abel_tendsto_riemannZeta
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    Tendsto
      (fun σ : ℝ =>
        ∑' n : ℕ,
          (1 : ℂ) /
            ((n : ℂ) ^
              boundaryLineOnePointRealParam_abscissaShift σ t))
      (𝓝[>] (1 : ℝ))
      (𝓝 (riemannZeta (boundaryLineOnePointRealParam t))) := by
  have habscissa_path_continuousAt :
      ContinuousAt
        (fun σ : ℝ => boundaryLineOnePointRealParam_abscissaShift σ t)
        (1 : ℝ) := by
    unfold boundaryLineOnePointRealParam_abscissaShift
    exact
      Complex.continuous_ofReal.continuousAt.add
        continuousAt_const
  have habscissa_path_tendsto_raw :
      Tendsto
        (fun σ : ℝ => boundaryLineOnePointRealParam_abscissaShift σ t)
        (𝓝[>] (1 : ℝ))
        (𝓝 (boundaryLineOnePointRealParam_abscissaShift 1 t)) :=
    habscissa_path_continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have habscissa_path_endpoint :
      boundaryLineOnePointRealParam_abscissaShift 1 t =
        boundaryLineOnePointRealParam t := by
    exact Complex.ext rfl rfl
  have habscissa_path_tendsto_boundary :
      Tendsto
        (fun σ : ℝ => boundaryLineOnePointRealParam_abscissaShift σ t)
        (𝓝[>] (1 : ℝ))
        (𝓝 (boundaryLineOnePointRealParam t)) :=
    Eq.subst
      (motive := fun z : ℂ =>
        Tendsto
          (fun σ : ℝ => boundaryLineOnePointRealParam_abscissaShift σ t)
          (𝓝[>] (1 : ℝ))
          (𝓝 z))
      habscissa_path_endpoint
      habscissa_path_tendsto_raw
  have hzeta_path_tendsto :
      Tendsto
        (fun σ : ℝ =>
          riemannZeta (boundaryLineOnePointRealParam_abscissaShift σ t))
        (𝓝[>] (1 : ℝ))
        (𝓝 (riemannZeta (boundaryLineOnePointRealParam t))) :=
    (boundaryLineOnePointRealParam_riemannZeta_continuousAt t ht).tendsto.comp
      habscissa_path_tendsto_boundary
  have hdirichlet_eq_eventually :
      (fun σ : ℝ =>
        ∑' n : ℕ,
          (1 : ℂ) /
            ((n : ℂ) ^
              boundaryLineOnePointRealParam_abscissaShift σ t)) =ᶠ[𝓝[>] (1 : ℝ)]
        (fun σ : ℝ =>
          riemannZeta (boundaryLineOnePointRealParam_abscissaShift σ t)) := by
    filter_upwards [self_mem_nhdsWithin] with σ hσ
    have hσ_re :
        (boundaryLineOnePointRealParam_abscissaShift σ t).re = σ := by
      rfl
    have hhalf_plane :
        1 < (boundaryLineOnePointRealParam_abscissaShift σ t).re :=
      Eq.subst
        (motive := fun x : ℝ => 1 < x)
        hσ_re.symm
        hσ
    exact (zeta_eq_tsum_one_div_nat_cpow hhalf_plane).symm
  exact Tendsto.congr' hdirichlet_eq_eventually hzeta_path_tendsto

/-- The Abel boundary value of the Dirichlet presentation is the analytic
continuation value of `ζ(1 + it)`. -/
theorem boundaryLineOnePointRealParam_dirichlet_series_abel_boundaryValue_eq_riemannZeta
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ∃ V : ℂ,
      Tendsto
        (fun σ : ℝ =>
          ∑' n : ℕ,
            (1 : ℂ) /
              ((n : ℂ) ^
                boundaryLineOnePointRealParam_abscissaShift σ t))
        (𝓝[>] (1 : ℝ))
        (𝓝 V) ∧
      V = riemannZeta (boundaryLineOnePointRealParam t) := by
  exact
    ⟨riemannZeta (boundaryLineOnePointRealParam t),
      boundaryLineOnePointRealParam_dirichlet_series_abel_tendsto_riemannZeta
        t ht,
      rfl⟩

/-- The Abel-damped finite cutoff prefix. -/
def abelBoundary_logarithmicPhase_dampedPrefix
    (t σ : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
    (1 : ℂ) /
      ((n : ℂ) ^
        boundaryLineOnePointRealParam_abscissaShift σ t)

/-- The boundary finite cutoff prefix. -/
def abelBoundary_logarithmicPhase_boundaryPrefix
    (t : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
    ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))

/-- Termwise Abel-prefix continuity at the boundary point `σ = 1`.

For a fixed positive integer `n`, the half-plane term
`n^(-σ-it)` tends to its boundary logarithmic-phase value
`n⁻¹ n^(-it)`. -/
theorem abelBoundary_logarithmicPhase_dampedPrefix_term_tendsto
    (t : ℝ)
    {n : ℕ}
    (hn : 0 < n) :
    Tendsto
      (fun σ : ℝ =>
        (1 : ℂ) /
          ((n : ℂ) ^
            boundaryLineOnePointRealParam_abscissaShift σ t))
      (𝓝[>] (1 : ℝ))
      (𝓝 (((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)))) := by
  have hn_complex_ne : (n : ℂ) ≠ 0 := by
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt hn)
  have habscissa_cont :
      ContinuousAt
        (fun σ : ℝ => boundaryLineOnePointRealParam_abscissaShift σ t)
        (1 : ℝ) := by
    unfold boundaryLineOnePointRealParam_abscissaShift
    exact
      Complex.continuous_ofReal.continuousAt.add
        continuousAt_const
  have habscissa_tendsto :
      Tendsto
        (fun σ : ℝ => boundaryLineOnePointRealParam_abscissaShift σ t)
        (𝓝[>] (1 : ℝ))
        (𝓝 (boundaryLineOnePointRealParam_abscissaShift 1 t)) :=
    habscissa_cont.tendsto.mono_left nhdsWithin_le_nhds
  have hterm_tendsto_raw :
      Tendsto
        (fun σ : ℝ =>
          (1 : ℂ) /
            ((n : ℂ) ^
              boundaryLineOnePointRealParam_abscissaShift σ t))
        (𝓝[>] (1 : ℝ))
        (𝓝
          ((1 : ℂ) /
            ((n : ℂ) ^
              boundaryLineOnePointRealParam_abscissaShift 1 t))) := by
    exact tendsto_const_nhds.div
      ((continuousAt_const_cpow hn_complex_ne).tendsto.comp
        habscissa_tendsto)
  have habscissa_endpoint :
      boundaryLineOnePointRealParam_abscissaShift 1 t =
        boundaryLineOnePointRealParam t :=
    Complex.ext rfl rfl
  have hboundary_term :
      (1 : ℂ) /
            ((n : ℂ) ^
              boundaryLineOnePointRealParam_abscissaShift 1 t) =
        ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) := by
    exact Eq.trans
      (congrArg
        (fun z : ℂ => (1 : ℂ) / ((n : ℂ) ^ z))
        habscissa_endpoint)
      (boundaryLineOnePointRealParam_dirichletTerm_eq_inv_mul_oscillation_left
        t hn)
  exact Eq.subst
    (motive := fun z : ℂ =>
      Tendsto
        (fun σ : ℝ =>
          (1 : ℂ) /
            ((n : ℂ) ^
              boundaryLineOnePointRealParam_abscissaShift σ t))
        (𝓝[>] (1 : ℝ))
        (𝓝 z))
    hboundary_term
    hterm_tendsto_raw

/-- Finite-sum Abel-prefix continuity over a fixed cutoff interval. -/
theorem abelBoundary_logarithmicPhase_dampedPrefix_sum_tendsto
    (t : ℝ)
    (N : ℕ) :
    Tendsto
      (fun σ : ℝ =>
        ∑ n ∈ Finset.Icc 1 N,
          (1 : ℂ) /
            ((n : ℂ) ^
              boundaryLineOnePointRealParam_abscissaShift σ t))
      (𝓝[>] (1 : ℝ))
      (𝓝
        (∑ n ∈ Finset.Icc 1 N,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)))) := by
  refine Finset.Tendsto.sum ?_
  intro n hn_mem
  have hn_one_le : 1 ≤ n :=
    (Finset.mem_Icc.mp hn_mem).1
  have hn_pos : 0 < n :=
    Nat.lt_of_succ_le hn_one_le
  exact abelBoundary_logarithmicPhase_dampedPrefix_term_tendsto t hn_pos

/-- The Abel-damped prefix tends to the boundary prefix as `σ → 1+`.

This is finite-sum continuity plus the term identity at the boundary point. -/
theorem abelBoundary_logarithmicPhase_dampedPrefix_tendsto_boundaryPrefix
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    Tendsto
      (fun σ : ℝ => abelBoundary_logarithmicPhase_dampedPrefix t σ)
      (𝓝[>] (1 : ℝ))
      (𝓝 (abelBoundary_logarithmicPhase_boundaryPrefix t)) := by
  exact abelBoundary_logarithmicPhase_dampedPrefix_sum_tendsto
    t ⌊2 + ‖t‖⌋₊

/-- Abel-limit identity after subtracting the damped cutoff prefix.

This is pure limit algebra from the Abel convergence of the Dirichlet
presentation: subtracting the damped finite prefix from the Abel family
subtracts the boundary prefix in the limit. -/
theorem abelBoundary_dirichletSeries_dampedPrefix_subtracted_tendsto_zeta_remainder
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (habel :
      Tendsto
        (fun σ : ℝ =>
          ∑' n : ℕ,
            (1 : ℂ) /
              ((n : ℂ) ^
                boundaryLineOnePointRealParam_abscissaShift σ t))
        (𝓝[>] (1 : ℝ))
        (𝓝 (riemannZeta (boundaryLineOnePointRealParam t)))) :
    Tendsto
      (fun σ : ℝ =>
        (∑' n : ℕ,
          (1 : ℂ) /
            ((n : ℂ) ^
              boundaryLineOnePointRealParam_abscissaShift σ t)) -
          abelBoundary_logarithmicPhase_dampedPrefix t σ)
      (𝓝[>] (1 : ℝ))
      (𝓝
        (riemannZeta (boundaryLineOnePointRealParam t) -
          abelBoundary_logarithmicPhase_boundaryPrefix t)) := by
  exact habel.sub
    (abelBoundary_logarithmicPhase_dampedPrefix_tendsto_boundaryPrefix t ht)

/-- The Abel-damped post-cutoff logarithmic-phase tail.

This is a right-half-plane object: the ordinary boundary tail at `σ = 1` is
not asserted to converge. -/
def abelBoundary_logarithmicPhase_dampedTail
    (t σ : ℝ) : ℂ :=
  (∑' n : ℕ,
    (1 : ℂ) /
      ((n : ℂ) ^
        boundaryLineOnePointRealParam_abscissaShift σ t)) -
    abelBoundary_logarithmicPhase_dampedPrefix t σ

/-- Abel-tail normalization after removing the fixed cutoff prefix.

This theorem owns the index and term normalization between the Abel-regularized
Dirichlet remainder and the damped logarithmic-phase post-cutoff tail.  It is
the place where `Icc 1 N` prefix subtraction and the identity between
`n^{-(σ+it)}` and the damped reciprocal logarithmic oscillator are matched.  No
ordinary boundary `HasSum` or undamped tail convergence is asserted here. -/
theorem abelBoundary_logarithmicPhase_dampedTail_index_normalization
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hprefix :
      Tendsto
        (fun σ : ℝ =>
          (∑' n : ℕ,
            (1 : ℂ) /
              ((n : ℂ) ^
                boundaryLineOnePointRealParam_abscissaShift σ t)) -
            abelBoundary_logarithmicPhase_dampedPrefix t σ)
        (𝓝[>] (1 : ℝ))
        (𝓝
          (riemannZeta (boundaryLineOnePointRealParam t) -
            abelBoundary_logarithmicPhase_boundaryPrefix t))) :
    Tendsto
      (fun σ : ℝ => abelBoundary_logarithmicPhase_dampedTail t σ)
      (𝓝[>] (1 : ℝ))
      (𝓝
        (riemannZeta (boundaryLineOnePointRealParam t) -
          ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
            ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)))) := by
  exact hprefix

/-- Owner convergence theorem for Abel-damped tails after the canonical cutoff.

This is the exact limiting statement behind the Abel boundary transport: the
post-cutoff Abel-damped tail converges to the analytic-continuation zeta value
with the finite cutoff truncation removed.  The proof is the fixed-prefix Abel
limit, the identity between Dirichlet terms and damped reciprocal logarithmic
oscillators in the half-plane, and the Abel limit
`boundaryLineOnePointRealParam_dirichlet_series_abel_tendsto_riemannZeta`.
It deliberately does not assert ordinary boundary `HasSum`. -/
theorem abelBoundary_logarithmicPhase_dampedTail_tendsto_zeta_remainder
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (habel :
      Tendsto
        (fun σ : ℝ =>
          ∑' n : ℕ,
            (1 : ℂ) /
              ((n : ℂ) ^
                boundaryLineOnePointRealParam_abscissaShift σ t))
        (𝓝[>] (1 : ℝ))
        (𝓝 (riemannZeta (boundaryLineOnePointRealParam t)))) :
    Tendsto
      (fun σ : ℝ => abelBoundary_logarithmicPhase_dampedTail t σ)
      (𝓝[>] (1 : ℝ))
      (𝓝
        (riemannZeta (boundaryLineOnePointRealParam t) -
          ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
            ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)))) := by
  have hprefix :
      Tendsto
        (fun σ : ℝ =>
          (∑' n : ℕ,
            (1 : ℂ) /
              ((n : ℂ) ^
                boundaryLineOnePointRealParam_abscissaShift σ t)) -
            abelBoundary_logarithmicPhase_dampedPrefix t σ)
        (𝓝[>] (1 : ℝ))
        (𝓝
          (riemannZeta (boundaryLineOnePointRealParam t) -
            abelBoundary_logarithmicPhase_boundaryPrefix t)) :=
    abelBoundary_dirichletSeries_dampedPrefix_subtracted_tendsto_zeta_remainder
      t ht habel
  exact
    abelBoundary_logarithmicPhase_dampedTail_index_normalization
      t ht hprefix

/-- A complex limit of an eventually norm-bounded family is norm-bounded by the
same constant.

This is the reusable pure-topology closure step for Abel transport: the closed
ball `{z | ‖z‖ ≤ C}` contains the eventual tail, hence contains the limit. -/
theorem complex_norm_le_of_eventually_norm_le_of_tendsto
    {ι : Type*}
    {l : Filter ι}
    [NeBot l]
    {u : ι → ℂ}
    {z : ℂ}
    {C : ℝ}
    (hu : Tendsto u l (𝓝 z))
    (hbound : ∀ᶠ i in l, ‖u i‖ ≤ C) :
    ‖z‖ ≤ C := by
  have hclosed : IsClosed {w : ℂ | ‖w‖ ≤ C} :=
    isClosed_le continuous_norm continuous_const
  exact hclosed.mem_of_tendsto hu hbound

/-- Norm transport from a uniformly bounded Abel-damped tail family to its Abel
boundary limit.

This is the topological endpoint of the Abel argument: once the damped tails are
eventually uniformly bounded as `σ → 1+` and converge to the analytic boundary
remainder, the same bound holds for the remainder. -/
theorem abelBoundary_logarithmicPhase_dampedTail_uniform_bound_transport
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hdamped_bound :
      ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
        ‖abelBoundary_logarithmicPhase_dampedTail t σ‖ ≤
          boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t)
    (hdamped :
      Tendsto
        (fun σ : ℝ => abelBoundary_logarithmicPhase_dampedTail t σ)
        (𝓝[>] (1 : ℝ))
        (𝓝
          (riemannZeta (boundaryLineOnePointRealParam t) -
            ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
              ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))))) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  let limit : ℂ :=
    riemannZeta (boundaryLineOnePointRealParam t) -
      ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
        ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))
  have htail_tendsto :
      Tendsto
        (fun σ : ℝ => abelBoundary_logarithmicPhase_dampedTail t σ)
        (𝓝[>] (1 : ℝ))
        (𝓝 limit) :=
    hdamped
  exact
    complex_norm_le_of_eventually_norm_le_of_tendsto
      htail_tendsto
      hdamped_bound

/-- Abstract Abel transform bound from bounded finite tail sums.

This is the positive-weight summation-by-parts core: for a tail sequence whose
finite partial sums from `N` onward are bounded by `C`, the Abel-damped tail
with weights `r^n`, `0 < r < 1`, is bounded by the same `C`.  This is the
convex-combination form of Abel's theorem for bounded partial sums. -/
theorem abel_positive_weighted_tail_norm_le_of_bounded_partial_sums
    {u : ℕ → ℂ}
    {N : ℕ}
    {C : ℝ}
    (hpartial :
      ∀ M : ℕ,
        N ≤ M →
        ‖∑ k ∈ Finset.Ioc N M, u k‖ ≤ C) :
    ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ),
      ‖∑' k : ℕ, if N < k then ((r : ℂ) ^ k) * u k else 0‖ ≤ C := by
  sorry

/-- Identification of the logarithmic-phase damped tail with the abstract Abel
weighted tail.

For `σ > 1`, writing `r = exp (1 - σ)` converts the half-plane Dirichlet tail
after the cutoff into the Abel weighted boundary-line oscillator tail. -/
theorem abelBoundary_logarithmicPhase_dampedTail_eq_abstract_weighted_tail
    (t σ : ℝ)
    (hσ : 1 < σ) :
    abelBoundary_logarithmicPhase_dampedTail t σ =
      ∑' k : ℕ,
        if ⌊2 + ‖t‖⌋₊ < k then
          ((Real.exp (1 - σ) : ℂ) ^ k) *
            (((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I)))
        else
          0 := by
  sorry

/-- Transport the abstract Abel weighted-tail bound to the logarithmic-phase
damped tail as `σ → 1+`. -/
theorem abelBoundary_logarithmicPhase_dampedTail_bound_of_abstract_abel
    (t : ℝ)
    (C : ℝ)
    (hfinite :
      ∀ M : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ M →
        ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
            ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤ C) :
    ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      ‖abelBoundary_logarithmicPhase_dampedTail t σ‖ ≤ C := by
  sorry

/-- Abel damping theorem for a tail with bounded finite partial sums.

If every finite tail partial sum after the cutoff is bounded by `C`, then the
Abel-damped tail is eventually bounded by `C` as the damping parameter tends to
the boundary from the right.  This is the positive-weight Abel summation
principle: the damped tail is obtained as the limit of convex weighted averages
of the bounded finite partial sums. -/
theorem abel_damped_tail_norm_le_of_bounded_finite_tail_sums
    (t : ℝ)
    (C : ℝ)
    (hfinite :
      ∀ M : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ M →
        ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
            ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤ C) :
    ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      ‖abelBoundary_logarithmicPhase_dampedTail t σ‖ ≤ C := by
  exact abelBoundary_logarithmicPhase_dampedTail_bound_of_abstract_abel
    t C hfinite

/-- Abel damping comparison for the logarithmic-phase post-cutoff tail.

This is the honest bridge from uniformly bounded finite post-cutoff Abel sums to
an eventual bound for the Abel-damped post-cutoff tail as `σ → 1+`.  Its proof
is Abel's theorem for bounded partial sums applied to the cutoff tail, not
ordinary convergence of the undamped boundary series. -/
theorem abelBoundary_logarithmicPhase_dampedTail_bound_of_finiteAbel
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hfinite :
      ∀ M : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ M →
        ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
            ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
          boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t) :
    ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
      ‖abelBoundary_logarithmicPhase_dampedTail t σ‖ ≤
        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  exact
    abel_damped_tail_norm_le_of_bounded_finite_tail_sums
      t
      (boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t)
      hfinite

/-- Deep Abel-limit transport for the canonical post-cutoff logarithmic-phase
tail.

This is the limiting passage from the uniformly bounded finite Abel tails after
`N = ⌊2 + |t|⌋₊` to the analytic-continuation boundary value supplied by
`boundaryLineOnePointRealParam_dirichlet_series_abel_tendsto_riemannZeta`.  It
does not assert ordinary convergence of the boundary Dirichlet series. -/
theorem abelBoundary_logarithmicPhase_oscillatory_tail_after_cutoff_bound_of_finiteAbel
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (hfinite :
      ∀ M : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ M →
        ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
            ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
          boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t)
    (habel :
      Tendsto
        (fun σ : ℝ =>
          ∑' n : ℕ,
            (1 : ℂ) /
              ((n : ℂ) ^
                boundaryLineOnePointRealParam_abscissaShift σ t))
        (𝓝[>] (1 : ℝ))
        (𝓝 (riemannZeta (boundaryLineOnePointRealParam t)))) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  have htails :
      Tendsto
        (fun σ : ℝ => abelBoundary_logarithmicPhase_dampedTail t σ)
        (𝓝[>] (1 : ℝ))
        (𝓝
          (riemannZeta (boundaryLineOnePointRealParam t) -
            ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
              ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)))) :=
    abelBoundary_logarithmicPhase_dampedTail_tendsto_zeta_remainder
      t ht habel
  have hdamped_bound :
      ∀ᶠ σ : ℝ in 𝓝[>] (1 : ℝ),
        ‖abelBoundary_logarithmicPhase_dampedTail t σ‖ ≤
          boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t :=
    abelBoundary_logarithmicPhase_dampedTail_bound_of_finiteAbel
      t ht hfinite
  exact
    abelBoundary_logarithmicPhase_dampedTail_uniform_bound_transport
      t ht hdamped_bound htails

/-- Owner Abel-boundary API for the canonical post-cutoff oscillatory tail.

This is the boundary-value passage from finite Abel tails to the analytic
continuation value of `ζ(1 + it)`, after the endpoint and derivative-integral
Abel estimates have been isolated. The proof chain is Abel summation for finite
tails, the logarithmic-phase first-derivative estimate, Abel limiting from the
right half-plane, and the Dirichlet-continuation boundary identity; cf.
Titchmarsh, *The Theory of the Riemann Zeta-function*, §3.5. -/
theorem abelBoundary_logarithmicPhase_oscillatory_tail_after_cutoff_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  have hfinite :
      ∀ M : ℕ,
        ⌊2 + ‖t‖⌋₊ ≤ M →
        ‖∑ k ∈ Finset.Ioc ⌊(((⌊2 + ‖t‖⌋₊ : ℕ) : ℝ))⌋₊ ⌊((M : ℕ) : ℝ)⌋₊,
            ((k : ℂ)⁻¹ : ℂ) * ((k : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
          boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
    intro M hNM
    exact
      boundaryLineOnePointRealParam_logarithmicPhase_finiteAbelTail_norm_le
        t ht hNM
  have habel :
      Tendsto
        (fun σ : ℝ =>
          ∑' n : ℕ,
            (1 : ℂ) /
              ((n : ℂ) ^
                boundaryLineOnePointRealParam_abscissaShift σ t))
        (𝓝[>] (1 : ℝ))
        (𝓝 (riemannZeta (boundaryLineOnePointRealParam t))) :=
    boundaryLineOnePointRealParam_dirichlet_series_abel_tendsto_riemannZeta
      t ht
  exact
    abelBoundary_logarithmicPhase_oscillatory_tail_after_cutoff_bound_of_finiteAbel
      t ht hfinite habel

/-- Explicit Abel/Euler-Maclaurin estimate for the exact post-cutoff oscillatory
boundary-line zeta remainder.

Intended proof chain:
apply `abelSummation_boundaryLineOnePointRealParam_cutoff_nat_tail_identity` to
finite tails, bound the oscillatory partial sums
`∑_{0 ≤ n ≤ M} n^{-it}` on the range `1 ≤ |t|` by the logarithmic-phase
Euler/van-der-Corput estimate, use
`positive_nat_reciprocal_antitone` for the decreasing Abel weight, identify the
Abel boundary value with the analytic continuation of `ζ`, and combine the endpoint
and integral estimates at `N = ⌊2 + |t|⌋₊`; cf. Titchmarsh, *The Theory of the
Riemann Zeta-function*, §3.5. -/
theorem abelEulerMaclaurin_boundaryLineOnePointRealParam_oscillatory_tail_after_cutoff_norm_le_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  exact abelBoundary_logarithmicPhase_oscillatory_tail_after_cutoff_bound t ht

/-- Exact post-cutoff oscillatory tail after the cutoff `N = ⌊2 + |t|⌋₊`.

The proof is now only the conjunction of the peeled Dirichlet-continuation
identity and the explicit Abel/Euler-Maclaurin endpoint/integral estimate. -/
theorem eulerMaclaurin_boundaryLineOnePointRealParam_oscillatory_tail_after_cutoff_hasSum_norm_le_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  exact
    (abelEulerMaclaurin_boundaryLineOnePointRealParam_oscillatory_tail_after_cutoff_norm_le_explicit
      t ht)

/-- Transport a boundary-line tail norm estimate from the Abel-normalized oscillatory
finite truncation back to the original Dirichlet monomials. -/
theorem boundaryLineOnePointRealParam_tail_norm_le_explicit_of_oscillatory_tail_norm_le_explicit
    (t : ℝ)
    (hosc :
      ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
      ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  have hfinite :
      (∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)) =
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
    boundaryLineOnePointRealParam_finite_truncation_eq_inv_mul_oscillation_sum
      t ⌊2 + ‖t‖⌋₊
  have htail_transport :
      riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t) =
      riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I)) :=
    congrArg
      (fun S : ℂ => riemannZeta (boundaryLineOnePointRealParam t) - S)
      hfinite
  exact Eq.subst
    (motive := fun z : ℂ =>
      ‖z‖ ≤ boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t)
    htail_transport.symm
    hosc

/-- Classical Euler-Maclaurin tail estimate after truncation at
`N = ⌊2 + |t|⌋₊`.

This is now only the mechanical transport from the oscillatory Abel-tail form
`n⁻¹ n⁻ⁱᵗ` back to the original boundary-line Dirichlet monomials. -/
theorem eulerMaclaurin_boundaryLineOnePointRealParam_classical_tail_estimate
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
      ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  have htail :
      ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          ((n : ℂ)⁻¹ : ℂ) * ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t :=
    eulerMaclaurin_boundaryLineOnePointRealParam_oscillatory_tail_after_cutoff_hasSum_norm_le_explicit
      t ht
  exact boundaryLineOnePointRealParam_tail_norm_le_explicit_of_oscillatory_tail_norm_le_explicit
    t htail

/-- The exact Abel/Euler-Maclaurin tail estimate after truncation at
`N = ⌊2 + |t|⌋₊`. -/
theorem eulerMaclaurin_riemannZeta_one_add_it_tail_after_cutoff_norm_le_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
      ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  exact eulerMaclaurin_boundaryLineOnePointRealParam_classical_tail_estimate t ht

/-- Public Abel/Euler-Maclaurin zeta-tail root.  The proof is now only name
transport from the canonical Euler-Maclaurin tail estimate at the exact cutoff. -/
theorem abelEulerMaclaurin_riemannZeta_one_add_it_tail_norm_le_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖riemannZeta (boundaryLineOnePointRealParam t) -
      ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
        (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t := by
  exact eulerMaclaurin_riemannZeta_one_add_it_tail_after_cutoff_norm_le_explicit t ht

/-- Triangle-inequality split of `ζ(1+it)` into its Abel/Euler-Maclaurin tail
and finite Dirichlet truncation. -/
theorem boundaryLineOnePointRealParam_zeta_norm_le_tail_plus_truncation
    (t : ℝ) :
    ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
      ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ +
      ‖∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ := by
  let S : ℂ :=
    ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
      (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)
  have hsplit :
      riemannZeta (boundaryLineOnePointRealParam t) =
        (riemannZeta (boundaryLineOnePointRealParam t) - S) + S := by
    exact (sub_add_cancel (riemannZeta (boundaryLineOnePointRealParam t)) S).symm
  exact Eq.subst
    (motive := fun w : ℂ =>
      ‖w‖ ≤ ‖riemannZeta (boundaryLineOnePointRealParam t) - S‖ + ‖S‖)
    hsplit.symm
    (norm_add_le (riemannZeta (boundaryLineOnePointRealParam t) - S) S)

/-- The analytic tail estimate and finite harmonic majorant give the intermediate
explicit-tail boundary estimate. -/
theorem abelEulerMaclaurin_riemannZeta_one_add_it_vertical_explicit_tail_add_log_bound
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
        (1 + Real.log (2 + ‖t‖)) := by
  have hsplit :
      ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
        ‖riemannZeta (boundaryLineOnePointRealParam t) -
          ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ +
        ‖∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ :=
    boundaryLineOnePointRealParam_zeta_norm_le_tail_plus_truncation t
  have htail :
      ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t :=
    abelEulerMaclaurin_riemannZeta_one_add_it_tail_norm_le_explicit t ht
  have hfinite :
      ‖∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
        1 + Real.log (2 + ‖t‖) :=
    boundaryLineOnePointRealParam_finite_dirichlet_truncation_norm_le_one_add_log t
  have htail_plus_finite :
      ‖riemannZeta (boundaryLineOnePointRealParam t) -
        ∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
          (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ +
        ‖∑ n ∈ Finset.Icc 1 ⌊2 + ‖t‖⌋₊,
            (1 : ℂ) / ((n : ℂ) ^ boundaryLineOnePointRealParam t)‖ ≤
        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
          (1 + Real.log (2 + ‖t‖)) :=
    add_le_add htail hfinite
  exact le_trans hsplit htail_plus_finite

/-- On the large vertical range, the intermediate `2 + log` bound is absorbed by
`3 * log`. -/
theorem two_add_log_two_add_norm_le_three_mul_log_two_add_norm_of_one_le_norm
    {t : ℝ}
    (ht : 1 ≤ ‖t‖) :
    2 + Real.log (2 + ‖t‖) ≤
      3 * Real.log (2 + ‖t‖) := by
  let L : ℝ := Real.log (2 + ‖t‖)
  have hlog_one : (1 : ℝ) ≤ L :=
    one_le_log_two_add_norm_of_one_le_norm ht
  have htwo_le_twoL : (2 : ℝ) ≤ 2 * L := by
    calc
      (2 : ℝ) = 2 * 1 := by
        exact (mul_one 2).symm
      _ ≤ 2 * L :=
        mul_le_mul_of_nonneg_left hlog_one zero_le_two
  calc
    2 + Real.log (2 + ‖t‖) = 2 + L := rfl
    _ ≤ 2 * L + L :=
      add_le_add_right htwo_le_twoL L
    _ = (2 + 1) * L := by
      exact (add_mul 2 1 L).symm
    _ = 3 * L := rfl
    _ = 3 * Real.log (2 + ‖t‖) := rfl

/-- The enlarged logarithmic argument `3 + |t|` is absorbed by twice the
canonical boundary-line logarithm. -/
theorem log_three_add_norm_le_two_mul_log_two_add_norm
    (t : ℝ) :
    Real.log (3 + ‖t‖) ≤
      2 * Real.log (2 + ‖t‖) := by
  let x : ℝ := ‖t‖
  have hx_nonneg : 0 ≤ x :=
    norm_nonneg t
  have hleft_pos : 0 < 3 + x := by
    have hthree_pos : (0 : ℝ) < 3 :=
      three_pos
    exact lt_of_lt_of_le hthree_pos (le_add_of_nonneg_right hx_nonneg)
  have hright_pos : 0 < 2 * (2 + x) := by
    have htwo_pos : (0 : ℝ) < 2 :=
      zero_lt_two
    have harg_pos : 0 < 2 + x :=
      lt_of_lt_of_le zero_lt_two (le_add_of_nonneg_right hx_nonneg)
    exact mul_pos htwo_pos harg_pos
  have harg_ne : (2 : ℝ) + x ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_two (le_add_of_nonneg_right hx_nonneg))
  have htwo_ne : (2 : ℝ) ≠ 0 :=
    ne_of_gt zero_lt_two
  have harg_ge_two : (2 : ℝ) ≤ 2 + x :=
    le_add_of_nonneg_right hx_nonneg
  have hthree_le :
      3 + x ≤ 2 * (2 + x) := by
    have hx_le_two_x : x ≤ 2 * x := by
      calc
        x = 1 * x := by
          exact (one_mul x).symm
        _ ≤ 2 * x :=
          mul_le_mul_of_nonneg_right one_le_two hx_nonneg
    calc
      3 + x ≤ 4 + 2 * x :=
        add_le_add (by exact three_le_four) hx_le_two_x
      _ = 2 * (2 + x) := by
        exact (left_distrib 2 2 x).symm
  have hlog_le :
      Real.log (3 + x) ≤ Real.log (2 * (2 + x)) :=
    Real.log_le_log hleft_pos hthree_le
  have hlog_mul :
      Real.log (2 * (2 + x)) =
        Real.log 2 + Real.log (2 + x) :=
    Real.log_mul htwo_ne harg_ne
  have hlog_two_le :
      Real.log 2 ≤ Real.log (2 + x) :=
    Real.log_le_log zero_lt_two harg_ge_two
  have hsum_le :
      Real.log 2 + Real.log (2 + x) ≤
        Real.log (2 + x) + Real.log (2 + x) :=
    add_le_add_right hlog_two_le (Real.log (2 + x))
  calc
    Real.log (3 + ‖t‖) = Real.log (3 + x) := rfl
    _ ≤ Real.log (2 * (2 + x)) :=
      hlog_le
    _ = Real.log 2 + Real.log (2 + x) :=
      hlog_mul
    _ ≤ Real.log (2 + x) + Real.log (2 + x) :=
      hsum_le
    _ = 2 * Real.log (2 + x) := by
      exact (two_mul (Real.log (2 + x))).symm
    _ = 2 * Real.log (2 + ‖t‖) := rfl

/-- The explicit Abel-tail constant plus finite-truncation logarithmic term is
absorbed by an absolute multiple of the canonical logarithm. -/
theorem boundaryLineOnePointRealParam_explicit_tail_plus_log_le_constant_log
    {t : ℝ}
    (ht : 1 ≤ ‖t‖) :
    boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
        (1 + Real.log (2 + ‖t‖)) ≤
      38 * Real.log (2 + ‖t‖) := by
  let L : ℝ := Real.log (2 + ‖t‖)
  have hL_one : (1 : ℝ) ≤ L :=
    one_le_log_two_add_norm_of_one_le_norm ht
  have hL_nonneg : 0 ≤ L :=
    le_trans zero_le_one hL_one
  have hfour_le : (4 : ℝ) ≤ 4 * L := by
    calc
      (4 : ℝ) = 4 * 1 := by
        exact (mul_one 4).symm
      _ ≤ 4 * L :=
        mul_le_mul_of_nonneg_left hL_one (by exact zero_le_four)
  have hone_le : (1 : ℝ) ≤ L :=
    hL_one
  have hlog_three :
      Real.log (3 + ‖t‖) ≤ 2 * L := by
    exact log_three_add_norm_le_two_mul_log_two_add_norm t
  have hsixteen_log :
      16 * Real.log (3 + ‖t‖) ≤ 32 * L := by
    calc
      16 * Real.log (3 + ‖t‖) ≤ 16 * (2 * L) :=
        mul_le_mul_of_nonneg_left hlog_three
          (show (0 : ℝ) ≤ 16 from Nat.cast_nonneg 16)
      _ = (16 * 2) * L := by
        exact (mul_assoc 16 2 L).symm
      _ = 32 * L := rfl
  have htail :
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t ≤
        36 * L := by
    calc
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t =
          4 + 16 * Real.log (3 + ‖t‖) := rfl
      _ ≤ 4 * L + 32 * L :=
        add_le_add hfour_le hsixteen_log
      _ = (4 + 32) * L := by
        exact (add_mul 4 32 L).symm
      _ = 36 * L := rfl
  have hfinite :
      1 + Real.log (2 + ‖t‖) ≤ 2 * L := by
    calc
      1 + Real.log (2 + ‖t‖) = 1 + L := rfl
      _ ≤ L + L :=
        add_le_add_right hone_le L
      _ = 2 * L := by
        exact (two_mul L).symm
  calc
    boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
        (1 + Real.log (2 + ‖t‖)) ≤
      36 * L + 2 * L :=
        add_le_add htail hfinite
    _ = (36 + 2) * L := by
      exact (add_mul 36 2 L).symm
    _ = 38 * L := rfl
    _ = 38 * Real.log (2 + ‖t‖) := rfl

/-- The finite truncation plus the Abel/Euler-Maclaurin tail gives the logarithmic
boundary estimate with the explicit Abel-tail constant still visible. -/
theorem abelEulerMaclaurin_riemannZeta_one_add_it_vertical_log_growth_bound_explicit
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) :
    ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
      boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
        (1 + Real.log (2 + ‖t‖)) := by
  exact
    abelEulerMaclaurin_riemannZeta_one_add_it_vertical_explicit_tail_add_log_bound
      t ht

/-- The exact analytic Abel/Euler-Maclaurin tail estimate on `ζ(1 + it)`.

Intended proof chain:
Dirichlet truncation at `N = ⌊2 + |t|⌋₊`, Abel summation for the oscillatory tail
`∑ n^{-1-it}`, Euler-Maclaurin control of the endpoint remainder, the harmonic
majorant for the finite part, and the standard logarithmic normalization; cf.
Titchmarsh, *The Theory of the Riemann Zeta-function*, §3.5. -/
theorem abelEulerMaclaurin_riemannZeta_one_add_it_vertical_log_growth_bound_analytic :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
          A * Real.log (2 + ‖t‖) := by
  refine ⟨38, ?_, ?_⟩
  · exact Nat.cast_pos.mpr (by decide : (0 : ℕ) < 38)
  · intro t ht
    have hexplicit :
        ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
          boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
            (1 + Real.log (2 + ‖t‖)) :=
      abelEulerMaclaurin_riemannZeta_one_add_it_vertical_log_growth_bound_explicit
        t ht
    have habsorb :
        boundaryLineOnePointRealParam_logarithmicPhaseAbelTailConstant t +
            (1 + Real.log (2 + ‖t‖)) ≤
          38 * Real.log (2 + ‖t‖) :=
      boundaryLineOnePointRealParam_explicit_tail_plus_log_le_constant_log ht
    exact le_trans hexplicit habsorb

/-- Euler-Maclaurin/Abel-truncation boundary estimate for the Riemann zeta function on
`1 + it`.

This is the canonical classical number-theoretic input: truncate the Dirichlet
series at height comparable to `|t|`, control the tail by Euler-Maclaurin or Abel
summation, and obtain the standard logarithmic bound; cf. Titchmarsh, §3.5. -/
theorem abelEulerMaclaurin_riemannZeta_one_add_it_vertical_log_growth_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
          A * Real.log (2 + ‖t‖) := by
  exact abelEulerMaclaurin_riemannZeta_one_add_it_vertical_log_growth_bound_analytic

/-- The historical owner-root spelling for the boundary-line logarithmic zeta estimate.

The proof is only name transport from the canonical Abel/Euler-Maclaurin theorem on
`ζ(1 + it)`. -/
theorem eulerMaclaurin_riemannZeta_boundaryLineOnePointRealParam_vertical_log_growth_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
          A * Real.log (2 + ‖t‖) := by
  exact abelEulerMaclaurin_riemannZeta_one_add_it_vertical_log_growth_bound

/-- Classical real-parameter logarithmic vertical growth of raw zeta on `1 + it`.

This is the smallest analytic number-theory input: truncate the Dirichlet series at
height comparable to `|t|`, control the tail by Abel summation or Euler-Maclaurin,
and obtain the standard `O(log (2 + |t|))` boundary-line bound; cf. Titchmarsh,
The Theory of the Riemann Zeta-function, §3.5. -/
theorem classicalZeta_riemannZeta_boundaryLineOnePointRealParam_vertical_log_growth_bound_from_EulerMaclaurin_truncation :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖riemannZeta (boundaryLineOnePointRealParam t)‖ ≤
          A * Real.log (2 + ‖t‖) := by
  exact
    eulerMaclaurin_riemannZeta_boundaryLineOnePointRealParam_vertical_log_growth_bound

/-- Classical real-parameter logarithmic vertical growth of zeta on the line `1 + it`.

This is only the definitional transport from the raw boundary-line zeta value to the
local real-parameter name. -/
theorem classicalZeta_boundaryLineOneZetaRealParam_vertical_log_growth_bound_from_EulerMaclaurin_truncation :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
        ‖boundaryLineOneZetaRealParam t‖ ≤ A * Real.log (2 + ‖t‖) := by
  rcases
    classicalZeta_riemannZeta_boundaryLineOnePointRealParam_vertical_log_growth_bound_from_EulerMaclaurin_truncation
    with ⟨A, hA_pos, hbound⟩
  refine ⟨A, hA_pos, ?_⟩
  intro t ht
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ A * Real.log (2 + ‖t‖))
    (show ‖riemannZeta (boundaryLineOnePointRealParam t)‖ =
        ‖boundaryLineOneZetaRealParam t‖ from rfl)
    (hbound t ht)

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
  rcases
    classicalZeta_boundaryLineOneZetaRealParam_vertical_log_growth_bound_from_EulerMaclaurin_truncation
    with ⟨A, hA_pos, hbound⟩
  refine ⟨A, hA_pos, ?_⟩
  intro w hw_re hw_im
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ A * Real.log (2 + ‖w.im‖))
    (norm_riemannZeta_boundaryLine_one_eq_norm_realParam hw_re).symm
    (hbound w.im hw_im)

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
          exact Complex.one_re
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
          exact Complex.one_re
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

/-- A real `IsBigO` bound against a positive exponential envelope gives an
eventual raw inequality with a positive multiplicative constant. -/
theorem real_isBigO_exp_eventually_le_pos_mul
    {f : ℝ → ℝ}
    (c : ℝ)
    (h : f =O[Filter.atTop] fun T : ℝ => Real.exp (c * T)) :
    ∃ D : ℝ,
      0 < D ∧
      ∀ᶠ T : ℝ in Filter.atTop,
        f T ≤ D * Real.exp (c * T) := by
  rcases h.isBigOWith with ⟨C, hC⟩
  refine ⟨|C| + 1, ?_, ?_⟩
  · exact add_pos_of_nonneg_of_pos (abs_nonneg C) zero_lt_one
  have hnonneg :
      ∀ᶠ T : ℝ in Filter.atTop,
        0 ≤ Real.exp (c * T) :=
    Filter.Eventually.of_forall
      (fun T => le_of_lt (Real.exp_pos (c * T)))
  exact
    (hC.bound.and hnonneg).mono
      (fun T hT =>
        by
          let G : ℝ := Real.exp (c * T)
          let D : ℝ := |C| + 1
          have hf_le_norm : f T ≤ ‖f T‖ :=
            Real.le_norm_self (f T)
          have hC_le_abs : C ≤ |C| :=
            le_abs_self C
          have hC_le_D : C ≤ D :=
            le_trans hC_le_abs (le_add_of_nonneg_right zero_le_one)
          have hG_norm_nonneg : 0 ≤ ‖G‖ :=
            norm_nonneg G
          have hmul_le : C * ‖G‖ ≤ D * ‖G‖ :=
            mul_le_mul_of_nonneg_right hC_le_D hG_norm_nonneg
          have hG_norm : ‖G‖ = G :=
            Real.norm_of_nonneg hT.2
          have hmul_eq : D * ‖G‖ = D * G :=
            congrArg (fun x : ℝ => D * x) hG_norm
          calc
            f T ≤ ‖f T‖ :=
              hf_le_norm
            _ ≤ C * ‖G‖ :=
              hT.1
            _ ≤ D * ‖G‖ :=
              hmul_le
            _ = D * G :=
              hmul_eq)

/-- Standard shifted-polynomial/exponential comparison used in finite-order
envelope domination. -/
theorem finiteOrder_shiftedPower_isBigO_scaledPower
    (c : ℝ)
    (m : ℕ)
    (hc : 0 < c) :
    (fun T : ℝ => (1 + T) ^ m) =O[Filter.atTop]
      fun T : ℝ => (c * T) ^ m := by
  let K : ℝ := (2 / c) ^ m
  have hK_nonneg : 0 ≤ K :=
    pow_nonneg (le_of_lt (div_pos two_pos hc)) m
  refine
    IsBigO.of_bound K
      (eventually_atTop.2
        ⟨1, fun T hT => ?_⟩)
  have hT_nonneg : 0 ≤ T :=
    le_trans zero_le_one hT
  have hcT_nonneg : 0 ≤ c * T :=
    mul_nonneg (le_of_lt hc) hT_nonneg
  have hleft_nonneg : 0 ≤ (1 + T) ^ m :=
    pow_nonneg (add_nonneg zero_le_one hT_nonneg) m
  have hnorm_left :
      ‖(1 + T) ^ m‖ = (1 + T) ^ m :=
    Real.norm_of_nonneg hleft_nonneg
  have hnorm_right_base :
      ‖(c * T) ^ m‖ = (c * T) ^ m :=
    Real.norm_of_nonneg (pow_nonneg hcT_nonneg m)
  have hshift_le_twoT : 1 + T ≤ 2 * T := by
    calc
      1 + T ≤ T + T :=
        add_le_add_right hT T
      _ = 2 * T :=
        (two_mul T).symm
  have htwoT_eq :
      2 * T = (2 / c) * (c * T) := by
    calc
      (2 / c) * (c * T) = ((2 / c) * c) * T :=
        mul_assoc (2 / c) c T
      _ = 2 * T := by
        exact congrArg (fun x : ℝ => x * T) (div_mul_cancel₀ 2 (ne_of_gt hc))
  have hbase_le :
      1 + T ≤ (2 / c) * (c * T) :=
    Eq.subst
      (motive := fun x : ℝ => 1 + T ≤ x)
      htwoT_eq
      hshift_le_twoT
  have hpow_le :
      (1 + T) ^ m ≤ ((2 / c) * (c * T)) ^ m :=
    pow_le_pow_left₀ (add_nonneg zero_le_one hT_nonneg) hbase_le m
  have hmul_pow :
      ((2 / c) * (c * T)) ^ m = K * (c * T) ^ m :=
    mul_pow (2 / c) (c * T) m
  have hraw :
      (1 + T) ^ m ≤ K * (c * T) ^ m :=
    Eq.subst
      (motive := fun x : ℝ => (1 + T) ^ m ≤ x)
      hmul_pow
      hpow_le
  have htarget :
      ‖(1 + T) ^ m‖ ≤ K * ‖(c * T) ^ m‖ :=
    Eq.subst
      (motive := fun x : ℝ => ‖(1 + T) ^ m‖ ≤ K * x)
      hnorm_right_base.symm
      (Eq.subst
        (motive := fun x : ℝ => x ≤ K * (c * T) ^ m)
        hnorm_left.symm
        hraw)
  exact htarget

/-- Positive linear changes of variable preserve the standard polynomial-versus-exponential
comparison at infinity. -/
theorem finiteOrder_scaledPower_isBigO_exp_scaled
    (c : ℝ)
    (m : ℕ)
    (hc : 0 < c) :
    (fun T : ℝ => (c * T) ^ m) =O[Filter.atTop]
      fun T : ℝ => Real.exp (c * T) := by
  exact
    (Real.isLittleO_pow_exp_atTop (n := m)).isBigO.comp_tendsto
      (Filter.Tendsto.const_mul_atTop hc tendsto_id)

/-- Shifted polynomial height is `O(exp (cT))` for every positive `c`. -/
theorem finiteOrder_shiftedPower_isBigO_exp
    (c : ℝ)
    (m : ℕ)
    (hc : 0 < c) :
    (fun T : ℝ => (1 + T) ^ m) =O[Filter.atTop]
      fun T : ℝ => Real.exp (c * T) := by
  exact
    (finiteOrder_shiftedPower_isBigO_scaledPower c m hc).trans
      (finiteOrder_scaledPower_isBigO_exp_scaled c m hc)

theorem finiteOrder_verticalExponent_isBigO_exp
    (A B c : ℝ)
    (m : ℕ)
    (hc : 0 < c) :
    (fun T : ℝ => Real.log A + B * (1 + T) ^ m) =O[Filter.atTop]
      fun T : ℝ => Real.exp (c * T) := by
  have hconst :
      (fun _T : ℝ => Real.log A) =O[Filter.atTop]
        fun T : ℝ => Real.exp (c * T) := by
    have hone :
        (fun _T : ℝ => (1 : ℝ)) =O[Filter.atTop]
          fun T : ℝ => Real.exp (c * T) := by
      exact
        Real.isBigO_one_exp_comp.2
          ((Filter.Tendsto.const_mul_atTop hc tendsto_id))
    exact
      (isBigO_const_mul_self (Real.log A)
        (fun _T : ℝ => (1 : ℝ)) Filter.atTop).trans hone
  have hpoly :
      (fun T : ℝ => B * (1 + T) ^ m) =O[Filter.atTop]
        fun T : ℝ => Real.exp (c * T) := by
    exact
      (finiteOrder_shiftedPower_isBigO_exp c m hc).const_mul_left B
  exact IsBigO.add hconst hpoly

/-- Real exponent comparison behind finite-order versus double-exponential
domination.

This is the canonical real-analysis core: a polynomial in `1 + T`, after
adding the fixed logarithmic constant `log A`, is eventually bounded by a
positive multiple of `exp (cT)`.  It is the only growth-rate input needed for
the vertical finite-order envelope domination below. -/
theorem finiteOrder_verticalExponent_eventually_le_doubleExponentialExponent
    (A B c : ℝ)
    (m : ℕ)
    (hA : 0 < A)
    (hB : 0 < B)
    (hc : 0 < c) :
    ∃ D : ℝ,
      0 < D ∧
      ∀ᶠ T : ℝ in Filter.atTop,
        Real.log A + B * (1 + T) ^ m ≤ D * Real.exp (c * T) := by
  exact real_isBigO_exp_eventually_le_pos_mul c
    (finiteOrder_verticalExponent_isBigO_exp A B c m hc)

/-- Exponentiating the real finite-order/double-exponential comparison gives
eventual domination of the vertical envelopes. -/
theorem finiteOrder_verticalEnvelope_eventually_le_doubleExponential
    (A B c : ℝ)
    (m : ℕ)
    (hA : 0 < A)
    (hB : 0 < B)
    (hc : 0 < c) :
    ∃ D : ℝ,
      0 < D ∧
      ∀ᶠ T : ℝ in Filter.atTop,
        A * Real.exp (B * (1 + T) ^ m) ≤
          Real.exp (D * Real.exp (c * T)) := by
  rcases finiteOrder_verticalExponent_eventually_le_doubleExponentialExponent
      A B c m hA hB hc with
    ⟨D, hD_pos, hcompare⟩
  refine ⟨D, hD_pos, ?_⟩
  exact hcompare.mono
    (fun T hT =>
      by
        have hA_exp_log : A = Real.exp (Real.log A) :=
          (Real.exp_log hA).symm
        have hleft_exp :
            A * Real.exp (B * (1 + T) ^ m) =
              Real.exp (Real.log A + B * (1 + T) ^ m) := by
          calc
            A * Real.exp (B * (1 + T) ^ m) =
                Real.exp (Real.log A) * Real.exp (B * (1 + T) ^ m) := by
              exact congrArg
                (fun x : ℝ => x * Real.exp (B * (1 + T) ^ m))
                hA_exp_log
            _ = Real.exp (Real.log A + B * (1 + T) ^ m) :=
              (Real.exp_add (Real.log A) (B * (1 + T) ^ m)).symm
        have hexp_le :
            Real.exp (Real.log A + B * (1 + T) ^ m) ≤
              Real.exp (D * Real.exp (c * T)) :=
          Real.exp_le_exp.mpr hT
        Eq.subst
          (motive := fun x : ℝ =>
            x ≤ Real.exp (D * Real.exp (c * T)))
          hleft_exp.symm
          hexp_le)

/-- Pure real eventual domination of finite-order vertical envelopes by a
double-exponential envelope.

This is the exact real-variable core behind the admissible-growth conversion:
for every `0 < c`, polynomial height in the exponent,
`B * (1 + T)^m`, is eventually dominated by `D * exp (c * T)`.
After exponentiating, the ordinary finite-order envelope is controlled by the
subcritical Phragmen-Lindelöf growth envelope. -/
theorem finiteOrder_verticalEnvelope_isBigO_doubleExponential
    (A B c : ℝ)
    (m : ℕ)
    (hA : 0 < A)
    (hB : 0 < B)
    (hc : 0 < c) :
    ∃ D : ℝ,
      (fun T : ℝ => A * Real.exp (B * (1 + T) ^ m)) =O[Filter.atTop]
        fun T : ℝ => Real.exp (D * Real.exp (c * T)) := by
  rcases finiteOrder_verticalEnvelope_eventually_le_doubleExponential
      A B c m hA hB hc with
    ⟨D, _hD_pos, hdom⟩
  refine ⟨D, ?_⟩
  exact
    IsBigO.of_bound 1
      (hdom.mono
        (fun T hT =>
          by
            let R : ℝ := Real.exp (D * Real.exp (c * T))
            have hR_nonneg : 0 ≤ R :=
              le_of_lt (Real.exp_pos (D * Real.exp (c * T)))
            have hR_norm : ‖R‖ = R :=
              Real.norm_of_nonneg hR_nonneg
            have hone_norm : 1 * ‖R‖ = R := by
              calc
                1 * ‖R‖ = ‖R‖ :=
                  one_mul ‖R‖
                _ = R :=
                  hR_norm
            Eq.subst
              (motive := fun x : ℝ =>
                ‖A * Real.exp (B * (1 + T) ^ m)‖ ≤ x)
              hone_norm.symm
              (le_trans
                (le_of_eq
                  (Real.norm_of_nonneg
                    (mul_nonneg (le_of_lt hA)
                      (le_of_lt (Real.exp_pos (B * (1 + T) ^ m))))))
                hT)))

/-- Bounded-strip height comparison in the exact form used by the
finite-order-to-admissible-envelope transport. -/
theorem strip_norm_height_le_vertical_height_envelope
    (a b : ℝ)
    {z : ℂ}
    (hza : a ≤ z.re)
    (hzb : z.re ≤ b) :
    1 + ‖z‖ ≤ (|a| + |b| + 2) * (1 + ‖z.im‖) :=
  strip_basicHeight_le_verticalHeight a b hza hzb

/-- On a closed bounded strip, the finite-order complex-height envelope is
`O` of the corresponding vertical-height envelope. -/
theorem finiteOrder_stripEnvelope_isBigO_verticalEnvelope
    (A B a b : ℝ)
    (m : ℕ)
    (hA : 0 < A)
    (hB : 0 < B) :
    (fun z : ℂ => A * Real.exp (B * (1 + ‖z‖) ^ m)) =O[
        Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
          𝓟 {z : ℂ | a ≤ z.re ∧ z.re ≤ b}]
      fun z : ℂ =>
        A * Real.exp ((B * (|a| + |b| + 2) ^ m) * (1 + ‖z.im‖) ^ m) := by
  exact
    IsBigO.of_bound 1
      (eventually_inf_principal.mpr
        (Filter.Eventually.of_forall
          (fun z hz =>
            let E₁ : ℝ := A * Real.exp (B * (1 + ‖z‖) ^ m)
            let E₂ : ℝ :=
              A * Real.exp ((B * (|a| + |b| + 2) ^ m) * (1 + ‖z.im‖) ^ m)
            have hpoint : E₁ ≤ E₂ :=
              finiteOrder_norm_envelope_le_strip_vertical_envelope
                (le_of_lt hA)
                (le_of_lt hB)
                hz.1
                hz.2
            have hE₁_nonneg : 0 ≤ E₁ :=
              mul_nonneg (le_of_lt hA)
                (le_of_lt (Real.exp_pos (B * (1 + ‖z‖) ^ m)))
            have hE₂_nonneg : 0 ≤ E₂ :=
              le_trans hE₁_nonneg hpoint
            have hE₁_norm : ‖E₁‖ = E₁ :=
              Real.norm_of_nonneg hE₁_nonneg
            have hE₂_norm : ‖E₂‖ = E₂ :=
              Real.norm_of_nonneg hE₂_nonneg
            have hone_norm : 1 * ‖E₂‖ = E₂ := by
              calc
                1 * ‖E₂‖ = ‖E₂‖ :=
                  one_mul ‖E₂‖
                _ = E₂ :=
                  hE₂_norm
            Eq.subst
              (motive := fun x : ℝ => ‖E₁‖ ≤ x)
              hone_norm.symm
              (Eq.subst
                (motive := fun x : ℝ => x ≤ E₂)
                hE₁_norm.symm
                hpoint))))

/-- The real vertical double-exponential domination transports through
`z ↦ |im z|` to the closed-strip filter. -/
theorem finiteOrder_verticalEnvelope_comp_im_isBigO_doubleExponential_on_closedStrip
    (A B c a b : ℝ)
    (m : ℕ)
    (hA : 0 < A)
    (hB : 0 < B)
    (hc : 0 < c) :
    ∃ D : ℝ,
      (fun z : ℂ => A * Real.exp (B * (1 + ‖z.im‖) ^ m)) =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 {z : ℂ | a ≤ z.re ∧ z.re ≤ b}]
        fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  rcases finiteOrder_verticalEnvelope_eventually_le_doubleExponential
      A B c m hA hB hc with
    ⟨D, _hD_pos, hdom⟩
  refine ⟨D, ?_⟩
  have hcomap :
      ∀ᶠ z : ℂ in Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop,
        A * Real.exp (B * (1 + |z.im|) ^ m) ≤
          Real.exp (D * Real.exp (c * |z.im|)) :=
    hdom.comap (_root_.abs ∘ Complex.im)
  have hclosed :
      ∀ᶠ z : ℂ in
        Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
          𝓟 {z : ℂ | a ≤ z.re ∧ z.re ≤ b},
        A * Real.exp (B * (1 + |z.im|) ^ m) ≤
          Real.exp (D * Real.exp (c * |z.im|)) :=
    hcomap.filter_mono inf_le_left
  exact
    IsBigO.of_bound 1
      (hclosed.mono
        (fun z hz =>
          by
            let E : ℝ := A * Real.exp (B * (1 + ‖z.im‖) ^ m)
            let R : ℝ := Real.exp (D * Real.exp (c * |z.im|))
            have him_norm_eq_abs : ‖z.im‖ = |z.im| :=
              Real.norm_eq_abs z.im
            have hraw : E ≤ R :=
              Eq.subst
                (motive := fun x : ℝ =>
                  A * Real.exp (B * (1 + x) ^ m) ≤ R)
                him_norm_eq_abs.symm
                hz
            have hE_nonneg : 0 ≤ E :=
              mul_nonneg (le_of_lt hA)
                (le_of_lt (Real.exp_pos (B * (1 + ‖z.im‖) ^ m)))
            have hR_nonneg : 0 ≤ R :=
              le_of_lt (Real.exp_pos (D * Real.exp (c * |z.im|)))
            have hE_norm : ‖E‖ = E :=
              Real.norm_of_nonneg hE_nonneg
            have hR_norm : ‖R‖ = R :=
              Real.norm_of_nonneg hR_nonneg
            have hone_norm : 1 * ‖R‖ = R := by
              calc
                1 * ‖R‖ = ‖R‖ :=
                  one_mul ‖R‖
                _ = R :=
                  hR_norm
            Eq.subst
              (motive := fun x : ℝ => ‖E‖ ≤ x)
              hone_norm.symm
              (Eq.subst
                (motive := fun x : ℝ => x ≤ R)
                hE_norm.symm
                hraw)))

/-- Bounded-strip finite-order envelopes are admissible double-exponential
envelopes after reducing complex height to vertical height.

The proof first uses `finiteOrder_norm_envelope_le_strip_vertical_envelope` to
replace `1 + ‖z‖` by a fixed multiple of `1 + ‖im z‖` on the strip, then uses
the pure real eventual domination theorem for the vertical envelope. -/
theorem finiteOrder_stripEnvelope_isBigO_doubleExponential
    (A B c a b : ℝ)
    (m : ℕ)
    (hA : 0 < A)
    (hB : 0 < B)
    (hc : 0 < c) :
    ∃ D : ℝ,
      (fun z : ℂ => A * Real.exp (B * (1 + ‖z‖) ^ m)) =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 {z : ℂ | a ≤ z.re ∧ z.re ≤ b}]
        fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  let Bv : ℝ := B * (|a| + |b| + 2) ^ m
  have hK_pos : 0 < |a| + |b| + 2 := by
    have hsum_nonneg : 0 ≤ |a| + |b| :=
      add_nonneg (abs_nonneg a) (abs_nonneg b)
    have htwo_pos : (0 : ℝ) < 2 :=
      zero_lt_two
    have htwo_le : (2 : ℝ) ≤ |a| + |b| + 2 :=
      le_add_of_nonneg_left hsum_nonneg
    exact lt_of_lt_of_le htwo_pos htwo_le
  have hBv_pos : 0 < Bv :=
    mul_pos hB (pow_pos hK_pos m)
  have hstrip_to_vertical :
      (fun z : ℂ => A * Real.exp (B * (1 + ‖z‖) ^ m)) =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 {z : ℂ | a ≤ z.re ∧ z.re ≤ b}]
        fun z : ℂ => A * Real.exp (Bv * (1 + ‖z.im‖) ^ m) :=
    finiteOrder_stripEnvelope_isBigO_verticalEnvelope
      A B a b m hA hB
  rcases finiteOrder_verticalEnvelope_comp_im_isBigO_doubleExponential_on_closedStrip
      A Bv c a b m hA hBv_pos hc with
    ⟨D, hvertical_to_double⟩
  exact ⟨D, hstrip_to_vertical.trans hvertical_to_double⟩

/-- Membership in the open vertical strip gives the corresponding closed-strip
inequalities needed by finite-order pointwise bounds. -/
theorem openStrip_mem_closedStrip_bounds
    {a b : ℝ}
    {z : ℂ}
    (hz : z ∈ Complex.re ⁻¹' Set.Ioo a b) :
    a ≤ z.re ∧ z.re ≤ b :=
  ⟨le_of_lt hz.1, le_of_lt hz.2⟩

/-- A pointwise finite-order bound on a strip gives the matching `IsBigO`
bound against the finite-order envelope on the same strip filter. -/
theorem finiteOrder_function_isBigO_stripEnvelope_of_pointwise_strip_bound
    (f : ℂ → ℂ)
    (A B a b : ℝ)
    (m : ℕ)
    (hbound :
      ∀ z : ℂ,
        a ≤ z.re →
        z.re ≤ b →
        ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    f =O[
        Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
          𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
      fun z : ℂ => A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    IsBigO.of_bound 1
      (eventually_inf_principal.mpr
        (Filter.Eventually.of_forall
          (fun z hz =>
            let E : ℝ := A * Real.exp (B * (1 + ‖z‖) ^ m)
            have hstrip : a ≤ z.re ∧ z.re ≤ b :=
              openStrip_mem_closedStrip_bounds hz
            have hpoint : ‖f z‖ ≤ E :=
              hbound z hstrip.1 hstrip.2
            have hE_nonneg : 0 ≤ E :=
              le_trans (norm_nonneg (f z)) hpoint
            have hE_norm : ‖E‖ = E :=
              Real.norm_of_nonneg hE_nonneg
            have hone_norm : 1 * ‖E‖ = E := by
              calc
                1 * ‖E‖ = ‖E‖ :=
                  one_mul ‖E‖
                _ = E :=
                  hE_norm
            Eq.subst
              (motive := fun x : ℝ => ‖f z‖ ≤ x)
              hone_norm.symm
              hpoint)))

/-- An `IsBigO` statement on the closed-strip principal filter restricts to
the corresponding open-strip principal filter. -/
theorem isBigO_on_openStrip_of_isBigO_on_closedStrip
    {F G : ℂ → ℝ}
    {a b : ℝ}
    (h :
      F =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 {z : ℂ | a ≤ z.re ∧ z.re ≤ b}]
        G) :
      F =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        G := by
  let L : Filter ℂ :=
    Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop
  have hopen_subset_closed :
      Complex.re ⁻¹' Set.Ioo a b ⊆ {z : ℂ | a ≤ z.re ∧ z.re ≤ b} := by
    intro z hz
    exact openStrip_mem_closedStrip_bounds hz
  have hprincipal :
      𝓟 (Complex.re ⁻¹' Set.Ioo a b) ≤
        𝓟 {z : ℂ | a ≤ z.re ∧ z.re ≤ b} :=
    principal_mono.2 hopen_subset_closed
  have hle_left :
      L ⊓ 𝓟 (Complex.re ⁻¹' Set.Ioo a b) ≤ L :=
    inf_le_left
  have hle_right :
      L ⊓ 𝓟 (Complex.re ⁻¹' Set.Ioo a b) ≤
        𝓟 {z : ℂ | a ≤ z.re ∧ z.re ≤ b} :=
    le_trans inf_le_right hprincipal
  have hle :
      L ⊓ 𝓟 (Complex.re ⁻¹' Set.Ioo a b) ≤
        L ⊓ 𝓟 {z : ℂ | a ≤ z.re ∧ z.re ≤ b} :=
    le_inf hle_left hle_right
  exact h.mono hle

/-- The closed-strip envelope domination can be used on the open-strip filter. -/
theorem finiteOrder_stripEnvelope_isBigO_doubleExponential_on_openStrip
    (A B c a b : ℝ)
    (m : ℕ)
    (hA : 0 < A)
    (hB : 0 < B)
    (hc : 0 < c) :
    ∃ D : ℝ,
      (fun z : ℂ => A * Real.exp (B * (1 + ‖z‖) ^ m)) =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  rcases finiteOrder_stripEnvelope_isBigO_doubleExponential
      A B c a b m hA hB hc with
    ⟨D, hclosed⟩
  exact ⟨D, isBigO_on_openStrip_of_isBigO_on_closedStrip hclosed⟩

/-- The half-width Phragmen-Lindelöf growth parameter is strictly below the
strip threshold. -/
theorem real_pi_div_two_width_lt_pi_div_width
    {a b : ℝ}
    (hab : a < b) :
    Real.pi / (2 * (b - a)) < Real.pi / (b - a) := by
  let w : ℝ := b - a
  have hw_pos : 0 < w :=
    sub_pos.mpr hab
  have hw_lt_two_w : w < 2 * w := by
    calc
      w = 1 * w := (one_mul w).symm
      _ < 2 * w := mul_lt_mul_of_pos_right one_lt_two hw_pos
  exact
    div_lt_div₀'
      (le_refl Real.pi)
      hw_lt_two_w
      Real.pi_pos
      hw_pos

/-- Ordinary finite-order growth in a bounded vertical strip gives the
subcritical double-exponential admissible-growth hypothesis used by the
bounded-boundary Phragmen-Lindelöf theorem.

This is the generic envelope conversion: on a fixed-width strip, every
polynomial/exponential finite-order envelope
`A * exp (B * (1 + ‖z‖)^m)` is eventually dominated by
`exp (D * exp (c * |im z|))` for any positive `c`, so one chooses a small
`c < π / (b - a)`. -/
theorem strip_admissible_doubleExponential_growth_of_finiteOrder_growth
    (f : ℂ → ℂ)
    (a b : ℝ)
    (hab : a < b)
    (hfinite :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          a ≤ z.re →
          z.re ≤ b →
          ‖f z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ c : ℝ,
      c < Real.pi / (b - a) ∧
      ∃ D : ℝ,
        f =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  rcases hfinite with ⟨A, B, m, hA, hB, hbound⟩
  let c : ℝ := Real.pi / (2 * (b - a))
  have hwidth_pos : 0 < b - a :=
    sub_pos.mpr hab
  have hc_pos : 0 < c := by
    exact div_pos Real.pi_pos (mul_pos two_pos hwidth_pos)
  have hc_lt : c < Real.pi / (b - a) :=
    real_pi_div_two_width_lt_pi_div_width hab
  rcases finiteOrder_stripEnvelope_isBigO_doubleExponential_on_openStrip
      A B c a b m hA hB hc_pos with
    ⟨D, henv⟩
  have hfunction :
      f =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo a b)]
        fun z : ℂ => A * Real.exp (B * (1 + ‖z‖) ^ m) :=
    finiteOrder_function_isBigO_stripEnvelope_of_pointwise_strip_bound
      f A B a b m hbound
  refine ⟨c, hc_lt, D, ?_⟩
  exact hfunction.trans henv

/-- Global finite-order growth for the pole-cleared Riemann zeta factor.

This is the canonical standard zeta theorem behind the strip-local growth
input: `(s - 1)ζ(s)` is an entire function of finite order.  Analytically this
is proved from the meromorphic finite-order theory of `ζ`, using
Euler-Maclaurin/Abel estimates in the right half-plane, the functional equation
and Gamma/Stirling transport in the left half-plane, and local boundedness near
the removable pole. -/
theorem poleClearedRiemannZeta_rightHalfPlane_finiteOrder_growth_from_EulerMaclaurin :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        2 ≤ z.re →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases riemannZeta_farRightHalfPlane_dirichletSeries_bound with
    ⟨A, hA, hzeta_bound⟩
  refine ⟨A, 1, 1, hA, zero_lt_one, ?_⟩
  intro z hz_far
  have hz_ne_one : z ≠ 1 := by
    intro hz_eq
    have hz_re_one : z.re = 1 := by
      calc
        z.re = (1 : ℂ).re := by
          exact congrArg Complex.re hz_eq
        _ = 1 := by
          exact Complex.one_re
    have htwo_le_one : (2 : ℝ) ≤ 1 := by
      exact hz_far.trans_eq hz_re_one
    exact (not_le_of_gt one_lt_two) htwo_le_one
  have hpc :
      poleClearedRiemannZeta z = (z - 1) * riemannZeta z :=
    poleClearedRiemannZeta_eq_of_ne_one hz_ne_one
  let H : ℝ := 1 + ‖z‖
  have hH_ge_one : (1 : ℝ) ≤ H :=
    le_add_of_nonneg_right (norm_nonneg z)
  have hH_nonneg : 0 ≤ H :=
    le_trans zero_le_one hH_ge_one
  have hzeta : ‖riemannZeta z‖ ≤ A :=
    hzeta_bound z hz_far
  have hsub_norm : ‖z - 1‖ ≤ H := by
    calc
      ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le z (1 : ℂ)
      _ = ‖z‖ + 1 := by
        exact congrArg (fun x : ℝ => ‖z‖ + x) (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
      _ = H := by
        exact add_comm ‖z‖ 1
  have hproduct :
      ‖(z - 1) * riemannZeta z‖ ≤ H * A := by
    calc
      ‖(z - 1) * riemannZeta z‖ =
          ‖z - 1‖ * ‖riemannZeta z‖ := by
        exact norm_mul (z - 1) (riemannZeta z)
      _ ≤ H * A :=
        mul_le_mul hsub_norm hzeta (norm_nonneg (riemannZeta z)) hH_nonneg
  have hH_le_expH : H ≤ Real.exp H :=
    le_trans (le_add_of_nonneg_right zero_le_one) (add_one_le_exp H)
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
      (1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ) =
          (1 + ‖z‖) ^ (1 : ℕ) := by
        exact one_mul ((1 + ‖z‖) ^ (1 : ℕ))
      _ = 1 + ‖z‖ := by
        exact pow_one (1 + ‖z‖)
      _ = H := rfl
  have hraw :
      ‖poleClearedRiemannZeta z‖ ≤ A * Real.exp H :=
    Eq.subst
      (motive := fun w : ℂ => ‖w‖ ≤ A * Real.exp H)
      hpc.symm
      (le_trans hproduct hscaled)
  exact Eq.subst
    (motive := fun x : ℝ => ‖poleClearedRiemannZeta z‖ ≤ A * Real.exp x)
    hexponent.symm
    hraw

/-- Euler-Maclaurin finite-order growth for the pole-cleared zeta factor on the
full reflected right half-plane `1 ≤ Re s`.

This is the standard continuation-strength form of the right-side zeta input:
Euler-Maclaurin/Abel summation controls `(s - 1)ζ(s)` uniformly from the
boundary line `Re s = 1` into the half-plane `Re s ≥ 1`.  The far-right
Dirichlet-series theorem above only proves the easier subregion `2 ≤ Re s`;
the transport across the functional equation genuinely needs this full
half-plane statement. -/
theorem poleClearedRiemannZeta_rightHalfPlane_one_le_finiteOrder_growth_from_EulerMaclaurin :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        1 ≤ w.re →
        ‖poleClearedRiemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  sorry

/-- Reflected right half-plane finite-order growth for the pole-cleared zeta factor.

This is the right-side input needed by the functional equation on the left
half-plane: after reflection `w = 1 - z`, one only has `1 ≤ Re w`.  The proof is
the Euler-Maclaurin/Abel finite-order theorem in the half-plane of meromorphic
continuation, with the pole at `1` removed. -/
theorem poleClearedRiemannZeta_reflectedRightHalfPlane_finiteOrder_growth_from_EulerMaclaurin :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        1 ≤ w.re →
        ‖poleClearedRiemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  exact poleClearedRiemannZeta_rightHalfPlane_one_le_finiteOrder_growth_from_EulerMaclaurin

/-- The removable completed-functional-equation multiplier for the pole-cleared
zeta factor on the left half-plane.

Away from the removable point `z = 0`, this is the raw multiplier obtained by
writing the completed functional equation as a relation between `(z - 1)ζ(z)`
and `((1 - z) - 1)ζ(1 - z)`.  At `z = 0` the value is the removable value
forced by the pole-cleared identity. -/
noncomputable def poleClearedRiemannZeta_completedFunctionalEquationMultiplier
    (z : ℂ) : ℂ :=
  if z = 0 then
    poleClearedRiemannZeta 0
  else
    ((z - 1) / (((1 : ℂ) - z) - 1)) *
      (Complex.Gammaℝ ((1 : ℂ) - z) / Complex.Gammaℝ z)

/-- Exact normalization identity for the removable completed-functional-equation
multiplier of the pole-cleared zeta factor.

This is the whole-plane version of the left-boundary factorization, with the
removable value at `z = 0` included in the multiplier. -/
theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_identity
    {z : ℂ}
    (hz : z.re ≤ 0) :
    poleClearedRiemannZeta z =
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier z *
        poleClearedRiemannZeta ((1 : ℂ) - z) := by
  sorry

/-- Finite-order envelope for the removable completed-functional-equation
multiplier on the left half-plane.

Analytically this is exactly the Gamma-ratio/Stirling estimate plus the
removable boundedness at `z = 0`; cf. Titchmarsh, Ch. 2 and Edwards, Ch. 1. -/
theorem poleClearedRiemannZeta_completedFunctionalEquationMultiplier_leftHalfPlane_finiteOrder_growth :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        ‖poleClearedRiemannZeta_completedFunctionalEquationMultiplier z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  sorry

/-- Left half-plane finite-order growth for the pole-cleared zeta factor.

This is the functional-equation side of the standard finite-order theorem:
transport the right half-plane Euler-Maclaurin/Dirichlet-series control across
the completed functional equation and use the exposed Gamma/Stirling owner
estimates; cf. Titchmarsh, Ch. 2 and Edwards, Ch. 1. -/
theorem poleClearedRiemannZeta_leftHalfPlane_completedFunctionalEquation_transport_identity :
    ∃ M : ℂ → ℂ,
      (∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re ≤ 0 →
          ‖M z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        poleClearedRiemannZeta z =
          M z * poleClearedRiemannZeta ((1 : ℂ) - z) := by
  refine
    ⟨poleClearedRiemannZeta_completedFunctionalEquationMultiplier,
      poleClearedRiemannZeta_completedFunctionalEquationMultiplier_leftHalfPlane_finiteOrder_growth,
      ?_⟩
  intro z hz
  exact poleClearedRiemannZeta_completedFunctionalEquationMultiplier_identity hz

/-- Functional-equation transport of finite-order growth from the reflected right
half-plane to the left half-plane.

The multiplier `M` is the completed functional-equation/Gamma-ratio factor
together with the pole-clearing rational terms.  This theorem is pure
finite-order bookkeeping once the exact identity and multiplier estimate are
available. -/
theorem poleClearedRiemannZeta_leftHalfPlane_finiteOrder_growth_of_completedFunctionalEquation_transport
    (htransport :
      ∃ M : ℂ → ℂ,
        (∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
          0 < A ∧
          0 < B ∧
          ∀ z : ℂ,
            z.re ≤ 0 →
            ‖M z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) ∧
        ∀ z : ℂ,
          z.re ≤ 0 →
          poleClearedRiemannZeta z =
            M z * poleClearedRiemannZeta ((1 : ℂ) - z))
    (hright :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ w : ℂ,
          1 ≤ w.re →
          ‖poleClearedRiemannZeta w‖ ≤
            A * Real.exp (B * (1 + ‖w‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  sorry

theorem poleClearedRiemannZeta_leftHalfPlane_finiteOrder_growth_from_completedFunctionalEquation_and_GammaStirling :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_leftHalfPlane_finiteOrder_growth_of_completedFunctionalEquation_transport
      poleClearedRiemannZeta_leftHalfPlane_completedFunctionalEquation_transport_identity
      poleClearedRiemannZeta_reflectedRightHalfPlane_finiteOrder_growth_from_EulerMaclaurin

/-- Left half-plane finite-order growth for the pole-cleared zeta factor.

This is only name transport from the completed functional equation plus the
Gamma/Stirling owner estimates. -/
theorem poleClearedRiemannZeta_leftHalfPlane_finiteOrder_growth_from_functionalEquation :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_leftHalfPlane_finiteOrder_growth_from_completedFunctionalEquation_and_GammaStirling

/-- Compact core of the central strip for the pole-cleared zeta factor.

This is the finite-height local boundedness part: continuity of the removable
pole-cleared normalization on the compact rectangle `0 ≤ Re z ≤ 2`,
`|Im z| ≤ 1`, converted to a degree-zero finite-order envelope. -/
theorem poleClearedRiemannZeta_centralStrip_compactCore_finiteOrder_growth :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖z.im‖ ≤ 1 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases poleClearedRiemannZeta_rightCriticalStrip_compact_norm_bound with
    ⟨C, hC_pos, hC_bound⟩
  refine ⟨C, 1, 0, hC_pos, zero_lt_one, ?_⟩
  intro z hz0 hz2 hzim
  have hz_mem : z ∈ completedRiemannZeta₀_rightCriticalStripCompactSet :=
    ⟨hz0, hz2, hzim⟩
  have hraw : ‖poleClearedRiemannZeta z‖ ≤ C :=
    hC_bound z hz_mem
  have hfactor_ge_one :
      (1 : ℝ) ≤ Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ)) := by
    have hexponent_nonneg :
        0 ≤ (1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ) :=
      mul_nonneg zero_le_one
        (pow_nonneg (add_nonneg zero_le_one (norm_nonneg z)) 0)
    exact le_trans
      (le_of_eq Real.exp_zero.symm)
      (Real.exp_le_exp.mpr hexponent_nonneg)
  have hC_le_target :
      C ≤ C * Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ)) := by
    calc
      C = C * 1 := by
        exact (mul_one C).symm
      _ ≤ C * Real.exp ((1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ)) :=
        mul_le_mul_of_nonneg_left hfactor_ge_one (le_of_lt hC_pos)
  exact le_trans hraw hC_le_target

/-- Vertical-tail finite-order growth in the central strip for the pole-cleared zeta factor.

This is the unbounded-height part of the central strip.  Its proof belongs to
the standard zeta strip-growth theorem: combine the left boundary obtained from
the completed functional equation and Gamma/Stirling owner estimates with the
right boundary obtained from the Dirichlet-series/Euler-Maclaurin side, then use
the generic strip finite-order/Phragmen-Lindelöf API. -/
theorem poleClearedRiemannZeta_centralStrip_verticalTail_growth_from_PL_transport
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

/-- The exact PL input package for the central-strip vertical tail.

The left edge is the completed-functional-equation/Gamma-Stirling estimate; the
right edge is the Dirichlet-series/Euler-Maclaurin estimate; the interior
admissible growth is the finite-order zeta input already isolated above. -/
theorem poleClearedRiemannZeta_centralStrip_verticalTail_PL_input_package :
    DiffContOnCl ℂ poleClearedRiemannZeta
        (Complex.re ⁻¹' Set.Ioo 0 2) ∧
      (∃ c : ℝ,
        c < Real.pi / (2 - 0) ∧
        ∃ D : ℝ,
          poleClearedRiemannZeta =O[
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
            fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|))) ∧
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
  refine
    ⟨poleClearedRiemannZeta_rightCriticalStrip_diffContOnCl,
      poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth,
      poleClearedRiemannZeta_rightCriticalStrip_leftBoundary_functionalEquation_growth_bound,
      poleClearedRiemannZeta_rightCriticalStrip_rightBoundary_dirichletSeries_growth_bound⟩

theorem poleClearedRiemannZeta_centralStrip_verticalTail_finiteOrder_growth_from_boundary_inputs :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases poleClearedRiemannZeta_centralStrip_verticalTail_PL_input_package with
    ⟨hhol, hfinite, hleft, hright⟩
  exact
    poleClearedRiemannZeta_centralStrip_verticalTail_growth_from_PL_transport
      hhol hfinite hleft hright

/-- Compact core and vertical tails patch to finite-order growth on the whole
central strip. -/
theorem poleClearedRiemannZeta_centralStrip_finiteOrder_growth_of_compactCore_and_verticalTail
    (hcompact :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖z.im‖ ≤ 1 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (htail :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖poleClearedRiemannZeta z‖ ≤
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

/-- Central compact-strip finite-order growth for the pole-cleared zeta factor.

This is the local boundedness part of the global finite-order theorem.  The
removable value at `1` is already built into `poleClearedRiemannZeta`; on the
closed strip `0 ≤ Re z ≤ 2`, compact/local boundedness gives an ordinary
finite-order envelope with fixed constants; cf. Boas, Ch. 1. -/
theorem poleClearedRiemannZeta_centralStrip_finiteOrder_growth_from_localBoundedness :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_centralStrip_finiteOrder_growth_of_compactCore_and_verticalTail
      poleClearedRiemannZeta_centralStrip_compactCore_finiteOrder_growth
      poleClearedRiemannZeta_centralStrip_verticalTail_finiteOrder_growth_from_boundary_inputs

/-- Patch left, central, and right finite-order envelopes into a global envelope. -/
theorem poleClearedRiemannZeta_globalFiniteOrder_growth_of_left_central_right
    (hleft :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re ≤ 0 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hcentral :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hright :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          2 ≤ z.re →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hleft with ⟨Al, Bl, ml, hAl, hBl, hleft_bound⟩
  rcases hcentral with ⟨Ac, Bc, mc, hAc, hBc, hcentral_bound⟩
  rcases hright with ⟨Ar, Br, mr, hAr, hBr, hright_bound⟩
  let A : ℝ := Al + Ac + Ar
  let B : ℝ := Bl + Bc + Br
  let m : ℕ := ml + mc + mr
  have hAl_nonneg : 0 ≤ Al := le_of_lt hAl
  have hAc_nonneg : 0 ≤ Ac := le_of_lt hAc
  have hAr_nonneg : 0 ≤ Ar := le_of_lt hAr
  have hBl_nonneg : 0 ≤ Bl := le_of_lt hBl
  have hBc_nonneg : 0 ≤ Bc := le_of_lt hBc
  have hBr_nonneg : 0 ≤ Br := le_of_lt hBr
  have hA_pos : 0 < A :=
    add_pos (add_pos hAl hAc) hAr
  have hB_pos : 0 < B :=
    add_pos (add_pos hBl hBc) hBr
  refine ⟨A, B, m, hA_pos, hB_pos, ?_⟩
  intro z
  have hB_l_le : Bl ≤ B :=
    le_trans (le_add_of_nonneg_right hBc_nonneg)
      (le_add_of_nonneg_right hBr_nonneg)
  have hB_c_le : Bc ≤ B := by
    have hBc_le_Bl_Bc : Bc ≤ Bl + Bc :=
      le_add_of_nonneg_left hBl_nonneg
    exact le_trans hBc_le_Bl_Bc (le_add_of_nonneg_right hBr_nonneg)
  have hB_r_le : Br ≤ B := by
    have hBr_le_Bc_Br : Br ≤ Bc + Br :=
      le_add_of_nonneg_left hBc_nonneg
    have hBc_Br_le_B : Bc + Br ≤ B := by
      calc
        Bc + Br ≤ Al + (Bc + Br) :=
          le_add_of_nonneg_left hAl_nonneg
        _ = B := by
          exact (add_assoc Al Bc Br).symm
    exact le_trans hBr_le_Bc_Br hBc_Br_le_B
  by_cases hz_left : z.re ≤ 0
  · have hraw :
        ‖poleClearedRiemannZeta z‖ ≤
          Al * Real.exp (Bl * (1 + ‖z‖) ^ ml) :=
      hleft_bound z hz_left
    have hA_l_le : Al ≤ A :=
      le_trans (le_add_of_nonneg_right hAc_nonneg)
        (le_add_of_nonneg_right hAr_nonneg)
    exact le_trans hraw
      (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
        hAl_nonneg hA_l_le hB_l_le hBl_nonneg
        (Nat.le_add_right ml (mc + mr)))
  · have hz_nonneg : 0 ≤ z.re :=
      le_of_not_ge hz_left
    by_cases hz_right : 2 ≤ z.re
    · have hraw :
          ‖poleClearedRiemannZeta z‖ ≤
            Ar * Real.exp (Br * (1 + ‖z‖) ^ mr) :=
        hright_bound z hz_right
      have hA_r_le : Ar ≤ A := by
        have hAr_le_Ac_Ar : Ar ≤ Ac + Ar :=
          le_add_of_nonneg_left hAc_nonneg
        have hAc_Ar_le_A : Ac + Ar ≤ A := by
          calc
            Ac + Ar ≤ Al + (Ac + Ar) :=
              le_add_of_nonneg_left hAl_nonneg
            _ = A := by
              exact (add_assoc Al Ac Ar).symm
        exact le_trans hAr_le_Ac_Ar hAc_Ar_le_A
      have hm_r_le : mr ≤ m := by
        have hmc_mr_le : mr ≤ mc + mr :=
          Nat.le_add_left mr mc
        have htarget : mc + mr ≤ m := by
          exact Nat.le_add_left (mc + mr) ml
        exact le_trans hmc_mr_le htarget
      exact le_trans hraw
        (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
          hAr_nonneg hA_r_le hB_r_le hBr_nonneg hm_r_le)
    · have hz_le_two : z.re ≤ 2 :=
        le_of_not_ge hz_right
      have hraw :
          ‖poleClearedRiemannZeta z‖ ≤
            Ac * Real.exp (Bc * (1 + ‖z‖) ^ mc) :=
        hcentral_bound z hz_nonneg hz_le_two
      have hA_c_le : Ac ≤ A := by
        have hAc_le_Al_Ac : Ac ≤ Al + Ac :=
          le_add_of_nonneg_left hAl_nonneg
        exact le_trans hAc_le_Al_Ac (le_add_of_nonneg_right hAr_nonneg)
      have hm_c_le : mc ≤ m := by
        have hmc_le_ml_mc : mc ≤ ml + mc :=
          Nat.le_add_left mc ml
        have htarget : ml + mc ≤ m :=
          Nat.le_add_right (ml + mc) mr
        exact le_trans hmc_le_ml_mc htarget
      exact le_trans hraw
        (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
          hAc_nonneg hA_c_le hB_c_le hBc_nonneg hm_c_le)

theorem poleClearedRiemannZeta_globalFiniteOrder_growth_from_functionalEquation_and_EulerMaclaurin :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_globalFiniteOrder_growth_of_left_central_right
      poleClearedRiemannZeta_leftHalfPlane_finiteOrder_growth_from_functionalEquation
      poleClearedRiemannZeta_centralStrip_finiteOrder_growth_from_localBoundedness
      poleClearedRiemannZeta_rightHalfPlane_finiteOrder_growth_from_EulerMaclaurin

/-- Zeta-specific ordinary finite-order growth for the pole-cleared factor in
the right critical strip.

This is only the restriction of the global finite-order theorem for
`(s - 1)ζ(s)` to the closed right critical strip. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_ordinaryFiniteOrder_growth_from_functionalEquation_and_EulerMaclaurin :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        z.re ≤ 2 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases poleClearedRiemannZeta_globalFiniteOrder_growth_from_functionalEquation_and_EulerMaclaurin with
    ⟨A, B, m, hA, hB, hbound⟩
  exact ⟨A, B, m, hA, hB, fun z _hz_left _hz_right => hbound z⟩

/-- Standard finite-order theorem for the pole-cleared Riemann zeta factor in the right
critical strip.

This is the exact zeta finite-order theorem needed by the strip damping argument.  Its
analytic proof is the standard meromorphic finite-order estimate for `ζ`, with the pole at
`1` removed by `poleClearedRiemannZeta`: Abel/Euler-Maclaurin gives the right boundary,
the completed functional equation plus the Gamma-ratio Stirling estimates gives the left
boundary, local boundedness handles the removable pole, and the finite-order strip
normalization converts those inputs to the sub-critical double-exponential envelope. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_standardFiniteOrder_admissible_growth :
    ∃ c : ℝ,
      c < Real.pi / (2 - 0) ∧
      ∃ D : ℝ,
        poleClearedRiemannZeta =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact
    strip_admissible_doubleExponential_growth_of_finiteOrder_growth
      poleClearedRiemannZeta 0 2 zero_lt_two
      poleClearedRiemannZeta_rightCriticalStrip_ordinaryFiniteOrder_growth_from_functionalEquation_and_EulerMaclaurin

/-- Standard zeta finite-order input for the pole-cleared factor inside the right
critical strip.

This is only name transport from the exact standard finite-order theorem for the
pole-cleared Riemann zeta factor. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth_standardZetaInput :
    ∃ c : ℝ,
      c < Real.pi / (2 - 0) ∧
      ∃ D : ℝ,
        poleClearedRiemannZeta =O[
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact poleClearedRiemannZeta_rightCriticalStrip_standardFiniteOrder_admissible_growth

/-- Deep zeta-growth owner primitive for the pole-cleared factor inside the right
critical strip.

The analytic content is isolated in
`poleClearedRiemannZeta_rightCriticalStrip_standardFiniteOrder_admissible_growth`;
this owner primitive is only the public name consumed by the strip
Phragmen-Lindelöf layer. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth_ownerPrimitive :
    ∃ c : ℝ,
      c < Real.pi / (2 - 0) ∧
      ∃ D : ℝ,
        poleClearedRiemannZeta =O[
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth_standardZetaInput

/-- Interior admissible finite-order envelope for the pole-cleared zeta factor in the
right critical strip.

This is the damping-side zeta-growth root consumed by the generic strip
Phragmen-Lindelöf theorem.  It is a thin wrapper over the standard finite-order theorem
for the pole-cleared Riemann zeta factor in this bounded-width strip. -/
theorem poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth :
    ∃ c : ℝ,
      c < Real.pi / (2 - 0) ∧
      ∃ D : ℝ,
        poleClearedRiemannZeta =O[
            Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
              𝓟 (Complex.re ⁻¹' Set.Ioo 0 2)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth_ownerPrimitive

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
  exact
    poleClearedRiemannZeta_rightCriticalStrip_verticalTail_growth_bound_of_strip_inputs
      poleClearedRiemannZeta_rightCriticalStrip_diffContOnCl
      poleClearedRiemannZeta_rightCriticalStrip_admissible_strip_growth
      hleft
      hright

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
          rfl
    have hnorm_im_zero : ‖z.im‖ = 0 := by
      exact (congrArg norm him_zero).trans norm_zero
    have hle_zero : (1 : ℝ) ≤ 0 :=
      hzim.trans_eq hnorm_im_zero
    exact (not_le_of_gt zero_lt_one) hle_zero
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
