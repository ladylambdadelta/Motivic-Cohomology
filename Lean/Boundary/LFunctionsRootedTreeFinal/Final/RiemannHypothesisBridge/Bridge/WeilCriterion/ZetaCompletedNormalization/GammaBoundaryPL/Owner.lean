import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.Owner

/-!
# Gamma boundary growth and strip Phragmen-Lindelof transport

This file is a mechanically split owner layer from the completed normalization
package.  It preserves the original declaration order and keeps downstream
imports routed through `ZetaCompletedNormalization.Owner`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

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
    have hdiv : (-z / 2 : ℂ).re = -z.re / 2 := by
      norm_num [Complex.div_re_ofReal, Complex.neg_re]
    have hdiv' : -z.re / 2 ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz_re)
        (by norm_num : (0 : ℝ) ≤ 2)
    exact hdiv ▸ hdiv'
  have hnorm_eq : ‖π ^ (-z / 2 : ℂ)‖ = π ^ (-z / 2 : ℂ).re := by
    exact Complex.abs_cpow_eq_rpow_re_of_pos hpi_pos (-z / 2 : ℂ)
  have hnorm_le_one : ‖π ^ (-z / 2 : ℂ)‖ ≤ 1 := by
    exact hnorm_eq ▸
      Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt hpi_one_lt) hre_nonpos
  have hnorm_pos : 0 < ‖π ^ (-z / 2 : ℂ)‖ := by
    exact hnorm_eq ▸ Real.rpow_pos_of_pos hpi_pos (-z / 2 : ℂ).re
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
      exact Complex.abs_cpow_eq_rpow_re_of_pos hpi_pos_real (-z / 2 : ℂ)
    exact hnorm_eq ▸ Real.rpow_pos_of_pos hpi_pos_real (-z / 2 : ℂ).re
  have hgamma_pos : 0 < ‖Complex.Gamma (z / 2)‖ :=
    norm_pos_iff.mpr
      (ComplexGamma_halfArgument_ne_zero_of_re_nonneg_and_one_le_norm hz_re hz_norm)
  calc
    Real.log ‖π ^ (-z / 2) * Complex.Gamma (z / 2)‖ =
        Real.log (‖π ^ (-z / 2 : ℂ)‖ * ‖Complex.Gamma (z / 2)‖) := by
      exact congrArg Real.log (norm_mul (π ^ (-z / 2 : ℂ)) (Complex.Gamma (z / 2)))
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
    have hone_le_H : (1 : ℝ) ≤ H :=
      le_add_of_nonneg_right (norm_nonneg z)
    have : 2 + ‖z‖ = H + 1 := harg_eq
    nlinarith [this, hone_le_H]
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
    calc
      C * H ^ m * (2 * H) = (2 * C) * (H ^ m * H) := by ring
      _ = (2 * C) * H ^ (m + 1) := by
        exact congrArg (fun t : ℝ => (2 * C) * t) (pow_succ H m).symm
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
          norm_num [Real.exp_zero]
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
          norm_num [Real.exp_zero]
    exact hscaled.trans_eq hcollapse

/-- The vertical height is bounded by the ordinary complex height. -/
theorem vertical_basicHeight_le_complex_basicHeight
    (z : ℂ) :
    1 + ‖z.im‖ ≤ 1 + ‖z‖ := by
  have him_le_norm : ‖z.im‖ ≤ ‖z‖ := by
  have him_abs_le_norm : |z.im| ≤ ‖z‖ := by
    exact Complex.abs_im_le_abs z
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

end
end LFunctions
end Boundary
