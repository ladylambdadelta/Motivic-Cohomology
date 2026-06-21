import Mathlib.Data.Real.Pi.Bounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.Owner

/-!
# Gamma boundary growth primitives

This owner layer contains the Gamma/Stirling growth estimates used by completed-zeta boundary normalization.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

theorem Complex.Gamma_closedRightHalfPlane_sectorial_and_vertical_stirling_bounds_classical :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    (∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        Complex.closedRightHalfPlaneSector w →
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
                (1 + ‖b‖) ^ (1 / 2 - a)) := fun hbranch => by
  exact
    ⟨(Complex.Gamma_closedRightHalfPlane_sectorial_stirling_expansion_with_vertical_bounds_classical
        hbranch).2.1,
      (Complex.Gamma_closedRightHalfPlane_sectorial_stirling_expansion_with_vertical_bounds_classical
        hbranch).2.2⟩

/-- Standard sectorial logarithmic Stirling for `Complex.Gamma` in the closed right half-plane.

This is the standard special-function input closest to the literature: the
sectorial Stirling expansion for `log Γ(w)` on a closed sector avoiding the
negative real axis, specialized to `0 ≤ w.re` and converted to a log-norm
upper bound.  The radius is written as `2 * ‖w‖` so the downstream
half-argument transport is formula-level; cf. DLMF §5.11. -/
theorem Complex.Gamma_sectorial_rightHalfPlane_stirling_log_norm_bound_classical :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := fun hbranch => by
  exact
    (Complex.Gamma_closedRightHalfPlane_sectorial_and_vertical_stirling_bounds_classical
      hbranch).1

/-- Standard sectorial logarithmic Stirling for `Complex.Gamma` in the closed right half-plane.

This is name transport from the classical sectorial `log Γ` estimate. -/
theorem Complex.Gamma_sectorial_rightHalfPlane_stirling_log_norm_bound_standard :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := fun hbranch => by
  exact Complex.Gamma_sectorial_rightHalfPlane_stirling_log_norm_bound_classical hbranch

/-- Standard sectorial logarithmic Stirling for `Complex.Gamma` in the closed right half-plane.

This is only name transport from the canonical sectorial Gamma log-norm input. -/
theorem Complex.logGamma_sectorial_rightHalfPlane_stirling_log_norm_bound_standard :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := fun hbranch => by
  exact Complex.Gamma_sectorial_rightHalfPlane_stirling_log_norm_bound_standard hbranch

/-- Sectorial logarithmic Stirling for `Complex.Gamma` in the closed right half-plane.

This is the canonical sectorial Gamma root for the normalization chain.  It is
formula-level transport from the standard Mathlib-shaped sectorial Stirling
estimate for `Complex.Gamma`; cf. DLMF §5.11. -/
theorem Complex.logGamma_sectorial_rightHalfPlane_stirling_log_norm_bound :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := fun hbranch => by
  exact Complex.logGamma_sectorial_rightHalfPlane_stirling_log_norm_bound_standard hbranch

/-- The standard sectorial complex-Stirling input for `Complex.Gamma` in the closed
right half-plane.

This owner-root spelling is retained for the normalization chain.  Its proof is only
name transport from the canonical sectorial `log Γ` Stirling input. -/
theorem sectorialComplexGammaStirling_rightHalfPlane_log_linear_growth_bound_degree_one :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := fun hbranch => by
  exact Complex.logGamma_sectorial_rightHalfPlane_stirling_log_norm_bound hbranch

/-- Transport the sectorial `Complex.Gamma` estimate from `w` to the half-argument
`w = z / 2`. -/
theorem halfArgument_re_pos_of_re_pos
    {z : ℂ}
    (hz_re : 0 < z.re) :
    0 < (z / 2).re := by
  have hdiv : (z / 2 : ℂ).re = z.re / (2 : ℝ) :=
    RCLike.div_re_ofReal (z := z) (r := (2 : ℝ))
  have hhalf_pos : 0 < z.re / (2 : ℝ) :=
    div_pos hz_re two_pos
  calc
    0 < z.re / (2 : ℝ) := hhalf_pos
    _ = (z / 2 : ℂ).re := hdiv.symm

/-- Nonnegative real part places the half-argument in the closed right-half-plane sector. -/
theorem halfArgument_closedRightHalfPlaneSector_of_re_nonneg
    {z : ℂ}
    (hz_re : 0 ≤ z.re) :
    Complex.closedRightHalfPlaneSector (z / 2 : ℂ) :=
  halfArgument_re_nonneg_of_re_nonneg hz_re

/-- Strictly positive real part places the half-argument in the closed
right-half-plane sector. -/
theorem halfArgument_closedRightHalfPlaneSector_of_re_pos
    {z : ℂ}
    (hz_re : 0 < z.re) :
    Complex.closedRightHalfPlaneSector (z / 2 : ℂ) :=
  halfArgument_closedRightHalfPlaneSector_of_re_nonneg (le_of_lt hz_re)

/-- Transport the sectorial `Complex.Gamma` estimate from `w` to the half-argument
`w = z / 2`. -/
theorem sectorialComplexGammaStirling_halfArgument_rightHalfPlane_log_linear_growth_bound_degree_one_of_sectorial
    (hsector :
      ∃ C : ℝ,
        0 < C ∧
        ∀ w : ℂ,
          0 < w.re →
          Complex.closedRightHalfPlaneSector w →
          (1 / 2 : ℝ) ≤ ‖w‖ →
          Real.log ‖Complex.Gamma w‖ ≤
            C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖)) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
        1 ≤ ‖z‖ →
        Real.log ‖Complex.Gamma (z / 2)‖ ≤
          C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
  match hsector with
  | ⟨C, hC_pos, hC⟩ =>
      exact
        ⟨C, hC_pos, fun z hz_re hz_norm =>
          by
            have hz_half_re : 0 < (z / 2).re :=
              halfArgument_re_pos_of_re_pos hz_re
            have hz_half_sector : Complex.closedRightHalfPlaneSector (z / 2 : ℂ) :=
              halfArgument_closedRightHalfPlaneSector_of_re_pos hz_re
            have hz_half_norm : (1 / 2 : ℝ) ≤ ‖z / 2‖ :=
              halfArgument_norm_ge_one_half_of_one_le_norm hz_norm
            have hraw :
                Real.log ‖Complex.Gamma (z / 2)‖ ≤
                  C * (1 + 2 * ‖z / 2‖) * Real.log (2 + 2 * ‖z / 2‖) :=
              hC (z / 2) hz_half_re hz_half_sector hz_half_norm
            have htarget_eq :
                C * (1 + 2 * ‖z / 2‖) * Real.log (2 + 2 * ‖z / 2‖) =
                  C * (1 + ‖z‖) * Real.log (2 + ‖z‖) :=
              sectorialGammaEnvelope_halfArgument_eq C z
            calc
              Real.log ‖Complex.Gamma (z / 2)‖ ≤
                  C * (1 + 2 * ‖z / 2‖) * Real.log (2 + 2 * ‖z / 2‖) :=
                hraw
              _ = C * (1 + ‖z‖) * Real.log (2 + ‖z‖) :=
                htarget_eq⟩

/-- Real-part transport for the negative half argument. -/
theorem neg_halfArgument_re_eq_neg_re_div_two
    (z : ℂ) :
    (-z / 2 : ℂ).re = -z.re / 2 := by
  have hdiv : (-z / 2 : ℂ).re = (-z).re / (2 : ℝ) :=
    RCLike.div_re_ofReal (z := -z) (r := (2 : ℝ))
  have hneg : (-z).re = -z.re :=
    Complex.neg_re z
  calc
    (-z / 2 : ℂ).re = (-z).re / (2 : ℝ) := hdiv
    _ = -z.re / 2 := congrArg (fun x : ℝ => x / 2) hneg

/-- The real part of the negative half argument is nonpositive in the right half-plane. -/
theorem neg_halfArgument_re_nonpos_of_re_nonneg
    {z : ℂ}
    (hz_re : 0 ≤ z.re) :
    (-z / 2 : ℂ).re ≤ 0 := by
  have hdiv_nonpos : -z.re / 2 ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hz_re) zero_le_two
  calc
    (-z / 2 : ℂ).re = -z.re / 2 :=
      neg_halfArgument_re_eq_neg_re_div_two z
    _ ≤ 0 :=
      hdiv_nonpos

/-- Classical sectorial log-Gamma growth for the half-argument in the closed right
half-plane.

This is the exact missing special-function theorem: sectorial Stirling for
`Γ(w)` on `0 ≤ w.re`, transported to `w = z / 2` and measured against `‖z‖`;
cf. DLMF §5.11. -/
theorem sectorialComplexGammaStirling_halfArgument_rightHalfPlane_log_linear_growth_bound_degree_one :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
        1 ≤ ‖z‖ →
        Real.log ‖Complex.Gamma (z / 2)‖ ≤
          C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := fun hbranch => by
  exact
    sectorialComplexGammaStirling_halfArgument_rightHalfPlane_log_linear_growth_bound_degree_one_of_sectorial
      (sectorialComplexGammaStirling_rightHalfPlane_log_linear_growth_bound_degree_one hbranch)

/-- The `π ^ (-z / 2)` normalization contributes no positive log-growth in the right
half-plane. -/
theorem pi_cpow_neg_halfArgument_rightHalfPlane_log_norm_nonpos
    {z : ℂ}
    (hz_re : 0 ≤ z.re) :
    Real.log ‖(π : ℂ) ^ (-z / 2 : ℂ)‖ ≤ 0 := by
  have hpi_pos : (0 : ℝ) < π := Real.pi_pos
  have hpi_one_lt : (1 : ℝ) < π :=
    lt_trans (Nat.one_lt_ofNat : (1 : ℝ) < 3) Real.pi_gt_three
  have hre_nonpos : (-z / 2 : ℂ).re ≤ 0 := by
    exact neg_halfArgument_re_nonpos_of_re_nonneg hz_re
  have hnorm_eq : ‖(π : ℂ) ^ (-z / 2 : ℂ)‖ = π ^ (-z / 2 : ℂ).re := by
    exact Complex.abs_cpow_eq_rpow_re_of_pos hpi_pos (-z / 2 : ℂ)
  have hnorm_le_one : ‖(π : ℂ) ^ (-z / 2 : ℂ)‖ ≤ 1 := by
    exact hnorm_eq ▸
      Real.rpow_le_one_of_one_le_of_nonpos (le_of_lt hpi_one_lt) hre_nonpos
  have hnorm_pos : 0 < ‖(π : ℂ) ^ (-z / 2 : ℂ)‖ := by
    exact hnorm_eq ▸ Real.rpow_pos_of_pos hpi_pos (-z / 2 : ℂ).re
  exact Real.log_nonpos hnorm_pos.le hnorm_le_one

/-- The `π ^ (-z / 2)` normalization is bounded by the same log-linear envelope. -/
theorem pi_cpow_neg_halfArgument_rightHalfPlane_log_linear_growth_bound_degree_one :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        1 ≤ ‖z‖ →
        Real.log ‖(π : ℂ) ^ (-z / 2 : ℂ)‖ ≤
          C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
  exact
    ⟨1, zero_lt_one, fun z hz_re _hz_norm =>
      by
        have hlog_nonpos :
            Real.log ‖(π : ℂ) ^ (-z / 2 : ℂ)‖ ≤ 0 :=
          pi_cpow_neg_halfArgument_rightHalfPlane_log_norm_nonpos hz_re
        have hnorm_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
        have hleft_nonneg : 0 ≤ 1 + ‖z‖ :=
          add_nonneg zero_le_one hnorm_nonneg
        have hlog_arg_ge_one : (1 : ℝ) ≤ 2 + ‖z‖ :=
          one_le_two_add_complex_norm z
        have hlog_nonneg : 0 ≤ Real.log (2 + ‖z‖) :=
          Real.log_nonneg hlog_arg_ge_one
        have htarget_nonneg :
            0 ≤ (1 : ℝ) * (1 + ‖z‖) * Real.log (2 + ‖z‖) :=
          mul_nonneg (mul_nonneg zero_le_one hleft_nonneg) hlog_nonneg
        exact le_trans hlog_nonpos htarget_nonneg⟩

/-- Log norm of the normalized half-argument Gamma factor splits into the normalization
term and the Gamma term on the right-half-plane Stirling region. -/
theorem log_norm_halfArgument_normalized_complexGamma_le_sum_log_norm_factors
    {z : ℂ}
    (hz_re : 0 ≤ z.re)
    (hz_norm : 1 ≤ ‖z‖) :
    Real.log ‖(π : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)‖ ≤
      Real.log ‖(π : ℂ) ^ (-z / 2 : ℂ)‖ +
        Real.log ‖Complex.Gamma (z / 2)‖ := by
  have hpi_pos : 0 < ‖(π : ℂ) ^ (-z / 2 : ℂ)‖ := by
    have hpi_pos_real : (0 : ℝ) < π := Real.pi_pos
    have hnorm_eq : ‖(π : ℂ) ^ (-z / 2 : ℂ)‖ = π ^ (-z / 2 : ℂ).re := by
      exact Complex.abs_cpow_eq_rpow_re_of_pos hpi_pos_real (-z / 2 : ℂ)
    exact hnorm_eq ▸ Real.rpow_pos_of_pos hpi_pos_real (-z / 2 : ℂ).re
  have hgamma_pos : 0 < ‖Complex.Gamma (z / 2)‖ :=
    norm_pos_iff.mpr
      (ComplexGamma_halfArgument_ne_zero_of_re_nonneg_and_one_le_norm hz_re hz_norm)
  calc
    Real.log ‖(π : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)‖ =
        Real.log (‖(π : ℂ) ^ (-z / 2 : ℂ)‖ * ‖Complex.Gamma (z / 2)‖) := by
      exact congrArg Real.log
        (norm_mul ((π : ℂ) ^ (-z / 2 : ℂ)) (Complex.Gamma (z / 2)))
    _ ≤ Real.log ‖(π : ℂ) ^ (-z / 2 : ℂ)‖ +
        Real.log ‖Complex.Gamma (z / 2)‖ := by
      exact le_of_eq (Real.log_mul hpi_pos.ne' hgamma_pos.ne')

/-- Combining the sectorial Gamma estimate and the `π` normalization gives the normalized
half-argument estimate. -/
theorem halfArgument_normalized_rightHalfPlane_log_linear_growth_bound_degree_one_of_Gamma_and_pi
    (hGamma :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          0 < z.re →
          1 ≤ ‖z‖ →
          Real.log ‖Complex.Gamma (z / 2)‖ ≤
            C * (1 + ‖z‖) * Real.log (2 + ‖z‖))
    (hPi :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          1 ≤ ‖z‖ →
          Real.log ‖(π : ℂ) ^ (-z / 2 : ℂ)‖ ≤
            C * (1 + ‖z‖) * Real.log (2 + ‖z‖)) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
        1 ≤ ‖z‖ →
        Real.log ‖(π : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)‖ ≤
          C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
  match hGamma, hPi with
  | ⟨CGamma, hCGamma_pos, hCGamma⟩, ⟨CPi, hCPi_pos, hCPi⟩ =>
      exact
        ⟨CPi + CGamma, add_pos hCPi_pos hCGamma_pos, fun z hz_re hz_norm =>
          by
            have hsplit :
                Real.log ‖(π : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)‖ ≤
                  Real.log ‖(π : ℂ) ^ (-z / 2 : ℂ)‖ +
                    Real.log ‖Complex.Gamma (z / 2)‖ :=
              log_norm_halfArgument_normalized_complexGamma_le_sum_log_norm_factors
                (le_of_lt hz_re) hz_norm
            have hsum :
                Real.log ‖(π : ℂ) ^ (-z / 2 : ℂ)‖ +
                    Real.log ‖Complex.Gamma (z / 2)‖ ≤
                  CPi * (1 + ‖z‖) * Real.log (2 + ‖z‖) +
                    CGamma * (1 + ‖z‖) * Real.log (2 + ‖z‖) :=
              add_le_add (hCPi z (le_of_lt hz_re) hz_norm) (hCGamma z hz_re hz_norm)
            have hcombine :
                CPi * (1 + ‖z‖) * Real.log (2 + ‖z‖) +
                    CGamma * (1 + ‖z‖) * Real.log (2 + ‖z‖) =
                  (CPi + CGamma) * (1 + ‖z‖) * Real.log (2 + ‖z‖) :=
              logLinearEnvelope_add_constants
                CPi CGamma (1 + ‖z‖) (Real.log (2 + ‖z‖))
            exact le_trans hsplit (le_trans hsum (le_of_eq hcombine))⟩

/-- Sectorial complex Stirling in the normalized half-argument form needed by `Gammaℝ`.

This is the canonical classical special-function estimate: Stirling's expansion for
`Γ(z / 2)` in the closed right half-plane, with the harmless `π ^ (-z / 2)`
normalization absorbed into the constant; cf. DLMF §5.11. -/
theorem sectorialComplexGammaStirling_halfArgument_normalized_rightHalfPlane_log_linear_growth_bound_degree_one :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
        1 ≤ ‖z‖ →
        Real.log ‖(π : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)‖ ≤
          C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := fun hbranch => by
  exact
    halfArgument_normalized_rightHalfPlane_log_linear_growth_bound_degree_one_of_Gamma_and_pi
      (sectorialComplexGammaStirling_halfArgument_rightHalfPlane_log_linear_growth_bound_degree_one
        hbranch)
      pi_cpow_neg_halfArgument_rightHalfPlane_log_linear_growth_bound_degree_one

/-- The historical owner-root spelling for the sectorial complex Stirling estimate.

The proof is only name transport from the canonical sectorial `Complex.Gamma`
Stirling primitive. -/
theorem sectorialStirling_complexGamma_halfArgument_normalized_rightHalfPlane_log_linear_growth_bound_degree_one :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
        1 ≤ ‖z‖ →
        Real.log ‖(π : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)‖ ≤
          C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := fun hbranch => by
  exact
    sectorialComplexGammaStirling_halfArgument_normalized_rightHalfPlane_log_linear_growth_bound_degree_one
      hbranch

/-- Classical sectorial Stirling growth for the inline half-argument normalized Gamma
factor.

This is the smallest special-function input for the right-half-plane normalization:
complex Stirling for `π^(-z/2) Γ(z/2)` on `0 ≤ re z`, with `1 ≤ ‖z‖` excluding
the origin; cf. DLMF §5.11. -/
theorem classicalStirling_complexGamma_halfArgument_normalized_rightHalfPlane_log_linear_growth_bound_degree_one_from_sectorialStirling :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
        1 ≤ ‖z‖ →
        Real.log ‖(π : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)‖ ≤
          C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := fun hbranch => by
  exact
    sectorialStirling_complexGamma_halfArgument_normalized_rightHalfPlane_log_linear_growth_bound_degree_one
      hbranch

/-- Classical sectorial Stirling growth for the unfolded normalized real-Gamma factor.

This is the exact special-function input behind the right-half-plane `Gammaℝ`
normalization.  The proof is now only transport from the inline half-argument
Stirling input through the local unfolded name. -/
theorem classicalStirling_unfoldedNormalizedGammaℝFactor_rightHalfPlane_log_linear_growth_bound_degree_one_from_sectorialStirling :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
        1 ≤ ‖z‖ →
        Real.log ‖unfoldedNormalizedGammaℝFactor z‖ ≤
          C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := fun hbranch => by
  match
    classicalStirling_complexGamma_halfArgument_normalized_rightHalfPlane_log_linear_growth_bound_degree_one_from_sectorialStirling
      hbranch
  with
  | ⟨C, hC_pos, hbound⟩ =>
      exact
        ⟨C, hC_pos, fun z hz_re hz_norm =>
          calc
            Real.log ‖unfoldedNormalizedGammaℝFactor z‖ =
                Real.log ‖(π : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)‖ :=
              (log_norm_halfArgument_normalized_complexGamma_eq_log_norm_unfoldedNormalizedGammaℝFactor z).symm
            _ ≤ C * (1 + ‖z‖) * Real.log (2 + ‖z‖) :=
              hbound z hz_re hz_norm⟩

/-- Classical complex-Stirling growth for the half-argument normalized Gamma factor.

This is only the formula-level transport from the unfolded owner primitive to the
inline half-argument Gamma expression. -/
theorem classicalStirling_complexGamma_halfArgument_normalized_rightHalfPlane_log_linear_growth_bound_degree_one :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
        1 ≤ ‖z‖ →
        Real.log ‖(π : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)‖ ≤
          C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := fun hbranch => by
  match
    classicalStirling_unfoldedNormalizedGammaℝFactor_rightHalfPlane_log_linear_growth_bound_degree_one_from_sectorialStirling
      hbranch
  with
  | ⟨C, hC_pos, hbound⟩ =>
      exact
        ⟨C, hC_pos, fun z hz_re hz_norm =>
          calc
            Real.log ‖(π : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)‖ =
                Real.log ‖unfoldedNormalizedGammaℝFactor z‖ :=
              log_norm_halfArgument_normalized_complexGamma_eq_log_norm_unfoldedNormalizedGammaℝFactor z
            _ ≤ C * (1 + ‖z‖) * Real.log (2 + ‖z‖) :=
              hbound z hz_re hz_norm⟩

/-- Classical complex-Stirling growth for the unfolded normalized real-Gamma factor.

This theorem is only the definitional transport from the half-argument Gamma
formula to the local unfolded `Gammaℝ` name. -/
theorem classicalStirling_unfoldedNormalizedGammaℝFactor_rightHalfPlane_log_linear_growth_bound_degree_one :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
        1 ≤ ‖z‖ →
        Real.log ‖unfoldedNormalizedGammaℝFactor z‖ ≤
          C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := fun hbranch => by
  exact
    classicalStirling_unfoldedNormalizedGammaℝFactor_rightHalfPlane_log_linear_growth_bound_degree_one_from_sectorialStirling
      hbranch

/-- Classical Stirling growth for the completed real Gamma factor after unfolding
`Gammaℝ`.

This keeps the exact classical input in unfolded normalized form while exposing the
older formula spelling used by the surrounding normalization wrappers. -/
theorem classicalStirling_unfoldedGammaℝ_rightHalfPlane_log_linear_growth_bound_degree_one :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
        1 ≤ ‖z‖ →
        Real.log ‖(π : ℂ) ^ (-z / 2) * Complex.Gamma (z / 2)‖ ≤
          C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := fun hbranch => by
  exact classicalStirling_unfoldedNormalizedGammaℝFactor_rightHalfPlane_log_linear_growth_bound_degree_one
    hbranch

/-- The unfolded normalized classical Stirling estimate transfers to `Gammaℝ` by the
definitional normalization identity. -/
theorem Gammaℝ_rightHalfPlane_log_linear_growth_bound_degree_one_of_unfoldedNormalized
    (hStirling :
      ∃ C : ℝ,
        0 < C ∧
        ∀ z : ℂ,
          0 < z.re →
          1 ≤ ‖z‖ →
          Real.log ‖unfoldedNormalizedGammaℝFactor z‖ ≤
            C * (1 + ‖z‖) * Real.log (2 + ‖z‖)) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
        1 ≤ ‖z‖ →
        Real.log ‖Complex.Gammaℝ z‖ ≤
          C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := by
  match hStirling with
  | ⟨C, hC_pos, hC⟩ =>
      exact
        ⟨C, hC_pos, fun z hz_re hz_norm =>
          by
            calc
              Real.log ‖Complex.Gammaℝ z‖ =
                  Real.log ‖unfoldedNormalizedGammaℝFactor z‖ :=
                log_norm_Gammaℝ_eq_log_norm_unfoldedNormalizedGammaℝFactor z
              _ ≤ C * (1 + ‖z‖) * Real.log (2 + ‖z‖) :=
                hC z hz_re hz_norm⟩

/-- Classical right-half-plane logarithmic Stirling growth for the completed real Gamma
factor away from `0`, in the usual fixed-degree log-linear Stirling shape. -/
theorem classicalStirling_Gammaℝ_rightHalfPlane_log_linear_growth_bound_degree_one :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
        1 ≤ ‖z‖ →
        Real.log ‖Complex.Gammaℝ z‖ ≤
          C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := fun hbranch => by
  exact Gammaℝ_rightHalfPlane_log_linear_growth_bound_degree_one_of_unfoldedNormalized
    (classicalStirling_unfoldedNormalizedGammaℝFactor_rightHalfPlane_log_linear_growth_bound_degree_one
      hbranch)

/-- Standard right-half-plane logarithmic Stirling growth for the completed real Gamma
factor away from `0`, in the usual fixed-degree log-linear Stirling shape.

The exclusion `1 ≤ ‖z‖` is necessary for the classical right-half-plane Stirling
region; in Mathlib's finite-valued `Gammaℝ`, the classical pole faces are represented by
zeros, and this region avoids the zero at `0`. -/
theorem Gammaℝ_rightHalfPlane_stirling_log_linear_growth_bound_degree_one_standard :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ C : ℝ,
      0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
        1 ≤ ‖z‖ →
        Real.log ‖Complex.Gammaℝ z‖ ≤
          C * (1 + ‖z‖) * Real.log (2 + ‖z‖) := fun hbranch => by
  exact classicalStirling_Gammaℝ_rightHalfPlane_log_linear_growth_bound_degree_one hbranch

/-- Standard right-half-plane logarithmic Stirling growth for the completed real Gamma
factor away from `0`, converted from the fixed-degree owner statement into the finite
degree envelope used downstream. -/
theorem Gammaℝ_rightHalfPlane_stirling_log_linear_growth_bound_standard :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
        1 ≤ ‖z‖ →
        Real.log ‖Complex.Gammaℝ z‖ ≤
          C * (1 + ‖z‖) ^ m * Real.log (2 + ‖z‖) := fun hbranch => by
  match Gammaℝ_rightHalfPlane_stirling_log_linear_growth_bound_degree_one_standard hbranch with
  | ⟨C, hC_pos, hbound⟩ =>
      exact
        ⟨C, 1, hC_pos, fun z hz_re hz_norm =>
          by
            have hpow_one : (1 + ‖z‖) ^ (1 : ℕ) = 1 + ‖z‖ :=
              pow_one (1 + ‖z‖)
            calc
              Real.log ‖Complex.Gammaℝ z‖ ≤
                  C * (1 + ‖z‖) * Real.log (2 + ‖z‖) :=
                hbound z hz_re hz_norm
              _ = C * (1 + ‖z‖) ^ (1 : ℕ) * Real.log (2 + ‖z‖) :=
                congrArg (fun x : ℝ => C * x * Real.log (2 + ‖z‖))
                  hpow_one.symm⟩

/-- The shifted radius `2 + x` is `H + 1` when `H = 1 + x`. -/
theorem two_add_eq_one_add_radius_add_one
    (x H : ℝ)
    (hH : H = 1 + x) :
    2 + x = H + 1 := by
  calc
    2 + x = (1 + 1 : ℝ) + x := by
      exact congrArg (fun t : ℝ => t + x) one_add_one_eq_two.symm
    _ = 1 + (1 + x) := by
      exact add_assoc (1 : ℝ) 1 x
    _ = (1 + x) + 1 := by
      exact add_comm (1 : ℝ) (1 + x)
    _ = H + 1 := by
      exact congrArg (fun t : ℝ => t + 1) hH.symm

/-- The shifted radius is dominated by twice the base radius. -/
theorem two_add_le_two_mul_one_add_of_nonneg
    {x H : ℝ}
    (hH : H = 1 + x)
    (hone_le_H : (1 : ℝ) ≤ H) :
    2 + x ≤ 2 * H := by
  have harg_eq : 2 + x = H + 1 :=
    two_add_eq_one_add_radius_add_one x H hH
  have hsum_le : H + 1 ≤ H + H :=
    add_le_add_left hone_le_H H
  have htwo_mul : H + H = 2 * H :=
    (two_mul H).symm
  have hstart : 2 + x ≤ H + 1 := by
    calc
      2 + x = H + 1 := harg_eq
      _ ≤ H + 1 := le_refl (H + 1)
  exact le_trans hstart (le_trans hsum_le (le_of_eq htwo_mul))

/-- Product reassociation for absorbing one logarithmic radius into the finite-power envelope. -/
theorem logGrowth_absorbed_product_eq
    (C H : ℝ)
    (m : ℕ) :
    C * H ^ m * (2 * H) = (2 * C) * H ^ (m + 1) := by
  have htwo_mul : 2 * H = H + H :=
    two_mul H
  have hsplit :
      C * H ^ m * (H + H) = C * H ^ m * H + C * H ^ m * H :=
    mul_add (C * H ^ m) H H
  have hdouble :
      C * H ^ m * H + C * H ^ m * H = 2 * (C * H ^ m * H) :=
    (two_mul (C * H ^ m * H)).symm
  have hassoc_left :
      2 * (C * H ^ m * H) = (2 * C) * (H ^ m * H) := by
    calc
      2 * (C * H ^ m * H) = (2 * (C * H ^ m)) * H := by
        exact (mul_assoc (2 : ℝ) (C * H ^ m) H).symm
      _ = ((2 * C) * H ^ m) * H := by
        exact congrArg (fun t : ℝ => t * H) (mul_assoc (2 : ℝ) C (H ^ m)).symm
      _ = (2 * C) * (H ^ m * H) := by
        exact mul_assoc (2 * C) (H ^ m) H
  have hpow :
      (2 * C) * (H ^ m * H) = (2 * C) * H ^ (m + 1) :=
    congrArg (fun t : ℝ => (2 * C) * t) (pow_succ H m).symm
  calc
    C * H ^ m * (2 * H) = C * H ^ m * (H + H) := by
      exact congrArg (fun t : ℝ => C * H ^ m * t) htwo_mul
    _ = C * H ^ m * H + C * H ^ m * H := hsplit
    _ = 2 * (C * H ^ m * H) := hdouble
    _ = (2 * C) * (H ^ m * H) := hassoc_left
    _ = (2 * C) * H ^ (m + 1) := hpow

/-- The log-linear right-half-plane Stirling estimate implies the coarser finite-power
logarithmic envelope used by the completed-zeta normalization chain. -/
theorem Gammaℝ_rightHalfPlane_stirling_log_growth_bound_of_log_linear
    (hStirling :
      ∃ C : ℝ, ∃ m : ℕ,
        0 < C ∧
        ∀ z : ℂ,
          0 < z.re →
          1 ≤ ‖z‖ →
          Real.log ‖Complex.Gammaℝ z‖ ≤
            C * (1 + ‖z‖) ^ m * Real.log (2 + ‖z‖)) :
    ∃ C : ℝ, ∃ m : ℕ,
      ∀ z : ℂ,
        0 < z.re →
        1 ≤ ‖z‖ →
        Real.log ‖Complex.Gammaℝ z‖ ≤
          C * (1 + ‖z‖) ^ m := by
  match hStirling with
  | ⟨C, m, hC_pos, hbound⟩ =>
      exact
        ⟨2 * C, m + 1, fun z hz_re hz_norm =>
          by
            let H : ℝ := 1 + ‖z‖
            have hH_def : H = 1 + ‖z‖ :=
              rfl
            have hH_nonneg : 0 ≤ H :=
              le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))
            have hlog_arg_pos : 0 < 2 + ‖z‖ :=
              add_pos_of_pos_of_nonneg two_pos (norm_nonneg z)
            have hlog_le_arg :
                Real.log (2 + ‖z‖) ≤ 2 + ‖z‖ :=
              Real.log_le_self hlog_arg_pos.le
            have hone_le_H : (1 : ℝ) ≤ H :=
              le_add_of_nonneg_right (norm_nonneg z)
            have harg_le_twoH : 2 + ‖z‖ ≤ 2 * H :=
              two_add_le_two_mul_one_add_of_nonneg hH_def hone_le_H
            have hlog_le_twoH :
                Real.log (2 + ‖z‖) ≤ 2 * H :=
              le_trans hlog_le_arg harg_le_twoH
            have hleft_nonneg : 0 ≤ C * H ^ m :=
              mul_nonneg (le_of_lt hC_pos) (pow_nonneg hH_nonneg m)
            have hmul_log_le :
                C * H ^ m * Real.log (2 + ‖z‖) ≤ C * H ^ m * (2 * H) :=
              mul_le_mul_of_nonneg_left hlog_le_twoH hleft_nonneg
            have htarget_eq :
                C * H ^ m * (2 * H) = (2 * C) * H ^ (m + 1) :=
              logGrowth_absorbed_product_eq C H m
            exact
              calc
                Real.log ‖Complex.Gammaℝ z‖ ≤
                    C * H ^ m * Real.log (2 + ‖z‖) :=
                  hbound z hz_re hz_norm
                _ ≤ C * H ^ m * (2 * H) :=
                  hmul_log_le
                _ = (2 * C) * H ^ (m + 1) :=
                  htarget_eq⟩

/-- Standard right-half-plane logarithmic Stirling growth for the completed real Gamma
factor away from `0`. -/
theorem Gammaℝ_rightHalfPlane_stirling_log_growth_bound_standard :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ C : ℝ, ∃ m : ℕ,
      ∀ z : ℂ,
        0 < z.re →
        1 ≤ ‖z‖ →
        Real.log ‖Complex.Gammaℝ z‖ ≤
          C * (1 + ‖z‖) ^ m := fun hbranch => by
  exact Gammaℝ_rightHalfPlane_stirling_log_growth_bound_of_log_linear
    (Gammaℝ_rightHalfPlane_stirling_log_linear_growth_bound_standard hbranch)

/-- Right-half-plane logarithmic Stirling growth for the archimedean factor away from `0`.

This is the canonical owner primitive for Mathlib's completed real Gamma factor. -/
theorem Gammaℝ_rightHalfPlane_stirling_log_growth_bound_ownerPrimitive :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ C : ℝ, ∃ m : ℕ,
      ∀ z : ℂ,
        0 < z.re →
        1 ≤ ‖z‖ →
        Real.log ‖Complex.Gammaℝ z‖ ≤
          C * (1 + ‖z‖) ^ m := fun hbranch => by
  exact Gammaℝ_rightHalfPlane_stirling_log_growth_bound_standard hbranch

/-- Right-half-plane logarithmic Stirling growth for the archimedean factor away from `0`.

This public owner theorem is the thin wrapper used by the completed-normalization
finite-order chain. -/
theorem Gammaℝ_rightHalfPlane_stirling_log_growth_bound :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ C : ℝ, ∃ m : ℕ,
      ∀ z : ℂ,
        0 < z.re →
        1 ≤ ‖z‖ →
        Real.log ‖Complex.Gammaℝ z‖ ≤
          C * (1 + ‖z‖) ^ m := fun hbranch => by
  exact Gammaℝ_rightHalfPlane_stirling_log_growth_bound_ownerPrimitive hbranch

/-- Vertical-tail logarithmic Stirling estimate for `Gammaℝ` in the right critical strip. -/
theorem Gammaℝ_rightCriticalStrip_verticalTail_stirling_log_growth_bound :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ C : ℝ, ∃ m : ℕ,
      ∀ z : ℂ,
        0 < z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        Real.log ‖Complex.Gammaℝ z‖ ≤
          C * (1 + ‖z‖) ^ m := fun hbranch => by
  match Gammaℝ_rightHalfPlane_stirling_log_growth_bound hbranch with
  | ⟨C, m, hC⟩ =>
      exact
        ⟨C, m, fun z hz0 _hz2 hzim =>
          hC z hz0 (one_le_norm_of_one_le_norm_im hzim)⟩

/-- Exponentiated right-half-plane Stirling growth for `Gammaℝ`, away from the pole at `0`. -/
theorem Gammaℝ_rightHalfPlane_stirling_growth_bound :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 < z.re →
        1 ≤ ‖z‖ →
        ‖Complex.Gammaℝ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := fun hbranch => by
  have hlog_growth :
      ∃ C : ℝ, ∃ m : ℕ,
        ∀ z : ℂ,
          (0 < z.re ∧ 1 ≤ ‖z‖) →
          Real.log ‖Complex.Gammaℝ z‖ ≤ C * (1 + ‖z‖) ^ m := by
    match Gammaℝ_rightHalfPlane_stirling_log_growth_bound hbranch with
    | ⟨C, m, hC⟩ =>
        exact ⟨C, m, fun z hz => hC z hz.1 hz.2⟩
  match
    Gammaℝ_finiteOrder_growth_bound_of_log_growth_on_region
      (fun z : ℂ => 0 < z.re ∧ 1 ≤ ‖z‖)
      hlog_growth
  with
  | ⟨A, B, m, hA, hB, hbound⟩ =>
      exact
        ⟨A, B, m, hA, hB, fun z hz_re hz_norm =>
          hbound z ⟨hz_re, hz_norm⟩⟩

/-- Vertical-tail Stirling estimate for `Gammaℝ` in the right critical strip.

This is a standard analytic primitive for the zero ledger: it supplies the
archimedean part of finite-order control on the completed zero packet. -/
theorem Gammaℝ_rightCriticalStrip_verticalTail_stirling_growth_bound :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 < z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖Complex.Gammaℝ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := fun hbranch => by
  match Gammaℝ_rightHalfPlane_stirling_growth_bound hbranch with
  | ⟨A, B, m, hA, hB, hbound⟩ =>
      exact
        ⟨A, B, m, hA, hB, fun z hz0 _hz2 hzim =>
          hbound z hz0 (one_le_norm_of_one_le_norm_im hzim)⟩

end
end LFunctions
end Boundary
