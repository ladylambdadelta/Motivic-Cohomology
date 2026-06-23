import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.VerticalRecurrence.VerticalStrip.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.SectorialLog.Owner

/-!
# Vertical recurrence: sectorial Stirling transport

This file owns the sectorial transport shift definitions and the sectorial
Stirling normalized form for shifted real-part Gamma bounds.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- The deterministic strip shift written as a local abbreviation for the
vertical-strip Stirling transport. -/
def Complex.verticalStripTransportShift (A : ℝ) : ℕ :=
  Complex.verticalStripRightShift A

/-- The deterministic transport shift moves the strip into the closed right
half-plane. -/
theorem Complex.verticalStripTransportShift_closedRightHalfPlaneSector
    {A x y : ℝ}
    (hx : A ≤ x) :
    Complex.closedRightHalfPlaneSector
      (Complex.fixedRealPartVerticalPoint
        (x + Complex.verticalStripTransportShift A) y) := by
  exact
    Complex.fixedRealPartVerticalPoint_verticalStripRightShift_closedRightHalfPlaneSector
      hx

/-- The deterministic transport shift moves the strip into the strict right
half-plane. -/
theorem Complex.verticalStripTransportShift_re_pos
    {A x y : ℝ}
    (hx : A ≤ x) :
    0 <
      (Complex.fixedRealPartVerticalPoint
        (x + Complex.verticalStripTransportShift A) y).re := by
  exact
    Complex.fixedRealPartVerticalPoint_verticalStripRightShift_re_pos
      hx

/-- Large vertical height gives the sectorial radius cutoff after the
deterministic transport shift. -/
theorem Complex.verticalStripTransportShift_radius_ge_of_height_ge
    {A x y H : ℝ}
    (hH : H ≤ ‖y‖) :
    H ≤
      ‖Complex.fixedRealPartVerticalPoint
        (x + Complex.verticalStripTransportShift A) y‖ := by
  exact
    Complex.fixedRealPartVerticalPoint_verticalStripRightShift_radius_ge_of_height_ge
      hH

/-- The deterministic transport shift is the complex horizontal translation
appearing in the finite Gamma recurrence. -/
theorem Complex.fixedRealPartVerticalPoint_add_verticalStripTransportShift
    (A x y : ℝ) :
    Complex.fixedRealPartVerticalPoint
        (x + Complex.verticalStripTransportShift A) y =
      Complex.fixedRealPartVerticalPoint x y +
        (Complex.verticalStripTransportShift A : ℂ) := by
  exact Complex.fixedRealPartVerticalPoint_add_verticalStripRightShift A x y

/-- Sectorial Stirling gives uniform two-sided bounds for the normalized
Stirling factor on the deterministically shifted vertical strip. -/
theorem Complex.sectorialStirling_shiftedNormalizedFactor_twoSided_bounds
    (hStirling : ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖)
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
    ‖Complex.Gamma
              (Complex.fixedRealPartVerticalPoint
                (x + Complex.verticalStripTransportShift A) y) *
              Complex.exp
                (Complex.fixedRealPartVerticalPoint
                  (x + Complex.verticalStripTransportShift A) y) *
              (Complex.fixedRealPartVerticalPoint
                (x + Complex.verticalStripTransportShift A) y) ^
                ((1 / 2 : ℂ) -
                  Complex.fixedRealPartVerticalPoint
                    (x + Complex.verticalStripTransportShift A) y)‖ ≤ C ∧
          c ≤
            ‖Complex.Gamma
              (Complex.fixedRealPartVerticalPoint
                (x + Complex.verticalStripTransportShift A) y) *
              Complex.exp
                (Complex.fixedRealPartVerticalPoint
                  (x + Complex.verticalStripTransportShift A) y) *
              (Complex.fixedRealPartVerticalPoint
                (x + Complex.verticalStripTransportShift A) y) ^
                ((1 / 2 : ℂ) -
                  Complex.fixedRealPartVerticalPoint
                    (x + Complex.verticalStripTransportShift A) y)‖ := by
  match hStirling with
  | ⟨R, K, hR_pos, hK_pos, hStirling_pointwise⟩ =>
      let s : ℝ := Real.sqrt (2 * Real.pi)
      let H : ℝ := max R (max (4 * K / s) 1)
      have hH_pos : 0 < H :=
        lt_of_lt_of_le zero_lt_one
          (le_trans
            (le_max_right (4 * K / s) 1)
            (le_max_right R (max (4 * K / s) 1)))
      have hC_pos : 0 < 2 * s :=
        mul_pos two_pos (Real.sqrt_pos.mpr (mul_pos two_pos Real.pi_pos))
      have hc_pos : 0 < s / 2 :=
        half_pos (Real.sqrt_pos.mpr (mul_pos two_pos Real.pi_pos))
      have hpointwise :
          ∀ x y : ℝ,
            A ≤ x →
            x ≤ B →
            H ≤ ‖y‖ →
              ‖Complex.Gamma
                  (Complex.fixedRealPartVerticalPoint
                    (x + Complex.verticalStripTransportShift A) y) *
                  Complex.exp
                    (Complex.fixedRealPartVerticalPoint
                      (x + Complex.verticalStripTransportShift A) y) *
                  (Complex.fixedRealPartVerticalPoint
                    (x + Complex.verticalStripTransportShift A) y) ^
                    ((1 / 2 : ℂ) -
                      Complex.fixedRealPartVerticalPoint
                        (x + Complex.verticalStripTransportShift A) y)‖ ≤ 2 * s ∧
              s / 2 ≤
                ‖Complex.Gamma
                  (Complex.fixedRealPartVerticalPoint
                    (x + Complex.verticalStripTransportShift A) y) *
                  Complex.exp
                    (Complex.fixedRealPartVerticalPoint
                      (x + Complex.verticalStripTransportShift A) y) *
                  (Complex.fixedRealPartVerticalPoint
                    (x + Complex.verticalStripTransportShift A) y) ^
                    ((1 / 2 : ℂ) -
                      Complex.fixedRealPartVerticalPoint
                        (x + Complex.verticalStripTransportShift A) y)‖ := by
        intro x y hxA _hxB hy
        let w : ℂ :=
          Complex.fixedRealPartVerticalPoint
            (x + Complex.verticalStripTransportShift A) y
        have hw_sector : Complex.closedRightHalfPlaneSector w :=
          Complex.verticalStripTransportShift_closedRightHalfPlaneSector hxA
        have hw_radius_H : H ≤ ‖w‖ :=
          Complex.verticalStripTransportShift_radius_ge_of_height_ge hy
        have hw_R : R ≤ ‖w‖ :=
          le_trans (le_max_left R (max (4 * K / s) 1)) hw_radius_H
        have hw_one : 1 ≤ ‖w‖ :=
          le_trans
            (le_trans
              (le_max_right (4 * K / s) 1)
              (le_max_right R (max (4 * K / s) 1)))
            hw_radius_H
        have hw_norm_pos : 0 < ‖w‖ :=
          lt_of_lt_of_le zero_lt_one hw_one
        have hw_cutoff_half : 4 * K / s ≤ ‖w‖ :=
          le_trans
            (le_trans
              (le_max_left (4 * K / s) 1)
              (le_max_right R (max (4 * K / s) 1)))
            hw_radius_H
        have herror_half :
            K / ‖w‖ ≤ s / 2 :=
          real_stirlingError_div_norm_le_half_sqrt_two_pi_of_cutoff
            K ‖w‖ hK_pos hw_norm_pos hw_cutoff_half
        have hhalf_le_s : s / 2 ≤ s := by
          have hs_nonneg : 0 ≤ s :=
            Real.sqrt_nonneg (2 * Real.pi)
          exact
            (div_le_iff₀ zero_lt_two).mpr
              (by
                calc
                  s ≤ s + s := le_add_of_nonneg_right hs_nonneg
                  _ = 2 * s := (two_mul s).symm
                  _ = s * 2 := mul_comm 2 s)
        have herror_full :
            K / ‖w‖ ≤ s :=
          le_trans herror_half hhalf_le_s
        constructor
        · exact
            Complex.normalizedGammaFactor_norm_le_two_sqrt_two_pi_of_exponentialStirling_error
              R K hStirling_pointwise w hw_sector hw_R herror_full
        · exact
            Complex.half_sqrt_two_pi_le_normalizedGammaFactor_norm_of_exponentialStirling_error
              R K hStirling_pointwise w hw_sector hw_R herror_half
      exact ⟨H, 2 * s, s / 2, hH_pos, hC_pos, hc_pos, hpointwise⟩

/-- Branch-package sectorial Stirling gives uniform two-sided bounds for the
normalized Stirling factor on the deterministically shifted vertical strip.

The deterministic shift has real part at least `1`, so the strict
right-half-plane hypotheses in the Binet owner theorem are satisfied at every
shifted strip point. -/
theorem Complex.sectorialStirling_shiftedNormalizedFactor_twoSided_bounds_of_branchPackage
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
    ‖Complex.Gamma
              (Complex.fixedRealPartVerticalPoint
                (x + Complex.verticalStripTransportShift A) y) *
              Complex.exp
                (Complex.fixedRealPartVerticalPoint
                  (x + Complex.verticalStripTransportShift A) y) *
              (Complex.fixedRealPartVerticalPoint
                (x + Complex.verticalStripTransportShift A) y) ^
                ((1 / 2 : ℂ) -
                  Complex.fixedRealPartVerticalPoint
                    (x + Complex.verticalStripTransportShift A) y)‖ ≤ C ∧
          c ≤
            ‖Complex.Gamma
              (Complex.fixedRealPartVerticalPoint
                (x + Complex.verticalStripTransportShift A) y) *
              Complex.exp
                (Complex.fixedRealPartVerticalPoint
                  (x + Complex.verticalStripTransportShift A) y) *
              (Complex.fixedRealPartVerticalPoint
                (x + Complex.verticalStripTransportShift A) y) ^
                ((1 / 2 : ℂ) -
                  Complex.fixedRealPartVerticalPoint
                    (x + Complex.verticalStripTransportShift A) y)‖ := by
  match Complex.sectorialStirling_normalizedGamma_closedRightHalfPlane hbranch with
  | ⟨R, K, hR_pos, hK_pos, hStirling_pointwise⟩ =>
      let s : ℝ := Real.sqrt (2 * Real.pi)
      let H : ℝ := max R (max (4 * K / s) 1)
      have hH_pos : 0 < H :=
        lt_of_lt_of_le zero_lt_one
          (le_trans
            (le_max_right (4 * K / s) 1)
            (le_max_right R (max (4 * K / s) 1)))
      have hC_pos : 0 < 2 * s :=
        mul_pos two_pos (Real.sqrt_pos.mpr (mul_pos two_pos Real.pi_pos))
      have hc_pos : 0 < s / 2 :=
        half_pos (Real.sqrt_pos.mpr (mul_pos two_pos Real.pi_pos))
      have hcoh :
          Complex.BinetSecondFormulaBranchCoherence :=
        Complex.BinetSecondFormulaBranchUniformTailAbsorption.coherence
          hbranch
      have hfinite_real :
          ∀ x : ℝ,
            0 < x →
              ∀ N : ℕ,
                Complex.binetAbelPlanaLogGammaFiniteApproximation N (x : ℂ) =
                  Complex.binetAbelPlanaFiniteMainTerm N (x : ℂ) +
                    Complex.binetAbelPlanaFiniteBoundaryCorrection N (x : ℂ) +
                      Complex.binetAbelPlanaFiniteContourRemainder N (x : ℂ) :=
        hcoh.2.1
      have hfinite_open :
          ∀ z : ℂ,
            0 < z.re →
              (∀ N : ℕ,
                Complex.binetAbelPlanaLogGammaFiniteApproximation N z =
                  Complex.binetAbelPlanaFiniteMainTerm N z +
                    Complex.binetAbelPlanaFiniteBoundaryCorrection N z +
                      Complex.binetAbelPlanaFiniteContourRemainder N z) ∧
              (∀ᶠ y : ℂ in 𝓝 z,
                ∀ N : ℕ,
                  Complex.binetAbelPlanaLogGammaFiniteApproximation N y =
                    Complex.binetAbelPlanaFiniteMainTerm N y +
                      Complex.binetAbelPlanaFiniteBoundaryCorrection N y +
                        Complex.binetAbelPlanaFiniteContourRemainder N y) :=
        hcoh.2.2
      have hpointwise :
          ∀ x y : ℝ,
            A ≤ x →
            x ≤ B →
            H ≤ ‖y‖ →
              ‖Complex.Gamma
                  (Complex.fixedRealPartVerticalPoint
                    (x + Complex.verticalStripTransportShift A) y) *
                  Complex.exp
                    (Complex.fixedRealPartVerticalPoint
                      (x + Complex.verticalStripTransportShift A) y) *
                  (Complex.fixedRealPartVerticalPoint
                    (x + Complex.verticalStripTransportShift A) y) ^
                    ((1 / 2 : ℂ) -
                      Complex.fixedRealPartVerticalPoint
                        (x + Complex.verticalStripTransportShift A) y)‖ ≤ 2 * s ∧
              s / 2 ≤
                ‖Complex.Gamma
                  (Complex.fixedRealPartVerticalPoint
                    (x + Complex.verticalStripTransportShift A) y) *
                  Complex.exp
                    (Complex.fixedRealPartVerticalPoint
                      (x + Complex.verticalStripTransportShift A) y) *
                  (Complex.fixedRealPartVerticalPoint
                    (x + Complex.verticalStripTransportShift A) y) ^
                    ((1 / 2 : ℂ) -
                      Complex.fixedRealPartVerticalPoint
                        (x + Complex.verticalStripTransportShift A) y)‖ := by
        intro x y hxA _hxB hy
        let w : ℂ :=
          Complex.fixedRealPartVerticalPoint
            (x + Complex.verticalStripTransportShift A) y
        have hw_re_pos : 0 < w.re :=
          Complex.verticalStripTransportShift_re_pos hxA
        have hw_sector : Complex.closedRightHalfPlaneSector w :=
          Complex.verticalStripTransportShift_closedRightHalfPlaneSector hxA
        have hw_radius_H : H ≤ ‖w‖ :=
          Complex.verticalStripTransportShift_radius_ge_of_height_ge hy
        have hw_R : R ≤ ‖w‖ :=
          le_trans (le_max_left R (max (4 * K / s) 1)) hw_radius_H
        have hw_one : 1 ≤ ‖w‖ :=
          le_trans
            (le_trans
              (le_max_right (4 * K / s) 1)
              (le_max_right R (max (4 * K / s) 1)))
            hw_radius_H
        have hw_norm_pos : 0 < ‖w‖ :=
          lt_of_lt_of_le zero_lt_one hw_one
        have hw_cutoff_half : 4 * K / s ≤ ‖w‖ :=
          le_trans
            (le_trans
              (le_max_left (4 * K / s) 1)
              (le_max_right R (max (4 * K / s) 1)))
            hw_radius_H
        have herror_half :
            K / ‖w‖ ≤ s / 2 :=
          real_stirlingError_div_norm_le_half_sqrt_two_pi_of_cutoff
            K ‖w‖ hK_pos hw_norm_pos hw_cutoff_half
        have hhalf_le_s : s / 2 ≤ s := by
          have hs_nonneg : 0 ≤ s :=
            Real.sqrt_nonneg (2 * Real.pi)
          exact
            (div_le_iff₀ zero_lt_two).mpr
              (by
                calc
                  s ≤ s + s := le_add_of_nonneg_right hs_nonneg
                  _ = 2 * s := (two_mul s).symm
                  _ = s * 2 := mul_comm 2 s)
        have herror_full :
            K / ‖w‖ ≤ s :=
          le_trans herror_half hhalf_le_s
        have hStirling_w :
            ‖Complex.Gamma w * Complex.exp w *
                w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
              K / ‖w‖ :=
          hStirling_pointwise w hw_re_pos hw_sector hw_R
            hfinite_real hfinite_open
        constructor
        · exact
            Complex.normalizedGammaFactor_norm_le_two_sqrt_two_pi_of_pointwise_exponentialStirling_error
              K w hStirling_w herror_full
        · exact
            Complex.half_sqrt_two_pi_le_norm_of_norm_sub_sqrt_two_pi_le_half
              (Complex.Gamma w * Complex.exp w * w ^ ((1 / 2 : ℂ) - w))
              (le_trans hStirling_w herror_half)
      exact ⟨H, 2 * s, s / 2, hH_pos, hC_pos, hc_pos, hpointwise⟩

/-- Positivity of the exponential/power denominator in normalized Stirling away
from the origin. -/
theorem Complex.stirlingDenominator_pos_of_ne_zero
    {w : ℂ}
    (hw_ne : w ≠ 0) :
    0 < ‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖ := by
  have hexp_pos : 0 < ‖Complex.exp w‖ :=
    norm_pos_iff.mpr (Complex.exp_ne_zero w)
  have hcpow_ne : w ^ ((1 / 2 : ℂ) - w) ≠ 0 := by
    intro hzero
    have hbase_zero : w = 0 :=
      ((Complex.cpow_eq_zero_iff w ((1 / 2 : ℂ) - w)).mp hzero).1
    exact hw_ne hbase_zero
  have hcpow_pos : 0 < ‖w ^ ((1 / 2 : ℂ) - w)‖ :=
    norm_pos_iff.mpr hcpow_ne
  exact mul_pos hexp_pos hcpow_pos

end

end LFunctions
end Boundary
