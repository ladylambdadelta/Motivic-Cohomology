import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.BinetKernel.Owner

/-!
# Normalized Stirling bridge for Gamma

This file owns the bridge from the Binet remainder package to the normalized
sectorial Stirling estimate.  It is placed between the Binet kernel layer and
the sectorial log layer so the proof graph stays acyclic.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology

/-- Binet's logarithmic formula implies the normalized sectorial Stirling
estimate for `Γ`.

This is the bridge from the Binet remainder control to the normalized
Stirling factor. -/
theorem Complex.sectorialStirling_normalizedGamma_closedRightHalfPlane_from_binetSecondFormula :
    ∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        0 < w.re →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖ := by
  match
      Complex.binetSecondFormula_logGamma_with_remainder_bound_closedRightHalfPlane_requires_tail_absorption with
  | ⟨R, K, hR, hK, hBinet⟩ =>
    let R' : ℝ := max R K
    let K' : ℝ := 2 * Real.sqrt (2 * Real.pi) * K
    have hR' : 0 < R' :=
      lt_of_lt_of_le hR (le_max_left R K)
    have hsqrt_pos : 0 < Real.sqrt (2 * Real.pi) :=
      Real.sqrt_pos_of_pos (mul_pos two_pos Real.pi_pos)
    have hK' : 0 < K' := by
      have htwo_sqrt_pos : 0 < 2 * Real.sqrt (2 * Real.pi) :=
        mul_pos two_pos hsqrt_pos
      exact mul_pos htwo_sqrt_pos hK
    exact
      ⟨R', K', hR', hK',
        fun w hw_re_pos hw_radius =>
          have hR_le : R ≤ ‖w‖ :=
            le_trans (le_max_left R K) hw_radius
          have hK_le : K ≤ ‖w‖ :=
            le_trans (le_max_right R K) hw_radius
          match hBinet w hw_re_pos hR_le with
          | ⟨hlog, hrem⟩ =>
            let E : ℂ := Complex.binetSecondFormulaRemainder w
            have hnorm_pos : 0 < ‖w‖ :=
              lt_of_lt_of_le hR' hw_radius
            have hsmall : ‖E‖ ≤ 1 := by
              have hdiv_le_one : K / ‖w‖ ≤ 1 :=
                (div_le_one₀ hnorm_pos.le).mpr hK_le
              exact hrem.trans hdiv_le_one
            have hw_ne : w ≠ 0 :=
              norm_pos_iff.mp hnorm_pos
            have hGamma_ne : Complex.Gamma w ≠ 0 :=
              Complex.Gamma_ne_zero_of_re_pos hw_re_pos
            have hlinear :
                ‖Complex.Gamma w * Complex.exp w *
                    w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
                  2 * Real.sqrt (2 * Real.pi) * ‖E‖ :=
              Complex.normalizedGammaStirlingFactor_sub_sqrt_two_pi_norm_le_of_binetRemainder_norm_le_one
                hGamma_ne hw_ne hlog hsmall
            have hscale :
                2 * Real.sqrt (2 * Real.pi) * ‖E‖ ≤
                  K' / ‖w‖ := by
              have hconst_nonneg : 0 ≤ 2 * Real.sqrt (2 * Real.pi) :=
                le_of_lt (mul_pos two_pos hsqrt_pos)
              have hmul_rem :
                  2 * Real.sqrt (2 * Real.pi) * ‖E‖ ≤
                    2 * Real.sqrt (2 * Real.pi) * (K / ‖w‖) :=
                mul_le_mul_of_nonneg_left hrem hconst_nonneg
              have htarget_eq :
                  2 * Real.sqrt (2 * Real.pi) * (K / ‖w‖) = K' / ‖w‖ := by
                calc
                  2 * Real.sqrt (2 * Real.pi) * (K / ‖w‖) =
                      (2 * Real.sqrt (2 * Real.pi) * K) / ‖w‖ := by
                    exact (mul_div_assoc (2 * Real.sqrt (2 * Real.pi)) K ‖w‖).symm
                  _ = K' / ‖w‖ := rfl
              exact hmul_rem.trans_eq htarget_eq
            hlinear.trans hscale⟩

end
end LFunctions
end Boundary
