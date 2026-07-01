import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.VerticalRecurrence.Sectorial.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.VerticalRecurrence.Angular.Denominator

/-!
# Shifted fixed vertical Gamma envelope bounds

This subowner contains the shifted fixed-vertical Gamma envelope transports.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- Pointwise transport from normalized Stirling-factor bounds and reciprocal
denominator comparison to raw Gamma envelope bounds. -/
theorem Complex.shiftedRawGammaEnvelope_pointwise_of_normalized_factor_and_denominator
    {w : ℂ}
    {E Cn cn Cd cd : ℝ}
    (hD_pos : 0 < ‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖)
    (hrecip_upper :
      1 / (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) ≤ Cd * E)
    (hrecip_lower :
      cd * E ≤
        1 / (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖))
    (hnorm_upper :
      ‖Complex.Gamma w * Complex.exp w *
          w ^ ((1 / 2 : ℂ) - w)‖ ≤ Cn)
    (hnorm_lower :
      cn ≤
        ‖Complex.Gamma w * Complex.exp w *
          w ^ ((1 / 2 : ℂ) - w)‖)
    (hCn_pos : 0 < Cn)
    (hcn_pos : 0 < cn) :
    ‖Complex.Gamma w‖ ≤ (Cn * Cd) * E ∧
      (cn * cd) * E ≤ ‖Complex.Gamma w‖ := by
  let D : ℝ := ‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖
  have hgamma_upper_raw :
      ‖Complex.Gamma w‖ ≤ Cn / D :=
    Complex.Gamma_norm_le_of_normalizedGammaStirlingFactor_norm_le
      w Cn hnorm_upper hD_pos
  have hgamma_lower_raw :
      cn / D ≤ ‖Complex.Gamma w‖ :=
    Complex.Gamma_norm_ge_of_normalizedGammaStirlingFactor_norm_ge
      w cn hnorm_lower hD_pos
  have hCn_nonneg : 0 ≤ Cn :=
    le_of_lt hCn_pos
  have hcn_nonneg : 0 ≤ cn :=
    le_of_lt hcn_pos
  have hupper_scale :
      Cn / D ≤ (Cn * Cd) * E := by
    have hdiv_eq : Cn / D = Cn * (1 / D) := by
      calc
        Cn / D = Cn * D⁻¹ := div_eq_mul_inv Cn D
        _ = Cn * (1 / D) := by
          exact congrArg (fun u : ℝ => Cn * u) (one_div D).symm
    have hmul :
        Cn * (1 / D) ≤ Cn * (Cd * E) :=
      mul_le_mul_of_nonneg_left hrecip_upper hCn_nonneg
    have htarget :
        Cn * (Cd * E) = (Cn * Cd) * E :=
      (mul_assoc Cn Cd E).symm
    exact le_trans (le_of_eq hdiv_eq)
      (le_trans hmul (le_of_eq htarget))
  have hlower_scale :
      (cn * cd) * E ≤ cn / D := by
    have hleft_assoc :
        (cn * cd) * E = cn * (cd * E) :=
      mul_assoc cn cd E
    have hmul :
        cn * (cd * E) ≤ cn * (1 / D) :=
      mul_le_mul_of_nonneg_left hrecip_lower hcn_nonneg
    have hdiv_eq : cn * (1 / D) = cn / D := by
      calc
        cn * (1 / D) = cn * D⁻¹ := by
          exact congrArg (fun u : ℝ => cn * u) (one_div D)
        _ = cn / D := (div_eq_mul_inv cn D).symm
    exact le_trans (le_of_eq hleft_assoc)
      (le_trans hmul (le_of_eq hdiv_eq))
  exact
    And.intro
      (le_trans hgamma_upper_raw hupper_scale)
      (le_trans hlower_scale hgamma_lower_raw)

theorem Complex.sectorialStirling_shiftedRawGammaEnvelope_of_normalizedStirling
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
                (x + Complex.verticalStripTransportShift A) y)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope
              (x + Complex.verticalStripTransportShift A) y ∧
            c * Complex.fixedRealPartVerticalStirlingEnvelope
              (x + Complex.verticalStripTransportShift A) y ≤
            ‖Complex.Gamma
              (Complex.fixedRealPartVerticalPoint
                (x + Complex.verticalStripTransportShift A) y)‖ := by
  match Complex.sectorialStirling_shiftedNormalizedFactor_twoSided_bounds
      hStirling A B with
  | ⟨Hn, Cn, cn, hHn_pos, hCn_pos, hcn_pos, hnormalized⟩ =>
  match Complex.shiftedVerticalStirlingDenominator_reciprocal_comparable A B with
  | ⟨Hd, Cd, cd, hHd_pos, hCd_pos, hcd_pos, hdenom⟩ =>
    let H : ℝ := max Hn Hd
    exact
      ⟨H, Cn * Cd, cn * cd,
        lt_of_lt_of_le hHn_pos (le_max_left Hn Hd),
        mul_pos hCn_pos hCd_pos,
        mul_pos hcn_pos hcd_pos,
        fun x y hxA hxB hy =>
          have hy_n : Hn ≤ ‖y‖ :=
            le_trans (le_max_left Hn Hd) hy
          have hy_d : Hd ≤ ‖y‖ :=
            le_trans (le_max_right Hn Hd) hy
          let w : ℂ :=
            Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y
          let E : ℝ :=
            Complex.fixedRealPartVerticalStirlingEnvelope
              (x + Complex.verticalStripTransportShift A) y
          let D : ℝ :=
            ‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖
          have hnormalized_xy := hnormalized x y hxA hxB hy_n
          have hdenom_xy := hdenom x y hxA hxB hy_d
          Complex.shiftedRawGammaEnvelope_pointwise_of_normalized_factor_and_denominator
            hdenom_xy.1 hdenom_xy.2.1 hdenom_xy.2.2
            hnormalized_xy.1 hnormalized_xy.2 hCn_pos hcn_pos⟩

/-- Branch-package shifted raw Gamma envelope bounds.

This is the same denominator transport as
`sectorialStirling_shiftedRawGammaEnvelope_of_normalizedStirling`, but it
consumes the full Binet branch package directly so the strict right-half-plane
and coherence hypotheses are discharged at the shifted-strip owner level. -/
theorem Complex.sectorialStirling_shiftedRawGammaEnvelope_of_branchPackage
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
                (x + Complex.verticalStripTransportShift A) y)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope
              (x + Complex.verticalStripTransportShift A) y ∧
            c * Complex.fixedRealPartVerticalStirlingEnvelope
              (x + Complex.verticalStripTransportShift A) y ≤
            ‖Complex.Gamma
              (Complex.fixedRealPartVerticalPoint
                (x + Complex.verticalStripTransportShift A) y)‖ := by
  match Complex.sectorialStirling_shiftedNormalizedFactor_twoSided_bounds_of_branchPackage
      hbranch A B with
  | ⟨Hn, Cn, cn, hHn_pos, hCn_pos, hcn_pos, hnormalized⟩ =>
  match Complex.shiftedVerticalStirlingDenominator_reciprocal_comparable A B with
  | ⟨Hd, Cd, cd, hHd_pos, hCd_pos, hcd_pos, hdenom⟩ =>
    let H : ℝ := max Hn Hd
    exact
      ⟨H, Cn * Cd, cn * cd,
        lt_of_lt_of_le hHn_pos (le_max_left Hn Hd),
        mul_pos hCn_pos hCd_pos,
        mul_pos hcn_pos hcd_pos,
        fun x y hxA hxB hy =>
          have hy_n : Hn ≤ ‖y‖ :=
            le_trans (le_max_left Hn Hd) hy
          have hy_d : Hd ≤ ‖y‖ :=
            le_trans (le_max_right Hn Hd) hy
          let w : ℂ :=
            Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y
          let E : ℝ :=
            Complex.fixedRealPartVerticalStirlingEnvelope
              (x + Complex.verticalStripTransportShift A) y
          let D : ℝ :=
            ‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖
          have hnormalized_xy := hnormalized x y hxA hxB hy_n
          have hdenom_xy := hdenom x y hxA hxB hy_d
          Complex.shiftedRawGammaEnvelope_pointwise_of_normalized_factor_and_denominator
            hdenom_xy.1 hdenom_xy.2.1 hdenom_xy.2.2
            hnormalized_xy.1 hnormalized_xy.2 hCn_pos hcn_pos⟩

end
end LFunctions
end Boundary
