import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.VerticalRecurrence.Sectorial.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.VerticalRecurrence.Owner

/-!
# Fixed vertical Gamma envelope bounds

This file is a sequential owner sublayer split out of
`ZetaCompletedNormalization.GammaStirlingNormalization.Owner`.  Declaration order is preserved.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

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
          have hD_pos : 0 < D :=
            hdenom_xy.1
          have hrecip_upper : 1 / D ≤ Cd * E :=
            hdenom_xy.2.1
          have hrecip_lower : cd * E ≤ 1 / D :=
            hdenom_xy.2.2
          have hgamma_upper_raw :
              ‖Complex.Gamma w‖ ≤ Cn / D :=
            Complex.Gamma_norm_le_of_normalizedGammaStirlingFactor_norm_le
              w Cn hnormalized_xy.1 hD_pos
          have hgamma_lower_raw :
              cn / D ≤ ‖Complex.Gamma w‖ :=
            Complex.Gamma_norm_ge_of_normalizedGammaStirlingFactor_norm_ge
              w cn hnormalized_xy.2 hD_pos
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
          And.intro
            (le_trans hgamma_upper_raw hupper_scale)
            (le_trans hlower_scale hgamma_lower_raw)⟩

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
          have hD_pos : 0 < D :=
            hdenom_xy.1
          have hrecip_upper : 1 / D ≤ Cd * E :=
            hdenom_xy.2.1
          have hrecip_lower : cd * E ≤ 1 / D :=
            hdenom_xy.2.2
          have hgamma_upper_raw :
              ‖Complex.Gamma w‖ ≤ Cn / D :=
            Complex.Gamma_norm_le_of_normalizedGammaStirlingFactor_norm_le
              w Cn hnormalized_xy.1 hD_pos
          have hgamma_lower_raw :
              cn / D ≤ ‖Complex.Gamma w‖ :=
            Complex.Gamma_norm_ge_of_normalizedGammaStirlingFactor_norm_ge
              w cn hnormalized_xy.2 hD_pos
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
          And.intro
            (le_trans hgamma_upper_raw hupper_scale)
            (le_trans hlower_scale hgamma_lower_raw)⟩

/-- Finite recurrence transport from shifted raw Gamma bounds and recurrence
product bounds back to the original vertical strip.

The shifted envelope has power `x + N - 1/2`; division by the recurrence product
contributes exactly a fixed polynomial factor of degree `N`, which is absorbed
into strip-dependent constants and recovers the unshifted envelope. -/
theorem Complex.verticalStripGammaBounds_of_shiftedRawBounds_and_recurrenceProduct
    (A B : ℝ)
    (N : ℕ)
    (_hshift_eq : N = Complex.verticalStripTransportShift A)
    (hshifted :
      ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
        0 < H ∧
        0 < C ∧
        0 < c ∧
        ∀ x y : ℝ,
          A ≤ x →
          x ≤ B →
          H ≤ ‖y‖ →
            ‖Complex.Gamma
                (Complex.fixedRealPartVerticalPoint (x + N) y)‖ ≤
              C * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y ∧
            c * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y ≤
              ‖Complex.Gamma
                (Complex.fixedRealPartVerticalPoint (x + N) y)‖)
    (hproduct :
      ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
        0 < H ∧
        0 < C ∧
        0 < c ∧
        ∀ x y : ℝ,
          A ≤ x →
          x ≤ B →
          H ≤ ‖y‖ →
            ‖Complex.gammaRecurrenceProduct
                (Complex.fixedRealPartVerticalPoint x y) N‖ ≤
              C * (1 + ‖y‖) ^ (N : ℝ) ∧
            c * (1 + ‖y‖) ^ (N : ℝ) ≤
              ‖Complex.gammaRecurrenceProduct
                (Complex.fixedRealPartVerticalPoint x y) N‖)
    (hfactor_ne :
      ∃ H : ℝ,
        0 < H ∧
        ∀ x y : ℝ,
          A ≤ x →
          x ≤ B →
          H ≤ ‖y‖ →
            ∀ j : ℕ,
              j < N →
                Complex.fixedRealPartVerticalPoint x y + (j : ℂ) ≠ 0) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope x y ∧
            c * Complex.fixedRealPartVerticalStirlingEnvelope x y ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ := by
  match hshifted with
  | ⟨Hs, Cs, cs, hHs_pos, hCs_pos, hcs_pos, hshifted_bound⟩ =>
  match hproduct with
  | ⟨Hp, Cp, cp, hHp_pos, hCp_pos, hcp_pos, hproduct_bound⟩ =>
  match hfactor_ne with
  | ⟨Hn, hHn_pos, hfactor_ne_pointwise⟩ =>
  let H : ℝ := max Hs (max Hp Hn)
  exact
    ⟨H, Cs / cp, cs / Cp,
      lt_of_lt_of_le hHs_pos (le_max_left Hs (max Hp Hn)),
      div_pos hCs_pos hcp_pos,
      div_pos hcs_pos hCp_pos,
      fun x y hxA hxB hy =>
        have hy_s : Hs ≤ ‖y‖ :=
          le_trans (le_max_left Hs (max Hp Hn)) hy
        have hy_p : Hp ≤ ‖y‖ :=
          le_trans (le_trans (le_max_left Hp Hn) (le_max_right Hs (max Hp Hn))) hy
        have hy_n : Hn ≤ ‖y‖ :=
          le_trans (le_trans (le_max_right Hp Hn) (le_max_right Hs (max Hp Hn))) hy
        have hshifted_xy := hshifted_bound x y hxA hxB hy_s
        have hproduct_xy := hproduct_bound x y hxA hxB hy_p
        have hfactor_xy :
            ∀ j : ℕ,
              j < N →
                Complex.fixedRealPartVerticalPoint x y + (j : ℂ) ≠ 0 :=
          hfactor_ne_pointwise x y hxA hxB hy_n
        have hnorm_rec :
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ =
              ‖Complex.Gamma
                (Complex.fixedRealPartVerticalPoint x y + (N : ℂ))‖ /
                ‖Complex.gammaRecurrenceProduct
                  (Complex.fixedRealPartVerticalPoint x y) N‖ :=
          Complex.Gamma_norm_eq_shifted_norm_div_gammaRecurrenceProduct_norm
            N hfactor_xy
        have hshift_point :
            Complex.fixedRealPartVerticalPoint x y + (N : ℂ) =
              Complex.fixedRealPartVerticalPoint (x + N) y := by
          exact (Complex.fixedRealPartVerticalPoint_add_natCast x y N).symm
        have hshifted_norm :
            ‖Complex.Gamma
                (Complex.fixedRealPartVerticalPoint x y + (N : ℂ))‖ =
              ‖Complex.Gamma
                (Complex.fixedRealPartVerticalPoint (x + N) y)‖ :=
          congrArg (fun z : ℂ => ‖Complex.Gamma z‖) hshift_point
        let R : ℝ := 1 + ‖y‖
        have hR_pos : 0 < R :=
          add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg y)
        have hRpow_pos : 0 < R ^ (N : ℝ) :=
          Real.rpow_pos_of_pos hR_pos (N : ℝ)
        have hprod_lower_pos :
            0 < cp * R ^ (N : ℝ) :=
          mul_pos hcp_pos hRpow_pos
        have hprod_upper_pos :
            0 < Cp * R ^ (N : ℝ) :=
          mul_pos hCp_pos hRpow_pos
        have hprod_norm_pos :
            0 <
              ‖Complex.gammaRecurrenceProduct
                (Complex.fixedRealPartVerticalPoint x y) N‖ :=
          lt_of_lt_of_le hprod_lower_pos hproduct_xy.2
        have hshifted_upper :
            ‖Complex.Gamma
                (Complex.fixedRealPartVerticalPoint x y + (N : ℂ))‖ ≤
              Cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y :=
          calc
            ‖Complex.Gamma
                (Complex.fixedRealPartVerticalPoint x y + (N : ℂ))‖ =
              ‖Complex.Gamma
                (Complex.fixedRealPartVerticalPoint (x + N) y)‖ :=
              hshifted_norm
            _ ≤ Cs *
                Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y :=
              hshifted_xy.1
        have hshifted_lower :
            cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y ≤
              ‖Complex.Gamma
                (Complex.fixedRealPartVerticalPoint x y + (N : ℂ))‖ :=
          calc
            cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y ≤
              ‖Complex.Gamma
                (Complex.fixedRealPartVerticalPoint (x + N) y)‖ :=
              hshifted_xy.2
            _ =
              ‖Complex.Gamma
                (Complex.fixedRealPartVerticalPoint x y + (N : ℂ))‖ :=
              hshifted_norm.symm
        have hupper_div :
            ‖Complex.Gamma
                (Complex.fixedRealPartVerticalPoint x y + (N : ℂ))‖ /
                ‖Complex.gammaRecurrenceProduct
                  (Complex.fixedRealPartVerticalPoint x y) N‖ ≤
              Cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y /
                (cp * R ^ (N : ℝ)) := by
            have hstep_den :
                ‖Complex.Gamma
                    (Complex.fixedRealPartVerticalPoint x y + (N : ℂ))‖ /
                    ‖Complex.gammaRecurrenceProduct
                      (Complex.fixedRealPartVerticalPoint x y) N‖ ≤
                  ‖Complex.Gamma
                    (Complex.fixedRealPartVerticalPoint x y + (N : ℂ))‖ /
                    (cp * R ^ (N : ℝ)) :=
              div_le_div_of_nonneg_left
                (norm_nonneg
                  (Complex.Gamma
                    (Complex.fixedRealPartVerticalPoint x y + (N : ℂ))))
                hprod_lower_pos
                hproduct_xy.2
            have hstep_num :
                ‖Complex.Gamma
                    (Complex.fixedRealPartVerticalPoint x y + (N : ℂ))‖ /
                    (cp * R ^ (N : ℝ)) ≤
                  Cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y /
                    (cp * R ^ (N : ℝ)) :=
              div_le_div_of_nonneg_right hshifted_upper (le_of_lt hprod_lower_pos)
            exact le_trans hstep_den hstep_num
        have hlower_div :
            cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y /
                (Cp * R ^ (N : ℝ)) ≤
              ‖Complex.Gamma
                (Complex.fixedRealPartVerticalPoint x y + (N : ℂ))‖ /
                ‖Complex.gammaRecurrenceProduct
                  (Complex.fixedRealPartVerticalPoint x y) N‖ := by
            have hnum_nonneg :
                0 ≤ cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y :=
              mul_nonneg (le_of_lt hcs_pos)
                (Complex.fixedRealPartVerticalStirlingEnvelope_nonneg (x + N) y)
            have hstep_den :
                cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y /
                    (Cp * R ^ (N : ℝ)) ≤
                  cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y /
                    ‖Complex.gammaRecurrenceProduct
                      (Complex.fixedRealPartVerticalPoint x y) N‖ :=
              div_le_div_of_nonneg_left
                hnum_nonneg
                hprod_norm_pos
                hproduct_xy.1
            have hstep_num :
                cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y /
                    ‖Complex.gammaRecurrenceProduct
                      (Complex.fixedRealPartVerticalPoint x y) N‖ ≤
                  ‖Complex.Gamma
                    (Complex.fixedRealPartVerticalPoint x y + (N : ℂ))‖ /
                    ‖Complex.gammaRecurrenceProduct
                      (Complex.fixedRealPartVerticalPoint x y) N‖ :=
              div_le_div_of_nonneg_right hshifted_lower
                (le_of_lt hprod_norm_pos)
            exact le_trans hstep_den hstep_num
          And.intro
          (have htarget :
              Cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y /
                  (cp * R ^ (N : ℝ)) =
                (Cs / cp) * Complex.fixedRealPartVerticalStirlingEnvelope x y :=
            Complex.fixedRealPartVerticalStirlingEnvelope_natShift_div_scale_eq
              x y N Cs cp hcp_pos
          calc
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ =
              ‖Complex.Gamma
                (Complex.fixedRealPartVerticalPoint x y + (N : ℂ))‖ /
                ‖Complex.gammaRecurrenceProduct
                  (Complex.fixedRealPartVerticalPoint x y) N‖ :=
              hnorm_rec
            _ ≤ Cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y /
                (cp * R ^ (N : ℝ)) :=
              hupper_div
            _ = (Cs / cp) *
                Complex.fixedRealPartVerticalStirlingEnvelope x y :=
              htarget)
          (have htarget :
              cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y /
                  (Cp * R ^ (N : ℝ)) =
                (cs / Cp) * Complex.fixedRealPartVerticalStirlingEnvelope x y :=
            Complex.fixedRealPartVerticalStirlingEnvelope_natShift_div_scale_eq
              x y N cs Cp hCp_pos
          calc
            (cs / Cp) * Complex.fixedRealPartVerticalStirlingEnvelope x y =
              cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y /
                (Cp * R ^ (N : ℝ)) :=
              htarget.symm
            _ ≤
              ‖Complex.Gamma
                (Complex.fixedRealPartVerticalPoint x y + (N : ℂ))‖ /
                ‖Complex.gammaRecurrenceProduct
                  (Complex.fixedRealPartVerticalPoint x y) N‖ :=
              hlower_div
            _ = ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ :=
              hnorm_rec.symm)⟩

/-- Sectorial Stirling at the deterministic right shift, transported back
through the finite Gamma recurrence product.

This is the single non-special-function owner sink for the vertical-strip
transport.  It combines the deterministic shift geometry, the exact Gamma
recurrence product identity, and the finite-product upper/lower estimates. -/
theorem Complex.sectorialLogGammaAsymptotic_verticalStrip_largeHeight_bounds_of_recurrenceProduct
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
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope x y ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope x y ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ := by
  let N : ℕ := Complex.verticalStripTransportShift A
  have hshifted_transport :
      ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
        0 < H ∧
        0 < C ∧
        0 < c ∧
        ∀ x y : ℝ,
          A ≤ x →
          x ≤ B →
          H ≤ ‖y‖ →
            ‖Complex.Gamma
                (Complex.fixedRealPartVerticalPoint (x + N) y)‖ ≤
              C * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y ∧
            c * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y ≤
              ‖Complex.Gamma
                (Complex.fixedRealPartVerticalPoint (x + N) y)‖ := by
    exact
      Complex.sectorialStirling_shiftedRawGammaEnvelope_of_normalizedStirling
        hStirling A B
  exact
    Complex.verticalStripGammaBounds_of_shiftedRawBounds_and_recurrenceProduct
      A B N rfl
      hshifted_transport
      (Complex.gammaRecurrenceProduct_verticalStrip_twoSided_bounds A B N)
      (Complex.gammaRecurrenceProduct_factors_ne_zero_on_verticalStrip_largeHeight
        A B N)

/-- Deterministic finite-recurrence transport from closed-right-half-plane
sectorial Stirling to a vertical strip.

The shift is `Complex.verticalStripRightShift A`.  Applying sectorial Stirling
to `z + N` is justified by
`fixedRealPartVerticalPoint_verticalStripRightShift_closedRightHalfPlaneSector`
and the height/radius comparison.  The finite product
`gammaRecurrenceProduct z N` is controlled uniformly on the strip because `N`
is fixed and the strip real part is bounded; Gamma recurrence gives
`Γ z = Γ (z + N) / gammaRecurrenceProduct z N`. -/
theorem Complex.sectorialLogGammaAsymptotic_verticalStrip_largeHeight_bounds_of_deterministicShift
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
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope x y ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope x y ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ := by
  exact
    Complex.sectorialLogGammaAsymptotic_verticalStrip_largeHeight_bounds_of_recurrenceProduct
      hStirling A B

/-- Vertical-strip two-sided Stirling bounds as a consequence of sectorial
log-Gamma Stirling.

For a strip that crosses the left half-plane, choose a natural shift `N` with
`-A ≤ N`.  The shifted points `z + N` lie in the closed right half-plane and
the sectorial logarithmic Stirling theorem applies there; the finite Gamma
recurrence product transports the estimate back to `z`.  The coordinate and
radius facts above supply the non-Stirling geometry of this reduction. -/
theorem Complex.sectorialLogGammaAsymptotic_verticalStrip_largeHeight_bounds
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
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope x y ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope x y ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ := by
  exact
    Complex.sectorialLogGammaAsymptotic_verticalStrip_largeHeight_bounds_of_deterministicShift
      hStirling A B

/-- Standard vertical-strip specialization of sectorial Stirling.

On every compact real strip `A ≤ Re z ≤ B`, the vertical tails lie in closed
sectors avoiding the negative real axis.  Sectorial Stirling therefore gives
uniform two-sided Gamma bounds with the classical
`exp (-π |y| / 2) (1 + |y|)^(x - 1/2)` profile.  This is the upstream
fixed-line owner theorem; cf. Whittaker-Watson, Ch. XII and DLMF §5.11. -/
theorem Complex.sectorialStirling_verticalStrip_largeHeight_classical
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
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope x y ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope x y ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ := by
  let N : ℕ := Complex.verticalStripTransportShift A
  have hshifted_transport :
      ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
        0 < H ∧
        0 < C ∧
        0 < c ∧
        ∀ x y : ℝ,
          A ≤ x →
          x ≤ B →
          H ≤ ‖y‖ →
            ‖Complex.Gamma
                (Complex.fixedRealPartVerticalPoint (x + N) y)‖ ≤
              C * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y ∧
            c * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y ≤
              ‖Complex.Gamma
                (Complex.fixedRealPartVerticalPoint (x + N) y)‖ := by
    exact
      Complex.sectorialStirling_shiftedRawGammaEnvelope_of_branchPackage
        hbranch A B
  exact
    Complex.verticalStripGammaBounds_of_shiftedRawBounds_and_recurrenceProduct
      A B N rfl
      hshifted_transport
      (Complex.gammaRecurrenceProduct_verticalStrip_twoSided_bounds A B N)
      (Complex.gammaRecurrenceProduct_factors_ne_zero_on_verticalStrip_largeHeight
        A B N)

/-- Classical large-height fixed-real-part vertical Stirling theorem.

For arbitrary real part `a`, the vertical line `a + i b` is not contained in
the closed right half-plane when `a < 0`.  The correct owner input is therefore
the fixed-line specialization of sectorial Stirling in sectors avoiding the
negative real axis, with constants depending on `a`; cf. DLMF §5.11. -/
theorem Complex.fixedRealPartVerticalStirling_largeHeight_classical
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
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
  match Complex.sectorialStirling_verticalStrip_largeHeight_classical hbranch a a with
  | ⟨H, C, c, hH_pos, hC_pos, hc_pos, hstrip⟩ =>
  exact
    ⟨H, C, c, hH_pos, hC_pos, hc_pos,
      fun b hb =>
        hstrip a b (le_refl a) (le_refl a) hb⟩

/-- Large-height fixed-real-part vertical Stirling bounds for `Complex.Gamma`.

For an arbitrary fixed real part `a`, the vertical line `a + ib` eventually
lies in a closed sector avoiding the negative real axis, with sector aperture
depending on `a`.  Sectorial Stirling there gives the two-sided
`exp (-π |b| / 2) (1 + |b|)^(a - 1/2)` envelope. -/
theorem Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_largeHeight_classical
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
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
  exact Complex.fixedRealPartVerticalStirling_largeHeight_classical hbranch a

/-- The compact-height part of a fixed vertical line. -/
def Complex.fixedRealPartVerticalCompactHeightSet
    (H : ℝ) : Set ℝ :=
  {b : ℝ | (1 / 2 : ℝ) ≤ ‖b‖ ∧ ‖b‖ ≤ H}

/-- Closed real strip with compact vertical-height window.

This is the two-dimensional compact-height owner domain needed for uniform
Gamma and Gamma-ratio bounds when the real part varies in a closed interval. -/
def Complex.closedRealStripCompactHeightSet
    (A B L H : ℝ) : Set ℂ :=
  {z : ℂ | A ≤ z.re} ∩ {z : ℂ | z.re ≤ B} ∩
    {z : ℂ | L ≤ ‖z.im‖} ∩ {z : ℂ | ‖z.im‖ ≤ H}

/-- The closed real-strip compact-height set is closed. -/
theorem Complex.closedRealStripCompactHeightSet_isClosed
    (A B L H : ℝ) :
    IsClosed (Complex.closedRealStripCompactHeightSet A B L H) := by
  have hleft : IsClosed {z : ℂ | A ≤ z.re} :=
    isClosed_le continuous_const Complex.continuous_re
  have hright : IsClosed {z : ℂ | z.re ≤ B} :=
    isClosed_le Complex.continuous_re continuous_const
  have him_lower : IsClosed {z : ℂ | L ≤ ‖z.im‖} :=
    isClosed_le continuous_const (Complex.continuous_im.norm)
  have him_upper : IsClosed {z : ℂ | ‖z.im‖ ≤ H} :=
    isClosed_le (Complex.continuous_im.norm) continuous_const
  exact ((hleft.inter hright).inter him_lower).inter him_upper

/-- The closed real-strip compact-height set is bounded. -/
theorem Complex.closedRealStripCompactHeightSet_isBounded
    (A B L H : ℝ) :
    Bornology.IsBounded (Complex.closedRealStripCompactHeightSet A B L H) := by
  refine isBounded_iff_forall_norm_le.2 ⟨|A| + |B| + H + 1, ?_⟩
  intro z hz
  have hz_left : A ≤ z.re := hz.1.1.1
  have hz_right : z.re ≤ B := hz.1.1.2
  have hz_im_upper : ‖z.im‖ ≤ H := hz.2
  have hre_abs_le : |z.re| ≤ |A| + |B| := by
    have hleft_bound : -(|A| + |B|) ≤ z.re := by
      have hneg_sum : -(|A| + |B|) = -|A| + -|B| :=
        neg_add |A| |B|
      have hneg_sum_le : -|A| + -|B| ≤ -|A| := by
        have hb_nonpos : -|B| ≤ 0 :=
          neg_nonpos.mpr (abs_nonneg B)
        exact
          le_trans
            (add_le_add_left hb_nonpos (-|A|))
            (le_of_eq (add_zero (-|A|)))
      have hneg_abs_A_le_A : -|A| ≤ A :=
        neg_abs_le A
      exact
        le_trans
          (le_of_eq hneg_sum)
          (le_trans hneg_sum_le (le_trans hneg_abs_A_le_A hz_left))
    have hright_bound : z.re ≤ |A| + |B| := by
      have hB_le_abs_B : B ≤ |B| :=
        le_abs_self B
      have h_abs_B_le_sum : |B| ≤ |A| + |B| :=
        le_add_of_nonneg_left (abs_nonneg A)
      exact le_trans hz_right (le_trans hB_le_abs_B h_abs_B_le_sum)
    exact abs_le.mpr ⟨hleft_bound, hright_bound⟩
  have him_abs_le : |z.im| ≤ H := by
    exact
      Eq.subst
        (motive := fun x : ℝ => x ≤ H)
        (Real.norm_eq_abs z.im)
        hz_im_upper
  have hnorm_le_coord : ‖z‖ ≤ |z.re| + |z.im| :=
    Eq.subst
      (motive := fun x : ℝ => x ≤ |z.re| + |z.im|)
      (Complex.norm_eq_abs z).symm
      (Complex.abs_le_abs_re_add_abs_im z)
  have hcoord_le : |z.re| + |z.im| ≤ (|A| + |B|) + H :=
    add_le_add hre_abs_le him_abs_le
  have htarget : (|A| + |B|) + H ≤ |A| + |B| + H + 1 :=
    le_add_of_nonneg_right zero_le_one
  exact le_trans hnorm_le_coord (le_trans hcoord_le htarget)

/-- The closed real-strip compact-height set is compact. -/
theorem Complex.closedRealStripCompactHeightSet_isCompact
    (A B L H : ℝ) :
    IsCompact (Complex.closedRealStripCompactHeightSet A B L H) :=
  Metric.isCompact_of_isClosed_isBounded
    (Complex.closedRealStripCompactHeightSet_isClosed A B L H)
    (Complex.closedRealStripCompactHeightSet_isBounded A B L H)

/-- `Complex.Gamma` has no zeros on a closed real strip whose imaginary
coordinate is bounded away from zero. -/
theorem Complex.Gamma_ne_zero_on_closedRealStripCompactHeightSet
    (A B L H : ℝ)
    (hL_pos : 0 < L)
    {w : ℂ}
    (hw : w ∈ Complex.closedRealStripCompactHeightSet A B L H) :
    Complex.Gamma w ≠ 0 :=
  fun hzero =>
    match (Complex.Gamma_eq_zero_iff w).mp hzero with
    | ⟨n, hn⟩ =>
        have him_eq : w.im = (-(n : ℂ)).im :=
          congrArg Complex.im hn
        have hright_im : (-(n : ℂ)).im = 0 := by
          calc
            (-(n : ℂ)).im = -((n : ℂ).im) := Complex.neg_im (n : ℂ)
            _ = -0 := congrArg Neg.neg (Complex.ofReal_im (n : ℝ))
            _ = 0 := neg_zero
        have hw_im_zero : w.im = 0 :=
          Eq.trans him_eq hright_im
        have hnorm_zero : ‖w.im‖ = 0 := by
          calc
            ‖w.im‖ = ‖(0 : ℝ)‖ := congrArg norm hw_im_zero
            _ = 0 := norm_zero
        have hL_le_zero : L ≤ 0 := by
          calc
            L ≤ ‖w.im‖ := hw.1.2
            _ = 0 := hnorm_zero
        (not_lt_of_ge hL_le_zero) hL_pos

/-- `Complex.Gamma` is continuous on a closed real strip whose imaginary
coordinate is bounded away from zero. -/
theorem Complex.continuousOn_Gamma_closedRealStripCompactHeightSet
    (A B L H : ℝ)
    (hL_pos : 0 < L) :
    ContinuousOn
      Complex.Gamma
      (Complex.closedRealStripCompactHeightSet A B L H) :=
  fun w hw =>
    have hgamma_ne : Complex.Gamma w ≠ 0 :=
      Complex.Gamma_ne_zero_on_closedRealStripCompactHeightSet A B L H hL_pos hw
    have hpole_free : ∀ n : ℕ, w ≠ -n :=
      fun n hn =>
        hgamma_ne ((Complex.Gamma_eq_zero_iff w).mpr ⟨n, hn⟩)
    (Complex.differentiableAt_Gamma w hpole_free).continuousAt.continuousWithinAt

/-- Compact-height closed-rectangle bound for the Gamma norm. -/
theorem Complex.Gamma_closedRealStripCompactHeightSet_bound
    (A B L H : ℝ)
    (hL_pos : 0 < L) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        w ∈ Complex.closedRealStripCompactHeightSet A B L H →
          ‖Complex.Gamma w‖ ≤ C := by
  match IsCompact.exists_bound_of_continuousOn
      (Complex.closedRealStripCompactHeightSet_isCompact A B L H)
      (Complex.continuousOn_Gamma_closedRealStripCompactHeightSet
        A B L H hL_pos) with
  | ⟨M, hM⟩ =>
      let C : ℝ := max 1 M
      have hC_pos : 0 < C :=
        lt_of_lt_of_le zero_lt_one (le_max_left 1 M)
      exact
        ⟨C, hC_pos,
          fun w hw =>
            calc
              ‖Complex.Gamma w‖ ≤ M := hM w hw
              _ ≤ C := le_max_right 1 M⟩

/-- Pointwise form of the compact-height closed-rectangle Gamma bound. -/
theorem Complex.Gamma_closedRealStrip_compactHeight_bound
    (A B L H : ℝ)
    (hL_pos : 0 < L) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        A ≤ w.re →
        w.re ≤ B →
        L ≤ ‖w.im‖ →
        ‖w.im‖ ≤ H →
          ‖Complex.Gamma w‖ ≤ C := by
  match Complex.Gamma_closedRealStripCompactHeightSet_bound A B L H hL_pos with
  | ⟨C, hC_pos, hC⟩ =>
      exact
        ⟨C, hC_pos,
          fun w hw_left hw_right hw_lower hw_upper =>
            hC w ⟨⟨⟨hw_left, hw_right⟩, hw_lower⟩, hw_upper⟩⟩

/-- The reciprocal Gamma function is continuous on a closed real-strip
compact-height rectangle whose imaginary coordinate is bounded away from zero. -/
theorem Complex.continuousOn_Gamma_inv_closedRealStripCompactHeightSet
    (A B L H : ℝ)
    (hL_pos : 0 < L) :
    ContinuousOn
      (fun w : ℂ => (Complex.Gamma w)⁻¹)
      (Complex.closedRealStripCompactHeightSet A B L H) :=
  fun w hw =>
    have hgamma_ne : Complex.Gamma w ≠ 0 :=
      Complex.Gamma_ne_zero_on_closedRealStripCompactHeightSet A B L H hL_pos hw
    have hpole_free : ∀ n : ℕ, w ≠ -n :=
      fun n hn =>
        hgamma_ne ((Complex.Gamma_eq_zero_iff w).mpr ⟨n, hn⟩)
    have hgamma_cont : ContinuousAt Complex.Gamma w :=
      (Complex.differentiableAt_Gamma w hpole_free).continuousAt
    (hgamma_cont.inv₀ hgamma_ne).continuousWithinAt

/-- Compact-height closed-rectangle bound for the reciprocal Gamma norm. -/
theorem Complex.Gamma_inv_closedRealStripCompactHeightSet_bound
    (A B L H : ℝ)
    (hL_pos : 0 < L) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        w ∈ Complex.closedRealStripCompactHeightSet A B L H →
          ‖(Complex.Gamma w)⁻¹‖ ≤ C := by
  match IsCompact.exists_bound_of_continuousOn
      (Complex.closedRealStripCompactHeightSet_isCompact A B L H)
      (Complex.continuousOn_Gamma_inv_closedRealStripCompactHeightSet
        A B L H hL_pos) with
  | ⟨M, hM⟩ =>
      let C : ℝ := max 1 M
      have hC_pos : 0 < C :=
        lt_of_lt_of_le zero_lt_one (le_max_left 1 M)
      exact
        ⟨C, hC_pos,
          fun w hw =>
            calc
              ‖(Complex.Gamma w)⁻¹‖ ≤ M := hM w hw
              _ ≤ C := le_max_right 1 M⟩

/-- Pointwise form of the compact-height closed-rectangle reciprocal Gamma bound. -/
theorem Complex.Gamma_inv_closedRealStrip_compactHeight_bound
    (A B L H : ℝ)
    (hL_pos : 0 < L) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        A ≤ w.re →
        w.re ≤ B →
        L ≤ ‖w.im‖ →
        ‖w.im‖ ≤ H →
          ‖(Complex.Gamma w)⁻¹‖ ≤ C := by
  match Complex.Gamma_inv_closedRealStripCompactHeightSet_bound A B L H hL_pos with
  | ⟨C, hC_pos, hC⟩ =>
      exact
        ⟨C, hC_pos,
          fun w hw_left hw_right hw_lower hw_upper =>
            hC w ⟨⟨⟨hw_left, hw_right⟩, hw_lower⟩, hw_upper⟩⟩

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

/-- The fixed vertical-line point depends continuously on the height. -/
theorem Complex.continuousAt_fixedRealPartVerticalPoint_height
    (a b : ℝ) :
    ContinuousAt (fun x : ℝ => Complex.fixedRealPartVerticalPoint a x) b := by
  exact continuousAt_const.add
    (Complex.continuous_ofReal.continuousAt.mul continuousAt_const)

/-- The fixed vertical-line Stirling envelope depends continuously on height. -/
theorem Complex.continuousAt_fixedRealPartVerticalStirlingEnvelope_height
    (a b : ℝ) :
    ContinuousAt
      (fun x : ℝ => Complex.fixedRealPartVerticalStirlingEnvelope a x) b := by
  have hbase_pos : 0 < 1 + ‖b‖ :=
    lt_of_lt_of_le zero_lt_one
      (le_add_of_nonneg_right (norm_nonneg b))
  have hexp_arg_cont :
      ContinuousAt (fun x : ℝ => (-(Real.pi / 2)) * ‖x‖) b :=
    continuousAt_const.mul continuousAt_id.norm
  have hpow_base_cont :
      ContinuousAt (fun x : ℝ => 1 + ‖x‖) b :=
    continuousAt_const.add continuousAt_id.norm
  exact
    hexp_arg_cont.rexp.mul
      (hpow_base_cont.rpow_const (Or.inl hbase_pos.ne'))

/-- The fixed-line compact-height set is compact. -/
theorem Complex.fixedRealPartVerticalCompactHeightSet_isCompact
    (H : ℝ) :
    IsCompact (Complex.fixedRealPartVerticalCompactHeightSet H) := by
  have hclosed_inner : IsClosed {b : ℝ | (1 / 2 : ℝ) ≤ ‖b‖} :=
    isClosed_Ici.preimage continuous_norm
  have hclosed_outer : IsClosed {b : ℝ | ‖b‖ ≤ H} :=
    isClosed_Iic.preimage continuous_norm
  have hclosed :
      IsClosed (Complex.fixedRealPartVerticalCompactHeightSet H) :=
    hclosed_inner.inter hclosed_outer
  have hsubset :
      Complex.fixedRealPartVerticalCompactHeightSet H ⊆ Set.Icc (-H) H := by
    exact
      fun b hb =>
        have hb_abs_le : |b| ≤ H := by
          calc
            |b| = ‖b‖ := (Real.norm_eq_abs b).symm
            _ ≤ H := hb.2
        abs_le.mp hb_abs_le
  exact isCompact_Icc.of_isClosed_subset hclosed hsubset

/-- The fixed-line compact-height set is nonempty once `H ≥ 1 / 2`. -/
theorem Complex.fixedRealPartVerticalCompactHeightSet_nonempty
    {H : ℝ}
    (hH : (1 / 2 : ℝ) ≤ H) :
    (Complex.fixedRealPartVerticalCompactHeightSet H).Nonempty := by
  have hhalf_nonneg : (0 : ℝ) ≤ 1 / 2 :=
    le_of_lt (half_pos zero_lt_one)
  have hnorm_half : ‖(1 / 2 : ℝ)‖ = 1 / 2 :=
    Real.norm_of_nonneg hhalf_nonneg
  exact
    ⟨(1 / 2 : ℝ),
      And.intro
      (le_of_eq hnorm_half.symm)
      (calc
        ‖(1 / 2 : ℝ)‖ = 1 / 2 := hnorm_half
        _ ≤ H := hH)⟩

/-- `Gamma` is nonzero on the fixed-line compact-height strip. -/
theorem Complex.Gamma_fixedRealPartVerticalPoint_ne_zero_of_compactHeight
    {a H b : ℝ}
    (hb : b ∈ Complex.fixedRealPartVerticalCompactHeightSet H) :
    Complex.Gamma (Complex.fixedRealPartVerticalPoint a b) ≠ 0 := by
  exact
    fun hzero =>
      match (Complex.Gamma_eq_zero_iff
          (Complex.fixedRealPartVerticalPoint a b)).mp hzero with
      | ⟨n, hn⟩ =>
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
          Eq.trans (congrArg norm hb_zero) (norm_zero : ‖(0 : ℝ)‖ = 0)
        have hhalf_pos : (0 : ℝ) < 1 / 2 :=
          half_pos zero_lt_one
        have hnot : ¬ (1 / 2 : ℝ) ≤ 0 :=
          not_le.mpr hhalf_pos
        have hhalf_le_zero : (1 / 2 : ℝ) ≤ 0 := by
          calc
            (1 / 2 : ℝ) ≤ ‖b‖ := hb.1
            _ = 0 := hnorm_zero
        hnot hhalf_le_zero

/-- The fixed-line Gamma ratio is continuous on compact-height sets. -/
theorem Complex.continuousOn_fixedRealPartVerticalGammaRatio_compactHeight
    (a H : ℝ) :
    ContinuousOn
      (fun b : ℝ =>
        ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ /
          Complex.fixedRealPartVerticalStirlingEnvelope a b)
      (Complex.fixedRealPartVerticalCompactHeightSet H) := by
  exact
    fun b hb =>
      have hgamma_ne :
          Complex.Gamma (Complex.fixedRealPartVerticalPoint a b) ≠ 0 :=
        Complex.Gamma_fixedRealPartVerticalPoint_ne_zero_of_compactHeight hb
      have hpole_free :
          ∀ n : ℕ, Complex.fixedRealPartVerticalPoint a b ≠ -n :=
        fun n hn =>
          hgamma_ne ((Complex.Gamma_eq_zero_iff
            (Complex.fixedRealPartVerticalPoint a b)).mpr ⟨n, hn⟩)
      have hpoint_cont :
          ContinuousAt (fun x : ℝ => Complex.fixedRealPartVerticalPoint a x) b := by
        exact Complex.continuousAt_fixedRealPartVerticalPoint_height a b
      have hgamma_cont :
          ContinuousAt
            (fun x : ℝ => Complex.Gamma (Complex.fixedRealPartVerticalPoint a x))
            b :=
        (Complex.differentiableAt_Gamma
          (Complex.fixedRealPartVerticalPoint a b) hpole_free).continuousAt.comp
          hpoint_cont
      have hnum_cont :
          ContinuousAt
            (fun x : ℝ => ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a x)‖)
            b :=
        hgamma_cont.norm
      have hbase_pos : 0 < 1 + ‖b‖ :=
        lt_of_lt_of_le zero_lt_one
          (le_add_of_nonneg_right (norm_nonneg b))
      have henv_cont :
          ContinuousAt
            (fun x : ℝ => Complex.fixedRealPartVerticalStirlingEnvelope a x)
            b := by
        exact Complex.continuousAt_fixedRealPartVerticalStirlingEnvelope_height a b
      have henv_ne :
          Complex.fixedRealPartVerticalStirlingEnvelope a b ≠ 0 :=
        ne_of_gt (Complex.fixedRealPartVerticalStirlingEnvelope_pos a b)
      (hnum_cont.div henv_cont henv_ne).continuousWithinAt

/-- The upper ratio is continuous on compact-height sets. -/
theorem Complex.continuousOn_fixedRealPartVerticalGammaUpperRatio_compactHeight
    (a H : ℝ) :
    ContinuousOn
      (fun b : ℝ => Complex.fixedRealPartVerticalGammaUpperRatio a b)
      (Complex.fixedRealPartVerticalCompactHeightSet H) :=
  Complex.continuousOn_fixedRealPartVerticalGammaRatio_compactHeight a H

/-- The lower ratio is continuous on compact-height sets. -/
theorem Complex.continuousOn_fixedRealPartVerticalGammaLowerRatio_compactHeight
    (a H : ℝ) :
    ContinuousOn
      (fun b : ℝ => Complex.fixedRealPartVerticalGammaLowerRatio a b)
      (Complex.fixedRealPartVerticalCompactHeightSet H) :=
  Complex.continuousOn_fixedRealPartVerticalGammaRatio_compactHeight a H

/-- The fixed-line Gamma ratio is nonnegative on compact-height sets. -/
theorem Complex.fixedRealPartVerticalGammaRatio_nonneg_on_compactHeight
    (a H : ℝ)
    {b : ℝ}
    (_hb : b ∈ Complex.fixedRealPartVerticalCompactHeightSet H) :
    0 ≤ Complex.fixedRealPartVerticalGammaLowerRatio a b := by
  have hnum_nonneg :
      0 ≤ ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ :=
    norm_nonneg (Complex.Gamma (Complex.fixedRealPartVerticalPoint a b))
  have hden_pos :
      0 < Complex.fixedRealPartVerticalStirlingEnvelope a b :=
    Complex.fixedRealPartVerticalStirlingEnvelope_pos a b
  have hden_nonneg :
      0 ≤ Complex.fixedRealPartVerticalStirlingEnvelope a b :=
    le_of_lt hden_pos
  exact div_nonneg hnum_nonneg hden_nonneg

/-- The fixed-line Gamma ratio is positive on compact-height sets. -/
theorem Complex.fixedRealPartVerticalGammaRatio_pos_on_compactHeight
    (a H : ℝ)
    {b : ℝ}
    (hb : b ∈ Complex.fixedRealPartVerticalCompactHeightSet H) :
    0 < Complex.fixedRealPartVerticalGammaLowerRatio a b := by
  have hgamma_ne :
      Complex.Gamma (Complex.fixedRealPartVerticalPoint a b) ≠ 0 :=
    Complex.Gamma_fixedRealPartVerticalPoint_ne_zero_of_compactHeight hb
  have hnum_pos :
      0 < ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ :=
    norm_pos_iff.mpr hgamma_ne
  have hden_pos :
      0 < Complex.fixedRealPartVerticalStirlingEnvelope a b :=
    Complex.fixedRealPartVerticalStirlingEnvelope_pos a b
  exact div_pos hnum_pos hden_pos

/-- Compact-height upper ratio has a positive global upper bound. -/
theorem Complex.fixedRealPartVerticalGammaUpperRatio_compactHeight_bound
    (a H : ℝ) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ b : ℝ,
        b ∈ Complex.fixedRealPartVerticalCompactHeightSet H →
          Complex.fixedRealPartVerticalGammaUpperRatio a b ≤ C := by
  match IsCompact.exists_bound_of_continuousOn
      (Complex.fixedRealPartVerticalCompactHeightSet_isCompact H)
      (Complex.continuousOn_fixedRealPartVerticalGammaUpperRatio_compactHeight
        a H) with
  | ⟨M, hM⟩ =>
  let C : ℝ := max 1 M
  have hC_pos : 0 < C :=
    lt_of_lt_of_le zero_lt_one (le_max_left 1 M)
  exact
    ⟨C, hC_pos,
      fun b hb =>
        calc
          Complex.fixedRealPartVerticalGammaUpperRatio a b ≤
              ‖Complex.fixedRealPartVerticalGammaUpperRatio a b‖ := by
            exact le_trans
              (le_abs_self (Complex.fixedRealPartVerticalGammaUpperRatio a b))
              (le_of_eq
                (Real.norm_eq_abs
                  (Complex.fixedRealPartVerticalGammaUpperRatio a b)).symm)
          _ ≤ M := hM b hb
          _ ≤ C := le_max_right 1 M⟩

/-- Compact-height lower ratio has a positive global lower bound. -/
theorem Complex.fixedRealPartVerticalGammaLowerRatio_compactHeight_pos_bound
    (a H : ℝ)
    (hH_half : (1 / 2 : ℝ) ≤ H) :
    ∃ c : ℝ,
      0 < c ∧
      ∀ b : ℝ,
        b ∈ Complex.fixedRealPartVerticalCompactHeightSet H →
          c ≤ Complex.fixedRealPartVerticalGammaLowerRatio a b := by
  have hcompact :
      IsCompact (Complex.fixedRealPartVerticalCompactHeightSet H) :=
    Complex.fixedRealPartVerticalCompactHeightSet_isCompact H
  have hnonempty :
      (Complex.fixedRealPartVerticalCompactHeightSet H).Nonempty :=
    Complex.fixedRealPartVerticalCompactHeightSet_nonempty hH_half
  have hcont :
      ContinuousOn
        (fun b : ℝ => Complex.fixedRealPartVerticalGammaLowerRatio a b)
        (Complex.fixedRealPartVerticalCompactHeightSet H) :=
    Complex.continuousOn_fixedRealPartVerticalGammaLowerRatio_compactHeight
      a H
  match hcompact.exists_isMinOn hnonempty hcont with
  | ⟨b₀, hb₀, hb₀_min⟩ =>
  let c : ℝ := Complex.fixedRealPartVerticalGammaLowerRatio a b₀
  have hc_pos : 0 < c :=
    Complex.fixedRealPartVerticalGammaRatio_pos_on_compactHeight a H hb₀
  exact
    ⟨c, hc_pos, fun b hb => hb₀_min hb⟩

/-- Canonical compact-height ratio theorem for a fixed vertical line.

The proof is the standard compactness argument: the height set is compact,
the Gamma ratio is continuous there, `Gamma` has no zeros on it because
`|b| ≥ 1/2`, and the fixed-line Stirling envelope is strictly positive. -/
theorem Complex.fixedRealPartVerticalGammaRatio_compactHeight_bounds
    (a H : ℝ)
    (hH_pos : 0 < H)
    [hH_half_dec : Decidable ((1 / 2 : ℝ) ≤ H)] :
    ∃ C : ℝ, ∃ c : ℝ,
      0 < C ∧
      0 < c ∧
      ∀ b : ℝ,
        b ∈ Complex.fixedRealPartVerticalCompactHeightSet H →
          Complex.fixedRealPartVerticalGammaUpperRatio a b ≤ C ∧
          c ≤ Complex.fixedRealPartVerticalGammaLowerRatio a b := by
  match Complex.fixedRealPartVerticalGammaUpperRatio_compactHeight_bound
      a H with
  | ⟨C, hC_pos, hC⟩ =>
  if hH_half : (1 / 2 : ℝ) ≤ H then
    match Complex.fixedRealPartVerticalGammaLowerRatio_compactHeight_pos_bound
        a H hH_half with
    | ⟨c, hc_pos, hc⟩ =>
    exact ⟨C, c, hC_pos, hc_pos, fun b hb => ⟨hC b hb, hc b hb⟩⟩
  else
    have hhalf_lt_H : H < (1 / 2 : ℝ) :=
      lt_of_not_ge hH_half
    have hone_pos : (0 : ℝ) < 1 :=
      zero_lt_one
    exact
      ⟨C, 1, hC_pos, hone_pos,
        fun b hb =>
          have hle : (1 / 2 : ℝ) ≤ H :=
            le_trans hb.1 hb.2
          False.elim ((not_lt_of_ge hle) hhalf_lt_H)⟩

/-- Ratio bounds on the compact-height part of a fixed vertical line.

This is the compactness/nonvanishing owner certificate: local regularity supplies a
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
  exact
    fun b hb_inner hb_outer =>
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
      ⟨hupper, hlower⟩

/-- Compact-height patch for fixed-real-part vertical Stirling bounds.

On the compact set `1 / 2 ≤ |b| ≤ H`, local regularity and nonvanishing of `Γ` on
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
  match Complex.fixedRealPartVerticalGammaRatio_bounds_on_compactHeight
      a H hH_pos with
  | ⟨C, c, hC_pos, hc_pos, hratio⟩ =>
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
                  ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖)
    (hcompact_half_dec : ∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H))
    (height_split_dec : ∀ H b : ℝ, Decidable (H ≤ ‖b‖)) :
    ∃ C : ℝ, ∃ c : ℝ,
      0 < C ∧
      0 < c ∧
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := by
  match hlarge with
  | ⟨H, Clarge, clarge, hH_pos, hClarge_pos, hclarge_pos, hlarge_bound⟩ =>
  letI : Decidable ((1 / 2 : ℝ) ≤ H) := hcompact_half_dec H
  match hcompact H hH_pos with
  | ⟨Ccompact, ccompact, hCcompact_pos, hccompact_pos, hcompact_bound⟩ =>
  let C : ℝ := max Clarge Ccompact
  let c : ℝ := min clarge ccompact
  have hC_pos : 0 < C :=
    lt_of_lt_of_le hClarge_pos (le_max_left Clarge Ccompact)
  have hc_pos : 0 < c :=
    lt_min hclarge_pos hccompact_pos
  exact
    ⟨C, c, hC_pos, hc_pos,
      fun b hb =>
        have hE_nonneg :
            0 ≤ Complex.fixedRealPartVerticalStirlingEnvelope a b :=
          Complex.fixedRealPartVerticalStirlingEnvelope_nonneg a b
        if hb_large : H ≤ ‖b‖ then
          have hlarge_b :
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
          ⟨le_trans hlarge_b.1 hupper_constant,
            le_trans hlower_constant hlarge_b.2⟩
        else
          have hb_compact_upper : ‖b‖ ≤ H :=
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
          ⟨le_trans hcompact_b.1 hupper_constant,
            le_trans hlower_constant hcompact_b.2⟩⟩

/-- Fixed-real-part vertical two-sided Stirling bounds for `Complex.Gamma`.

This is the exact fixed-line specialization theorem in the classical Stirling
API.  Deriving it from the sectorial exponential asymptotic requires the full
vertical-line argument analysis of
`w ^ ((1 / 2 : ℂ) - w)`, including the `exp (-π |b| / 2)` factor and matching
lower bound. -/
theorem Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_classical
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (a : ℝ)
    (hcompact_half_dec : ∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H))
    (height_split_dec : ∀ H b : ℝ, Decidable (H ≤ ‖b‖)) :
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
        hbranch a)
      (Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_compactHeight
        a)
      hcompact_half_dec
      height_split_dec

/-- Two-sided fixed-real-part vertical Stirling envelope for `Complex.Gamma`.

This is the fixed-line specialization of sectorial complex Stirling after
separating the argument of `a + i b`: it supplies the matching
`exp (-π |b| / 2) (1 + |b|)^(a - 1/2)` upper and lower envelopes on every
fixed real line.  The public one-sided estimates below are just projections
from this two-sided classical input. -/
theorem Complex.fixedLineVerticalGammaTwoSidedEnvelope :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    (∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H)) →
    (∀ H b : ℝ, Decidable (H ≤ ‖b‖)) →
    ∀ a : ℝ,
      ∃ C : ℝ, ∃ c : ℝ,
        0 < C ∧
        0 < c ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
              C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
            c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
              ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := fun hbranch =>
  fun hcompact_half_dec height_split_dec a =>
    Complex.Gamma_fixedRealPart_vertical_twoSided_norm_stirling_bounds_classical
      hbranch a hcompact_half_dec height_split_dec

/-- Standard sectorial `log Γ` Stirling upper bound on the closed right half-plane.

This is the logarithmic special-function root after peeling the downstream
growth theory: Stirling's expansion for `log Γ(w)` on a closed sector avoiding
the negative real axis gives a uniform
`O((1 + ‖w‖) log (2 + ‖w‖))` bound on the closed right half-plane; cf. DLMF
§5.11. The bound is stated for `log ‖Γ(w)‖`, the real part of `log Γ(w)`, so
later Gamma-real normalization steps do not need a branch of `logGamma`. -/
theorem Complex.logGamma_closedRightHalfPlane_sectorial_log_norm_bound_classical :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := fun hbranch => by
  match Complex.sectorialGammaExponentialEnvelope_closedRightHalfPlane hbranch with
  | ⟨C, hC_pos, hbound⟩ =>
    have hcoh :
        Complex.BinetSecondFormulaBranchCoherence :=
      Complex.BinetSecondFormulaBranchUniformTailAbsorption.coherence hbranch
    exact
      ⟨C, hC_pos,
        fun w hw_re_pos hw_sector hw_norm =>
          hbound w hw_re_pos hw_sector hw_norm hcoh.2.1 hcoh.2.2⟩

/-- Fixed-line vertical upper envelope for `Complex.Gamma`.

For each fixed real part `a`, Stirling's formula on the vertical line
`a + i b` gives exponential decay `exp (-π |b| / 2)` and polynomial factor
`(1 + |b|)^(a - 1/2)`; cf. DLMF §5.11. -/
theorem Complex.fixedLineVerticalGammaUpperEnvelope :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    (∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H)) →
    (∀ H b : ℝ, Decidable (H ≤ ‖b‖)) →
    ∀ a : ℝ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope a b := fun hbranch =>
  fun hcompact_half_dec height_split_dec =>
  by
  exact
    fun a =>
      match Complex.fixedLineVerticalGammaTwoSidedEnvelope
          hbranch hcompact_half_dec height_split_dec a with
      | ⟨C, c, hC_pos, hc_pos, hbounds⟩ =>
        ⟨C, hC_pos, fun b hb => (hbounds b hb).1⟩

/-- Fixed-real-part vertical Stirling upper bound for `Complex.Gamma`.

This is the direct fixed-line classical estimate: for each fixed real part `a`,
`Γ(a + i b)` has vertical decay `exp (-π |b| / 2)` and polynomial factor
`(1 + |b|)^(a - 1/2)`; cf. DLMF §5.11. -/
theorem Complex.Gamma_fixedRealPart_vertical_stirling_upper_bound_classical :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    (∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H)) →
    (∀ H b : ℝ, Decidable (H ≤ ‖b‖)) →
    ∀ a : ℝ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
            C * Real.exp (-(Real.pi / 2) * ‖b‖) *
              (1 + ‖b‖) ^ (a - 1 / 2) := fun hbranch =>
  fun hcompact_half_dec height_split_dec => by
  intro a
  match Complex.fixedLineVerticalGammaUpperEnvelope
      hbranch hcompact_half_dec height_split_dec a with
  | ⟨C, hC_pos, hupper⟩ =>
    exact
      ⟨C, hC_pos, fun b hb =>
        calc
          ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ =
              ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := rfl
          _ ≤ C * Complex.fixedRealPartVerticalStirlingEnvelope a b :=
            hupper b hb
          _ = C * Real.exp (-(Real.pi / 2) * ‖b‖) *
              (1 + ‖b‖) ^ (a - 1 / 2) := by
            exact
              (mul_assoc C (Real.exp (-(Real.pi / 2) * ‖b‖))
                ((1 + ‖b‖) ^ (a - 1 / 2))).symm⟩

/-- Fixed-line vertical lower envelope for `Complex.Gamma`.

For each fixed real part `a`, the lower half of vertical Stirling gives the
matching positive constant in front of the same exponential-polynomial
envelope; cf. DLMF §5.11. -/
theorem Complex.fixedLineVerticalGammaLowerEnvelope :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    (∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H)) →
    (∀ H b : ℝ, Decidable (H ≤ ‖b‖)) →
    ∀ a : ℝ,
      ∃ c : ℝ,
        0 < c ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := fun hbranch =>
  fun hcompact_half_dec height_split_dec =>
  by
  exact
    fun a =>
      match Complex.fixedLineVerticalGammaTwoSidedEnvelope
          hbranch hcompact_half_dec height_split_dec a with
      | ⟨C, c, hC_pos, hc_pos, hbounds⟩ =>
        ⟨c, hc_pos, fun b hb => (hbounds b hb).2⟩

/-- Fixed-real-part vertical Stirling lower bound for `Complex.Gamma`.

This is the lower half of the classical fixed-line estimate, isolated so the
reciprocal estimate is a norm-order transport rather than an independent
primitive. -/
theorem Complex.Gamma_fixedRealPart_vertical_stirling_lower_bound_classical :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    (∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H)) →
    (∀ H b : ℝ, Decidable (H ≤ ‖b‖)) →
    ∀ a : ℝ,
      ∃ c : ℝ,
        0 < c ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          c * Real.exp (-(Real.pi / 2) * ‖b‖) *
              (1 + ‖b‖) ^ (a - 1 / 2) ≤
            ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ := fun hbranch =>
  fun hcompact_half_dec height_split_dec => by
  intro a
  match Complex.fixedLineVerticalGammaLowerEnvelope
      hbranch hcompact_half_dec height_split_dec a with
  | ⟨c, hc_pos, hlower⟩ =>
    exact
      ⟨c, hc_pos, fun b hb =>
        calc
          c * Real.exp (-(Real.pi / 2) * ‖b‖) *
              (1 + ‖b‖) ^ (a - 1 / 2) =
            c * Complex.fixedRealPartVerticalStirlingEnvelope a b := by
            exact
              mul_assoc c (Real.exp (-(Real.pi / 2) * ‖b‖))
                ((1 + ‖b‖) ^ (a - 1 / 2))
          _ ≤ ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ :=
            hlower b hb
          _ = ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ := rfl⟩

/-- Two-sided fixed-real-part vertical Stirling bounds for `Complex.Gamma`, with the
fixed-line point and envelope named by the owner API.

This is the reusable bundled form of the classical fixed-line asymptotic estimates:
downstream reciprocal and quotient arguments should consume this statement rather
than repeatedly unpacking the two split roots. -/
theorem Complex.Gamma_fixedRealPart_vertical_twoSided_stirling_bounds_owner
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (a : ℝ)
    (hcompact_half_dec : ∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H))
    (height_split_dec : ∀ H b : ℝ, Decidable (H ≤ ‖b‖)) :
    ∃ C : ℝ, ∃ c : ℝ,
      0 < C ∧
      0 < c ∧
      ∀ b : ℝ,
        1 / 2 ≤ ‖b‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope a b ∧
            c * Complex.fixedRealPartVerticalStirlingEnvelope a b ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ := by
  match Complex.fixedLineVerticalGammaUpperEnvelope
      hbranch hcompact_half_dec height_split_dec a with
  | ⟨C, hC_pos, hupper⟩ =>
  match Complex.fixedLineVerticalGammaLowerEnvelope
      hbranch hcompact_half_dec height_split_dec a with
  | ⟨c, hc_pos, hlower⟩ =>
  exact
    ⟨C, c, hC_pos, hc_pos, fun b hb => ⟨hupper b hb, hlower b hb⟩⟩

/-- Classical Gamma/Stirling owner package on the closed right half-plane.

This package is now only product assembly from the canonical local
special-function roots above: sectorial exponential Stirling, its log-norm
consequence, and the two fixed-real-part vertical estimates. -/
theorem Complex.Gamma_closedRightHalfPlane_sectorial_stirling_package_classical :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    (∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H)) →
    (∀ H b : ℝ, Decidable (H ≤ ‖b‖)) →
    (∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        0 < w.re →
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖) ∧
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
              (1 + ‖b‖) ^ (a - 1 / 2)) ∧
    (∀ a : ℝ,
      ∃ c : ℝ,
        0 < c ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          c * Real.exp (-(Real.pi / 2) * ‖b‖) *
              (1 + ‖b‖) ^ (a - 1 / 2) ≤
            ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖) := fun hbranch =>
  fun hcompact_half_dec height_split_dec =>
  by
  have hcoh :
      Complex.BinetSecondFormulaBranchCoherence :=
    Complex.BinetSecondFormulaBranchUniformTailAbsorption.coherence hbranch
  have hexp :
      ∃ R : ℝ, ∃ K : ℝ,
        0 < R ∧
        0 < K ∧
        ∀ w : ℂ,
          0 < w.re →
          Complex.closedRightHalfPlaneSector w →
          R ≤ ‖w‖ →
          ‖Complex.Gamma w * Complex.exp w *
              w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
            K / ‖w‖ := by
    match Complex.Gamma_closedRightHalfPlane_sectorial_exponential_stirling_expansion_classical hbranch with
    | ⟨R, K, hR_pos, hK_pos, hbound⟩ =>
      exact
        ⟨R, K, hR_pos, hK_pos,
          fun w hw_re_pos hw_sector hw_norm =>
            hbound w hw_re_pos hw_sector hw_norm hcoh.2.1 hcoh.2.2⟩
  exact
    ⟨hexp,
      Complex.logGamma_closedRightHalfPlane_sectorial_log_norm_bound_classical hbranch,
      Complex.Gamma_fixedRealPart_vertical_stirling_upper_bound_classical
        hbranch hcompact_half_dec height_split_dec,
      Complex.Gamma_fixedRealPart_vertical_stirling_lower_bound_classical
        hbranch hcompact_half_dec height_split_dec⟩

/-- Sectorial log-norm consequence of closed-sector logarithmic Stirling for
`Complex.Gamma` on the closed right half-plane. -/
theorem Complex.Gamma_closedRightHalfPlane_sectorial_log_norm_bound_classical :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
        Complex.closedRightHalfPlaneSector w →
        (1 / 2 : ℝ) ≤ ‖w‖ →
        Real.log ‖Complex.Gamma w‖ ≤
          C * (1 + 2 * ‖w‖) * Real.log (2 + 2 * ‖w‖) := fun hbranch =>
  Complex.logGamma_closedRightHalfPlane_sectorial_log_norm_bound_classical hbranch

/-- `Complex.Gamma` is nonzero on fixed vertical lines away from the real-axis
pole convention when `|b| ≥ 1/2`. -/
theorem Complex.Gamma_fixedRealPart_vertical_ne_zero_of_half_le_norm
    (a b : ℝ)
    (hb : (1 / 2 : ℝ) ≤ ‖b‖) :
    Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I) ≠ 0 := by
  exact
    fun hzero =>
      match (Complex.Gamma_eq_zero_iff ((a : ℂ) + (b : ℂ) * Complex.I)).mp hzero with
      | ⟨n, hn⟩ =>
        have him_eq : (((a : ℂ) + (b : ℂ) * Complex.I).im) = (-(n : ℂ)).im :=
          congrArg Complex.im hn
        have hleft_im :
            (((a : ℂ) + (b : ℂ) * Complex.I).im) = b := by
          have hmul_im : ((b : ℂ) * Complex.I).im = b :=
            Complex.mul_I_im (b : ℂ)
          have hadd_im :
              (((a : ℂ) + (b : ℂ) * Complex.I).im) =
                (a : ℂ).im + ((b : ℂ) * Complex.I).im :=
            Complex.add_im (a : ℂ) ((b : ℂ) * Complex.I)
          have hofReal_im : (a : ℂ).im = 0 :=
            Complex.ofReal_im a
          have hsum_eq : (a : ℂ).im + ((b : ℂ) * Complex.I).im = 0 + b :=
            congrArg₂ HAdd.hAdd hofReal_im hmul_im
          calc
            (((a : ℂ) + (b : ℂ) * Complex.I).im) =
                (a : ℂ).im + ((b : ℂ) * Complex.I).im := hadd_im
            _ = 0 + b := hsum_eq
            _ = b := zero_add b
        have hright_im : (-(n : ℂ)).im = 0 := by
          calc
            (-(n : ℂ)).im = -((n : ℂ).im) := Complex.neg_im (n : ℂ)
            _ = -0 := congrArg Neg.neg (Complex.ofReal_im (n : ℝ))
            _ = 0 := neg_zero
        have hb_zero : b = 0 :=
          Eq.trans hleft_im.symm (Eq.trans him_eq hright_im)
        have hnorm_zero : ‖b‖ = 0 :=
          Eq.trans (congrArg norm hb_zero) (norm_zero : ‖(0 : ℝ)‖ = 0)
        have hhalf_pos : (0 : ℝ) < 1 / 2 :=
          half_pos zero_lt_one
        have hnot : ¬ (1 / 2 : ℝ) ≤ 0 :=
          not_le.mpr hhalf_pos
        have hhalf_le_zero : (1 / 2 : ℝ) ≤ 0 := by
          calc
            (1 / 2 : ℝ) ≤ ‖b‖ := hb
            _ = 0 := hnorm_zero
        hnot hhalf_le_zero

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
  exact
    fun b hb =>
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
        have hx_def : x = (Real.pi / 2) * ‖b‖ := rfl
        have hH_def : H = 1 + ‖b‖ := rfl
        calc
          c * Real.exp (-x) * H ^ (a - 1 / 2) =
              c * Real.exp (-((Real.pi / 2) * ‖b‖)) *
                H ^ (a - 1 / 2) := by
            exact
              congrArg
                (fun u : ℝ => c * Real.exp (-u) * H ^ (a - 1 / 2))
                hx_def
          _ = c * Real.exp (-(Real.pi / 2) * ‖b‖) *
                H ^ (a - 1 / 2) := by
            exact
              congrArg
                (fun u : ℝ => c * Real.exp u * H ^ (a - 1 / 2))
                (neg_mul (Real.pi / 2) ‖b‖).symm
          _ = c * Real.exp (-(Real.pi / 2) * ‖b‖) *
                (1 + ‖b‖) ^ (a - 1 / 2) := by
            exact
              congrArg
                (fun u : ℝ =>
                  c * Real.exp (-(Real.pi / 2) * ‖b‖) *
                    u ^ (a - 1 / 2))
                hH_def
          _ ≤ ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ :=
            hlower b hb
          _ = ‖G‖ := rfl
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
        have hexp_neg_inv_eq : (Real.exp (-x))⁻¹ = Real.exp x := by
          calc
            (Real.exp (-x))⁻¹ = ((Real.exp x)⁻¹)⁻¹ :=
              congrArg Inv.inv hexp_neg_eq
            _ = Real.exp x := inv_inv (Real.exp x)
        have hpow_neg_eq :
            H ^ (1 / 2 - a) = (H ^ (a - 1 / 2))⁻¹ := by
          have hneg : 1 / 2 - a = -(a - 1 / 2) := by
            exact (neg_sub a (1 / 2)).symm
          exact Eq.trans
            (congrArg (fun y : ℝ => H ^ y) hneg)
            (Real.rpow_neg (le_of_lt hH_pos) (a - 1 / 2))
        calc
          (c * Real.exp (-x) * H ^ (a - 1 / 2))⁻¹ =
              (H ^ (a - 1 / 2))⁻¹ * (c * Real.exp (-x))⁻¹ := by
                exact mul_inv_rev (c * Real.exp (-x)) (H ^ (a - 1 / 2))
          _ = (H ^ (a - 1 / 2))⁻¹ *
              ((Real.exp (-x))⁻¹ * c⁻¹) := by
                exact congrArg
                  (fun y : ℝ => (H ^ (a - 1 / 2))⁻¹ * y)
                  (mul_inv_rev c (Real.exp (-x)))
          _ = c⁻¹ * (Real.exp (-x))⁻¹ * (H ^ (a - 1 / 2))⁻¹ := by
                calc
                  (H ^ (a - 1 / 2))⁻¹ *
                      ((Real.exp (-x))⁻¹ * c⁻¹) =
                    ((H ^ (a - 1 / 2))⁻¹ * (Real.exp (-x))⁻¹) * c⁻¹ :=
                      (mul_assoc (H ^ (a - 1 / 2))⁻¹ (Real.exp (-x))⁻¹ c⁻¹).symm
                  _ = c⁻¹ *
                      ((H ^ (a - 1 / 2))⁻¹ * (Real.exp (-x))⁻¹) :=
                    mul_comm ((H ^ (a - 1 / 2))⁻¹ * (Real.exp (-x))⁻¹) c⁻¹
                  _ = c⁻¹ *
                      ((Real.exp (-x))⁻¹ * (H ^ (a - 1 / 2))⁻¹) := by
                    exact congrArg
                      (fun y : ℝ => c⁻¹ * y)
                      (mul_comm (H ^ (a - 1 / 2))⁻¹ (Real.exp (-x))⁻¹)
                  _ = c⁻¹ * (Real.exp (-x))⁻¹ *
                      (H ^ (a - 1 / 2))⁻¹ :=
                    (mul_assoc c⁻¹ (Real.exp (-x))⁻¹
                      (H ^ (a - 1 / 2))⁻¹).symm
          _ = (c⁻¹ * Real.exp x) * (H ^ (a - 1 / 2))⁻¹ := by
                exact congrArg
                  (fun y : ℝ => (c⁻¹ * y) * (H ^ (a - 1 / 2))⁻¹)
                  hexp_neg_inv_eq
          _ = (c⁻¹ * Real.exp x) * H ^ (1 / 2 - a) := by
                exact congrArg
                  (fun y : ℝ => (c⁻¹ * Real.exp x) * y)
                  hpow_neg_eq.symm
          _ = c⁻¹ * Real.exp x * H ^ (1 / 2 - a) := rfl
      calc
        ‖G⁻¹‖ = ‖G‖⁻¹ := hG_inv_norm
        _ ≤ (c * Real.exp (-x) * H ^ (a - 1 / 2))⁻¹ :=
          hreciprocal_le
        _ = c⁻¹ * Real.exp x * H ^ (1 / 2 - a) :=
          htarget_eq

/-- Reciprocal transport for vertical-strip Gamma estimates.

A uniform lower Stirling bound on a real strip gives the matching reciprocal
upper bound on the same large-height region. -/
theorem Complex.Gamma_verticalStrip_reciprocal_bound_of_lower_bound
    {A B H c : ℝ}
    (hc_pos : 0 < c)
    (hlower :
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          c * Complex.fixedRealPartVerticalStirlingEnvelope x y ≤
            ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖) :
    ∀ x y : ℝ,
      A ≤ x →
      x ≤ B →
      H ≤ ‖y‖ →
        ‖(Complex.Gamma (Complex.fixedRealPartVerticalPoint x y))⁻¹‖ ≤
          c⁻¹ * Complex.fixedRealPartVerticalReciprocalStirlingEnvelope x y := by
  exact
    fun x y hx_left hx_right hy =>
      let R : ℝ := (Real.pi / 2) * ‖y‖
      let T : ℝ := 1 + ‖y‖
      let G : ℂ := Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)
      have hT_pos : 0 < T :=
        lt_of_lt_of_le zero_lt_one
          (le_add_of_nonneg_right (norm_nonneg y))
      have hexp_pos : 0 < Real.exp (-R) :=
        Real.exp_pos (-R)
      have hrpow_pos : 0 < T ^ (x - 1 / 2) :=
        Real.rpow_pos_of_pos hT_pos (x - 1 / 2)
      have henvelope_pos :
          0 < c * Real.exp (-R) * T ^ (x - 1 / 2) :=
        mul_pos (mul_pos hc_pos hexp_pos) hrpow_pos
      have hG_lower :
          c * Real.exp (-R) * T ^ (x - 1 / 2) ≤ ‖G‖ := by
        have hR_def : R = (Real.pi / 2) * ‖y‖ := rfl
        have hT_def : T = 1 + ‖y‖ := rfl
        calc
          c * Real.exp (-R) * T ^ (x - 1 / 2) =
              c * Real.exp (-((Real.pi / 2) * ‖y‖)) *
                T ^ (x - 1 / 2) := by
            exact
              congrArg
                (fun u : ℝ => c * Real.exp (-u) * T ^ (x - 1 / 2))
                hR_def
          _ = c * Real.exp (-(Real.pi / 2) * ‖y‖) *
                T ^ (x - 1 / 2) := by
            exact
              congrArg
                (fun u : ℝ => c * Real.exp u * T ^ (x - 1 / 2))
                (neg_mul (Real.pi / 2) ‖y‖).symm
          _ = c * Real.exp (-(Real.pi / 2) * ‖y‖) *
                (1 + ‖y‖) ^ (x - 1 / 2) := by
            exact
              congrArg
                (fun u : ℝ =>
                  c * Real.exp (-(Real.pi / 2) * ‖y‖) *
                    u ^ (x - 1 / 2))
                hT_def
          _ = c * Complex.fixedRealPartVerticalStirlingEnvelope x y := by
            exact
              mul_assoc c (Real.exp (-(Real.pi / 2) * ‖y‖))
                ((1 + ‖y‖) ^ (x - 1 / 2))
          _ ≤ ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ :=
            hlower x y hx_left hx_right hy
          _ = ‖G‖ := rfl
      have hG_inv_norm :
          ‖G⁻¹‖ = ‖G‖⁻¹ :=
        norm_inv G
      have hreciprocal_le :
          ‖G‖⁻¹ ≤ (c * Real.exp (-R) * T ^ (x - 1 / 2))⁻¹ :=
        inv_le_inv_of_le henvelope_pos hG_lower
      have htarget_eq :
          (c * Real.exp (-R) * T ^ (x - 1 / 2))⁻¹ =
            c⁻¹ * Complex.fixedRealPartVerticalReciprocalStirlingEnvelope x y := by
        have hexp_neg_eq : Real.exp (-R) = (Real.exp R)⁻¹ :=
          Real.exp_neg R
        have hexp_neg_inv_eq : (Real.exp (-R))⁻¹ = Real.exp R := by
          calc
            (Real.exp (-R))⁻¹ = ((Real.exp R)⁻¹)⁻¹ :=
              congrArg Inv.inv hexp_neg_eq
            _ = Real.exp R := inv_inv (Real.exp R)
        have hpow_neg_eq :
            T ^ (1 / 2 - x) = (T ^ (x - 1 / 2))⁻¹ := by
          have hneg : 1 / 2 - x = -(x - 1 / 2) := by
            exact (neg_sub x (1 / 2)).symm
          exact Eq.trans
            (congrArg (fun u : ℝ => T ^ u) hneg)
            (Real.rpow_neg (le_of_lt hT_pos) (x - 1 / 2))
        calc
          (c * Real.exp (-R) * T ^ (x - 1 / 2))⁻¹ =
              (T ^ (x - 1 / 2))⁻¹ * (c * Real.exp (-R))⁻¹ := by
                exact mul_inv_rev (c * Real.exp (-R)) (T ^ (x - 1 / 2))
          _ = (T ^ (x - 1 / 2))⁻¹ *
              ((Real.exp (-R))⁻¹ * c⁻¹) := by
                exact congrArg
                  (fun u : ℝ => (T ^ (x - 1 / 2))⁻¹ * u)
                  (mul_inv_rev c (Real.exp (-R)))
          _ = c⁻¹ * (Real.exp (-R))⁻¹ * (T ^ (x - 1 / 2))⁻¹ := by
                calc
                  (T ^ (x - 1 / 2))⁻¹ *
                      ((Real.exp (-R))⁻¹ * c⁻¹) =
                    ((T ^ (x - 1 / 2))⁻¹ * (Real.exp (-R))⁻¹) * c⁻¹ :=
                      (mul_assoc (T ^ (x - 1 / 2))⁻¹ (Real.exp (-R))⁻¹ c⁻¹).symm
                  _ = c⁻¹ *
                      ((T ^ (x - 1 / 2))⁻¹ * (Real.exp (-R))⁻¹) :=
                    mul_comm ((T ^ (x - 1 / 2))⁻¹ * (Real.exp (-R))⁻¹) c⁻¹
                  _ = c⁻¹ *
                      ((Real.exp (-R))⁻¹ * (T ^ (x - 1 / 2))⁻¹) := by
                    exact congrArg
                      (fun u : ℝ => c⁻¹ * u)
                      (mul_comm (T ^ (x - 1 / 2))⁻¹ (Real.exp (-R))⁻¹)
                  _ = c⁻¹ * (Real.exp (-R))⁻¹ *
                      (T ^ (x - 1 / 2))⁻¹ :=
                    (mul_assoc c⁻¹ (Real.exp (-R))⁻¹
                      (T ^ (x - 1 / 2))⁻¹).symm
          _ = (c⁻¹ * Real.exp R) * (T ^ (x - 1 / 2))⁻¹ := by
                exact congrArg
                  (fun u : ℝ => (c⁻¹ * u) * (T ^ (x - 1 / 2))⁻¹)
                  hexp_neg_inv_eq
          _ = (c⁻¹ * Real.exp R) * T ^ (1 / 2 - x) := by
                exact congrArg
                  (fun u : ℝ => (c⁻¹ * Real.exp R) * u)
                  hpow_neg_eq.symm
          _ = c⁻¹ * (Real.exp ((Real.pi / 2) * ‖y‖) *
                (1 + ‖y‖) ^ (1 / 2 - x)) := by
                have hR_def : R = (Real.pi / 2) * ‖y‖ := rfl
                have hT_def : T = 1 + ‖y‖ := rfl
                calc
                  (c⁻¹ * Real.exp R) * T ^ (1 / 2 - x) =
                    c⁻¹ * (Real.exp R * T ^ (1 / 2 - x)) :=
                      mul_assoc c⁻¹ (Real.exp R) (T ^ (1 / 2 - x))
                  _ = c⁻¹ * (Real.exp ((Real.pi / 2) * ‖y‖) *
                      T ^ (1 / 2 - x)) := by
                    exact congrArg
                      (fun u : ℝ => c⁻¹ * (Real.exp u * T ^ (1 / 2 - x)))
                      hR_def
                  _ = c⁻¹ * (Real.exp ((Real.pi / 2) * ‖y‖) *
                      (1 + ‖y‖) ^ (1 / 2 - x)) := by
                    exact congrArg
                      (fun u : ℝ =>
                        c⁻¹ * (Real.exp ((Real.pi / 2) * ‖y‖) *
                          u ^ (1 / 2 - x)))
                      hT_def
          _ = c⁻¹ * Complex.fixedRealPartVerticalReciprocalStirlingEnvelope x y := rfl
      calc
        ‖G⁻¹‖ = ‖G‖⁻¹ := hG_inv_norm
        _ ≤ (c * Real.exp (-R) * T ^ (x - 1 / 2))⁻¹ :=
          hreciprocal_le
        _ = c⁻¹ * Complex.fixedRealPartVerticalReciprocalStirlingEnvelope x y :=
          htarget_eq

/-- Large-height vertical-strip reciprocal Gamma bound from the lower half of
the uniform strip Stirling theorem. -/
theorem Complex.Gamma_inv_verticalStrip_largeHeight_stirling_bound_classical
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ,
      0 < H ∧
      0 < C ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ‖(Complex.Gamma (Complex.fixedRealPartVerticalPoint x y))⁻¹‖ ≤
            C * Complex.fixedRealPartVerticalReciprocalStirlingEnvelope x y := by
  match Complex.sectorialStirling_verticalStrip_largeHeight_classical hbranch A B with
  | ⟨H, C, c, hH_pos, _hC_pos, hc_pos, hbounds⟩ =>
      exact
        ⟨H, c⁻¹, hH_pos, inv_pos.mpr hc_pos,
          Complex.Gamma_verticalStrip_reciprocal_bound_of_lower_bound
            hc_pos
            (fun x y hx_left hx_right hy =>
              (hbounds x y hx_left hx_right hy).2)⟩

/-- Coordinate-free large-height vertical-strip reciprocal Gamma bound. -/
theorem Complex.Gamma_inv_verticalStrip_largeHeight_stirling_bound_classical_point
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ,
      0 < H ∧
      0 < C ∧
      ∀ w : ℂ,
        A ≤ w.re →
        w.re ≤ B →
        H ≤ ‖w.im‖ →
          ‖(Complex.Gamma w)⁻¹‖ ≤
            C * Complex.fixedRealPartVerticalReciprocalStirlingEnvelope w.re w.im := by
  match Complex.Gamma_inv_verticalStrip_largeHeight_stirling_bound_classical
      hbranch A B with
  | ⟨H, C, hH_pos, hC_pos, hbound⟩ =>
      exact
        ⟨H, C, hH_pos, hC_pos,
          fun w hw_left hw_right hw_im =>
            have hpoint : Complex.fixedRealPartVerticalPoint w.re w.im = w :=
              Complex.fixedRealPartVerticalPoint_re_im w
            have hnorm :
                ‖(Complex.Gamma w)⁻¹‖ =
                  ‖(Complex.Gamma
                    (Complex.fixedRealPartVerticalPoint w.re w.im))⁻¹‖ := by
              exact
                (congrArg
                  (fun u : ℂ => ‖(Complex.Gamma u)⁻¹‖)
                  hpoint).symm
            calc
              ‖(Complex.Gamma w)⁻¹‖ =
                  ‖(Complex.Gamma
                    (Complex.fixedRealPartVerticalPoint w.re w.im))⁻¹‖ :=
                hnorm
              _ ≤ C *
                  Complex.fixedRealPartVerticalReciprocalStirlingEnvelope
                    w.re w.im :=
                hbound w.re w.im hw_left hw_right hw_im⟩

/-- Large-height vertical-strip Gamma upper bound from the upper half of the
uniform strip Stirling theorem. -/
theorem Complex.Gamma_verticalStrip_largeHeight_stirling_bound_classical
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ,
      0 < H ∧
      0 < C ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope x y := by
  match Complex.sectorialStirling_verticalStrip_largeHeight_classical hbranch A B with
  | ⟨H, C, _c, hH_pos, hC_pos, _hc_pos, hbounds⟩ =>
      exact
        ⟨H, C, hH_pos, hC_pos,
          fun x y hx_left hx_right hy =>
            (hbounds x y hx_left hx_right hy).1⟩

/-- Coordinate-free large-height vertical-strip Gamma upper bound. -/
theorem Complex.Gamma_verticalStrip_largeHeight_stirling_bound_classical_point
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption)
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ,
      0 < H ∧
      0 < C ∧
      ∀ w : ℂ,
        A ≤ w.re →
        w.re ≤ B →
        H ≤ ‖w.im‖ →
          ‖Complex.Gamma w‖ ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope w.re w.im := by
  match Complex.Gamma_verticalStrip_largeHeight_stirling_bound_classical
      hbranch A B with
  | ⟨H, C, hH_pos, hC_pos, hbound⟩ =>
      exact
        ⟨H, C, hH_pos, hC_pos,
          fun w hw_left hw_right hw_im =>
            have hpoint : Complex.fixedRealPartVerticalPoint w.re w.im = w :=
              Complex.fixedRealPartVerticalPoint_re_im w
            have hnorm :
                ‖Complex.Gamma w‖ =
                  ‖Complex.Gamma
                    (Complex.fixedRealPartVerticalPoint w.re w.im)‖ := by
              exact
                (congrArg
                  (fun u : ℂ => ‖Complex.Gamma u‖)
                  hpoint).symm
            calc
              ‖Complex.Gamma w‖ =
                  ‖Complex.Gamma
                    (Complex.fixedRealPartVerticalPoint w.re w.im)‖ :=
                hnorm
              _ ≤ C *
                  Complex.fixedRealPartVerticalStirlingEnvelope
                    w.re w.im :=
                hbound w.re w.im hw_left hw_right hw_im⟩

/-- The direct fixed-line Stirling envelope is bounded by `1` on the closed
half-strip used by the `Gammaℝ` half-argument. -/
theorem Complex.fixedRealPartVerticalStirlingEnvelope_zero_half_le_one
    {x y : ℝ}
    (hx_half : x ≤ (1 / 2 : ℝ)) :
    Complex.fixedRealPartVerticalStirlingEnvelope x y ≤ 1 := by
  let T : ℝ := 1 + ‖y‖
  have hT_pos : 0 < T :=
    lt_of_lt_of_le zero_lt_one
      (le_add_of_nonneg_right (norm_nonneg y))
  have hT_ge_one : (1 : ℝ) ≤ T :=
    le_add_of_nonneg_right (norm_nonneg y)
  have hexponent_nonpos : x - 1 / 2 ≤ 0 :=
    sub_nonpos.mpr hx_half
  have hpow_le_one : T ^ (x - 1 / 2) ≤ 1 :=
    Real.rpow_le_one_of_one_le_of_nonpos hT_ge_one hexponent_nonpos
  have hpow_nonneg : 0 ≤ T ^ (x - 1 / 2) :=
    Real.rpow_nonneg (le_of_lt hT_pos) (x - 1 / 2)
  have hpi_div_nonneg : 0 ≤ Real.pi / 2 :=
    div_nonneg (le_of_lt Real.pi_pos) zero_le_two
  have hneg_pi_div_nonpos : -(Real.pi / 2) ≤ 0 :=
    neg_nonpos.mpr hpi_div_nonneg
  have hheight_nonneg : 0 ≤ ‖y‖ :=
    norm_nonneg y
  have hexp_arg_nonpos : -(Real.pi / 2) * ‖y‖ ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hneg_pi_div_nonpos hheight_nonneg
  have hexp_le_one :
      Real.exp (-(Real.pi / 2) * ‖y‖) ≤ 1 := by
    calc
      Real.exp (-(Real.pi / 2) * ‖y‖) ≤ Real.exp 0 :=
        Real.exp_le_exp.mpr hexp_arg_nonpos
      _ = 1 := Real.exp_zero
  have hexp_nonneg : 0 ≤ Real.exp (-(Real.pi / 2) * ‖y‖) :=
    le_of_lt (Real.exp_pos (-(Real.pi / 2) * ‖y‖))
  calc
    Complex.fixedRealPartVerticalStirlingEnvelope x y =
        Real.exp (-(Real.pi / 2) * ‖y‖) * T ^ (x - 1 / 2) := rfl
    _ ≤ 1 * 1 :=
      mul_le_mul hexp_le_one hpow_le_one hpow_nonneg zero_le_one
    _ = 1 := one_mul 1

/-- Uniform finite-order Gamma bound on the closed half-strip
`0 ≤ Re w ≤ 1/2`, away from the real axis. -/
theorem Complex.Gamma_zero_half_strip_verticalTail_finiteOrder_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        0 ≤ w.re →
        w.re ≤ (1 / 2 : ℝ) →
        (1 / 2 : ℝ) ≤ ‖w.im‖ →
          ‖Complex.Gamma w‖ ≤
            A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  match Complex.Gamma_verticalStrip_largeHeight_stirling_bound_classical_point
      hbranch 0 (1 / 2) with
  | ⟨H, Clarge, hH_pos, hClarge_pos, hlarge⟩ =>
  match Complex.Gamma_closedRealStrip_compactHeight_bound
      0 (1 / 2) (1 / 2) H one_half_pos with
  | ⟨Ccompact, hCcompact_pos, hcompact⟩ =>
      let A : ℝ := Clarge + Ccompact
      let B : ℝ := 1
      have hA_pos : 0 < A :=
        add_pos hClarge_pos hCcompact_pos
      have hB_pos : 0 < B := zero_lt_one
      have hClarge_le_A : Clarge ≤ A :=
        le_add_of_nonneg_right (le_of_lt hCcompact_pos)
      have hCcompact_le_A : Ccompact ≤ A :=
        le_add_of_nonneg_left (le_of_lt hClarge_pos)
      exact
        ⟨A, B, 1, hA_pos, hB_pos,
          fun w hw_re_nonneg hw_re_half hw_im_tail =>
            if hw_large : H ≤ ‖w.im‖ then
              have hlarge_w :
                  ‖Complex.Gamma w‖ ≤
                    Clarge * Complex.fixedRealPartVerticalStirlingEnvelope
                        w.re w.im :=
                hlarge w hw_re_nonneg hw_re_half hw_large
              have henv :
                  Complex.fixedRealPartVerticalStirlingEnvelope w.re w.im ≤ 1 :=
                Complex.fixedRealPartVerticalStirlingEnvelope_zero_half_le_one
                  hw_re_half
              have hscaled_env :
                  Clarge * Complex.fixedRealPartVerticalStirlingEnvelope
                      w.re w.im ≤ Clarge * 1 :=
                mul_le_mul_of_nonneg_left henv (le_of_lt hClarge_pos)
              have hconst_le_A : Clarge * 1 ≤ A := by
                calc
                  Clarge * 1 = Clarge := mul_one Clarge
                  _ ≤ A := hClarge_le_A
              have hbase_nonneg : 0 ≤ 1 + ‖w‖ :=
                le_trans zero_le_one
                  (le_add_of_nonneg_right (norm_nonneg w))
              have hpow_nonneg : 0 ≤ (1 + ‖w‖) ^ (1 : ℕ) :=
                pow_nonneg hbase_nonneg 1
              have hexponent_nonneg : 0 ≤ B * (1 + ‖w‖) ^ (1 : ℕ) :=
                mul_nonneg (le_of_lt hB_pos) hpow_nonneg
              have hone_le_exp :
                  (1 : ℝ) ≤ Real.exp (B * (1 + ‖w‖) ^ (1 : ℕ)) :=
                Real.one_le_exp hexponent_nonneg
              have hA_nonneg : 0 ≤ A :=
                le_of_lt hA_pos
              have hA_le_Aexp :
                  A ≤ A * Real.exp (B * (1 + ‖w‖) ^ (1 : ℕ)) := by
                calc
                  A = A * 1 := (mul_one A).symm
                  _ ≤ A * Real.exp (B * (1 + ‖w‖) ^ (1 : ℕ)) :=
                    mul_le_mul_of_nonneg_left hone_le_exp hA_nonneg
              calc
                ‖Complex.Gamma w‖ ≤
                    Clarge * Complex.fixedRealPartVerticalStirlingEnvelope
                      w.re w.im := hlarge_w
                _ ≤ Clarge * 1 := hscaled_env
                _ ≤ A := hconst_le_A
                _ ≤ A * Real.exp (B * (1 + ‖w‖) ^ (1 : ℕ)) :=
                  hA_le_Aexp
            else
              have hw_compact_upper : ‖w.im‖ ≤ H :=
                le_of_not_ge hw_large
              have hcompact_w :
                  ‖Complex.Gamma w‖ ≤ Ccompact :=
                hcompact w hw_re_nonneg hw_re_half hw_im_tail hw_compact_upper
              have hbase_nonneg : 0 ≤ 1 + ‖w‖ :=
                le_trans zero_le_one
                  (le_add_of_nonneg_right (norm_nonneg w))
              have hpow_nonneg : 0 ≤ (1 + ‖w‖) ^ (1 : ℕ) :=
                pow_nonneg hbase_nonneg 1
              have hexponent_nonneg : 0 ≤ B * (1 + ‖w‖) ^ (1 : ℕ) :=
                mul_nonneg (le_of_lt hB_pos) hpow_nonneg
              have hone_le_exp :
                  (1 : ℝ) ≤ Real.exp (B * (1 + ‖w‖) ^ (1 : ℕ)) :=
                Real.one_le_exp hexponent_nonneg
              have hA_nonneg : 0 ≤ A :=
                le_of_lt hA_pos
              have hA_le_Aexp :
                  A ≤ A * Real.exp (B * (1 + ‖w‖) ^ (1 : ℕ)) := by
                calc
                  A = A * 1 := (mul_one A).symm
                  _ ≤ A * Real.exp (B * (1 + ‖w‖) ^ (1 : ℕ)) :=
                    mul_le_mul_of_nonneg_left hone_le_exp hA_nonneg
              calc
                ‖Complex.Gamma w‖ ≤ Ccompact := hcompact_w
                _ ≤ A := hCcompact_le_A
                _ ≤ A * Real.exp (B * (1 + ‖w‖) ^ (1 : ℕ)) :=
                  hA_le_Aexp⟩

/-- The reciprocal fixed-line Stirling envelope is finite-order on the
half-strip used by the `Gammaℝ` half-argument. -/
theorem Complex.fixedRealPartVerticalReciprocalStirlingEnvelope_zero_half_le_exp
    {x y : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hx_half : x ≤ (1 / 2 : ℝ)) :
    Complex.fixedRealPartVerticalReciprocalStirlingEnvelope x y ≤
      Real.exp (((Real.pi / 2) + 1) *
        (1 + ‖Complex.fixedRealPartVerticalPoint x y‖)) := by
  let T : ℝ := 1 + ‖y‖
  let e : ℝ := 1 / 2 - x
  let P : ℂ := Complex.fixedRealPartVerticalPoint x y
  have hT_pos : 0 < T :=
    lt_of_lt_of_le zero_lt_one
      (le_add_of_nonneg_right (norm_nonneg y))
  have hT_ge_one : (1 : ℝ) ≤ T :=
    le_add_of_nonneg_right (norm_nonneg y)
  have he_nonneg : 0 ≤ e := by
    exact sub_nonneg.mpr hx_half
  have he_le_one : e ≤ 1 := by
    have hhalf_le_one : (1 / 2 : ℝ) ≤ 1 :=
      div_le_self zero_le_one one_le_two
    calc
      e = 1 / 2 - x := rfl
      _ ≤ 1 / 2 := sub_le_self (1 / 2 : ℝ) hx_nonneg
      _ ≤ 1 := hhalf_le_one
  have hrpow_le_T :
      T ^ e ≤ T := by
    calc
      T ^ e ≤ T ^ (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hT_ge_one he_le_one
      _ = T := Real.rpow_one T
  have hT_eq : T = ‖y‖ + 1 := by
    exact add_comm 1 ‖y‖
  have hT_le_exp_y : T ≤ Real.exp ‖y‖ := by
    calc
      T = ‖y‖ + 1 := hT_eq
      _ ≤ Real.exp ‖y‖ := Real.add_one_le_exp ‖y‖
  have hpow_le_exp_y :
      T ^ e ≤ Real.exp ‖y‖ :=
    le_trans hrpow_le_T hT_le_exp_y
  have hexp_nonneg : 0 ≤ Real.exp ((Real.pi / 2) * ‖y‖) :=
    le_of_lt (Real.exp_pos ((Real.pi / 2) * ‖y‖))
  have henvelope_le :
      Real.exp ((Real.pi / 2) * ‖y‖) * T ^ e ≤
        Real.exp ((Real.pi / 2) * ‖y‖) * Real.exp ‖y‖ :=
    mul_le_mul_of_nonneg_left hpow_le_exp_y hexp_nonneg
  have hexp_product :
      Real.exp ((Real.pi / 2) * ‖y‖) * Real.exp ‖y‖ =
        Real.exp (((Real.pi / 2) + 1) * ‖y‖) := by
    calc
      Real.exp ((Real.pi / 2) * ‖y‖) * Real.exp ‖y‖ =
          Real.exp (((Real.pi / 2) * ‖y‖) + ‖y‖) :=
        (Real.exp_add ((Real.pi / 2) * ‖y‖) ‖y‖).symm
      _ = Real.exp (((Real.pi / 2) + 1) * ‖y‖) := by
        have hsum :
            (Real.pi / 2) * ‖y‖ + ‖y‖ =
              ((Real.pi / 2) + 1) * ‖y‖ := by
          calc
            (Real.pi / 2) * ‖y‖ + ‖y‖ =
                (Real.pi / 2) * ‖y‖ + 1 * ‖y‖ := by
              exact congrArg (fun u : ℝ => (Real.pi / 2) * ‖y‖ + u)
                (one_mul ‖y‖).symm
            _ = ((Real.pi / 2) + 1) * ‖y‖ :=
              (add_mul (Real.pi / 2) 1 ‖y‖).symm
        exact congrArg Real.exp hsum
  have hy_norm_le_P : ‖y‖ ≤ ‖P‖ := by
    have him_le : ‖P.im‖ ≤ ‖P‖ :=
      Complex.abs_im_le_abs P
    have him_eq : P.im = y :=
      Complex.fixedRealPartVerticalPoint_im x y
    have hnorm_eq : ‖P.im‖ = ‖y‖ :=
      congrArg norm him_eq
    calc
      ‖y‖ = ‖P.im‖ := hnorm_eq.symm
      _ ≤ ‖P‖ := him_le
  have hy_le_one_add_P : ‖y‖ ≤ 1 + ‖P‖ :=
    le_trans hy_norm_le_P (le_add_of_nonneg_left zero_le_one)
  have hcoef_nonneg : 0 ≤ (Real.pi / 2) + 1 := by
    have hpi_div_nonneg : 0 ≤ Real.pi / 2 :=
      div_nonneg (le_of_lt Real.pi_pos) zero_le_two
    exact add_nonneg hpi_div_nonneg zero_le_one
  have hexponent_le :
      ((Real.pi / 2) + 1) * ‖y‖ ≤
        ((Real.pi / 2) + 1) * (1 + ‖P‖) :=
    mul_le_mul_of_nonneg_left hy_le_one_add_P hcoef_nonneg
  have hexp_le :
      Real.exp (((Real.pi / 2) + 1) * ‖y‖) ≤
        Real.exp (((Real.pi / 2) + 1) * (1 + ‖P‖)) :=
    Real.exp_le_exp.mpr hexponent_le
  calc
    Complex.fixedRealPartVerticalReciprocalStirlingEnvelope x y =
        Real.exp ((Real.pi / 2) * ‖y‖) * T ^ e := rfl
    _ ≤ Real.exp ((Real.pi / 2) * ‖y‖) * Real.exp ‖y‖ :=
      henvelope_le
    _ = Real.exp (((Real.pi / 2) + 1) * ‖y‖) :=
      hexp_product
    _ ≤ Real.exp (((Real.pi / 2) + 1) * (1 + ‖P‖)) :=
      hexp_le

/-- Uniform finite-order reciprocal Gamma bound on the closed half-strip
`0 ≤ Re w ≤ 1/2`, away from the real axis. -/
theorem Complex.Gamma_inv_zero_half_strip_verticalTail_finiteOrder_bound
    (hbranch : Complex.BinetSecondFormulaBranchUniformTailAbsorption) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        0 ≤ w.re →
        w.re ≤ (1 / 2 : ℝ) →
        (1 / 2 : ℝ) ≤ ‖w.im‖ →
          ‖(Complex.Gamma w)⁻¹‖ ≤
            A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  match Complex.Gamma_inv_verticalStrip_largeHeight_stirling_bound_classical_point
      hbranch 0 (1 / 2) with
  | ⟨H, Clarge, hH_pos, hClarge_pos, hlarge⟩ =>
  match Complex.Gamma_inv_closedRealStrip_compactHeight_bound
      0 (1 / 2) (1 / 2) H one_half_pos with
  | ⟨Ccompact, hCcompact_pos, hcompact⟩ =>
      let A : ℝ := Clarge + Ccompact
      let B : ℝ := (Real.pi / 2) + 1
      have hA_pos : 0 < A :=
        add_pos hClarge_pos hCcompact_pos
      have hB_pos : 0 < B := by
        have hpi_div_nonneg : 0 ≤ Real.pi / 2 :=
          div_nonneg (le_of_lt Real.pi_pos) zero_le_two
        exact lt_of_lt_of_le zero_lt_one
          (le_add_of_nonneg_left hpi_div_nonneg)
      have hClarge_le_A : Clarge ≤ A :=
        le_add_of_nonneg_right (le_of_lt hCcompact_pos)
      have hCcompact_le_A : Ccompact ≤ A :=
        le_add_of_nonneg_left (le_of_lt hClarge_pos)
      exact
        ⟨A, B, 1, hA_pos, hB_pos,
          fun w hw_re_nonneg hw_re_half hw_im_tail =>
            if hw_large : H ≤ ‖w.im‖ then
              have hlarge_w :
                  ‖(Complex.Gamma w)⁻¹‖ ≤
                    Clarge *
                      Complex.fixedRealPartVerticalReciprocalStirlingEnvelope
                        w.re w.im :=
                hlarge w hw_re_nonneg hw_re_half hw_large
              have henv :
                  Complex.fixedRealPartVerticalReciprocalStirlingEnvelope
                      w.re w.im ≤
                    Real.exp (B * (1 + ‖w‖)) := by
                have hpoint_eq :
                    Complex.fixedRealPartVerticalPoint w.re w.im = w := by
                  exact Complex.ext
                    (Complex.fixedRealPartVerticalPoint_re w.re w.im)
                    (Complex.fixedRealPartVerticalPoint_im w.re w.im)
                have hraw :
                    Complex.fixedRealPartVerticalReciprocalStirlingEnvelope
                        w.re w.im ≤
                      Real.exp (((Real.pi / 2) + 1) *
                        (1 + ‖Complex.fixedRealPartVerticalPoint w.re w.im‖)) :=
                  Complex.fixedRealPartVerticalReciprocalStirlingEnvelope_zero_half_le_exp
                    hw_re_nonneg hw_re_half
                have hB_def : B = (Real.pi / 2) + 1 := rfl
                have hexp_eq :
                    Real.exp (((Real.pi / 2) + 1) *
                        (1 + ‖Complex.fixedRealPartVerticalPoint w.re w.im‖)) =
                      Real.exp (B * (1 + ‖w‖)) := by
                  have hnorm_eq :
                      ‖Complex.fixedRealPartVerticalPoint w.re w.im‖ = ‖w‖ :=
                    congrArg norm hpoint_eq
                  calc
                    Real.exp (((Real.pi / 2) + 1) *
                        (1 + ‖Complex.fixedRealPartVerticalPoint w.re w.im‖)) =
                        Real.exp (((Real.pi / 2) + 1) * (1 + ‖w‖)) := by
                      exact congrArg
                        (fun u : ℝ => Real.exp (((Real.pi / 2) + 1) * (1 + u)))
                        hnorm_eq
                    _ = Real.exp (B * (1 + ‖w‖)) := by
                      exact congrArg
                        (fun u : ℝ => Real.exp (u * (1 + ‖w‖)))
                        hB_def.symm
                exact le_trans hraw (le_of_eq hexp_eq)
              have henv_nonneg :
                  0 ≤
                    Complex.fixedRealPartVerticalReciprocalStirlingEnvelope
                      w.re w.im :=
                le_of_lt
                  (Complex.fixedRealPartVerticalReciprocalStirlingEnvelope_pos
                    w.re w.im)
              have hexp_nonneg : 0 ≤ Real.exp (B * (1 + ‖w‖)) :=
                le_of_lt (Real.exp_pos (B * (1 + ‖w‖)))
              have hscaled_env :
                  Clarge *
                      Complex.fixedRealPartVerticalReciprocalStirlingEnvelope
                        w.re w.im ≤
                    Clarge * Real.exp (B * (1 + ‖w‖)) :=
                mul_le_mul_of_nonneg_left henv (le_of_lt hClarge_pos)
              have hscaled_const :
                  Clarge * Real.exp (B * (1 + ‖w‖)) ≤
                    A * Real.exp (B * (1 + ‖w‖)) :=
                mul_le_mul_of_nonneg_right hClarge_le_A hexp_nonneg
              have hpow_one :
                  (1 + ‖w‖) ^ (1 : ℕ) = 1 + ‖w‖ :=
                pow_one (1 + ‖w‖)
              calc
                ‖(Complex.Gamma w)⁻¹‖ ≤
                    Clarge *
                      Complex.fixedRealPartVerticalReciprocalStirlingEnvelope
                        w.re w.im := hlarge_w
                _ ≤ Clarge * Real.exp (B * (1 + ‖w‖)) :=
                  hscaled_env
                _ ≤ A * Real.exp (B * (1 + ‖w‖)) :=
                  hscaled_const
                _ = A * Real.exp (B * (1 + ‖w‖) ^ (1 : ℕ)) := by
                  exact congrArg (fun u : ℝ => A * Real.exp (B * u))
                    hpow_one.symm
            else
              have hw_compact_upper : ‖w.im‖ ≤ H :=
                le_of_not_ge hw_large
              have hcompact_w :
                  ‖(Complex.Gamma w)⁻¹‖ ≤ Ccompact :=
                hcompact w hw_re_nonneg hw_re_half hw_im_tail hw_compact_upper
              have hbase_nonneg : 0 ≤ 1 + ‖w‖ :=
                le_trans zero_le_one
                  (le_add_of_nonneg_right (norm_nonneg w))
              have hpow_nonneg : 0 ≤ (1 + ‖w‖) ^ (1 : ℕ) :=
                pow_nonneg hbase_nonneg 1
              have hexponent_nonneg : 0 ≤ B * (1 + ‖w‖) ^ (1 : ℕ) :=
                mul_nonneg (le_of_lt hB_pos) hpow_nonneg
              have hone_le_exp :
                  (1 : ℝ) ≤ Real.exp (B * (1 + ‖w‖) ^ (1 : ℕ)) :=
                Real.one_le_exp hexponent_nonneg
              have hCcompact_nonneg : 0 ≤ Ccompact :=
                le_of_lt hCcompact_pos
              have hconst_le_A :
                  Ccompact ≤ A :=
                hCcompact_le_A
              have hA_nonneg : 0 ≤ A :=
                le_of_lt hA_pos
              have hA_le_Aexp :
                  A ≤ A * Real.exp (B * (1 + ‖w‖) ^ (1 : ℕ)) := by
                calc
                  A = A * 1 := (mul_one A).symm
                  _ ≤ A * Real.exp (B * (1 + ‖w‖) ^ (1 : ℕ)) :=
                    mul_le_mul_of_nonneg_left hone_le_exp hA_nonneg
              calc
                ‖(Complex.Gamma w)⁻¹‖ ≤ Ccompact := hcompact_w
                _ ≤ A := hconst_le_A
                _ ≤ A * Real.exp (B * (1 + ‖w‖) ^ (1 : ℕ)) :=
                  hA_le_Aexp⟩

/-- Fixed-real-part reciprocal vertical Stirling bound for `Complex.Gamma`, obtained
from the lower fixed-line estimate by reciprocal transport. -/
theorem Complex.Gamma_fixedRealPart_vertical_reciprocal_stirling_bound_classical :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    (∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H)) →
    (∀ H b : ℝ, Decidable (H ≤ ‖b‖)) →
    ∀ a : ℝ,
      ∃ C : ℝ,
        0 < C ∧
        ∀ b : ℝ,
          1 / 2 ≤ ‖b‖ →
          ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
            C * Real.exp ((Real.pi / 2) * ‖b‖) *
              (1 + ‖b‖) ^ (1 / 2 - a) := by
  exact fun hbranch =>
  fun hcompact_half_dec height_split_dec =>
    fun a =>
      match Complex.Gamma_fixedRealPart_vertical_stirling_lower_bound_classical
          hbranch hcompact_half_dec height_split_dec a with
      | ⟨c, hc_pos, hlower⟩ =>
        ⟨c⁻¹, inv_pos.mpr hc_pos,
          Complex.Gamma_fixedRealPart_vertical_reciprocal_bound_of_lower_bound hc_pos hlower⟩

/-- Fixed-real-part vertical Stirling bounds for `Complex.Gamma` and its
reciprocal. -/
theorem Complex.Gamma_fixedRealPart_vertical_twoSided_stirling_bounds_classical :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    (∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H)) →
    (∀ H b : ℝ, Decidable (H ≤ ‖b‖)) →
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
  exact fun hbranch =>
  fun hcompact_half_dec height_split_dec =>
    fun a =>
      match Complex.Gamma_fixedRealPart_vertical_stirling_upper_bound_classical
          hbranch hcompact_half_dec height_split_dec a with
      | ⟨Cu, hCu_pos, hCu⟩ =>
      match Complex.Gamma_fixedRealPart_vertical_reciprocal_stirling_bound_classical
          hbranch hcompact_half_dec height_split_dec a with
      | ⟨Cr, hCr_pos, hCr⟩ =>
      let C : ℝ := Cu + Cr
      have hC_pos : 0 < C :=
        add_pos hCu_pos hCr_pos
      have hCu_le_C : Cu ≤ C :=
        le_add_of_nonneg_right (le_of_lt hCr_pos)
      have hCr_le_C : Cr ≤ C :=
        le_add_of_nonneg_left (le_of_lt hCu_pos)
      ⟨C, hC_pos,
        fun b hb =>
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
          And.intro
            (calc
              ‖Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I)‖ ≤
                  Cu * Real.exp (-(Real.pi / 2) * ‖b‖) *
                    (1 + ‖b‖) ^ (a - 1 / 2) :=
                hCu b hb
              _ = Cu * (Real.exp (-(Real.pi / 2) * ‖b‖) *
                    (1 + ‖b‖) ^ (a - 1 / 2)) :=
                hdirect_source_assoc
              _ ≤ C * (Real.exp (-(Real.pi / 2) * ‖b‖) *
                    (1 + ‖b‖) ^ (a - 1 / 2)) :=
                hdirect_scaled
              _ = C * Real.exp (-(Real.pi / 2) * ‖b‖) *
                    (1 + ‖b‖) ^ (a - 1 / 2) :=
                hdirect_target_assoc.symm)
            (calc
              ‖(Complex.Gamma ((a : ℂ) + (b : ℂ) * Complex.I))⁻¹‖ ≤
                  Cr * Real.exp ((Real.pi / 2) * ‖b‖) *
                    (1 + ‖b‖) ^ (1 / 2 - a) :=
                hCr b hb
              _ = Cr * (Real.exp ((Real.pi / 2) * ‖b‖) *
                    (1 + ‖b‖) ^ (1 / 2 - a)) :=
                hreciprocal_source_assoc
              _ ≤ C * (Real.exp ((Real.pi / 2) * ‖b‖) *
                    (1 + ‖b‖) ^ (1 / 2 - a)) :=
                hreciprocal_scaled
              _ = C * Real.exp ((Real.pi / 2) * ‖b‖) *
                    (1 + ‖b‖) ^ (1 / 2 - a) :=
                hreciprocal_target_assoc.symm)⟩

/-- Classical closed-sector Stirling expansion for `Complex.Gamma`, with the
sectorial and fixed-line consequences used by the normalization chain.

This owner theorem is now only the product assembly of the formula-level
Stirling input, its sectorial log-norm consequence, and the fixed-line vertical
estimates; cf. DLMF §5.11. -/
theorem Complex.Gamma_closedRightHalfPlane_sectorial_stirling_expansion_with_vertical_bounds_classical :
    Complex.BinetSecondFormulaBranchUniformTailAbsorption →
    (∀ H : ℝ, Decidable ((1 / 2 : ℝ) ≤ H)) →
    (∀ H b : ℝ, Decidable (H ≤ ‖b‖)) →
    (∃ R : ℝ, ∃ K : ℝ,
      0 < R ∧
      0 < K ∧
      ∀ w : ℂ,
        0 < w.re →
        Complex.closedRightHalfPlaneSector w →
        R ≤ ‖w‖ →
        ‖Complex.Gamma w * Complex.exp w *
            w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
          K / ‖w‖) ∧
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
                (1 + ‖b‖) ^ (1 / 2 - a)) := fun hbranch =>
  fun hcompact_half_dec height_split_dec => by
  have hcoh :
      Complex.BinetSecondFormulaBranchCoherence :=
    Complex.BinetSecondFormulaBranchUniformTailAbsorption.coherence hbranch
  have hexp :
      ∃ R : ℝ, ∃ K : ℝ,
        0 < R ∧
        0 < K ∧
        ∀ w : ℂ,
          0 < w.re →
          Complex.closedRightHalfPlaneSector w →
          R ≤ ‖w‖ →
          ‖Complex.Gamma w * Complex.exp w *
              w ^ ((1 / 2 : ℂ) - w) - (Real.sqrt (2 * Real.pi) : ℂ)‖ ≤
            K / ‖w‖ := by
    match Complex.Gamma_closedRightHalfPlane_sectorial_exponential_stirling_expansion_classical hbranch with
    | ⟨R, K, hR_pos, hK_pos, hbound⟩ =>
      exact
        ⟨R, K, hR_pos, hK_pos,
          fun w hw_re_pos hw_sector hw_norm =>
            hbound w hw_re_pos hw_sector hw_norm hcoh.2.1 hcoh.2.2⟩
  exact
    ⟨hexp,
      Complex.Gamma_closedRightHalfPlane_sectorial_log_norm_bound_classical hbranch,
      Complex.Gamma_fixedRealPart_vertical_twoSided_stirling_bounds_classical
        hbranch hcompact_half_dec height_split_dec⟩

/- Classical closed-sector Stirling estimates for `Complex.Gamma` are packaged
above by
`Complex.Gamma_closedRightHalfPlane_sectorial_stirling_expansion_with_vertical_bounds_classical`;
cf. DLMF §5.11. -/


end
end LFunctions
end Boundary
