import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.FixedVerticalEnvelope.ShiftedEnvelope

/-!
# Fixed vertical recurrence transport

This subowner transports shifted fixed-vertical Gamma bounds through the recurrence product.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

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

end
end LFunctions
end Boundary
