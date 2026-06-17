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
  apply Exists.elim
    (Complex.sectorialStirling_shiftedNormalizedFactor_twoSided_bounds
      hStirling A B)
  intro Hn hHn_data
  apply Exists.elim hHn_data
  intro Cn hCn_data
  apply Exists.elim hCn_data
  intro cn hnormalized_data
  have hHn_pos : 0 < Hn := hnormalized_data.1
  have hCn_pos : 0 < Cn := hnormalized_data.2.1
  have hcn_pos : 0 < cn := hnormalized_data.2.2.1
  have hnormalized :
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        Hn ≤ ‖y‖ →
          ‖Complex.normalizedGammaStirlingFactor
              (Complex.fixedRealPartVerticalPoint
                (x + Complex.verticalStripTransportShift A) y)‖ ≤ Cn ∧
            cn ≤ ‖Complex.normalizedGammaStirlingFactor
              (Complex.fixedRealPartVerticalPoint
                (x + Complex.verticalStripTransportShift A) y)‖ :=
    hnormalized_data.2.2.2
  apply Exists.elim
    (Complex.shiftedVerticalStirlingDenominator_reciprocal_comparable A B)
  intro Hd hHd_data
  apply Exists.elim hHd_data
  intro Cd hCd_data
  apply Exists.elim hCd_data
  intro cd hdenom_data
  have hHd_pos : 0 < Hd := hdenom_data.1
  have hCd_pos : 0 < Cd := hdenom_data.2.1
  have hcd_pos : 0 < cd := hdenom_data.2.2.1
  have hdenom :
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        Hd ≤ ‖y‖ →
          0 <
              ‖Complex.exp
                  (Complex.fixedRealPartVerticalPoint
                    (x + Complex.verticalStripTransportShift A) y)‖ *
                ‖Complex.fixedRealPartVerticalPoint
                    (x + Complex.verticalStripTransportShift A) y ^
                    ((1 / 2 : ℂ) -
                      Complex.fixedRealPartVerticalPoint
                        (x + Complex.verticalStripTransportShift A) y)‖ ∧
            1 /
                (‖Complex.exp
                    (Complex.fixedRealPartVerticalPoint
                      (x + Complex.verticalStripTransportShift A) y)‖ *
                  ‖Complex.fixedRealPartVerticalPoint
                      (x + Complex.verticalStripTransportShift A) y ^
                      ((1 / 2 : ℂ) -
                        Complex.fixedRealPartVerticalPoint
                          (x + Complex.verticalStripTransportShift A) y)‖) ≤
              Cd * Complex.fixedRealPartVerticalStirlingEnvelope
                (x + Complex.verticalStripTransportShift A) y ∧
            cd * Complex.fixedRealPartVerticalStirlingEnvelope
                (x + Complex.verticalStripTransportShift A) y ≤
              1 /
                (‖Complex.exp
                    (Complex.fixedRealPartVerticalPoint
                      (x + Complex.verticalStripTransportShift A) y)‖ *
                  ‖Complex.fixedRealPartVerticalPoint
                      (x + Complex.verticalStripTransportShift A) y ^
                      ((1 / 2 : ℂ) -
                        Complex.fixedRealPartVerticalPoint
                          (x + Complex.verticalStripTransportShift A) y)‖) :=
    hdenom_data.2.2.2
  let H : ℝ := max Hn Hd
  apply Exists.intro H
  apply Exists.intro (Cn * Cd)
  apply Exists.intro (cn * cd)
  apply And.intro
    (lt_of_lt_of_le hHn_pos (le_max_left Hn Hd))
  apply And.intro (mul_pos hCn_pos hCd_pos)
  apply And.intro (mul_pos hcn_pos hcd_pos)
  intro x y hxA hxB hy
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
      mul_assoc Cn Cd E
    exact le_trans (le_of_eq hdiv_eq)
      (le_trans hmul (le_of_eq htarget))
  have hlower_scale :
      (cn * cd) * E ≤ cn / D := by
    have hleft_assoc :
        (cn * cd) * E = cn * (cd * E) :=
      (mul_assoc cn cd E).symm
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
  constructor
  · exact le_trans hgamma_upper_raw hupper_scale
  · exact le_trans hlower_scale hgamma_lower_raw

/-- Finite recurrence transport from shifted raw Gamma bounds and recurrence
product bounds back to the original vertical strip.

The shifted envelope has power `x + N - 1/2`; division by the recurrence product
contributes exactly a fixed polynomial factor of degree `N`, which is absorbed
into strip-dependent constants and recovers the unshifted envelope. -/
theorem Complex.verticalStripGammaBounds_of_shiftedRawBounds_and_recurrenceProduct
    (A B : ℝ)
    (N : ℕ)
    (hshift_eq : N = Complex.verticalStripTransportShift A)
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
  apply Exists.intro H
  apply Exists.intro (Cs / cp)
  apply Exists.intro (cs / Cp)
  apply And.intro
    (lt_of_lt_of_le hHs_pos (le_max_left Hs (max Hp Hn)))
  apply And.intro (div_pos hCs_pos hcp_pos)
  apply And.intro (div_pos hcs_pos hCp_pos)
  intro x y hxA hxB hy
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
    Eq.subst
      (motive := fun t : ℝ =>
        t ≤ Cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y)
      hshifted_norm.symm
      hshifted_xy.1
  have hshifted_lower :
      cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y ≤
        ‖Complex.Gamma
          (Complex.fixedRealPartVerticalPoint x y + (N : ℂ))‖ :=
    Eq.subst
      (motive := fun t : ℝ =>
        cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y ≤ t)
      hshifted_norm.symm
      hshifted_xy.2
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
  constructor
  · have htarget :
        Cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y /
            (cp * R ^ (N : ℝ)) =
          (Cs / cp) * Complex.fixedRealPartVerticalStirlingEnvelope x y :=
      Complex.fixedRealPartVerticalStirlingEnvelope_natShift_div_scale_eq
        x y N Cs cp hcp_pos
    exact
      Eq.subst
        (motive := fun t : ℝ =>
          ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖ ≤ t)
        htarget
        (Eq.subst
          (motive := fun t : ℝ =>
            t ≤
              Cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y /
                (cp * R ^ (N : ℝ)))
          hnorm_rec.symm
          hupper_div)
  · have htarget :
        cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y /
            (Cp * R ^ (N : ℝ)) =
          (cs / Cp) * Complex.fixedRealPartVerticalStirlingEnvelope x y :=
      Complex.fixedRealPartVerticalStirlingEnvelope_natShift_div_scale_eq
        x y N cs Cp hCp_pos
    exact
      Eq.subst
        (motive := fun t : ℝ =>
          t ≤ ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint x y)‖)
        htarget
        (Eq.subst
          (motive := fun t : ℝ =>
            cs * Complex.fixedRealPartVerticalStirlingEnvelope (x + N) y /
                (Cp * R ^ (N : ℝ)) ≤ t)
          hnorm_rec.symm
          hlower_div)

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
      Eq.subst
        (motive := fun M : ℕ =>
          ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
            0 < H ∧
            0 < C ∧
            0 < c ∧
            ∀ x y : ℝ,
              A ≤ x →
              x ≤ B →
              H ≤ ‖y‖ →
                ‖Complex.Gamma
                    (Complex.fixedRealPartVerticalPoint (x + M) y)‖ ≤
                  C * Complex.fixedRealPartVerticalStirlingEnvelope (x + M) y ∧
                c * Complex.fixedRealPartVerticalStirlingEnvelope (x + M) y ≤
                  ‖Complex.Gamma
                    (Complex.fixedRealPartVerticalPoint (x + M) y)‖)
        (show Complex.verticalStripTransportShift A = N from rfl)
        (Complex.sectorialStirling_shiftedRawGammaEnvelope_of_normalizedStirling
          hStirling A B)
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
    Complex.sectorialLogGammaAsymptotic_verticalStrip_largeHeight_bounds
      Complex.sectorialLogGammaAsymptotic_closedRightHalfPlane A B

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
  match Complex.sectorialStirling_verticalStrip_largeHeight_classical a a with
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
    intro b hb
    have hb_abs_le : |b| ≤ H := by
      exact Eq.subst
        (motive := fun x : ℝ => x ≤ H)
        (Real.norm_eq_abs b)
        hb.2
    exact abs_le.mp hb_abs_le
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
  exact Exists.intro (1 / 2 : ℝ)
    (And.intro
      (Eq.subst
        (motive := fun x : ℝ => (1 / 2 : ℝ) ≤ x)
        hnorm_half.symm
        (le_refl (1 / 2 : ℝ)))
      (Eq.subst
        (motive := fun x : ℝ => x ≤ H)
        hnorm_half.symm
        hH))

/-- `Gamma` is nonzero on the fixed-line compact-height strip. -/
theorem Complex.Gamma_fixedRealPartVerticalPoint_ne_zero_of_compactHeight
    {a H b : ℝ}
    (hb : b ∈ Complex.fixedRealPartVerticalCompactHeightSet H) :
    Complex.Gamma (Complex.fixedRealPartVerticalPoint a b) ≠ 0 := by
  intro hzero
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

/-- The fixed-line Gamma ratio is continuous on compact-height sets. -/
theorem Complex.continuousOn_fixedRealPartVerticalGammaRatio_compactHeight
    (a H : ℝ) :
    ContinuousOn
      (fun b : ℝ =>
        ‖Complex.Gamma (Complex.fixedRealPartVerticalPoint a b)‖ /
          Complex.fixedRealPartVerticalStirlingEnvelope a b)
      (Complex.fixedRealPartVerticalCompactHeightSet H) := by
  intro b hb
  have hgamma_ne :
      Complex.Gamma (Complex.fixedRealPartVerticalPoint a b) ≠ 0 :=
    Complex.Gamma_fixedRealPartVerticalPoint_ne_zero_of_compactHeight hb
  have hpole_free :
      ∀ n : ℕ, Complex.fixedRealPartVerticalPoint a b ≠ -n := by
    intro n hn
    exact hgamma_ne ((Complex.Gamma_eq_zero_iff
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
  exact (hnum_cont.div henv_cont henv_ne).continuousWithinAt

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
  apply Exists.intro C
  apply And.intro hC_pos
  intro b hb
  exact le_trans (hM b hb) (le_max_right 1 M)

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
  apply Exists.intro c
  apply And.intro hc_pos
  intro b hb
  exact hb₀_min b hb

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
  match Complex.fixedRealPartVerticalGammaUpperRatio_compactHeight_bound
      a H with
  | ⟨C, hC_pos, hC⟩ =>
  match Decidable.em ((1 / 2 : ℝ) ≤ H) with
  | Or.inl hH_half =>
    match Complex.fixedRealPartVerticalGammaLowerRatio_compactHeight_pos_bound
        a H hH_half with
    | ⟨c, hc_pos, hc⟩ =>
    exact ⟨C, c, hC_pos, hc_pos, fun b hb => ⟨hC b hb, hc b hb⟩⟩
  | Or.inr hH_half =>
    have hhalf_lt_H : H < (1 / 2 : ℝ) :=
      lt_of_not_ge hH_half
    have hone_pos : (0 : ℝ) < 1 :=
      zero_lt_one
    apply Exists.intro C
    apply Exists.intro 1
    apply And.intro hC_pos
    apply And.intro hone_pos
    intro b hb
    have hle : (1 / 2 : ℝ) ≤ H :=
      le_trans hb.1 hb.2
    exact False.elim ((not_lt_of_ge hle) hhalf_lt_H)

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
  match hlarge with
  | ⟨H, Clarge, clarge, hH_pos, hClarge_pos, hclarge_pos, hlarge_bound⟩ =>
  match hcompact H hH_pos with
  | ⟨Ccompact, ccompact, hCcompact_pos, hccompact_pos, hcompact_bound⟩ =>
  let C : ℝ := max Clarge Ccompact
  let c : ℝ := min clarge ccompact
  have hC_pos : 0 < C :=
    lt_of_lt_of_le hClarge_pos (le_max_left Clarge Ccompact)
  have hc_pos : 0 < c :=
    lt_min hclarge_pos hccompact_pos
  apply Exists.intro C
  apply Exists.intro c
  apply And.intro hC_pos
  apply And.intro hc_pos
  intro b hb
  have hE_nonneg :
      0 ≤ Complex.fixedRealPartVerticalStirlingEnvelope a b :=
    Complex.fixedRealPartVerticalStirlingEnvelope_nonneg a b
  match Decidable.em (H ≤ ‖b‖) with
  | Or.inl hb_large =>
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
    exact
      ⟨le_trans hlarge_b.1 hupper_constant,
        le_trans hlower_constant hlarge_b.2⟩
  | Or.inr hb_large =>
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
  match Complex.fixedLineVerticalGammaTwoSidedEnvelope a with
  | ⟨C, c, hC_pos, hc_pos, hbounds⟩ =>
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
  match Complex.fixedLineVerticalGammaTwoSidedEnvelope a with
  | ⟨C, c, hC_pos, hc_pos, hbounds⟩ =>
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
  match Complex.Gamma_fixedRealPart_vertical_stirling_upper_bound_classical a with
  | ⟨C, hC_pos, hupper⟩ =>
  match Complex.Gamma_fixedRealPart_vertical_stirling_lower_bound_classical a with
  | ⟨c, hc_pos, hlower⟩ =>
  apply Exists.intro C
  apply Exists.intro c
  apply And.intro hC_pos
  apply And.intro hc_pos
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
            exact (mul_inv_rev c (Real.exp (-x)) (H ^ (a - 1 / 2))).symm
      _ = (c⁻¹ * (Real.exp (-x))⁻¹) * (H ^ (a - 1 / 2))⁻¹ := by
            exact congrArg (fun y : ℝ => y * (H ^ (a - 1 / 2))⁻¹)
              (mul_inv_rev c (Real.exp (-x)) 1)
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
  match Complex.Gamma_fixedRealPart_vertical_stirling_lower_bound_classical a with
  | ⟨c, hc_pos, hlower⟩ =>
  apply Exists.intro c⁻¹
  apply And.intro (inv_pos.mpr hc_pos)
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
  match Complex.Gamma_fixedRealPart_vertical_stirling_upper_bound_classical a with
  | ⟨Cu, hCu_pos, hCu⟩ =>
  match Complex.Gamma_fixedRealPart_vertical_reciprocal_stirling_bound_classical a with
  | ⟨Cr, hCr_pos, hCr⟩ =>
  let C : ℝ := Cu + Cr
  have hC_pos : 0 < C :=
    add_pos hCu_pos hCr_pos
  have hCu_le_C : Cu ≤ C :=
    le_add_of_nonneg_right (le_of_lt hCr_pos)
  have hCr_le_C : Cr ≤ C :=
    le_add_of_nonneg_left (le_of_lt hCu_pos)
  apply Exists.intro C
  apply And.intro hC_pos
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


end
end LFunctions
end Boundary
