import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.EulerMaclaurinFormula.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.EulerContinuationTransport.FiniteOrderPL.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaBoundaryPL.DampedFamily.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.PoleClearedBoundarySetup.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.FiniteOrderAlgebra.Owner

/-!
# Right-half-plane Euler continuation growth

This file is a sequential owner sublayer split out of
`ZetaCompletedNormalization.EulerContinuationTransport.Owner`.  Declaration order is preserved.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
local notation "π" => Real.pi

/-- Global Abel/Euler truncation hypotheses needed on the left edge `re = 1`. -/
def BoundaryLineOneAbelPartialMajorant : Prop :=
  ∀ z : ℂ,
    z.re = 1 →
    1 ≤ ‖z.im‖ →
    boundaryLineOneVerticalTruncationHypotheses z

/-- The global `Re s = 1` Abel truncation package follows from the real-parameter
boundary-line owner package applied to the imaginary coordinate. -/
theorem boundaryLineOneAbelPartialMajorant_from_realParam_ownerGap :
    BoundaryLineOneAbelPartialMajorant := by
  exact
    fun z _hz_re hz_im =>
      boundaryLineOnePointRealParam_verticalTruncationHypotheses_ownerGap
        z.im hz_im

/-- Uniform bounded-boundary vertical-tail input for the strip `1 ≤ re ≤ 2`. -/
def PoleClearedOneTwoStripBoundedTailBoundary : Prop :=
  ∃ A : ℝ,
    0 < A ∧
    (∀ z : ℂ,
      z.re = 1 →
      1 ≤ ‖z.im‖ →
      ‖poleClearedRiemannZeta z‖ ≤ A) ∧
    (∀ z : ℂ,
      z.re = 2 →
      1 ≤ ‖z.im‖ →
      ‖poleClearedRiemannZeta z‖ ≤ A)

/-- Uniform bounded-boundary compact-height input for the strip `1 ≤ re ≤ 2`. -/
def PoleClearedOneTwoStripCompactBoundaryBound : Prop :=
  ∃ C : ℝ,
    0 < C ∧
    (∀ z : ℂ,
      z.re = 1 →
      ¬ 1 ≤ ‖z.im‖ →
      ‖poleClearedRiemannZeta z‖ ≤ C) ∧
    (∀ z : ℂ,
      z.re = 2 →
      ¬ 1 ≤ ‖z.im‖ →
      ‖poleClearedRiemannZeta z‖ ≤ C)

/-- The compact-height boundary input on `1 ≤ re ≤ 2` follows from the owner
compact bound on the larger right-critical rectangle. -/
theorem poleClearedOneTwoStripCompactBoundaryBound_from_rightCriticalStrip_compact :
    PoleClearedOneTwoStripCompactBoundaryBound := by
  match poleClearedRiemannZeta_rightCriticalStrip_compact_norm_bound with
  | ⟨C, hC_pos, hC_bound⟩ =>
      exact
        ⟨C, hC_pos,
          fun z hz_re hz_im_not_large =>
            have hz_zero : 0 ≤ z.re :=
              le_trans zero_le_one (le_of_eq hz_re.symm)
            have hz_two : z.re ≤ 2 :=
              le_trans (le_of_eq hz_re) one_le_two
            have hz_im : ‖z.im‖ ≤ 1 :=
              le_of_not_ge hz_im_not_large
            have hz_mem : z ∈ completedRiemannZeta₀_rightCriticalStripCompactSet :=
              ⟨hz_zero, hz_two, hz_im⟩
            hC_bound z hz_mem,
          fun z hz_re hz_im_not_large =>
            have hz_zero : 0 ≤ z.re :=
              le_trans zero_le_two (le_of_eq hz_re.symm)
            have hz_two : z.re ≤ 2 :=
              le_of_eq hz_re
            have hz_im : ‖z.im‖ ≤ 1 :=
              le_of_not_ge hz_im_not_large
            have hz_mem : z ∈ completedRiemannZeta₀_rightCriticalStripCompactSet :=
              ⟨hz_zero, hz_two, hz_im⟩
            hC_bound z hz_mem⟩

/-- Local definition equation for the Euler-Maclaurin remainder package. -/
private lemma eulerMaclaurinPoleClearedZetaRemainderTerm_unfold
    (z : ℂ) :
    eulerMaclaurinPoleClearedZetaRemainderTerm z =
      poleClearedRiemannZeta z -
        (eulerMaclaurinPoleClearedZetaFinitePart z +
          eulerMaclaurinPoleClearedZetaMainTerm z +
          eulerMaclaurinPoleClearedZetaEndpointTerm z) :=
  rfl

/-- Local definition equation for the Euler-Maclaurin endpoint package. -/
private lemma eulerMaclaurinPoleClearedZetaEndpointTerm_unfold
    (z : ℂ) :
    eulerMaclaurinPoleClearedZetaEndpointTerm z =
      (-((z - 1) / 2)) *
        (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)) :=
  rfl

theorem poleClearedRiemannZeta_eq_eulerMaclaurin_one_two_strip_terms
    (z : ℂ) :
    poleClearedRiemannZeta z =
      eulerMaclaurinPoleClearedZetaFinitePart z +
        eulerMaclaurinPoleClearedZetaMainTerm z +
        eulerMaclaurinPoleClearedZetaEndpointTerm z +
        eulerMaclaurinPoleClearedZetaRemainderTerm z := by
  have hremainder :
      eulerMaclaurinPoleClearedZetaRemainderTerm z =
        poleClearedRiemannZeta z -
          (eulerMaclaurinPoleClearedZetaFinitePart z +
            eulerMaclaurinPoleClearedZetaMainTerm z +
            eulerMaclaurinPoleClearedZetaEndpointTerm z) :=
    eulerMaclaurinPoleClearedZetaRemainderTerm_unfold z
  let S : ℂ :=
    (eulerMaclaurinPoleClearedZetaFinitePart z +
      eulerMaclaurinPoleClearedZetaMainTerm z +
      eulerMaclaurinPoleClearedZetaEndpointTerm z)
  have hsub :
      poleClearedRiemannZeta z = (poleClearedRiemannZeta z - S) + S :=
    (sub_add_cancel (poleClearedRiemannZeta z) S).symm
  have hcomm :
      (poleClearedRiemannZeta z - S) + S =
        S + (poleClearedRiemannZeta z - S) :=
    add_comm (poleClearedRiemannZeta z - S) S
  exact Eq.trans (Eq.trans hsub hcomm)
    (congrArg (fun w : ℂ => S + w) hremainder.symm)

/-- Polynomial bound for the finite Dirichlet-polynomial piece in the bounded
Euler-Maclaurin strip. -/
theorem eulerMaclaurinPoleClearedZetaFinitePart_one_two_strip_polynomial_bound :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖eulerMaclaurinPoleClearedZetaFinitePart z‖ ≤ C * (1 + ‖z‖) ^ m := by
  exact eulerMaclaurinPoleClearedZetaFinitePart_sum_cardinality_polynomial_bound

/-- Polynomial bound for the pole-cancelling main term in the bounded
Euler-Maclaurin strip. -/
theorem eulerMaclaurinPoleClearedZetaMainTerm_one_two_strip_polynomial_bound :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖eulerMaclaurinPoleClearedZetaMainTerm z‖ ≤ C * (1 + ‖z‖) ^ m := by
  exact
    ⟨1, 0, zero_lt_one,
      fun z hz_one _hz_two =>
        have hterm :
            ‖eulerMaclaurinPoleClearedZetaMainTerm z‖ ≤ 1 :=
          eulerMaclaurinPoleClearedZetaMainTerm_norm_le_one z hz_one
        have hright : (1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ) = 1 := by
          calc
            (1 : ℝ) * (1 + ‖z‖) ^ (0 : ℕ) =
                (1 + ‖z‖) ^ (0 : ℕ) := by
              exact one_mul ((1 + ‖z‖) ^ (0 : ℕ))
            _ = 1 := by
              exact pow_zero (1 + ‖z‖)
        Eq.subst
          (motive := fun x : ℝ => ‖eulerMaclaurinPoleClearedZetaMainTerm z‖ ≤ x)
          hright.symm
          hterm⟩

/-- Polynomial bound for the endpoint correction in the bounded
Euler-Maclaurin strip. -/
theorem eulerMaclaurinPoleClearedZetaEndpointTerm_one_two_strip_polynomial_bound :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖eulerMaclaurinPoleClearedZetaEndpointTerm z‖ ≤ C * (1 + ‖z‖) ^ m := by
  exact
    ⟨1, 1, zero_lt_one,
      fun z hz_one _hz_two =>
          have hendpoint :
              eulerMaclaurinPoleClearedZetaEndpointTerm z =
                (-((z - 1) / 2)) *
                  (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)) :=
            eulerMaclaurinPoleClearedZetaEndpointTerm_unfold z
          let H : ℝ := 1 + ‖z‖
          have hH_nonneg : 0 ≤ H :=
            le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))
          have hsub_norm : ‖z - 1‖ ≤ H := by
            calc
              ‖z - 1‖ ≤ ‖z‖ + ‖(1 : ℂ)‖ :=
                norm_sub_le z (1 : ℂ)
              _ = ‖z‖ + 1 := by
                exact congrArg (fun x : ℝ => ‖z‖ + x) (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ))
              _ = H := by
                exact add_comm ‖z‖ 1
          have hdiv_two_norm : ‖(z - 1) / (2 : ℂ)‖ ≤ ‖z - 1‖ := by
            have hnorm_div :
                ‖(z - 1) / (2 : ℂ)‖ = ‖z - 1‖ / ‖(2 : ℂ)‖ :=
              norm_div (z - 1) (2 : ℂ)
            have htwo_norm : ‖(2 : ℂ)‖ = (2 : ℝ) := by
              calc
                ‖(2 : ℂ)‖ = ‖((2 : ℝ) : ℂ)‖ := rfl
                _ = ‖(2 : ℝ)‖ := by
                  exact RCLike.norm_ofReal 2
                _ = 2 := by
                  exact Real.norm_of_nonneg zero_le_two
            have hraw : ‖z - 1‖ / ‖(2 : ℂ)‖ ≤ ‖z - 1‖ := by
              have htwo_pos : (0 : ℝ) < ‖(2 : ℂ)‖ :=
                Eq.subst
                  (motive := fun x : ℝ => 0 < x)
                  htwo_norm.symm
                  zero_lt_two
              have hone_le_two : (1 : ℝ) ≤ ‖(2 : ℂ)‖ :=
                Eq.subst
                  (motive := fun x : ℝ => (1 : ℝ) ≤ x)
                  htwo_norm.symm
                  one_le_two
              exact div_le_self (norm_nonneg (z - 1)) hone_le_two
            exact Eq.subst
              (motive := fun x : ℝ => x ≤ ‖z - 1‖)
              hnorm_div.symm
              hraw
          have hfactor : ‖(z - 1) / (2 : ℂ)‖ ≤ H :=
            le_trans hdiv_two_norm hsub_norm
          have hrecip :
              ‖1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)‖ ≤ 1 :=
            eulerMaclaurinPoleClearedZetaEndpointReciprocal_norm_le_one z hz_one
          have hproduct :
              ‖(z - 1) / (2 : ℂ) *
                  (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z))‖ ≤
                H := by
            calc
              ‖(z - 1) / (2 : ℂ) *
                  (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z))‖ =
                  ‖(z - 1) / (2 : ℂ)‖ *
                    ‖1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)‖ := by
                exact norm_mul ((z - 1) / (2 : ℂ))
                  (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z))
              _ ≤ H * 1 :=
                mul_le_mul hfactor hrecip
                  (norm_nonneg (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)))
                  hH_nonneg
              _ = H := by
                exact mul_one H
          have hright : (1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ) = H := by
            calc
              (1 : ℝ) * (1 + ‖z‖) ^ (1 : ℕ) =
                  (1 + ‖z‖) ^ (1 : ℕ) := by
                exact one_mul ((1 + ‖z‖) ^ (1 : ℕ))
              _ = 1 + ‖z‖ := by
                exact pow_one (1 + ‖z‖)
              _ = H := rfl
          have hneg :
              ‖-((z - 1) / (2 : ℂ)) *
                  (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z))‖ =
                ‖(z - 1) / (2 : ℂ) *
                  (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z))‖ := by
            calc
              ‖-((z - 1) / (2 : ℂ)) *
                  (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z))‖ =
                  ‖-(((z - 1) / (2 : ℂ)) *
                    (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)))‖ := by
                exact congrArg norm (neg_mul ((z - 1) / (2 : ℂ))
                  (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)))
              _ =
                  ‖(z - 1) / (2 : ℂ) *
                    (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z))‖ := by
                exact norm_neg (((z - 1) / (2 : ℂ)) *
                  (1 / (((eulerMaclaurinPoleClearedZetaCutoff z : ℕ) : ℂ) ^ z)))
          Eq.subst
            (motive := fun x : ℝ =>
              ‖eulerMaclaurinPoleClearedZetaEndpointTerm z‖ ≤ x)
            hright.symm
            (Eq.subst
              (motive := fun w : ℂ => ‖w‖ ≤ H)
              hendpoint.symm
              (Eq.subst
                (motive := fun x : ℝ => x ≤ H)
                hneg.symm
                hproduct))⟩

/-- Polynomial bound for the Bernoulli-periodic Euler-Maclaurin remainder in
the bounded strip. -/
theorem eulerMaclaurinPoleClearedZetaRemainderTerm_one_two_strip_polynomial_bound :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖eulerMaclaurinPoleClearedZetaRemainderTerm z‖ ≤ C * (1 + ‖z‖) ^ m := by
  exact eulerMaclaurinPoleClearedZetaRemainderTerm_integral_majorant_polynomial_bound

/-- Four polynomial Euler-Maclaurin term bounds assemble to a polynomial bound
for the pole-cleared zeta factor. -/
theorem poleClearedRiemannZeta_one_two_strip_polynomial_bound_of_eulerMaclaurin_term_bounds
    (hfinite :
      ∃ C : ℝ, ∃ m : ℕ,
        0 < C ∧
        ∀ z : ℂ,
          1 ≤ z.re →
          z.re ≤ 2 →
          ‖eulerMaclaurinPoleClearedZetaFinitePart z‖ ≤ C * (1 + ‖z‖) ^ m)
    (hmain :
      ∃ C : ℝ, ∃ m : ℕ,
        0 < C ∧
        ∀ z : ℂ,
          1 ≤ z.re →
          z.re ≤ 2 →
          ‖eulerMaclaurinPoleClearedZetaMainTerm z‖ ≤ C * (1 + ‖z‖) ^ m)
    (hendpoint :
      ∃ C : ℝ, ∃ m : ℕ,
        0 < C ∧
        ∀ z : ℂ,
          1 ≤ z.re →
          z.re ≤ 2 →
          ‖eulerMaclaurinPoleClearedZetaEndpointTerm z‖ ≤ C * (1 + ‖z‖) ^ m)
    (hremainder :
      ∃ C : ℝ, ∃ m : ℕ,
        0 < C ∧
        ∀ z : ℂ,
          1 ≤ z.re →
          z.re ≤ 2 →
          ‖eulerMaclaurinPoleClearedZetaRemainderTerm z‖ ≤ C * (1 + ‖z‖) ^ m) :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖poleClearedRiemannZeta z‖ ≤ C * (1 + ‖z‖) ^ m := by
  match hfinite with
  | ⟨Cf, mf, hCf, hf⟩ =>
      match hmain with
      | ⟨Cm, mm, hCm, hm⟩ =>
          match hendpoint with
          | ⟨Ce, me, hCe, he⟩ =>
              match hremainder with
              | ⟨Cr, mr, hCr, hr⟩ =>
                    let C : ℝ := Cf + Cm + Ce + Cr
                    let m : ℕ := max (max mf mm) (max me mr)
                    have hCf_nonneg : 0 ≤ Cf := le_of_lt hCf
                    have hCm_nonneg : 0 ≤ Cm := le_of_lt hCm
                    have hCe_nonneg : 0 ≤ Ce := le_of_lt hCe
                    have hCr_nonneg : 0 ≤ Cr := le_of_lt hCr
                    exact
                      ⟨C, m, add_pos (add_pos (add_pos hCf hCm) hCe) hCr,
                      fun z hz_one hz_two =>
                          let H : ℝ := 1 + ‖z‖
                          have hH_ge_one : (1 : ℝ) ≤ H :=
                            le_add_of_nonneg_right (norm_nonneg z)
                          have hH_nonneg : 0 ≤ H :=
                            le_trans zero_le_one hH_ge_one
                          have hmf : H ^ mf ≤ H ^ m := by
                            have hmf_le : mf ≤ m :=
                              le_trans (Nat.le_max_left mf mm)
                                (Nat.le_max_left (max mf mm) (max me mr))
                            exact pow_le_pow_right₀ hH_ge_one hmf_le
                          have hmm : H ^ mm ≤ H ^ m := by
                            have hmm_le : mm ≤ m :=
                              le_trans (Nat.le_max_right mf mm)
                                (Nat.le_max_left (max mf mm) (max me mr))
                            exact pow_le_pow_right₀ hH_ge_one hmm_le
                          have hme : H ^ me ≤ H ^ m := by
                            have hme_le : me ≤ m :=
                              le_trans (Nat.le_max_left me mr)
                                (Nat.le_max_right (max mf mm) (max me mr))
                            exact pow_le_pow_right₀ hH_ge_one hme_le
                          have hmr : H ^ mr ≤ H ^ m := by
                            have hmr_le : mr ≤ m :=
                              le_trans (Nat.le_max_right me mr)
                                (Nat.le_max_right (max mf mm) (max me mr))
                            exact pow_le_pow_right₀ hH_ge_one hmr_le
                          have hf' :
                              ‖eulerMaclaurinPoleClearedZetaFinitePart z‖ ≤ Cf * H ^ m :=
                            le_trans (hf z hz_one hz_two)
                              (mul_le_mul_of_nonneg_left hmf hCf_nonneg)
                          have hm' :
                              ‖eulerMaclaurinPoleClearedZetaMainTerm z‖ ≤ Cm * H ^ m :=
                            le_trans (hm z hz_one hz_two)
                              (mul_le_mul_of_nonneg_left hmm hCm_nonneg)
                          have he' :
                              ‖eulerMaclaurinPoleClearedZetaEndpointTerm z‖ ≤ Ce * H ^ m :=
                            le_trans (he z hz_one hz_two)
                              (mul_le_mul_of_nonneg_left hme hCe_nonneg)
                          have hr' :
                              ‖eulerMaclaurinPoleClearedZetaRemainderTerm z‖ ≤ Cr * H ^ m :=
                            le_trans (hr z hz_one hz_two)
                              (mul_le_mul_of_nonneg_left hmr hCr_nonneg)
                          have hformula :
                              poleClearedRiemannZeta z =
                                eulerMaclaurinPoleClearedZetaFinitePart z +
                                  eulerMaclaurinPoleClearedZetaMainTerm z +
                                  eulerMaclaurinPoleClearedZetaEndpointTerm z +
                                  eulerMaclaurinPoleClearedZetaRemainderTerm z :=
                            poleClearedRiemannZeta_eq_eulerMaclaurin_one_two_strip_terms z
                          have htriangle :
                              ‖poleClearedRiemannZeta z‖ ≤
                                ‖eulerMaclaurinPoleClearedZetaFinitePart z‖ +
                                  ‖eulerMaclaurinPoleClearedZetaMainTerm z‖ +
                                  ‖eulerMaclaurinPoleClearedZetaEndpointTerm z‖ +
                                  ‖eulerMaclaurinPoleClearedZetaRemainderTerm z‖ := by
                            exact Eq.subst
                              (motive := fun w : ℂ =>
                                ‖w‖ ≤
                                  ‖eulerMaclaurinPoleClearedZetaFinitePart z‖ +
                                    ‖eulerMaclaurinPoleClearedZetaMainTerm z‖ +
                                    ‖eulerMaclaurinPoleClearedZetaEndpointTerm z‖ +
                                    ‖eulerMaclaurinPoleClearedZetaRemainderTerm z‖)
                              hformula.symm
                              (le_trans
                                (norm_add_le
                                  (eulerMaclaurinPoleClearedZetaFinitePart z +
                                    eulerMaclaurinPoleClearedZetaMainTerm z +
                                    eulerMaclaurinPoleClearedZetaEndpointTerm z)
                                  (eulerMaclaurinPoleClearedZetaRemainderTerm z))
                                (add_le_add_right
                                  (le_trans
                                    (norm_add_le
                                      (eulerMaclaurinPoleClearedZetaFinitePart z +
                                        eulerMaclaurinPoleClearedZetaMainTerm z)
                                      (eulerMaclaurinPoleClearedZetaEndpointTerm z))
                                    (add_le_add_right
                                      (norm_add_le
                                        (eulerMaclaurinPoleClearedZetaFinitePart z)
                                        (eulerMaclaurinPoleClearedZetaMainTerm z))
                                      ‖eulerMaclaurinPoleClearedZetaEndpointTerm z‖))
                                  ‖eulerMaclaurinPoleClearedZetaRemainderTerm z‖))
                          have hsum_bound :
                              ‖eulerMaclaurinPoleClearedZetaFinitePart z‖ +
                                  ‖eulerMaclaurinPoleClearedZetaMainTerm z‖ +
                                  ‖eulerMaclaurinPoleClearedZetaEndpointTerm z‖ +
                                  ‖eulerMaclaurinPoleClearedZetaRemainderTerm z‖ ≤
                                C * H ^ m := by
                            have hsum :
                                ‖eulerMaclaurinPoleClearedZetaFinitePart z‖ +
                                    ‖eulerMaclaurinPoleClearedZetaMainTerm z‖ +
                                    ‖eulerMaclaurinPoleClearedZetaEndpointTerm z‖ +
                                    ‖eulerMaclaurinPoleClearedZetaRemainderTerm z‖ ≤
                                  Cf * H ^ m + Cm * H ^ m + Ce * H ^ m + Cr * H ^ m :=
                              add_le_add (add_le_add (add_le_add hf' hm') he') hr'
                            have hcombine :
                                Cf * H ^ m + Cm * H ^ m + Ce * H ^ m + Cr * H ^ m =
                                  C * H ^ m := by
                              calc
                                Cf * H ^ m + Cm * H ^ m + Ce * H ^ m + Cr * H ^ m =
                                    (Cf + Cm) * H ^ m + Ce * H ^ m + Cr * H ^ m := by
                                  exact congrArg (fun x : ℝ => x + Ce * H ^ m + Cr * H ^ m)
                                    (add_mul Cf Cm (H ^ m)).symm
                                _ = (Cf + Cm + Ce) * H ^ m + Cr * H ^ m := by
                                  exact congrArg (fun x : ℝ => x + Cr * H ^ m)
                                    (add_mul (Cf + Cm) Ce (H ^ m)).symm
                                _ = (Cf + Cm + Ce + Cr) * H ^ m := by
                                  exact (add_mul (Cf + Cm + Ce) Cr (H ^ m)).symm
                                _ = C * H ^ m := rfl
                            exact hsum.trans_eq hcombine
                          le_trans htriangle hsum_bound⟩

/-- Euler-Maclaurin formula/remainder polynomial bound for the pole-cleared zeta
factor on the closed strip `1 ≤ Re s ≤ 2`.

This is the precise classical analytic input behind the strip continuation
estimate.  In standard notation it comes from the Euler-Maclaurin continuation
formula
`ζ(s) = Σ_{n<N} n^{-s} + N^{1-s}/(s-1) + O(N^{-σ}) +
  s ∫_N^∞ B₁({x}) x^{-s-1} dx`,
after multiplying by `s - 1` and taking `N` comparable to `2 + |Im s|`.
The finite Dirichlet polynomial, the pole-cancelling term `N^{1-s}`, the
endpoint correction, and the Bernoulli-remainder integral are all polynomially
bounded in `1 + ‖s‖` uniformly for `1 ≤ σ ≤ 2`; cf. Titchmarsh, §3.5 and
Davenport, Ch. 12. -/
theorem eulerMaclaurin_poleClearedRiemannZeta_one_two_strip_formula_remainder_polynomial_bound :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖poleClearedRiemannZeta z‖ ≤ C * (1 + ‖z‖) ^ m := by
  exact
    poleClearedRiemannZeta_one_two_strip_polynomial_bound_of_eulerMaclaurin_term_bounds
      eulerMaclaurinPoleClearedZetaFinitePart_one_two_strip_polynomial_bound
      eulerMaclaurinPoleClearedZetaMainTerm_one_two_strip_polynomial_bound
      eulerMaclaurinPoleClearedZetaEndpointTerm_one_two_strip_polynomial_bound
      eulerMaclaurinPoleClearedZetaRemainderTerm_one_two_strip_polynomial_bound

/-- Polynomial Euler-Maclaurin growth on the closed strip implies the
finite-order exponential envelope used by the strip admissibility API. -/
theorem poleClearedRiemannZeta_one_two_strip_finiteOrder_growth_of_polynomial_bound
    (hpoly :
      ∃ C : ℝ, ∃ m : ℕ,
        0 < C ∧
        ∀ z : ℂ,
          1 ≤ z.re →
          z.re ≤ 2 →
          ‖poleClearedRiemannZeta z‖ ≤ C * (1 + ‖z‖) ^ m) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match hpoly with
  | ⟨C, m, hC, hbound⟩ =>
      exact
        ⟨C, 1, m, hC, zero_lt_one,
          fun z hz_one hz_two =>
            let H : ℝ := 1 + ‖z‖
            have hH_nonneg : 0 ≤ H :=
              le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))
            have hpow_nonneg : 0 ≤ H ^ m :=
              pow_nonneg hH_nonneg m
            have hone_le_exp :
                (1 : ℝ) ≤ Real.exp ((1 : ℝ) * H ^ m) := by
              have hexponent_nonneg : 0 ≤ (1 : ℝ) * H ^ m :=
                mul_nonneg zero_le_one hpow_nonneg
              exact le_trans
                (le_of_eq Real.exp_zero.symm)
                (Real.exp_le_exp.mpr hexponent_nonneg)
            have hHpow_le_exp :
                H ^ m ≤ Real.exp ((1 : ℝ) * H ^ m) := by
              have hbase :
                  H ^ m ≤ H ^ m + 1 :=
                le_add_of_nonneg_right zero_le_one
              have hadd :
                  H ^ m + 1 ≤ Real.exp (H ^ m) :=
                Real.add_one_le_exp (H ^ m)
              have hexp_eq :
                  Real.exp (H ^ m) = Real.exp ((1 : ℝ) * H ^ m) := by
                exact congrArg Real.exp (one_mul (H ^ m)).symm
              exact hbase.trans (hadd.trans_eq hexp_eq)
            have htarget :
                C * H ^ m ≤ C * Real.exp ((1 : ℝ) * H ^ m) :=
              mul_le_mul_of_nonneg_left hHpow_le_exp (le_of_lt hC)
            le_trans (hbound z hz_one hz_two) htarget⟩

/-- Pointwise finite-order Euler-Maclaurin continuation estimate for the
removable pole-cleared zeta on `1 ≤ Re s ≤ 2`.

This is the exact standard continuation estimate behind the strip admissibility
input: Euler-Maclaurin gives finite-order growth for the meromorphic zeta
continuation on the closed bounded-width strip, and the pole-cleared
normalization removes the singularity at `s = 1`. -/
theorem poleClearedRiemannZeta_one_two_strip_finiteOrder_growth_from_EulerMaclaurin_continuation :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact
    poleClearedRiemannZeta_one_two_strip_finiteOrder_growth_of_polynomial_bound
      eulerMaclaurin_poleClearedRiemannZeta_one_two_strip_formula_remainder_polynomial_bound

/-- Interior admissible-growth input for the `1 < Re s < 2` strip.

This is the exact remaining growth hypothesis consumed by the generic
Phragmen-Lindelöf API.  Analytically it is the subcritical strip growth of the
removable pole-cleared zeta in the bounded strip, obtained from the standard
Euler-Maclaurin continuation estimates. -/
theorem poleClearedRiemannZeta_one_two_strip_admissible_growth_from_EulerMaclaurin_continuation :
    ∃ c : ℝ,
      c < Real.pi / (2 - 1) ∧
      ∃ D : ℝ,
        poleClearedRiemannZeta =O[
          Filter.comap (_root_.abs ∘ Complex.im) Filter.atTop ⊓
            𝓟 (Complex.re ⁻¹' Set.Ioo 1 2)]
          fun z : ℂ => Real.exp (D * Real.exp (c * |z.im|)) := by
  exact
    strip_admissible_doubleExponential_growth_of_finiteOrder_growth
      poleClearedRiemannZeta 1 2 one_lt_two
      poleClearedRiemannZeta_one_two_strip_finiteOrder_growth_from_EulerMaclaurin_continuation

/-- Vertical-tail finite-order growth for the removable pole-cleared zeta on
`1 ≤ Re s ≤ 2`, obtained from the two boundary estimates and strip PL. -/
theorem poleClearedRiemannZeta_one_two_strip_verticalTail_growth_from_boundary_and_PL
    (hpartialLeft : BoundaryLineOneAbelPartialMajorant)
    (hcompactBoundary : PoleClearedOneTwoStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        1 ≤ ‖z.im‖ →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  exact strip_growth_bound_of_holomorphic_boundary_growth_and_finite_order
    poleClearedRiemannZeta 1 2 one_lt_two
    poleClearedRiemannZeta_one_two_strip_diffContOnCl
    poleClearedRiemannZeta_one_two_strip_admissible_growth_from_EulerMaclaurin_continuation
    (match poleClearedRiemannZeta_one_two_strip_leftBoundary_growth_from_EulerMaclaurin with
    | ⟨A, B, m, hA, hB, hleft⟩ =>
        ⟨A, B, m, hA, hB,
          fun z hz_re hz_im =>
            hleft z hz_re hz_im (hpartialLeft z hz_re hz_im)⟩)
    poleClearedRiemannZeta_one_two_strip_rightBoundary_growth_from_dirichletSeries


/-- Compact-height finite-order growth for the removable pole-cleared zeta on
`1 ≤ Re s ≤ 2`. -/
theorem poleClearedRiemannZeta_one_two_strip_compactCore_growth_from_localBoundedness :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖z.im‖ ≤ 1 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match poleClearedRiemannZeta_rightCriticalStrip_compact_norm_bound with
  | ⟨C, hC_pos, hC_bound⟩ =>
      exact
        ⟨C, 1, 0, hC_pos, zero_lt_one,
          fun z hz_one hz_two hz_im =>
            have hz_zero : 0 ≤ z.re :=
              le_trans zero_le_one hz_one
            have hz_mem : z ∈ completedRiemannZeta₀_rightCriticalStripCompactSet :=
              ⟨hz_zero, hz_two, hz_im⟩
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
            le_trans hraw hC_le_target⟩

/-- Compact core and PL vertical tail patch to finite-order growth on the
whole bounded strip `1 ≤ Re s ≤ 2`. -/
theorem poleClearedRiemannZeta_one_two_strip_growth_of_compactCore_and_verticalTail
    (hcompact :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          1 ≤ z.re →
          z.re ≤ 2 →
          ‖z.im‖ ≤ 1 →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (htail :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          1 ≤ z.re →
          z.re ≤ 2 →
          1 ≤ ‖z.im‖ →
          ‖poleClearedRiemannZeta z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        1 ≤ z.re →
        z.re ≤ 2 →
        ‖poleClearedRiemannZeta z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  match hcompact with
  | ⟨Ac, Bc, mc, hAc, hBc, hc⟩ =>
      match htail with
      | ⟨At, Bt, mt, hAt, hBt, ht⟩ =>
          exact
            ⟨Ac + At, Bc + Bt, mc + mt, add_pos hAc hAt, add_pos hBc hBt,
              fun z hz_one hz_two =>
                have hAc_nonneg : 0 ≤ Ac := le_of_lt hAc
                have hAt_nonneg : 0 ≤ At := le_of_lt hAt
                have hBc_nonneg : 0 ≤ Bc := le_of_lt hBc
                have hBt_nonneg : 0 ≤ Bt := le_of_lt hBt
                match le_total ‖z.im‖ 1 with
                | Or.inl hcompact_im =>
                    le_trans (hc z hz_one hz_two hcompact_im)
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
                    le_trans (ht z hz_one hz_two htail_im)
                      (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                        hAt_nonneg
                        (le_add_of_nonneg_left hAc_nonneg)
                        (le_add_of_nonneg_left hBc_nonneg)
                        hBt_nonneg
                        hdegree)⟩

/-- Bounded-width Euler-Maclaurin/PL growth for the removable pole-cleared zeta
normalization on `1 ≤ Re s ≤ 2`.

This is the exact strip owner input: Euler-Maclaurin gives the boundary-line
estimate at `Re s = 1`, the Dirichlet-series estimate gives the right edge at
`Re s = 2`, and the generic vertical-strip Phragmen-Lindelöf finite-order API
transports these boundary estimates across the strip.  The removable
normalization is essential at `s = 1`; the raw product is recovered only after
this theorem. -/
theorem poleClearedRiemannZeta_one_two_strip_finiteOrder_growth_from_EulerMaclaurin_boundary_and_PL
    (hpartialLeft : BoundaryLineOneAbelPartialMajorant)
    (hcompactBoundary : PoleClearedOneTwoStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        1 ≤ w.re →
        w.re ≤ 2 →
        ‖poleClearedRiemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  exact
    poleClearedRiemannZeta_one_two_strip_growth_of_compactCore_and_verticalTail
      poleClearedRiemannZeta_one_two_strip_compactCore_growth_from_localBoundedness
      (poleClearedRiemannZeta_one_two_strip_verticalTail_growth_from_boundary_and_PL
        hpartialLeft hcompactBoundary)

/-- Bounded-width Euler-Maclaurin/continuation growth for the raw pole-cleared
zeta product on `1 ≤ Re s ≤ 2`.

This is the exact bounded-strip standard input: Euler-Maclaurin gives the
boundary-line estimate at `Re s = 1`, the Dirichlet series gives the right edge
at `Re s = 2`, and the pole-cleared product is holomorphic across `s = 1`, so
the generic vertical-strip Phragmen-Lindelöf finite-order API gives the
bounded-width envelope. -/
theorem classicalZeta_poleCleared_rightHalfPlane_one_le_two_le_finiteOrder_growth_from_EulerMaclaurin_strip
    (hpartialLeft : BoundaryLineOneAbelPartialMajorant)
    (hcompactBoundary : PoleClearedOneTwoStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        1 ≤ w.re →
        w.re ≤ 2 →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  match poleClearedRiemannZeta_one_two_strip_finiteOrder_growth_from_EulerMaclaurin_boundary_and_PL
      hpartialLeft hcompactBoundary with
  | ⟨A, B, m, hA, hB, hbound⟩ =>
      exact
        ⟨A, B, m, hA, hB,
          fun w hw_one hw_two =>
            dite (w = 1)
              (fun hw_eq_one =>
                have hraw_zero :
                    (w - 1) * riemannZeta w = 0 := by
                  have hfactor_zero : w - 1 = 0 := by
                    exact sub_eq_zero.mpr hw_eq_one
                  exact Eq.subst
                    (motive := fun u : ℂ => u * riemannZeta w = 0)
                    hfactor_zero.symm
                    (zero_mul (riemannZeta w))
                have htarget_nonneg :
                    0 ≤ A * Real.exp (B * (1 + ‖w‖) ^ m) :=
                  mul_nonneg (le_of_lt hA)
                    (le_of_lt (Real.exp_pos (B * (1 + ‖w‖) ^ m)))
                Eq.subst
                  (motive := fun u : ℂ =>
                    ‖u‖ ≤ A * Real.exp (B * (1 + ‖w‖) ^ m))
                  hraw_zero.symm
                  (Eq.subst
                    (motive := fun x : ℝ =>
                      x ≤ A * Real.exp (B * (1 + ‖w‖) ^ m))
                    (norm_zero : ‖(0 : ℂ)‖ = (0 : ℝ)).symm
                    htarget_nonneg))
              (fun hw_ne_one =>
                have hpole :
                    poleClearedRiemannZeta w = (w - 1) * riemannZeta w :=
                  poleClearedRiemannZeta_eq_of_ne_one hw_ne_one
                Eq.subst
                  (motive := fun u : ℂ =>
                    ‖u‖ ≤ A * Real.exp (B * (1 + ‖w‖) ^ m))
                  hpole
                  (hbound w hw_one hw_two))⟩

/-- Patch `1 ≤ Re s ≤ 2` Euler-Maclaurin/PL growth with the far-right
Dirichlet-series growth to obtain the full right half-plane. -/
theorem classicalZeta_poleCleared_rightHalfPlane_one_le_finiteOrder_growth_of_strip_and_farRight
    (hstrip :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ w : ℂ,
          1 ≤ w.re →
          w.re ≤ 2 →
          ‖(w - 1) * riemannZeta w‖ ≤
            A * Real.exp (B * (1 + ‖w‖) ^ m))
    (hfar :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ w : ℂ,
          2 ≤ w.re →
          ‖(w - 1) * riemannZeta w‖ ≤
            A * Real.exp (B * (1 + ‖w‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        1 ≤ w.re →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  match hstrip with
  | ⟨As, Bs, ms, hAs, hBs, hstrip_bound⟩ =>
      match hfar with
      | ⟨Af, Bf, mf, hAf, hBf, hfar_bound⟩ =>
            let A : ℝ := As + Af
            let B : ℝ := Bs + Bf
            let m : ℕ := ms + mf
            have hAs_nonneg : 0 ≤ As := le_of_lt hAs
            have hAf_nonneg : 0 ≤ Af := le_of_lt hAf
            have hBs_nonneg : 0 ≤ Bs := le_of_lt hBs
            have hBf_nonneg : 0 ≤ Bf := le_of_lt hBf
            have hA_pos : 0 < A :=
              add_pos hAs hAf
            have hB_pos : 0 < B :=
              add_pos hBs hBf
            exact
              ⟨A, B, m, hA_pos, hB_pos,
                fun w hw_one =>
                    match le_total w.re 2 with
                    | Or.inl hw_two =>
                        le_trans (hstrip_bound w hw_one hw_two)
                          (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                            hAs_nonneg
                            (le_add_of_nonneg_right hAf_nonneg)
                            (le_add_of_nonneg_right hBf_nonneg)
                            hBs_nonneg
                            (Nat.le_add_right ms mf))
                    | Or.inr hw_two =>
                        have hdegree : mf ≤ ms + mf := by
                          exact Eq.subst
                            (motive := fun d : ℕ => mf ≤ d)
                            (Nat.add_comm mf ms)
                            (Nat.le_add_right mf ms)
                        le_trans (hfar_bound w hw_two)
                          (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                            hAf_nonneg
                            (le_add_of_nonneg_left hAs_nonneg)
                            (le_add_of_nonneg_left hBs_nonneg)
                            hBf_nonneg
                            hdegree)⟩

/-- Classical Euler-Maclaurin half-plane finite-order theorem for the raw
pole-cleared Riemann zeta factor.

This is the exact analytic owner input absent from mathlib in the required
form.  It is the standard theorem that Euler-Maclaurin summation gives
polynomial, hence finite-order, growth for `(s - 1)ζ(s)` uniformly on
`Re s ≥ 1`; the factor `(s - 1)` removes the simple pole at `1`.  See
Titchmarsh, Ch. 3, or Edwards, Ch. 1. -/
theorem classicalZeta_poleCleared_rightHalfPlane_one_le_finiteOrder_growth_from_EulerMaclaurin
    (hpartialLeft : BoundaryLineOneAbelPartialMajorant)
    (hcompactBoundary : PoleClearedOneTwoStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        1 ≤ w.re →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  exact
    classicalZeta_poleCleared_rightHalfPlane_one_le_finiteOrder_growth_of_strip_and_farRight
      (classicalZeta_poleCleared_rightHalfPlane_one_le_two_le_finiteOrder_growth_from_EulerMaclaurin_strip
        hpartialLeft hcompactBoundary)
      riemannZeta_poleCleared_rightHalfPlane_two_le_finiteOrder_growth_from_dirichletSeries

/-- Euler-Maclaurin finite-order growth for the pole-cleared zeta factor on the
full reflected right half-plane `1 ≤ Re s`.

This is the standard continuation-strength form of the right-side zeta input:
Euler-Maclaurin/Abel summation controls `(s - 1)ζ(s)` uniformly from the
boundary line `Re s = 1` into the half-plane `Re s ≥ 1`.  The far-right
Dirichlet-series theorem above only proves the easier subregion `2 ≤ Re s`;
the transport across the functional equation genuinely needs this full
half-plane statement. -/
theorem riemannZeta_poleCleared_rightHalfPlane_one_le_finiteOrder_growth_from_EulerMaclaurin_standard
    (hpartialLeft : BoundaryLineOneAbelPartialMajorant)
    (hcompactBoundary : PoleClearedOneTwoStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        1 ≤ w.re →
        ‖(w - 1) * riemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  exact
    classicalZeta_poleCleared_rightHalfPlane_one_le_finiteOrder_growth_from_EulerMaclaurin
      hpartialLeft hcompactBoundary

/-- The standard Euler-Maclaurin bound for `(s - 1)ζ(s)` gives the removable
pole-cleared zeta bound on `1 ≤ Re s`. -/
theorem poleClearedRiemannZeta_rightHalfPlane_one_le_finiteOrder_growth_of_raw_EulerMaclaurin
    (hraw :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ w : ℂ,
          1 ≤ w.re →
          ‖(w - 1) * riemannZeta w‖ ≤
            A * Real.exp (B * (1 + ‖w‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        1 ≤ w.re →
        ‖poleClearedRiemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  match hraw with
  | ⟨A, B, m, hA, hB, hraw_bound⟩ =>
      exact
        ⟨A + 1, B, m, add_pos hA zero_lt_one, hB,
          fun w hw_re =>
            have hA_nonneg : 0 ≤ A := le_of_lt hA
            have hA_le : A ≤ A + 1 :=
              le_add_of_nonneg_right zero_le_one
            dite (w = 1)
              (fun hw_one =>
                have hpole_one :
                    poleClearedRiemannZeta w = 1 := by
                  exact Eq.subst
                    (motive := fun u : ℂ => poleClearedRiemannZeta u = 1)
                    hw_one.symm
                    poleClearedRiemannZeta_one
                have hfactor_ge_one :
                    (1 : ℝ) ≤ Real.exp (B * (1 + ‖w‖) ^ m) := by
                  have hbase_nonneg : 0 ≤ 1 + ‖w‖ :=
                    le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg w))
                  have hexponent_nonneg : 0 ≤ B * (1 + ‖w‖) ^ m :=
                    mul_nonneg (le_of_lt hB) (pow_nonneg hbase_nonneg m)
                  exact le_trans (le_of_eq Real.exp_zero.symm)
                    (Real.exp_le_exp.mpr hexponent_nonneg)
                have hone_le_A : (1 : ℝ) ≤ A + 1 :=
                  le_add_of_nonneg_left hA_nonneg
                have htarget :
                    (1 : ℝ) ≤ (A + 1) * Real.exp (B * (1 + ‖w‖) ^ m) := by
                  calc
                    (1 : ℝ) ≤ A + 1 := hone_le_A
                    _ = (A + 1) * 1 := by
                      exact (mul_one (A + 1)).symm
                    _ ≤ (A + 1) * Real.exp (B * (1 + ‖w‖) ^ m) :=
                      mul_le_mul_of_nonneg_left hfactor_ge_one
                        (le_trans zero_le_one hone_le_A)
                Eq.subst
                  (motive := fun u : ℂ =>
                    ‖u‖ ≤ (A + 1) * Real.exp (B * (1 + ‖w‖) ^ m))
                  hpole_one.symm
                  (Eq.subst
                    (motive := fun x : ℝ =>
                      x ≤ (A + 1) * Real.exp (B * (1 + ‖w‖) ^ m))
                    (norm_one : ‖(1 : ℂ)‖ = (1 : ℝ)).symm
                    htarget))
              (fun hw_ne_one =>
                have hpole_raw :
                    poleClearedRiemannZeta w = (w - 1) * riemannZeta w :=
                  poleClearedRiemannZeta_eq_of_ne_one hw_ne_one
                have henlarge :
                    A * Real.exp (B * (1 + ‖w‖) ^ m) ≤
                      (A + 1) * Real.exp (B * (1 + ‖w‖) ^ m) :=
                  exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
                    hA_nonneg hA_le (le_refl B) (le_of_lt hB) (le_refl m)
                Eq.subst
                  (motive := fun u : ℂ =>
                    ‖u‖ ≤ (A + 1) * Real.exp (B * (1 + ‖w‖) ^ m))
                  hpole_raw.symm
                  ((hraw_bound w hw_re).trans henlarge))⟩

theorem poleClearedRiemannZeta_rightHalfPlane_one_le_finiteOrder_growth_from_EulerMaclaurin
    (hpartialLeft : BoundaryLineOneAbelPartialMajorant)
    (hcompactBoundary : PoleClearedOneTwoStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        1 ≤ w.re →
        ‖poleClearedRiemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  exact
    poleClearedRiemannZeta_rightHalfPlane_one_le_finiteOrder_growth_of_raw_EulerMaclaurin
      (riemannZeta_poleCleared_rightHalfPlane_one_le_finiteOrder_growth_from_EulerMaclaurin_standard
        hpartialLeft hcompactBoundary)

/-- Reflected right half-plane finite-order growth for the pole-cleared zeta factor.

This is the right-side input needed by the functional equation on the left
half-plane: after reflection `w = 1 - z`, one only has `1 ≤ Re w`.  The proof is
the Euler-Maclaurin/Abel finite-order theorem in the half-plane of meromorphic
continuation, with the pole at `1` removed. -/
theorem poleClearedRiemannZeta_reflectedRightHalfPlane_finiteOrder_growth_from_EulerMaclaurin
    (hpartialLeft : BoundaryLineOneAbelPartialMajorant)
    (hcompactBoundary : PoleClearedOneTwoStripCompactBoundaryBound) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ w : ℂ,
        1 ≤ w.re →
        ‖poleClearedRiemannZeta w‖ ≤
          A * Real.exp (B * (1 + ‖w‖) ^ m) := by
  exact poleClearedRiemannZeta_rightHalfPlane_one_le_finiteOrder_growth_from_EulerMaclaurin
    hpartialLeft hcompactBoundary

end
end LFunctions
end Boundary
