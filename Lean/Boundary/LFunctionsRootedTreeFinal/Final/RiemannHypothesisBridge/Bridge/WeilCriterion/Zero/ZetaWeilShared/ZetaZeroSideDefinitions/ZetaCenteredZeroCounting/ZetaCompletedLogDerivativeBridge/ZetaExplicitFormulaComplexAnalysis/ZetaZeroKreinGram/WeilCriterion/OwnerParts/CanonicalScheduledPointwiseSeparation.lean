import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaAnalyticPackage.ScheduledPointwiseFactorBoundData
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduledAnalyticPackage

/-!
# Canonical scheduled pointwise separation

This owner part exposes the generic scheduled singular-separation lemmas on the
canonical autocorrelation height schedule.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

theorem complex_imaginary_separation_le_complex_distance
    (z w : ℂ) :
    ‖z.im - w.im‖ ≤ ‖z - w‖ :=
  (Complex.abs_im_le_abs (z - w))

theorem complex_distance_lower_bound_of_imaginary_separation
    (z w : ℂ) (δ : ℝ)
    (hδ : δ ≤ ‖z.im - w.im‖) :
    δ ≤ ‖z - w‖ :=
  hδ.trans (complex_imaginary_separation_le_complex_distance z w)

theorem complex_imaginary_height_le_center_height_add_distance
    (z w : ℂ) :
    ‖w.im‖ ≤ ‖z.im‖ + ‖w - z‖ := by
  have hsub : w.im - z.im = (w - z).im := by
    exact rfl
  have hadd : w.im = (w - z).im + z.im :=
    sub_eq_iff_eq_add.mp hsub
  have hcoord : w.im = z.im + (w - z).im :=
    hadd.trans (add_comm (w - z).im z.im)
  calc
    ‖w.im‖ = ‖z.im + (w - z).im‖ := congrArg norm hcoord
    _ ≤ ‖z.im‖ + ‖(w - z).im‖ := norm_add_le _ _
    _ ≤ ‖z.im‖ + ‖w - z‖ :=
      add_le_add_left (Complex.abs_im_le_abs (w - z)) ‖z.im‖

theorem complex_imaginary_height_le_center_height_add_radius
    (z w : ℂ) (R : ℝ)
    (hR : ‖w - z‖ ≤ R) :
    ‖w.im‖ ≤ ‖z.im‖ + R :=
  (complex_imaginary_height_le_center_height_add_distance z w).trans
    (add_le_add_left hR ‖z.im‖)

theorem height_add_radius_pow_le_scaled_height_pow
    (T R : ℝ) (d : ℕ)
    (hT : 1 ≤ T)
    (hR_nonneg : 0 ≤ R)
    (hR : R ≤ 2) :
    (T + R) ^ d ≤ (3 * T) ^ d := by
  have htwo : (2 : ℝ) ≤ 2 * T := by
    have hmul : (2 : ℝ) * 1 ≤ 2 * T :=
      mul_le_mul_of_nonneg_left hT zero_le_two
    calc
      (2 : ℝ) = 2 * 1 := (mul_one (2 : ℝ)).symm
      _ ≤ 2 * T := hmul
  have hthree : T + 2 ≤ 3 * T := by
    have hpre : T + 2 ≤ T + 2 * T := add_le_add_left htwo T
    have hrewrite : T + 2 * T = 3 * T := by
      calc
        T + 2 * T = (1 + 2) * T := by
          calc
            T + 2 * T = 1 * T + 2 * T :=
              congrArg (fun q : ℝ => q + 2 * T) (one_mul T).symm
            _ = (1 + 2) * T := (add_mul 1 2 T).symm
        _ = (2 + 1) * T := congrArg (fun n : ℝ => n * T) (add_comm 1 2)
        _ = 3 * T := congrArg (fun n : ℝ => n * T) two_add_one_eq_three
    exact Eq.subst (motive := fun x : ℝ => T + 2 ≤ x) hrewrite hpre
  have hradius : T + R ≤ 3 * T :=
    le_trans (add_le_add_left hR T) hthree
  have hnonneg : 0 ≤ T + R := by
    have : 0 ≤ T := le_trans zero_le_one hT
    exact add_nonneg this hR_nonneg
  exact pow_le_pow_left₀ hnonneg hradius d

theorem complex_imaginary_height_le_center_height_add_mem_sphere_radius
    (z w : ℂ) (R : ℝ)
    (hw : w ∈ Metric.sphere z R) :
    ‖w.im‖ ≤ ‖z.im‖ + R := by
  have hdist : dist w z = R := Metric.mem_sphere.mp hw
  have hnorm : ‖w - z‖ ≤ R := hdist.le
  exact complex_imaginary_height_le_center_height_add_radius z w R hnorm

theorem complex_real_coordinate_lower_upper_of_mem_sphere
    (z w : ℂ) (R : ℝ)
    (hw : w ∈ Metric.sphere z R) :
    z.re - R ≤ w.re ∧ w.re ≤ z.re + R := by
  have hdist : dist w z = R := Metric.mem_sphere.mp hw
  have hnorm : ‖w - z‖ = R := by
    calc
      ‖w - z‖ = dist w z := dist_eq_norm w z
      _ = R := hdist
  have himag : ‖(w - z).re‖ ≤ R := by
    calc
      ‖(w - z).re‖ ≤ ‖w - z‖ := Complex.abs_re_le_abs (w - z)
      _ = R := hnorm
  have hleft : -R ≤ (w - z).re := neg_le_of_abs_le himag
  have hright : (w - z).re ≤ R := le_of_abs_le himag
  have hsub : w.re - z.re = (w - z).re := by
    exact rfl
  constructor
  · have hleft' : -R ≤ w.re - z.re :=
      Eq.subst (motive := fun q : ℝ => -R ≤ q) hsub.symm hleft
    have hleft'' : -R + z.re ≤ w.re :=
      (le_sub_iff_add_le).mp hleft'
    have hrewrite : z.re - R = -R + z.re := by
      calc
        z.re - R = z.re + (-R) := sub_eq_add_neg z.re R
        _ = -R + z.re := add_comm z.re (-R)
    exact Eq.subst (motive := fun q : ℝ => q ≤ w.re) hrewrite hleft''
  · have hright' : w.re - z.re ≤ R :=
      Eq.subst (motive := fun q : ℝ => q ≤ R) hsub.symm hright
    have hright'' : w.re ≤ R + z.re :=
      (sub_le_iff_le_add).mp hright'
    exact
      Eq.subst
        (motive := fun q : ℝ => w.re ≤ q)
        (add_comm R z.re)
        hright''

theorem complex_norm_le_center_norm_add_mem_sphere_radius
    (z w : ℂ) (R : ℝ)
    (hw : w ∈ Metric.sphere z R) :
    ‖w‖ ≤ ‖z‖ + R := by
  have hdist : dist w z = R := Metric.mem_sphere.mp hw
  have hnorm : ‖w - z‖ = R := by
    calc
      ‖w - z‖ = dist w z := dist_eq_norm w z
      _ = R := hdist
  have hdecomp : w = (w - z) + z := by
    exact (sub_add_cancel w z).symm
  calc
    ‖w‖ = ‖(w - z) + z‖ := congrArg norm hdecomp
    _ ≤ ‖w - z‖ + ‖z‖ := norm_add_le _ _
    _ = R + ‖z‖ := congrArg (fun q : ℝ => q + ‖z‖) hnorm
    _ = ‖z‖ + R := add_comm R ‖z‖

theorem sphere_height_polynomial_bound_of_mem_sphere_radius
    (z w : ℂ) (R : ℝ) (d : ℕ)
    (hw : w ∈ Metric.sphere z R)
    (hT : 1 ≤ 1 + ‖z.im‖)
    (hR_nonneg : 0 ≤ R) (hR : R ≤ 2) :
    (1 + ‖w.im‖) ^ d ≤ (3 * (1 + ‖z.im‖)) ^ d := by
  have himag : ‖w.im‖ ≤ ‖z.im‖ + R :=
    complex_imaginary_height_le_center_height_add_mem_sphere_radius z w R hw
  have hsum : 1 + ‖w.im‖ ≤ (1 + ‖z.im‖) + R := by
    exact add_le_add_left himag 1
  have hpow : (1 + ‖w.im‖) ^ d ≤ ((1 + ‖z.im‖) + R) ^ d :=
    pow_le_pow_left₀ (add_nonneg zero_le_one (norm_nonneg _)) hsum d
  exact hpow.trans
    (height_add_radius_pow_le_scaled_height_pow
      (1 + ‖z.im‖) R d hT hR_nonneg hR)

theorem sphere_amplitude_height_polynomial_bound_of_mem_sphere_radius
    (z w : ℂ) (R A : ℝ) (d : ℕ)
    (hw : w ∈ Metric.sphere z R)
    (hA : 0 ≤ A)
    (hT : 1 ≤ 1 + ‖z.im‖)
    (hR_nonneg : 0 ≤ R) (hR : R ≤ 2) :
    A * (1 + ‖w.im‖) ^ d ≤
      A * 3 ^ d * (1 + ‖z.im‖) ^ d := by
  have hheight :
      (1 + ‖w.im‖) ^ d ≤ (3 * (1 + ‖z.im‖)) ^ d :=
    sphere_height_polynomial_bound_of_mem_sphere_radius
      z w R d hw hT hR_nonneg hR
  have hamplitude :
      A * (1 + ‖w.im‖) ^ d ≤ A * (3 * (1 + ‖z.im‖)) ^ d :=
    mul_le_mul_of_nonneg_left hheight hA
  calc
    A * (1 + ‖w.im‖) ^ d ≤ A * (3 * (1 + ‖z.im‖)) ^ d := hamplitude
    _ = A * (3 ^ d * (1 + ‖z.im‖) ^ d) := by
      exact congrArg
        (fun q : ℝ => A * q)
        (mul_pow 3 (1 + ‖z.im‖) d)
    _ = A * 3 ^ d * (1 + ‖z.im‖) ^ d := by
      exact (mul_assoc A (3 ^ d) ((1 + ‖z.im‖) ^ d)).symm

theorem sphere_bound_of_center_height_polynomial_bound
    {G : ℂ → ℂ} (z : ℂ) (R A : ℝ) (d : ℕ)
    (hA : 0 ≤ A)
    (hT : 1 ≤ 1 + ‖z.im‖)
    (hR_nonneg : 0 ≤ R) (hR : R ≤ 2)
    (hbound : ∀ w : ℂ,
      w ∈ Metric.sphere z R →
        ‖G w‖ ≤ A * (1 + ‖w.im‖) ^ d) :
    ∀ w : ℂ,
      w ∈ Metric.sphere z R →
        ‖G w‖ ≤ A * 3 ^ d * (1 + ‖z.im‖) ^ d :=
  fun w hw =>
    (hbound w hw).trans
      (sphere_amplitude_height_polynomial_bound_of_mem_sphere_radius
        z w R A d hw hA hT hR_nonneg hR)

theorem sphere_bound_of_center_height_polynomial_bound_add_radius
    {G : ℂ → ℂ} (z : ℂ) (R A : ℝ) (d : ℕ)
    (hA : 0 ≤ A) (hR_nonneg : 0 ≤ R)
    (hbound : ∀ w : ℂ,
      w ∈ Metric.sphere z R →
        ‖G w‖ ≤ A * (1 + ‖w.im‖) ^ d) :
    ∀ w : ℂ,
      w ∈ Metric.sphere z R →
        ‖G w‖ ≤ A * (1 + ‖z.im‖ + R) ^ d := by
  intro w hw
  have hheight : ‖w.im‖ ≤ ‖z.im‖ + R :=
    complex_imaginary_height_le_center_height_add_mem_sphere_radius z w R hw
  have hsum : 1 + ‖w.im‖ ≤ 1 + ‖z.im‖ + R :=
    add_le_add_left hheight 1
  have hpow : (1 + ‖w.im‖) ^ d ≤ (1 + ‖z.im‖ + R) ^ d :=
    pow_le_pow_left₀
      (add_nonneg zero_le_one (norm_nonneg w.im)) hsum d
  have hamplitude :
      A * (1 + ‖w.im‖) ^ d ≤ A * (1 + ‖z.im‖ + R) ^ d :=
    mul_le_mul_of_nonneg_left hpow hA
  exact (hbound w hw).trans hamplitude

theorem zetaCompletedExplicitFormulaAutocorrelationTopPath_completedRiemannZeta_ne_zero_owner
    (f : ZetaAdmissibleFunction) (u x : ℝ)
    (hx : x ∈ Set.uIcc
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
      (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    completedRiemannZeta
      (zetaCompletedExplicitFormulaTopPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
          ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
        x) ≠ 0 :=
  (zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).topPath_completedRiemannZeta_ne_zero
    u
    x
    hx

theorem zetaCompletedExplicitFormulaAutocorrelationBottomPath_completedRiemannZeta_ne_zero_owner
    (f : ZetaAdmissibleFunction) (u x : ℝ)
    (hx : x ∈ Set.uIcc
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
      (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    completedRiemannZeta
      (zetaCompletedExplicitFormulaBottomPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
          ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
        x) ≠ 0 :=
  (zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).bottomPath_completedRiemannZeta_ne_zero
    u
    x
    hx

theorem zetaCompletedExplicitFormulaAutocorrelationTopPath_GammaReal_ne_zero_owner
    (f : ZetaAdmissibleFunction) (u x : ℝ)
    (hx : x ∈ Set.uIcc
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
      (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    Complex.Gammaℝ
      (zetaCompletedExplicitFormulaTopPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
          ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
        x) ≠ 0 :=
  (zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).topPath_GammaReal_ne_zero
    u
    x
    hx

theorem zetaCompletedExplicitFormulaAutocorrelationBottomPath_GammaReal_ne_zero_owner
    (f : ZetaAdmissibleFunction) (u x : ℝ)
    (hx : x ∈ Set.uIcc
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
      (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    Complex.Gammaℝ
      (zetaCompletedExplicitFormulaBottomPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
          ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
        x) ≠ 0 :=
  (zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).bottomPath_GammaReal_ne_zero
    u
    x
    hx

theorem zetaCompletedExplicitFormulaAutocorrelationTopPath_zetaSideFactor_ne_zero_owner
    (f : ZetaAdmissibleFunction) (u x : ℝ)
    (hx : x ∈ Set.uIcc
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
      (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    zetaSideFactor
      (zetaCompletedExplicitFormulaTopPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
          ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
        x) ≠ 0 :=
  zetaSideFactor_ne_zero
    (zetaCompletedExplicitFormulaAutocorrelationTopPath_completedRiemannZeta_ne_zero_owner
      f u x hx)
    (zetaCompletedExplicitFormulaAutocorrelationTopPath_GammaReal_ne_zero_owner
      f u x hx)

theorem zetaCompletedExplicitFormulaAutocorrelationBottomPath_zetaSideFactor_ne_zero_owner
    (f : ZetaAdmissibleFunction) (u x : ℝ)
    (hx : x ∈ Set.uIcc
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
      (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    zetaSideFactor
      (zetaCompletedExplicitFormulaBottomPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
          ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
        x) ≠ 0 :=
  zetaSideFactor_ne_zero
    (zetaCompletedExplicitFormulaAutocorrelationBottomPath_completedRiemannZeta_ne_zero_owner
      f u x hx)
    (zetaCompletedExplicitFormulaAutocorrelationBottomPath_GammaReal_ne_zero_owner
      f u x hx)

theorem zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_zetaSideFactor_ne_zero_owner
    (f : ZetaAdmissibleFunction) {z : ℂ}
    (hz : z ∈
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier) :
    zetaSideFactor z ≠ 0 := by
  have hcases :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_mem_cases
      f z hz
  exact Or.elim hcases
    (fun htop =>
      Exists.elim htop
        (fun u htop_u =>
          Exists.elim htop_u
            (fun x htop_x =>
              Eq.subst
                (motive := fun w : ℂ => zetaSideFactor w ≠ 0)
                htop_x.2.symm
                (zetaCompletedExplicitFormulaAutocorrelationTopPath_zetaSideFactor_ne_zero_owner
                  f u x htop_x.1))))
    (fun hbottom =>
      Exists.elim hbottom
        (fun u hbottom_u =>
          Exists.elim hbottom_u
            (fun x hbottom_x =>
              Eq.subst
                (motive := fun w : ℂ => zetaSideFactor w ≠ 0)
                hbottom_x.2.symm
                (zetaCompletedExplicitFormulaAutocorrelationBottomPath_zetaSideFactor_ne_zero_owner
                  f u x hbottom_x.1))))

theorem zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_inverseGamma_ne_zero_owner
    (f : ZetaAdmissibleFunction) {z : ℂ}
    (hz : z ∈
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier) :
    (Complex.Gammaℝ z)⁻¹ ≠ 0 := by
  have hcases :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_mem_cases
      f z hz
  exact Or.elim hcases
    (fun htop =>
      Exists.elim htop
        (fun u htop_u =>
          Exists.elim htop_u
            (fun x htop_x =>
              Eq.subst
                (motive := fun w : ℂ => (Complex.Gammaℝ w)⁻¹ ≠ 0)
                htop_x.2.symm
                (inv_ne_zero
                  (zetaCompletedExplicitFormulaAutocorrelationTopPath_GammaReal_ne_zero_owner
                    f u x htop_x.1)))))
    (fun hbottom =>
      Exists.elim hbottom
        (fun u hbottom_u =>
          Exists.elim hbottom_u
            (fun x hbottom_x =>
              Eq.subst
                (motive := fun w : ℂ => (Complex.Gammaℝ w)⁻¹ ≠ 0)
                hbottom_x.2.symm
              (inv_ne_zero
                  (zetaCompletedExplicitFormulaAutocorrelationBottomPath_GammaReal_ne_zero_owner
                    f u x hbottom_x.1)))))

/-- Every scheduled carrier point has a genuine inverse-Gamma regular
neighborhood.  This is the local analytic input for the noncompact carrier
construction; uniformity in height is supplied separately by the scheduled
growth estimates. -/
theorem zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_inverseGamma_closedBall_regular_owner
    (f : ZetaAdmissibleFunction) {z : ℂ}
    (hz : z ∈
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ w : ℂ, w ∈ Metric.closedBall z ε →
        (Complex.Gammaℝ w)⁻¹ ≠ 0 := by
  have hzero : (Complex.Gammaℝ z)⁻¹ ≠ 0 :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_inverseGamma_ne_zero_owner
      f hz
  have hgamma : Complex.Gammaℝ z ≠ 0 :=
    (inv_ne_zero.mp hzero)
  have hcont : ContinuousAt (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z :=
    (Gammaℝ_differentiableAt_of_ne_zero_locus
      (fun n hn => hgamma
        (Complex.Gammaℝ_eq_zero_iff.mpr ⟨n, hn⟩))).continuousAt.inv₀ hgamma
  rcases Metric.mem_nhds_iff.mp (hcont.eventually_ne hzero) with
    ⟨ε, hε, hball⟩
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro w hw
  have hdist : dist w z ≤ ε / 2 := Metric.mem_closedBall.mp hw
  exact hball (hdist.trans_lt (half_lt_self hε))

/-- The regular closed ball has a positive quantitative inverse-Gamma lower
bound. -/
theorem zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_inverseGamma_closedBall_lower_owner
    (f : ZetaAdmissibleFunction) {z : ℂ}
    (hz : z ∈
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      (∀ w : ℂ, w ∈ Metric.closedBall z ε →
        (Complex.Gammaℝ w)⁻¹ ≠ 0) ∧
      ∀ w : ℂ, w ∈ Metric.closedBall z ε →
        δ ≤ ‖(Complex.Gammaℝ w)⁻¹‖ := by
  rcases
      zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_inverseGamma_closedBall_regular_owner
        f hz with
    ⟨ε, hε, hregular⟩
  let s : Set ℂ := Metric.closedBall z ε
  have hs : IsCompact s := by
    exact Metric.isCompact_closedBall
  have hs_nonempty : s.Nonempty := by
    exact ⟨z, Metric.mem_closedBall_self (le_of_lt hε)⟩
  have hcontinuous :
      ContinuousOn (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) s := by
    intro w hw
    have hinv : (Complex.Gammaℝ w)⁻¹ ≠ 0 := hregular w hw
    have hgamma : Complex.Gammaℝ w ≠ 0 := inv_ne_zero.mp hinv
    exact
      ((Gammaℝ_differentiableAt_of_ne_zero_locus
        (fun n hn => hgamma
          (Complex.Gammaℝ_eq_zero_iff.mpr ⟨n, hn⟩))).continuousAt.inv₀ hgamma)
        .continuousWithinAt
  obtain ⟨δ, hδ, hδ_bound⟩ :=
    hs.exists_isMinOn hs_nonempty hcontinuous.norm
  refine ⟨ε, δ, hε, ?_, hregular, ?_⟩
  · exact norm_pos_iff.mpr (hregular z (Metric.mem_closedBall_self (le_of_lt hε)))
  · intro w hw
    exact hδ_bound hw

theorem zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_completedRiemannZeta_ne_zero_owner
    (f : ZetaAdmissibleFunction) {z : ℂ}
    (hz : z ∈
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier) :
    completedRiemannZeta z ≠ 0 := by
  have hcases :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_mem_cases
      f z hz
  exact Or.elim hcases
    (fun htop =>
      Exists.elim htop
        (fun u htop_u =>
          Exists.elim htop_u
            (fun x htop_x =>
              Eq.subst
                (motive := fun w : ℂ => completedRiemannZeta w ≠ 0)
                htop_x.2.symm
                (zetaCompletedExplicitFormulaAutocorrelationTopPath_completedRiemannZeta_ne_zero_owner
                  f u x htop_x.1))))
    (fun hbottom =>
      Exists.elim hbottom
        (fun u hbottom_u =>
          Exists.elim hbottom_u
            (fun x hbottom_x =>
              Eq.subst
                (motive := fun w : ℂ => completedRiemannZeta w ≠ 0)
                hbottom_x.2.symm
                (zetaCompletedExplicitFormulaAutocorrelationBottomPath_completedRiemannZeta_ne_zero_owner
                  f u x hbottom_x.1))))

theorem zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_completedRiemannZeta_closedBall_regular_owner
    (f : ZetaAdmissibleFunction) {z : ℂ}
    (hz : z ∈
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ w : ℂ, w ∈ Metric.closedBall z ε → completedRiemannZeta w ≠ 0 := by
  have hz0 : z ≠ 0 :=
    (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).ne_zero z hz
  have hz1 : z ≠ 1 :=
    (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).ne_one z hz
  have hzeta : completedRiemannZeta z ≠ 0 :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_completedRiemannZeta_ne_zero_owner
      f hz
  have hcont : ContinuousAt completedRiemannZeta z :=
    (differentiableAt_completedRiemannZeta hz0 hz1).continuousAt
  rcases Metric.mem_nhds_iff.mp (hcont.eventually_ne hzeta) with
    ⟨ε, hε, hball⟩
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro w hw
  have hdist : dist w z ≤ ε / 2 := Metric.mem_closedBall.mp hw
  exact hball (hdist.trans_lt (half_lt_self hε))

theorem completedRiemannZeta_positive_lower_bound_on_closedBall_of_regular_owner
    (z : ℂ) (ε : ℝ) (hε : 0 < ε)
    (hregular : ∀ w : ℂ, w ∈ Metric.closedBall z ε →
      completedRiemannZeta w ≠ 0)
    (hzero : ∀ w : ℂ, w ∈ Metric.closedBall z ε → w ≠ 0)
    (hone : ∀ w : ℂ, w ∈ Metric.closedBall z ε → w ≠ 1) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ w : ℂ, w ∈ Metric.closedBall z ε →
        δ ≤ ‖completedRiemannZeta w‖ := by
  let s : Set ℂ := Metric.closedBall z ε
  have hs : IsCompact s := by
    exact Metric.isCompact_closedBall
  have hs_nonempty : s.Nonempty := by
    exact ⟨z, Metric.mem_closedBall_self (le_of_lt hε)⟩
  have hcontinuous : ContinuousOn completedRiemannZeta s := by
    intro w hw
    exact (differentiableAt_completedRiemannZeta
      (hzero w hw) (hone w hw)).continuousAt.continuousWithinAt
  obtain ⟨δ, hδ, hδ_bound⟩ :=
    hs.exists_isMinOn hs_nonempty hcontinuous.norm
  refine ⟨δ, ?_, ?_⟩
  · exact norm_pos_iff.mpr (hregular z (Metric.mem_closedBall_self (le_of_lt hε)))
  · intro w hw
    exact hδ_bound hw

theorem zetaSideFactor_positive_lower_bound_of_component_lower_bounds_owner
    (z : ℂ) (R : ℝ) (mζ mΓ : ℝ)
    (hmζ : 0 < mζ) (hmΓ : 0 < mΓ)
    (hζ : ∀ w : ℂ, w ∈ Metric.closedBall z R →
      mζ ≤ ‖completedRiemannZeta w‖)
    (hΓ : ∀ w : ℂ, w ∈ Metric.closedBall z R →
      mΓ ≤ ‖(Complex.Gammaℝ w)⁻¹‖) :
    0 < mζ * mΓ ∧
      ∀ w : ℂ, w ∈ Metric.closedBall z R →
        mζ * mΓ ≤ ‖zetaSideFactor w‖ := by
  refine ⟨mul_pos hmζ hmΓ, ?_⟩
  intro w hw
  have hζ_nonneg : 0 ≤ ‖completedRiemannZeta w‖ := norm_nonneg _
  have hΓ_nonneg : 0 ≤ ‖(Complex.Gammaℝ w)⁻¹‖ := norm_nonneg _
  have hmul := mul_le_mul (hζ w hw) (hΓ w hw) hΓ_nonneg hζ_nonneg
  exact (show mζ * mΓ ≤
      ‖completedRiemannZeta w‖ * ‖(Complex.Gammaℝ w)⁻¹‖ from hmul).trans_eq
    (show ‖zetaSideFactor w‖ =
      ‖completedRiemannZeta w‖ * ‖(Complex.Gammaℝ w)⁻¹‖ from
      (norm_mul _ _).symm)

theorem zetaSideFactor_pointwise_lower_bound_of_component_bounds_owner
    (P : ℂ → Prop) (mζ mΓ : ℝ) (hmζ : 0 < mζ) (hmΓ : 0 < mΓ)
    (hζ : ∀ w : ℂ, P w → mζ ≤ ‖completedRiemannZeta w‖)
    (hΓ : ∀ w : ℂ, P w → mΓ ≤ ‖(Complex.Gammaℝ w)⁻¹‖) :
    0 < mζ * mΓ ∧
      ∀ w : ℂ, P w → mζ * mΓ ≤ ‖zetaSideFactor w‖ := by
  refine ⟨mul_pos hmζ hmΓ, ?_⟩
  intro w hw
  have hζ_nonneg : 0 ≤ ‖completedRiemannZeta w‖ := norm_nonneg _
  have hΓ_nonneg : 0 ≤ ‖(Complex.Gammaℝ w)⁻¹‖ := norm_nonneg _
  have hmul := mul_le_mul (hζ w hw) (hΓ w hw) hΓ_nonneg hζ_nonneg
  exact (show mζ * mΓ ≤
      ‖completedRiemannZeta w‖ * ‖(Complex.Gammaℝ w)⁻¹‖ from hmul).trans_eq
    (show ‖zetaSideFactor w‖ =
      ‖completedRiemannZeta w‖ * ‖(Complex.Gammaℝ w)⁻¹‖ from
      (norm_mul _ _).symm)

theorem zetaSideFactor_ne_zero_of_component_bounds_owner
    (P : ℂ → Prop) (mζ mΓ : ℝ) (hmζ : 0 < mζ) (hmΓ : 0 < mΓ)
    (hζ : ∀ w : ℂ, P w → mζ ≤ ‖completedRiemannZeta w‖)
    (hΓ : ∀ w : ℂ, P w → mΓ ≤ ‖(Complex.Gammaℝ w)⁻¹‖) :
    ∀ w : ℂ, P w → zetaSideFactor w ≠ 0 := by
  obtain ⟨hprod, hfactor⟩ :=
    zetaSideFactor_pointwise_lower_bound_of_component_bounds_owner
      P mζ mΓ hmζ hmΓ hζ hΓ
  intro w hw hzero
  have hnorm_zero : ‖zetaSideFactor w‖ = 0 := by
    calc
      ‖zetaSideFactor w‖ = ‖(0 : ℂ)‖ := congrArg norm hzero
      _ = 0 := norm_zero
  have hpositive : 0 < ‖zetaSideFactor w‖ :=
    lt_of_lt_of_le hprod (hfactor w hw)
  exact (ne_of_gt hpositive) hnorm_zero

theorem inverseGamma_ne_zero_of_component_lower_bound_owner
    (P : ℂ → Prop) (mΓ : ℝ) (hmΓ : 0 < mΓ)
    (hΓ : ∀ w : ℂ, P w → mΓ ≤ ‖(Complex.Gammaℝ w)⁻¹‖) :
    ∀ w : ℂ, P w → (Complex.Gammaℝ w)⁻¹ ≠ 0 := by
  intro w hw hzero
  have hnorm_zero : ‖(Complex.Gammaℝ w)⁻¹‖ = 0 := by
    calc
      ‖(Complex.Gammaℝ w)⁻¹‖ = ‖(0 : ℂ)‖ := congrArg norm hzero
      _ = 0 := norm_zero
  have hpositive : 0 < ‖(Complex.Gammaℝ w)⁻¹‖ :=
    lt_of_lt_of_le hmΓ (hΓ w hw)
  exact (ne_of_gt hpositive) hnorm_zero

theorem completedRiemannZeta_ne_zero_of_component_lower_bound_owner
    (P : ℂ → Prop) (mζ : ℝ) (hmζ : 0 < mζ)
    (hζ : ∀ w : ℂ, P w → mζ ≤ ‖completedRiemannZeta w‖) :
    ∀ w : ℂ, P w → completedRiemannZeta w ≠ 0 := by
  intro w hw hzero
  have hnorm_zero : ‖completedRiemannZeta w‖ = 0 := by
    calc
      ‖completedRiemannZeta w‖ = ‖(0 : ℂ)‖ := congrArg norm hzero
      _ = 0 := norm_zero
  have hpositive : 0 < ‖completedRiemannZeta w‖ :=
    lt_of_lt_of_le hmζ (hζ w hw)
  exact (ne_of_gt hpositive) hnorm_zero

theorem zetaSideFactor_ne_zero_of_component_nonzero_owner
    (P : ℂ → Prop)
    (hζ : ∀ w : ℂ, P w → completedRiemannZeta w ≠ 0)
    (hΓ : ∀ w : ℂ, P w → (Complex.Gammaℝ w)⁻¹ ≠ 0) :
    ∀ w : ℂ, P w → zetaSideFactor w ≠ 0 := by
  intro w hw
  exact mul_ne_zero (hζ w hw) (hΓ w hw)

theorem zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_zetaSideFactor_differentiableAt_owner
    (f : ZetaAdmissibleFunction) {z : ℂ}
    (hz : z ∈
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier) :
    DifferentiableAt ℂ zetaSideFactor z := by
  have hz0 : z ≠ 0 :=
    (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).ne_zero z hz
  have hz1 : z ≠ 1 :=
    (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).ne_one z hz
  have hgamma : Complex.Gammaℝ z ≠ 0 :=
    (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).gamma_ne_zero z hz
  change DifferentiableAt ℂ
    (fun w : ℂ => completedRiemannZeta w * (Complex.Gammaℝ w)⁻¹) z
  exact differentiableAt_completedZeta_factorized hz0 hz1 hgamma

theorem zetaCompletedExplicitFormulaAutocorrelationScheduledTopPath_zetaSideFactor_continuousOn_owner
    (f : ZetaAdmissibleFunction) (u : ℝ) :
    ContinuousOn
      (fun x : ℝ => zetaSideFactor
        (zetaCompletedExplicitFormulaTopPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x))
      (Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) := by
  intro x hx
  have hzmem :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_top_mem
      f u x hx
  have hfactor :
      ContinuousAt zetaSideFactor
        (zetaCompletedExplicitFormulaTopPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x) :=
    (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_zetaSideFactor_differentiableAt_owner
      f hzmem).continuousAt
  exact hfactor.comp x
    (zetaCompletedExplicitFormulaTopPath_continuous
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
        ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))).continuousAt

theorem zetaCompletedExplicitFormulaAutocorrelationScheduledBottomPath_zetaSideFactor_continuousOn_owner
    (f : ZetaAdmissibleFunction) (u : ℝ) :
    ContinuousOn
      (fun x : ℝ => zetaSideFactor
        (zetaCompletedExplicitFormulaBottomPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x))
      (Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) := by
  intro x hx
  have hzmem :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_bottom_mem
      f u x hx
  have hfactor :
      ContinuousAt zetaSideFactor
        (zetaCompletedExplicitFormulaBottomPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x) :=
    (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_zetaSideFactor_differentiableAt_owner
      f hzmem).continuousAt
  exact hfactor.comp x
    (zetaCompletedExplicitFormulaBottomPath_continuous
      ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
        ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))).continuousAt

theorem zetaSideNegLogDeriv_continuousAt_of_analyticAt_owner
    {z : ℂ}
    (hanalytic : AnalyticAt ℂ zetaSideFactor z)
    (hne : zetaSideFactor z ≠ 0) :
    ContinuousAt zetaSideNegLogDeriv z := by
  have hderiv :
      ContinuousAt (fun w : ℂ => deriv zetaSideFactor w) z :=
    analyticAt_deriv_continuousAt hanalytic
  have hfactor : ContinuousAt zetaSideFactor z :=
    hanalytic.continuousAt
  have hquot :
      ContinuousAt (fun w : ℂ => deriv zetaSideFactor w /
        zetaSideFactor w) z :=
    hderiv.div hfactor hne
  have hneg :
      ContinuousAt (fun w : ℂ => -deriv zetaSideFactor w /
        zetaSideFactor w) z :=
    hquot.neg
  have hdef :
      (fun w : ℂ => zetaSideNegLogDeriv w) =
        (fun w : ℂ => -deriv zetaSideFactor w /
          zetaSideFactor w) := by
    funext w
    exact zetaSideNegLogDeriv_eq_def w
  exact Eq.subst
    (motive := fun φ : ℂ → ℂ => ContinuousAt φ z)
    hdef.symm
    hneg

theorem completedZetaNegLogDeriv_norm_bound_of_pointwise_factor_bounds_owner
    {a b : ℝ} (E : CompletedZetaZeroExcisedStrip a b)
    (N : ℕ) (Czeta Cgamma : ℝ) (z : ℂ) (hz : z ∈ E.carrier)
    (hzeta : ‖zetaSideNegLogDeriv z‖ ≤
      Czeta * (1 + ‖z.im‖) ^ N)
    (hgamma : ‖inverseGammaCompletionLogDeriv z‖ ≤
      Cgamma * (1 + ‖z.im‖) ^ N) :
    ‖completedZetaNegLogDeriv z‖ ≤
      (Czeta + Cgamma) * (1 + ‖z.im‖) ^ N := by
  have hsplit : ‖completedZetaNegLogDeriv z‖ ≤
      ‖zetaSideNegLogDeriv z‖ + ‖inverseGammaCompletionLogDeriv z‖ :=
    completedZetaNegLogDeriv_norm_le_zetaSide_norm_add_inverseGammaCorrection_norm
      E z hz
  have hsum : ‖zetaSideNegLogDeriv z‖ +
      ‖inverseGammaCompletionLogDeriv z‖ ≤
      Czeta * (1 + ‖z.im‖) ^ N +
        Cgamma * (1 + ‖z.im‖) ^ N :=
    add_le_add hzeta hgamma
  calc
    ‖completedZetaNegLogDeriv z‖ ≤
        ‖zetaSideNegLogDeriv z‖ + ‖inverseGammaCompletionLogDeriv z‖ := hsplit
    _ ≤ Czeta * (1 + ‖z.im‖) ^ N +
        Cgamma * (1 + ‖z.im‖) ^ N := hsum
    _ = (Czeta + Cgamma) * (1 + ‖z.im‖) ^ N := by
      exact (add_mul Czeta Cgamma ((1 + ‖z.im‖) ^ N)).symm

theorem inverseGammaCompletionLogDeriv_norm_le_of_pointwise_deriv_inv_bound_owner
    (z : ℂ) (Cgamma : ℝ) (N : ℕ)
    (hbound : ‖deriv (fun ξ : ℂ => (Complex.Gammaℝ ξ)⁻¹) z /
      (Complex.Gammaℝ z)⁻¹‖ ≤ Cgamma * (1 + ‖z.im‖) ^ N) :
    ‖inverseGammaCompletionLogDeriv z‖ ≤
      Cgamma * (1 + ‖z.im‖) ^ N := by
  have hcorrection :
      inverseGammaCompletionLogDeriv z =
        deriv (fun ξ : ℂ => (Complex.Gammaℝ ξ)⁻¹) z /
          (Complex.Gammaℝ z)⁻¹ :=
    inverseGammaCompletionLogDeriv_eq z
  exact Eq.subst
    (motive := fun w : ℂ => ‖w‖ ≤ Cgamma * (1 + ‖z.im‖) ^ N)
    hcorrection.symm
    hbound

theorem completedZetaNegLogDeriv_norm_bound_of_pointwise_raw_factor_bounds_owner
    {a b : ℝ} (E : CompletedZetaZeroExcisedStrip a b)
    (N : ℕ) (Czeta Cgamma : ℝ) (z : ℂ) (hz : z ∈ E.carrier)
    (hzeta : ‖zetaSideNegLogDeriv z‖ ≤
      Czeta * (1 + ‖z.im‖) ^ N)
    (hgamma : ‖deriv (fun ξ : ℂ => (Complex.Gammaℝ ξ)⁻¹) z /
      (Complex.Gammaℝ z)⁻¹‖ ≤ Cgamma * (1 + ‖z.im‖) ^ N) :
    ‖completedZetaNegLogDeriv z‖ ≤
      (Czeta + Cgamma) * (1 + ‖z.im‖) ^ N := by
  have hcorrection :=
    inverseGammaCompletionLogDeriv_norm_le_of_pointwise_deriv_inv_bound_owner
      z Cgamma N hgamma
  exact completedZetaNegLogDeriv_norm_bound_of_pointwise_factor_bounds_owner
    E N Czeta Cgamma z hz hzeta hcorrection

theorem completedZetaNegLogDeriv_norm_bound_of_uniform_raw_factor_bounds_owner
    {a b : ℝ} (E : CompletedZetaZeroExcisedStrip a b)
    (Czeta Cgamma : ℝ) (z : ℂ) (hz : z ∈ E.carrier)
    (hzeta : ∀ w : ℂ, w ∈ E.carrier →
      ‖zetaSideNegLogDeriv w‖ ≤ Czeta)
    (hgamma : ∀ w : ℂ, w ∈ E.carrier →
      ‖deriv (fun ξ : ℂ => (Complex.Gammaℝ ξ)⁻¹) w /
        (Complex.Gammaℝ w)⁻¹‖ ≤ Cgamma) :
    ‖completedZetaNegLogDeriv z‖ ≤ Czeta + Cgamma := by
  have hzeta' : ‖zetaSideNegLogDeriv z‖ ≤
      Czeta * (1 + ‖z.im‖) ^ 0 := by
    have hpow : (1 + ‖z.im‖) ^ 0 = (1 : ℝ) := pow_zero _
    have hmul : Czeta * (1 + ‖z.im‖) ^ 0 = Czeta :=
      Eq.trans (congrArg (fun q : ℝ => Czeta * q) hpow) (mul_one Czeta)
    exact Eq.trans (hzeta z hz) hmul.symm
  have hgamma' : ‖deriv (fun ξ : ℂ => (Complex.Gammaℝ ξ)⁻¹) z /
        (Complex.Gammaℝ z)⁻¹‖ ≤ Cgamma * (1 + ‖z.im‖) ^ 0 := by
    have hpow : (1 + ‖z.im‖) ^ 0 = (1 : ℝ) := pow_zero _
    have hmul : Cgamma * (1 + ‖z.im‖) ^ 0 = Cgamma :=
      Eq.trans (congrArg (fun q : ℝ => Cgamma * q) hpow) (mul_one Cgamma)
    exact Eq.trans (hgamma z hz) hmul.symm
  have hbound := completedZetaNegLogDeriv_norm_bound_of_pointwise_raw_factor_bounds_owner
    E 0 Czeta Cgamma z hz hzeta' hgamma'
  have hpow : (1 + ‖z.im‖) ^ 0 = (1 : ℝ) := pow_zero _
  have hmul : (Czeta + Cgamma) * (1 + ‖z.im‖) ^ 0 =
      Czeta + Cgamma :=
    Eq.trans (congrArg (fun q : ℝ => (Czeta + Cgamma) * q) hpow)
      (mul_one (Czeta + Cgamma))
  calc
    ‖completedZetaNegLogDeriv z‖ ≤
        (Czeta + Cgamma) * (1 + ‖z.im‖) ^ 0 := hbound
    _ = Czeta + Cgamma := hmul

theorem zetaCompletedExplicitFormulaAutocorrelationScheduledTopPath_completedLogDeriv_uniform_bound_owner
    (f : ZetaAdmissibleFunction) (u : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : ℝ, x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
        ‖completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x)‖ ≤ B := by
  obtain ⟨Czeta, hCzeta, hzeta⟩ :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledTopPath_zetaSideLogDeriv_uniform_bound_owner
      f u
  obtain ⟨Cgamma, hCgamma, hgamma⟩ :=
    ExplicitFormulaCofinalHeightSchedule.topPath_inverseGamma_logDeriv_uniform_bound
      (zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f) u
  refine ⟨Czeta + Cgamma, add_nonneg hCzeta hCgamma, ?_⟩
  intro x hx
  let z := zetaCompletedExplicitFormulaTopPath
    ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
      ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x
  let E := zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f
  have hz : z ∈ E.carrier :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_top_mem f u x hx
  have hzeta' : ‖zetaSideNegLogDeriv z‖ ≤ Czeta * (1 + ‖z.im‖) ^ 0 := by
    have hpow : (1 + ‖z.im‖) ^ 0 = (1 : ℝ) := pow_zero _
    have hmul : Czeta * (1 + ‖z.im‖) ^ 0 = Czeta :=
      Eq.trans (congrArg (fun q : ℝ => Czeta * q) hpow) (mul_one Czeta)
    exact Eq.trans (hzeta x hx) hmul.symm
  have hgamma' : ‖deriv (fun ξ : ℂ => (Complex.Gammaℝ ξ)⁻¹) z /
      (Complex.Gammaℝ z)⁻¹‖ ≤ Cgamma * (1 + ‖z.im‖) ^ 0 := by
    have hpow : (1 + ‖z.im‖) ^ 0 = (1 : ℝ) := pow_zero _
    have hmul : Cgamma * (1 + ‖z.im‖) ^ 0 = Cgamma :=
      Eq.trans (congrArg (fun q : ℝ => Cgamma * q) hpow) (mul_one Cgamma)
    exact Eq.trans (hgamma x hx) hmul.symm
  have hbound := completedZetaNegLogDeriv_norm_bound_of_pointwise_raw_factor_bounds_owner
    E 0 Czeta Cgamma z hz hzeta' hgamma'
  exact hbound.trans_eq
    (Eq.trans
      (congrArg (fun q : ℝ => (Czeta + Cgamma) * q)
        (pow_zero (1 + ‖z.im‖)))
      (mul_one (Czeta + Cgamma)))

theorem zetaCompletedExplicitFormulaAutocorrelationScheduledBottomPath_completedLogDeriv_uniform_bound_owner
    (f : ZetaAdmissibleFunction) (u : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : ℝ, x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
        ‖completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x)‖ ≤ B := by
  obtain ⟨Czeta, hCzeta, hzeta⟩ :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledBottomPath_zetaSideLogDeriv_uniform_bound_owner
      f u
  obtain ⟨Cgamma, hCgamma, hgamma⟩ :=
    ExplicitFormulaCofinalHeightSchedule.bottomPath_inverseGamma_logDeriv_uniform_bound
      (zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f) u
  refine ⟨Czeta + Cgamma, add_nonneg hCzeta hCgamma, ?_⟩
  intro x hx
  let z := zetaCompletedExplicitFormulaBottomPath
    ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
      ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x
  let E := zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f
  have hz : z ∈ E.carrier :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_bottom_mem f u x hx
  have hzeta' : ‖zetaSideNegLogDeriv z‖ ≤ Czeta * (1 + ‖z.im‖) ^ 0 := by
    have hpow : (1 + ‖z.im‖) ^ 0 = (1 : ℝ) := pow_zero _
    have hmul : Czeta * (1 + ‖z.im‖) ^ 0 = Czeta :=
      Eq.trans (congrArg (fun q : ℝ => Czeta * q) hpow) (mul_one Czeta)
    exact Eq.trans (hzeta x hx) hmul.symm
  have hgamma' : ‖deriv (fun ξ : ℂ => (Complex.Gammaℝ ξ)⁻¹) z /
      (Complex.Gammaℝ z)⁻¹‖ ≤ Cgamma * (1 + ‖z.im‖) ^ 0 := by
    have hpow : (1 + ‖z.im‖) ^ 0 = (1 : ℝ) := pow_zero _
    have hmul : Cgamma * (1 + ‖z.im‖) ^ 0 = Cgamma :=
      Eq.trans (congrArg (fun q : ℝ => Cgamma * q) hpow) (mul_one Cgamma)
    exact Eq.trans (hgamma x hx) hmul.symm
  have hbound := completedZetaNegLogDeriv_norm_bound_of_pointwise_raw_factor_bounds_owner
    E 0 Czeta Cgamma z hz hzeta' hgamma'
  exact hbound.trans_eq
    (Eq.trans
      (congrArg (fun q : ℝ => (Czeta + Cgamma) * q)
        (pow_zero (1 + ‖z.im‖)))
      (mul_one (Czeta + Cgamma)))

theorem zetaCompletedExplicitFormulaAutocorrelationScheduledFiniteHeightHorizontalLogDerivControl_owner
    (f : ZetaAdmissibleFunction) (u : ℝ) :
    ∃ BTop BBottom : ℝ,
      0 ≤ BTop ∧ 0 ≤ BBottom ∧
      (∀ x : ℝ, x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
        ‖completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x)‖ ≤ BTop) ∧
      (∀ x : ℝ, x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
        ‖completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x)‖ ≤ BBottom) := by
  obtain ⟨BTop, hBTop, hTop⟩ :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledTopPath_completedLogDeriv_uniform_bound_owner
      f u
  obtain ⟨BBottom, hBBottom, hBottom⟩ :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledBottomPath_completedLogDeriv_uniform_bound_owner
      f u
  exact ⟨BTop, BBottom, hBTop, hBBottom, hTop, hBottom⟩

/- Collapse the two finite-height horizontal bounds to the single constant
   consumed by the contour-level polynomial package. -/
theorem zetaCompletedExplicitFormulaAutocorrelationScheduledFiniteHeightHorizontalLogDerivControl_common_owner
    (f : ZetaAdmissibleFunction) (u : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧
      (∀ x : ℝ, x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
        ‖completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x‖ ≤ B) ∧
      (∀ x : ℝ, x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
        ‖completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x‖ ≤ B) := by
  obtain ⟨BTop, BBottom, hBTop, hBBottom, hTop, hBottom⟩ :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledFiniteHeightHorizontalLogDerivControl_owner
      f u
  refine ⟨max BTop BBottom, le_max hBTop hBBottom, ?_, ?_⟩
  · intro x hx
    exact (hTop x hx).trans (le_max_left BTop BBottom)
  · intro x hx
    exact (hBottom x hx).trans (le_max_right BTop BBottom)

theorem zetaCompletedExplicitFormulaAutocorrelationScheduledTopPath_completedLogDeriv_bound_of_uniform_factor_bounds_owner
    (f : ZetaAdmissibleFunction) (u : ℝ) (N : ℕ) (Czeta Cgamma : ℝ)
    (hzeta : ∀ x : ℝ, x ∈ Set.uIcc
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
      (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      ‖zetaSideNegLogDeriv
        (zetaCompletedExplicitFormulaTopPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x)‖ ≤
        Czeta * (1 + ‖((zetaCompletedExplicitFormulaTopPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x).im‖) ^ N)
    (hgamma : ∀ x : ℝ, x ∈ Set.uIcc
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
      (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      ‖deriv (fun ξ : ℂ => (Complex.Gammaℝ ξ)⁻¹)
          (zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x) /
        (Complex.Gammaℝ
          (zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x))⁻¹‖ ≤
        Cgamma * (1 + ‖((zetaCompletedExplicitFormulaTopPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x).im‖) ^ N) :
    ∀ x : ℝ, x ∈ Set.uIcc
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
      (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
      ‖completedZetaNegLogDeriv
        (zetaCompletedExplicitFormulaTopPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x)‖ ≤
        (Czeta + Cgamma) * (1 + ‖((zetaCompletedExplicitFormulaTopPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x).im‖) ^ N := by
  intro x hx
  let z := zetaCompletedExplicitFormulaTopPath
    ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
      ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x
  let E := zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f
  have hz : z ∈ E.carrier :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_top_mem f u x hx
  exact completedZetaNegLogDeriv_norm_bound_of_pointwise_raw_factor_bounds_owner
    E N Czeta Cgamma z hz (hzeta x hx) (hgamma x hx)

theorem zetaCompletedExplicitFormulaAutocorrelationScheduledTopPath_zetaSideLogDeriv_continuousAt_owner
    (f : ZetaAdmissibleFunction) (u x : ℝ)
    (hx : x ∈ Set.uIcc
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
      (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    ContinuousAt zetaSideNegLogDeriv
      (zetaCompletedExplicitFormulaTopPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
          ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x) := by
  let z := zetaCompletedExplicitFormulaTopPath
    ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
      ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x
  have hzmem :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_top_mem
      f u x hx
  have hdiff : DifferentiableAt ℂ zetaSideFactor z :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_zetaSideFactor_differentiableAt_owner
      f hzmem
  have hne : zetaSideFactor z ≠ 0 := by
    exact zetaSideFactor_ne_zero
      ((zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).zeta_ne_zero z hzmem)
      ((zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).gamma_ne_zero z hzmem)
  have hlocal := zetaSideNegLogDeriv_continuousAt_of_analyticAt_owner
    hdiff.analyticAt hne
  exact hlocal

theorem zetaCompletedExplicitFormulaAutocorrelationScheduledTopPath_zetaSideLogDeriv_continuousOn_owner
    (f : ZetaAdmissibleFunction) (u : ℝ) :
    ContinuousOn
      (fun x : ℝ => zetaSideNegLogDeriv
        (zetaCompletedExplicitFormulaTopPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x))
      (Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) := by
  intro x hx
  exact
    (zetaCompletedExplicitFormulaAutocorrelationScheduledTopPath_zetaSideLogDeriv_continuousAt_owner
      f u x hx).continuousWithinAt

theorem zetaCompletedExplicitFormulaAutocorrelationScheduledTopPath_zetaSideLogDeriv_uniform_bound_owner
    (f : ZetaAdmissibleFunction) (u : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : ℝ, x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
        ‖zetaSideNegLogDeriv
          (zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x)‖ ≤ B := by
  let s : Set ℝ := Set.uIcc
    (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
    (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)
  obtain ⟨B, hB, hbound⟩ :=
    exists_norm_upper_bound_of_isCompact_of_continuousOn
      isCompact_uIcc
      (zetaCompletedExplicitFormulaAutocorrelationScheduledTopPath_zetaSideLogDeriv_continuousOn_owner
        f u)
  exact ⟨B, hB, hbound⟩

theorem zetaCompletedExplicitFormulaAutocorrelationScheduledBottomPath_zetaSideLogDeriv_continuousAt_owner
    (f : ZetaAdmissibleFunction) (u x : ℝ)
    (hx : x ∈ Set.uIcc
      (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
      (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    ContinuousAt zetaSideNegLogDeriv
      (zetaCompletedExplicitFormulaBottomPath
        ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
          ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x) := by
  let z := zetaCompletedExplicitFormulaBottomPath
    ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
      ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x
  have hzmem :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_bottom_mem
      f u x hx
  have hdiff : DifferentiableAt ℂ zetaSideFactor z := by
    have hz0 :=
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).ne_zero z hzmem
    have hz1 :=
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).ne_one z hzmem
    have hgamma :=
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).gamma_ne_zero z hzmem
    change DifferentiableAt ℂ
      (fun w : ℂ => completedRiemannZeta w * (Complex.Gammaℝ w)⁻¹) z
    exact differentiableAt_completedZeta_factorized hz0 hz1 hgamma
  have hne : zetaSideFactor z ≠ 0 := by
    exact zetaSideFactor_ne_zero
      ((zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).zeta_ne_zero z hzmem)
      ((zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).gamma_ne_zero z hzmem)
  exact zetaSideNegLogDeriv_continuousAt_of_analyticAt_owner
    hdiff.analyticAt hne

theorem zetaCompletedExplicitFormulaAutocorrelationScheduledBottomPath_zetaSideLogDeriv_continuousOn_owner
    (f : ZetaAdmissibleFunction) (u : ℝ) :
    ContinuousOn
      (fun x : ℝ => zetaSideNegLogDeriv
        (zetaCompletedExplicitFormulaBottomPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x))
      (Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) := by
  intro x hx
  exact
    (zetaCompletedExplicitFormulaAutocorrelationScheduledBottomPath_zetaSideLogDeriv_continuousAt_owner
      f u x hx).continuousWithinAt

theorem zetaCompletedExplicitFormulaAutocorrelationScheduledBottomPath_zetaSideLogDeriv_uniform_bound_owner
    (f : ZetaAdmissibleFunction) (u : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ x : ℝ, x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) →
        ‖zetaSideNegLogDeriv
          (zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u)) x)‖ ≤ B := by
  obtain ⟨B, hB, hbound⟩ :=
    exists_norm_upper_bound_of_isCompact_of_continuousOn
      isCompact_uIcc
      (zetaCompletedExplicitFormulaAutocorrelationScheduledBottomPath_zetaSideLogDeriv_continuousOn_owner
        f u)
  exact ⟨B, hB, hbound⟩

theorem zetaSideFactor_diffContOnCl_of_closedBall_regular
    (z : ℂ) (R : ℝ)
    (hregular : ∀ w : ℂ, w ∈ Metric.closedBall z R →
      w ≠ 0 ∧ w ≠ 1 ∧ Complex.Gammaℝ w ≠ 0) :
    DiffContOnCl ℂ zetaSideFactor (Metric.ball z R) := by
  apply DifferentiableOn.diffContOnCl
  intro w hw
  have hclosed : w ∈ Metric.closedBall z R :=
    closure_ball_subset_closedBall hw
  have hpoints := hregular w hclosed
  change DifferentiableAt ℂ
    (fun v : ℂ => completedRiemannZeta v * (Complex.Gammaℝ v)⁻¹) w
  exact differentiableAt_completedZeta_factorized
    hpoints.1
    hpoints.2.1
    hpoints.2.2

theorem inverseGamma_diffContOnCl_on_ball_owner
    (z : ℂ) (R : ℝ) :
    DiffContOnCl ℂ (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) (Metric.ball z R) :=
  Differentiable.diffContOnCl Complex.differentiable_Gammaℝ_inv

theorem inverseGamma_ne_zero_on_closedBall_of_center_re_gt_radius_owner
    (z : ℂ) (R : ℝ) (hR : R < z.re) :
    ∀ w : ℂ, w ∈ Metric.closedBall z R →
      (Complex.Gammaℝ w)⁻¹ ≠ 0 := by
  intro w hw
  have hdist : ‖w - z‖ ≤ R := by
    calc
      ‖w - z‖ = dist w z := (dist_eq_norm w z).symm
      _ = dist z w := dist_comm w z
      _ ≤ R := Metric.mem_closedBall.mp hw
  have hreal_norm : ‖(w - z).re‖ ≤ R := by
    exact (RCLike.norm_re_le_norm (w - z)).trans hdist
  have hreal_lower : -R ≤ (w - z).re :=
    neg_le_of_abs_le hreal_norm
  have hw_re_pos : 0 < w.re := by
    have hcenter : z.re - R ≤ w.re := by
      calc
        z.re - R = z.re + (-R) := sub_eq_add_neg z.re R
        _ ≤ z.re + (w - z).re := add_le_add_left hreal_lower z.re
        _ = w.re := by
          exact add_sub_cancel_left w.re z.re
    exact lt_of_lt_of_le (sub_pos.mpr hR) hcenter
  exact inv_ne_zero (Complex.Gammaℝ_ne_zero_of_re_pos w hw_re_pos)

theorem regularity_of_not_explicitFormulaContourSingularPoint_owner
    {w : ℂ}
    (hregular : ¬ explicitFormulaContourSingularPoint w) :
    w ≠ 0 ∧ w ≠ 1 ∧ Complex.Gammaℝ w ≠ 0 :=
  ⟨explicitFormulaContourSingularPoint.ne_zero_of_not hregular,
    explicitFormulaContourSingularPoint.ne_one_of_not hregular,
    explicitFormulaContourSingularPoint.gamma_ne_zero_of_not hregular⟩

theorem zetaSideFactor_diffContOnCl_of_closedBall_nonsingular
    (z : ℂ) (R : ℝ)
    (hnonsingular : ∀ w : ℂ, w ∈ Metric.closedBall z R →
      ¬ explicitFormulaContourSingularPoint w) :
    DiffContOnCl ℂ zetaSideFactor (Metric.ball z R) :=
  zetaSideFactor_diffContOnCl_of_closedBall_regular
    z R
    (fun w hw =>
      regularity_of_not_explicitFormulaContourSingularPoint_owner
        (hnonsingular w hw))

theorem closedBall_nonsingular_of_singular_separation
    (z : ℂ) (R δ : ℝ)
    (hseparated : ∀ q : ℂ,
      explicitFormulaContourSingularPoint q → δ ≤ ‖z - q‖)
    (hR : R < δ) :
    ∀ w : ℂ, w ∈ Metric.closedBall z R →
      ¬ explicitFormulaContourSingularPoint w := by
  intro w hw hsing
  have hnorm : ‖z - w‖ ≤ R := by
    calc
      ‖z - w‖ = dist z w := (dist_eq_norm z w).symm
      _ = dist w z := dist_comm z w
      _ ≤ R := Metric.mem_closedBall.mp hw
  have hlt : ‖z - w‖ < δ := hnorm.trans_lt hR
  exact (not_lt_of_ge (hseparated w hsing)) hlt

theorem completedRiemannZeta_positive_lower_bound_on_closedBall_of_singular_separation_owner
    (z : ℂ) (R δ : ℝ)
    (hseparated : ∀ q : ℂ,
      explicitFormulaContourSingularPoint q → δ ≤ ‖z - q‖)
    (hR : R < δ) (hR_pos : 0 < R) :
    ∃ m : ℝ, 0 < m ∧
      ∀ w : ℂ, w ∈ Metric.closedBall z R →
        m ≤ ‖completedRiemannZeta w‖ := by
  have hnonsingular :=
    closedBall_nonsingular_of_singular_separation z R δ hseparated hR
  have hregular : ∀ w : ℂ, w ∈ Metric.closedBall z R →
      completedRiemannZeta w ≠ 0 := by
    intro w hw hzero
    exact (hnonsingular w hw)
      (Or.inr (Or.inr (Or.inr (Or.inr ⟨
        explicitFormulaContourSingularPoint.ne_zero_of_not
          (hnonsingular w hw),
        explicitFormulaContourSingularPoint.ne_one_of_not
          (hnonsingular w hw),
        hzero⟩))))
  have hzero : ∀ w : ℂ, w ∈ Metric.closedBall z R → w ≠ 0 := by
    intro w hw hz
    exact (hnonsingular w hw) (Or.inl hz)
  have hone : ∀ w : ℂ, w ∈ Metric.closedBall z R → w ≠ 1 := by
    intro w hw hz
    exact (hnonsingular w hw) (Or.inr (Or.inl hz))
  exact completedRiemannZeta_positive_lower_bound_on_closedBall_of_regular_owner
    z R hR_pos hregular hzero hone

theorem singularSeparation_halfRadius
    (z : ℂ)
    (hseparation : ∃ δ : ℝ, 0 < δ ∧
      ∀ q : ℂ, explicitFormulaContourSingularPoint q → δ ≤ ‖z - q‖) :
    ∃ R δ : ℝ,
      0 < R ∧
      0 < δ ∧
      R < δ ∧
      (∀ q : ℂ,
        explicitFormulaContourSingularPoint q → δ ≤ ‖z - q‖) ∧
      (∀ w : ℂ, w ∈ Metric.closedBall z R →
        ¬ explicitFormulaContourSingularPoint w) := by
  obtain ⟨δ, hδ, hseparated⟩ := hseparation
  let R : ℝ := δ / 2
  have hR_pos : 0 < R := by
    exact div_pos hδ (by exact zero_lt_two)
  have hR_lt : R < δ := by
    have hdouble : δ < 2 * δ := by
      calc
        δ = δ + 0 := (add_zero δ).symm
        _ < δ + δ := add_lt_add_left hδ δ
        _ = 2 * δ := (two_mul δ).symm
    exact (div_lt_iff₀ (by exact zero_lt_two)).mpr
      hdouble
  exact ⟨R, δ, hR_pos, hδ, hR_lt, hseparated,
    closedBall_nonsingular_of_singular_separation z R δ hseparated hR_lt⟩

theorem singularSeparation_halfRadius_zetaSide_regular
    (z : ℂ)
    (hseparation : ∃ δ : ℝ, 0 < δ ∧
      ∀ q : ℂ, explicitFormulaContourSingularPoint q → δ ≤ ‖z - q‖) :
    ∃ R : ℝ,
      0 < R ∧
      DiffContOnCl ℂ zetaSideFactor (Metric.ball z R) ∧
      (∀ w : ℂ, w ∈ Metric.closedBall z R → zetaSideFactor w ≠ 0) := by
  obtain ⟨R, δ, hR, hδ, hRδ, hseparated, _hnonsingular⟩ :=
    singularSeparation_halfRadius z hseparation
  exact ⟨R, hR,
    zetaSideFactor_diffContOnCl_of_closedBall_nonsingular
      z R hnonsingular,
    zetaSideFactor_ne_zero_on_closedBall_of_singular_separation
      z R δ hseparated hRδ⟩

theorem singularSeparation_halfRadius_inverseGamma_regular
    (z : ℂ)
    (hseparation : ∃ δ : ℝ, 0 < δ ∧
      ∀ q : ℂ, explicitFormulaContourSingularPoint q → δ ≤ ‖z - q‖) :
    ∃ R : ℝ,
      0 < R ∧
      DiffContOnCl ℂ (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) (Metric.ball z R) ∧
      (∀ w : ℂ, w ∈ Metric.closedBall z R →
        (Complex.Gammaℝ w)⁻¹ ≠ 0) := by
  obtain ⟨R, δ, hR, hδ, hRδ, hseparated, hnonsingular⟩ :=
    singularSeparation_halfRadius z hseparation
  exact ⟨R, hR,
    inverseGamma_diffContOnCl_on_ball_owner z R,
    inverseGamma_ne_zero_on_closedBall_of_singular_separation
      z R δ hseparated hRδ⟩

theorem completedRiemannZeta_positive_lower_bound_of_pointwise_singular_separation_owner
    (z : ℂ)
    (hseparation : ∃ δ : ℝ, 0 < δ ∧
      ∀ q : ℂ, explicitFormulaContourSingularPoint q → δ ≤ ‖z - q‖) :
    ∃ R m : ℝ, 0 < R ∧ 0 < m ∧
      (∀ w : ℂ, w ∈ Metric.closedBall z R →
        m ≤ ‖completedRiemannZeta w‖) := by
  obtain ⟨R, δ, hR, hδ, hRδ, hseparated, _hnonsingular⟩ :=
    singularSeparation_halfRadius z hseparation
  obtain ⟨m, hm, hm_bound⟩ :=
    completedRiemannZeta_positive_lower_bound_on_closedBall_of_singular_separation_owner
      z R δ hseparated hRδ hR
  exact ⟨R, m, hR, hm, hm_bound⟩

theorem zetaSideFactor_diffContOnCl_of_singular_separation
    (z : ℂ) (R δ : ℝ)
    (hseparated : ∀ q : ℂ,
      explicitFormulaContourSingularPoint q → δ ≤ ‖z - q‖)
    (hR : R < δ) :
    DiffContOnCl ℂ zetaSideFactor (Metric.ball z R) :=
  zetaSideFactor_diffContOnCl_of_closedBall_nonsingular
    z R
    (closedBall_nonsingular_of_singular_separation z R δ hseparated hR)

theorem zetaSideFactor_ne_zero_on_closedBall_of_singular_separation
    (z : ℂ) (R δ : ℝ)
    (hseparated : ∀ q : ℂ,
      explicitFormulaContourSingularPoint q → δ ≤ ‖z - q‖)
    (hR : R < δ) :
    ∀ w : ℂ, w ∈ Metric.closedBall z R → zetaSideFactor w ≠ 0 := by
  apply zetaSideFactor_ne_zero_of_component_nonzero_owner
    (fun w : ℂ => w ∈ Metric.closedBall z R)
  · intro w hw
    exact explicitFormulaContourSingularPoint.completedRiemannZeta_ne_zero_of_not
      (closedBall_nonsingular_of_singular_separation z R δ hseparated hR w hw)
  · intro w hw
    exact inv_ne_zero.mpr
      (explicitFormulaContourSingularPoint.gamma_ne_zero_of_not
        (closedBall_nonsingular_of_singular_separation z R δ hseparated hR w hw))

theorem zetaSideFactor_positive_lower_bound_on_closedBall
    (z : ℂ) (R : ℝ)
    (hcontinuous : ContinuousOn zetaSideFactor (Metric.closedBall z R))
    (hne : ∀ w : ℂ, w ∈ Metric.closedBall z R → zetaSideFactor w ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ w : ℂ, w ∈ Metric.closedBall z R → δ ≤ ‖zetaSideFactor w‖ :=
  let hcompact : IsCompact (Metric.closedBall z R) := isCompact_closedBall
  obtain ⟨w₀, hw₀, hw₀_min⟩ :=
    hcompact.exists_isMinOn ⟨z, Metric.mem_closedBall_self⟩ hcontinuous.norm
  have hw₀_pos : 0 < ‖zetaSideFactor w₀‖ :=
    norm_pos_iff.mpr (hne w₀ hw₀)
  refine ⟨‖zetaSideFactor w₀‖, hw₀_pos, ?_⟩
  intro w hw
  exact hw₀_min hw

theorem zetaSideFactor_positive_lower_bound_on_closedBall_of_singular_separation
    (z : ℂ) (R δ : ℝ)
    (hseparated : ∀ q : ℂ,
      explicitFormulaContourSingularPoint q → δ ≤ ‖z - q‖)
    (hR : R < δ)
    (hcontinuous : ContinuousOn zetaSideFactor (Metric.closedBall z R)) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ w : ℂ, w ∈ Metric.closedBall z R → ε ≤ ‖zetaSideFactor w‖ :=
  zetaSideFactor_positive_lower_bound_on_closedBall
    z R
    hcontinuous
    (zetaSideFactor_ne_zero_on_closedBall_of_singular_separation
      z R δ hseparated hR)

theorem closedBall_continuousOn_of_diffContOnCl
    (z : ℂ) (R : ℝ) (hR : 0 < R)
    (hDiff : DiffContOnCl ℂ zetaSideFactor (Metric.ball z R)) :
    ContinuousOn zetaSideFactor (Metric.closedBall z R) := by
  have hcontinuous_closure :
      ContinuousOn zetaSideFactor (closure (Metric.ball z R)) :=
    hDiff.continuousOn
  exact Eq.subst
    (motive := fun s : Set ℂ => ContinuousOn zetaSideFactor s)
    (closure_ball z hR.ne')
    hcontinuous_closure

theorem zetaSideFactor_positive_lower_bound_on_closedBall_of_diffContOnCl
    (z : ℂ) (R : ℝ) (hR : 0 < R)
    (hDiff : DiffContOnCl ℂ zetaSideFactor (Metric.ball z R))
    (hne : ∀ w : ℂ, w ∈ Metric.closedBall z R → zetaSideFactor w ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ w : ℂ, w ∈ Metric.closedBall z R → ε ≤ ‖zetaSideFactor w‖ := by
  have hcontinuous_closedBall :=
    closedBall_continuousOn_of_diffContOnCl z R hR hDiff
  exact zetaSideFactor_positive_lower_bound_on_closedBall
    z R hcontinuous_closedBall hne

/- Pair the two compact zeta-side carriers at the owner level.  The two
separation radii may differ; taking the minimum only after the individual
compactness bounds have been proved preserves the exact hypotheses needed by
each face. -/
theorem zetaSideFactor_positive_lower_bound_on_pair_of_singular_separation
    (zTop zBottom : ℂ) (R δTop δBottom : ℝ)
    (hseparatedTop : ∀ q : ℂ,
      explicitFormulaContourSingularPoint q → δTop ≤ ‖zTop - q‖)
    (hseparatedBottom : ∀ q : ℂ,
      explicitFormulaContourSingularPoint q → δBottom ≤ ‖zBottom - q‖)
    (hRTop : R < δTop) (hRBottom : R < δBottom)
    (hcontinuousTop : ContinuousOn zetaSideFactor (Metric.closedBall zTop R))
    (hcontinuousBottom :
      ContinuousOn zetaSideFactor (Metric.closedBall zBottom R)) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ w : ℂ, w ∈ Metric.closedBall zTop R →
        ε ≤ ‖zetaSideFactor w‖) ∧
      (∀ w : ℂ, w ∈ Metric.closedBall zBottom R →
        ε ≤ ‖zetaSideFactor w‖) := by
  rcases zetaSideFactor_positive_lower_bound_on_closedBall_of_singular_separation
      zTop R δTop hseparatedTop hRTop hcontinuousTop with
    ⟨εTop, hεTop, hTop⟩
  rcases zetaSideFactor_positive_lower_bound_on_closedBall_of_singular_separation
      zBottom R δBottom hseparatedBottom hRBottom hcontinuousBottom with
    ⟨εBottom, hεBottom, hBottom⟩
  refine ⟨min εTop εBottom, ?_, ?_, ?_⟩
  · exact lt_min hεTop hεBottom
  · intro w hw
    exact (min_le_left εTop εBottom).trans (hTop w hw)
  · intro w hw
    exact (min_le_right εTop εBottom).trans (hBottom w hw)

theorem inverseGamma_ne_zero_on_closedBall_of_singular_separation
    (z : ℂ) (R δ : ℝ)
    (hseparated : ∀ q : ℂ,
      explicitFormulaContourSingularPoint q → δ ≤ ‖z - q‖)
    (hR : R < δ) :
    ∀ w : ℂ, w ∈ Metric.closedBall z R →
      (Complex.Gammaℝ w)⁻¹ ≠ 0 := by
  intro w hw
  have hnonsingular :=
    closedBall_nonsingular_of_singular_separation z R δ hseparated hR w hw
  have hgamma : Complex.Gammaℝ w ≠ 0 :=
    explicitFormulaContourSingularPoint.gamma_ne_zero_of_not hnonsingular
  exact inv_ne_zero hgamma

theorem inverseGamma_norm_pos_of_ne_zero_owner
    {z : ℂ} (hz : (Complex.Gammaℝ z)⁻¹ ≠ 0) :
    0 < ‖(Complex.Gammaℝ z)⁻¹‖ :=
  norm_pos_iff.mpr hz

theorem inverseGamma_positive_lower_bound_on_closedBall_of_singular_separation
    (z : ℂ) (R δ : ℝ)
    (hseparated : ∀ q : ℂ,
      explicitFormulaContourSingularPoint q → δ ≤ ‖z - q‖)
    (hR : R < δ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ w : ℂ, w ∈ Metric.closedBall z R →
        ε ≤ ‖(Complex.Gammaℝ w)⁻¹‖ := by
  let hcompact : IsCompact (Metric.closedBall z R) := isCompact_closedBall
  obtain ⟨w₀, hw₀, hw₀_min⟩ :=
    hcompact.exists_isMinOn ⟨z, Metric.mem_closedBall_self⟩
      Complex.differentiable_Gammaℝ_inv.continuous.continuousOn
  have hw₀_inverseGamma : (Complex.Gammaℝ w₀)⁻¹ ≠ 0 :=
    inverseGamma_ne_zero_on_closedBall_of_singular_separation
      z R δ hseparated hR w₀ hw₀
  have hw₀_pos : 0 < ‖(Complex.Gammaℝ w₀)⁻¹‖ :=
    norm_pos_iff.mpr hw₀_inverseGamma
  refine ⟨‖(Complex.Gammaℝ w₀)⁻¹‖, hw₀_pos, ?_⟩
  intro w hw
  exact hw₀_min hw

theorem inverseGamma_positive_lower_bound_on_closedBall_of_diffContOnCl
    (z : ℂ) (R : ℝ) (hR : 0 < R)
    (hDiff : DiffContOnCl ℂ
      (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) (Metric.ball z R))
    (hne : ∀ w : ℂ, w ∈ Metric.closedBall z R →
      (Complex.Gammaℝ w)⁻¹ ≠ 0) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ w : ℂ, w ∈ Metric.closedBall z R →
        ε ≤ ‖(Complex.Gammaℝ w)⁻¹‖ := by
  have hcontinuous_closure :
      ContinuousOn (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (closure (Metric.ball z R)) :=
    hDiff.continuousOn
  have hcontinuous_closedBall :
      ContinuousOn (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (Metric.closedBall z R) :=
    Eq.subst
      (motive := fun s : Set ℂ =>
        ContinuousOn (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) s)
      (closure_ball z hR.ne')
      hcontinuous_closure
  let hcompact : IsCompact (Metric.closedBall z R) := isCompact_closedBall
  obtain ⟨w₀, hw₀, hw₀_min⟩ :=
    hcompact.exists_isMinOn ⟨z, Metric.mem_closedBall_self⟩
      hcontinuous_closedBall.norm
  have hw₀_pos : 0 < ‖(Complex.Gammaℝ w₀)⁻¹‖ :=
    inverseGamma_norm_pos_of_ne_zero_owner (hne w₀ hw₀)
  refine ⟨‖(Complex.Gammaℝ w₀)⁻¹‖, hw₀_pos, ?_⟩
  intro w hw
  exact hw₀_min hw

theorem inverseGamma_positive_lower_bound_on_closedBall_of_center_re_gt_radius_owner
    (z : ℂ) (R : ℝ) (hR_pos : 0 < R) (hR : R < z.re) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ w : ℂ, w ∈ Metric.closedBall z R →
        ε ≤ ‖(Complex.Gammaℝ w)⁻¹‖ :=
  inverseGamma_positive_lower_bound_on_closedBall_of_diffContOnCl
    z R hR_pos
    (inverseGamma_diffContOnCl_on_ball_owner z R)
    (inverseGamma_ne_zero_on_closedBall_of_center_re_gt_radius_owner z R hR)

/- The local carrier hypotheses have a direct Cauchy consequence.  This is the
   owner bridge used when a finite scheduled carrier is assembled into
   inverse-Gamma bound data. -/
theorem inverseGamma_cauchy_log_derivative_bound_on_closedBall_owner
    (z : ℂ) (R : ℝ) (hR_pos : 0 < R)
    (hne : ∀ w : ℂ, w ∈ Metric.closedBall z R →
      (Complex.Gammaℝ w)⁻¹ ≠ 0) :
    ∃ B : ℝ, 0 < B ∧
      ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
          (Complex.Gammaℝ z)⁻¹‖ ≤ B := by
  exact inverseGamma_cauchy_log_derivative_bound_of_closedBall_nonzero
    R hR_pos
    (inverseGamma_diffContOnCl_on_ball_owner z R)
    hne

theorem inverseGamma_cauchy_log_derivative_bound_of_singular_separation_owner
    (z : ℂ) (R δ : ℝ) (hR_pos : 0 < R)
    (hseparated : ∀ q : ℂ,
      explicitFormulaContourSingularPoint q → δ ≤ ‖z - q‖)
    (hR : R < δ) :
    ∃ B : ℝ, 0 < B ∧
      ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
          (Complex.Gammaℝ z)⁻¹‖ ≤ B := by
  exact inverseGamma_cauchy_log_derivative_bound_on_closedBall_owner
    z R hR_pos
    (inverseGamma_ne_zero_on_closedBall_of_singular_separation
      z R δ hseparated hR)

theorem inverseGamma_positive_lower_bound_on_topPath_ball_of_radius_lt_c_owner
    (r : ExplicitFormulaRectangle) (x R : ℝ)
    (hcx : r.c ≤ x) (hR_pos : 0 < R) (hR : R < r.c) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ w : ℂ, w ∈ Metric.closedBall
          (zetaCompletedExplicitFormulaTopPath r x) R →
        ε ≤ ‖(Complex.Gammaℝ w)⁻¹‖ := by
  have hcenter : R < (zetaCompletedExplicitFormulaTopPath r x).re := by
    calc
      R < r.c := hR
      _ ≤ x := hcx
      _ = (zetaCompletedExplicitFormulaTopPath r x).re :=
        (zetaCompletedExplicitFormulaTopPath_re_eq r x).symm
  exact inverseGamma_positive_lower_bound_on_closedBall_of_center_re_gt_radius_owner
    (zetaCompletedExplicitFormulaTopPath r x) R hR_pos hcenter

theorem zetaSideFactor_positive_lower_bound_on_topPath_ball_of_singular_separation_owner
    (r : ExplicitFormulaRectangle) (x R δ : ℝ)
    (hseparated : ∀ q : ℂ,
      explicitFormulaContourSingularPoint q →
        δ ≤ ‖zetaCompletedExplicitFormulaTopPath r x - q‖)
    (hR_pos : 0 < R) (hR : R < δ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ w : ℂ, w ∈ Metric.closedBall
          (zetaCompletedExplicitFormulaTopPath r x) R →
        ε ≤ ‖zetaSideFactor w‖ := by
  have hdiff : DiffContOnCl ℂ zetaSideFactor
      (Metric.ball (zetaCompletedExplicitFormulaTopPath r x) R) :=
    zetaSideFactor_diffContOnCl_of_closedBall_nonsingular
      (zetaCompletedExplicitFormulaTopPath r x) R δ hseparated hR
  have hcontinuous :=
    closedBall_continuousOn_of_diffContOnCl
      (zetaCompletedExplicitFormulaTopPath r x) R hR_pos hdiff
  exact zetaSideFactor_positive_lower_bound_on_closedBall_of_singular_separation
    (zetaCompletedExplicitFormulaTopPath r x) R δ hseparated hR hcontinuous

theorem inverseGamma_positive_lower_bound_on_bottomPath_ball_of_radius_lt_c_owner
    (r : ExplicitFormulaRectangle) (x R : ℝ)
    (hcx : r.c ≤ x) (hR_pos : 0 < R) (hR : R < r.c) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ w : ℂ, w ∈ Metric.closedBall
          (zetaCompletedExplicitFormulaBottomPath r x) R →
        ε ≤ ‖(Complex.Gammaℝ w)⁻¹‖ := by
  have hcenter : R < (zetaCompletedExplicitFormulaBottomPath r x).re := by
    calc
      R < r.c := hR
      _ ≤ x := hcx
      _ = (zetaCompletedExplicitFormulaBottomPath r x).re :=
        (zetaCompletedExplicitFormulaBottomPath_re_eq r x).symm
  exact inverseGamma_positive_lower_bound_on_closedBall_of_center_re_gt_radius_owner
    (zetaCompletedExplicitFormulaBottomPath r x) R hR_pos hcenter

theorem zetaSideFactor_positive_lower_bound_on_bottomPath_ball_of_singular_separation_owner
    (r : ExplicitFormulaRectangle) (x R δ : ℝ)
    (hseparated : ∀ q : ℂ,
      explicitFormulaContourSingularPoint q →
        δ ≤ ‖zetaCompletedExplicitFormulaBottomPath r x - q‖)
    (hR_pos : 0 < R) (hR : R < δ) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ w : ℂ, w ∈ Metric.closedBall
          (zetaCompletedExplicitFormulaBottomPath r x) R →
        ε ≤ ‖zetaSideFactor w‖ := by
  have hdiff : DiffContOnCl ℂ zetaSideFactor
      (Metric.ball (zetaCompletedExplicitFormulaBottomPath r x) R) :=
    zetaSideFactor_diffContOnCl_of_closedBall_nonsingular
      (zetaCompletedExplicitFormulaBottomPath r x) R δ hseparated hR
  have hcontinuous :=
    closedBall_continuousOn_of_diffContOnCl
      (zetaCompletedExplicitFormulaBottomPath r x) R hR_pos hdiff
  exact zetaSideFactor_positive_lower_bound_on_closedBall_of_singular_separation
    (zetaCompletedExplicitFormulaBottomPath r x) R δ hseparated hR hcontinuous

theorem zetaSideFactor_positive_lower_bound_on_horizontal_pair_balls_of_singular_separation_owner
    (r : ExplicitFormulaRectangle) (x R δTop δBottom : ℝ)
    (hseparatedTop : ∀ q : ℂ,
      explicitFormulaContourSingularPoint q →
        δTop ≤ ‖zetaCompletedExplicitFormulaTopPath r x - q‖)
    (hseparatedBottom : ∀ q : ℂ,
      explicitFormulaContourSingularPoint q →
        δBottom ≤ ‖zetaCompletedExplicitFormulaBottomPath r x - q‖)
    (hR_pos : 0 < R) (hRTop : R < δTop) (hRBottom : R < δBottom) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ w : ℂ, w ∈ Metric.closedBall
          (zetaCompletedExplicitFormulaTopPath r x) R →
        ε ≤ ‖zetaSideFactor w‖) ∧
      (∀ w : ℂ, w ∈ Metric.closedBall
          (zetaCompletedExplicitFormulaBottomPath r x) R →
        ε ≤ ‖zetaSideFactor w‖) := by
  rcases zetaSideFactor_positive_lower_bound_on_topPath_ball_of_singular_separation_owner
      r x R δTop hseparatedTop hR_pos hRTop with
    ⟨εTop, hεTop, hTop⟩
  rcases zetaSideFactor_positive_lower_bound_on_bottomPath_ball_of_singular_separation_owner
      r x R δBottom hseparatedBottom hR_pos hRBottom with
    ⟨εBottom, hεBottom, hBottom⟩
  refine ⟨min εTop εBottom, lt_min hεTop hεBottom, ?_, ?_⟩
  · intro w hw
    exact (min_le_left εTop εBottom).trans (hTop w hw)
  · intro w hw
    exact (min_le_right εTop εBottom).trans (hBottom w hw)

/- A single lower bound for both horizontal carrier faces.  Keeping the
minimum-radius assembly here prevents each contour consumer from rebuilding
the same compactness argument with potentially different constants. -/
theorem inverseGamma_positive_lower_bound_on_horizontal_pair_balls_of_radius_lt_c_owner
    (r : ExplicitFormulaRectangle) (x R : ℝ)
    (hcx : r.c ≤ x) (hR_pos : 0 < R) (hR : R < r.c) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ w : ℂ, w ∈ Metric.closedBall
          (zetaCompletedExplicitFormulaTopPath r x) R →
        ε ≤ ‖(Complex.Gammaℝ w)⁻¹‖) ∧
      (∀ w : ℂ, w ∈ Metric.closedBall
          (zetaCompletedExplicitFormulaBottomPath r x) R →
        ε ≤ ‖(Complex.Gammaℝ w)⁻¹‖) := by
  rcases inverseGamma_positive_lower_bound_on_topPath_ball_of_radius_lt_c_owner
      r x R hcx hR_pos hR with
    ⟨εTop, hεTop, hTop⟩
  rcases inverseGamma_positive_lower_bound_on_bottomPath_ball_of_radius_lt_c_owner
      r x R hcx hR_pos hR with
    ⟨εBottom, hεBottom, hBottom⟩
  refine ⟨min εTop εBottom, ?_, ?_, ?_⟩
  · exact lt_min hεTop hεBottom
  · intro w hw
    exact (min_le_left εTop εBottom).trans (hTop w hw)
  · intro w hw
    exact (min_le_right εTop εBottom).trans (hBottom w hw)

theorem inverseGamma_positive_lower_bound_on_horizontal_pair_balls_of_singular_separation_owner
    (r : ExplicitFormulaRectangle) (x R δTop δBottom : ℝ)
    (hseparatedTop : ∀ q : ℂ,
      explicitFormulaContourSingularPoint q →
        δTop ≤ ‖zetaCompletedExplicitFormulaTopPath r x - q‖)
    (hseparatedBottom : ∀ q : ℂ,
      explicitFormulaContourSingularPoint q →
        δBottom ≤ ‖zetaCompletedExplicitFormulaBottomPath r x - q‖)
    (hR_pos : 0 < R) (hRTop : R < δTop) (hRBottom : R < δBottom) :
    ∃ ε : ℝ, 0 < ε ∧
      (∀ w : ℂ, w ∈ Metric.closedBall
          (zetaCompletedExplicitFormulaTopPath r x) R →
        ε ≤ ‖(Complex.Gammaℝ w)⁻¹‖) ∧
      (∀ w : ℂ, w ∈ Metric.closedBall
          (zetaCompletedExplicitFormulaBottomPath r x) R →
        ε ≤ ‖(Complex.Gammaℝ w)⁻¹‖) := by
  rcases inverseGamma_positive_lower_bound_on_closedBall_of_singular_separation
      (zetaCompletedExplicitFormulaTopPath r x) R δTop hseparatedTop hRTop with
    ⟨εTop, hεTop, hTop⟩
  rcases inverseGamma_positive_lower_bound_on_closedBall_of_singular_separation
      (zetaCompletedExplicitFormulaBottomPath r x) R δBottom hseparatedBottom hRBottom with
    ⟨εBottom, hεBottom, hBottom⟩
  refine ⟨min εTop εBottom, lt_min hεTop hεBottom, ?_, ?_⟩
  · intro w hw
    exact (min_le_left εTop εBottom).trans (hTop w hw)
  · intro w hw
    exact (min_le_right εTop εBottom).trans (hBottom w hw)

theorem zetaCompletedExplicitFormulaAutocorrelationTopPath_Gammaℝ_ne_zero_of_inputs
    (f : ZetaAdmissibleFunction) (u x : ℝ)
    (hTop_ne_zero :
      zetaCompletedExplicitFormulaTopPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
          x ≠ 0)
    (hTop_not_negative_even :
      ¬ ∃ n : ℕ,
        zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x = (-2 : ℂ) * (((n + 1 : ℕ) : ℂ))) :
    Complex.Gammaℝ
        (zetaCompletedExplicitFormulaTopPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
          x) ≠ 0 :=
  Gammaℝ_ne_zero_of_ne_zero_and_not_negative_even
    hTop_ne_zero
    hTop_not_negative_even

theorem zetaCompletedExplicitFormulaAutocorrelationBottomPath_Gammaℝ_ne_zero_of_inputs
    (f : ZetaAdmissibleFunction) (u x : ℝ)
    (hBottom_ne_zero :
      zetaCompletedExplicitFormulaBottomPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
          x ≠ 0)
    (hBottom_not_negative_even :
      ¬ ∃ n : ℕ,
        zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x = (-2 : ℂ) * (((n + 1 : ℕ) : ℂ))) :
    Complex.Gammaℝ
        (zetaCompletedExplicitFormulaBottomPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
          x) ≠ 0 :=
  Gammaℝ_ne_zero_of_ne_zero_and_not_negative_even
    hBottom_ne_zero
    hBottom_not_negative_even

/-! The carrier separation lemmas below control distance from the completed
zeros and Gamma poles.  They do not, by themselves, prove that the finite
zeta-side factor is nonzero.  This small owner lemma keeps that analytic
input explicit instead of silently treating geometric separation as
nonvanishing. -/

theorem zetaCompletedExplicitFormulaAutocorrelationTopPath_zetaSideFactor_ne_zero_of_inputs
    (f : ZetaAdmissibleFunction) (u x : ℝ)
    (hTopCompleted :
      completedRiemannZeta
          (zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x) ≠ 0)
    (hTopGamma :
      Complex.Gammaℝ
          (zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x) ≠ 0) :
    zetaSideFactor
        (zetaCompletedExplicitFormulaTopPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
          x) ≠ 0 :=
  zetaSideFactor_ne_zero hTopCompleted hTopGamma

theorem zetaCompletedExplicitFormulaAutocorrelationBottomPath_zetaSideFactor_ne_zero_of_inputs
    (f : ZetaAdmissibleFunction) (u x : ℝ)
    (hBottomCompleted :
      completedRiemannZeta
          (zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x) ≠ 0)
    (hBottomGamma :
      Complex.Gammaℝ
          (zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x) ≠ 0) :
    zetaSideFactor
        (zetaCompletedExplicitFormulaBottomPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
          x) ≠ 0 :=
  zetaSideFactor_ne_zero hBottomCompleted hBottomGamma

theorem zetaSideFactor_norm_pos_of_ne_zero_owner
    {z : ℂ} (hz : zetaSideFactor z ≠ 0) :
    0 < ‖zetaSideFactor z‖ :=
  norm_pos_iff.mpr hz

theorem zetaCompletedExplicitFormulaAutocorrelationTopPath_zetaSideFactor_norm_pos_of_inputs
    (f : ZetaAdmissibleFunction) (u x : ℝ)
    (hTopCompleted :
      completedRiemannZeta
          (zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x) ≠ 0)
    (hTopGamma :
      Complex.Gammaℝ
          (zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x) ≠ 0) :
    0 < ‖zetaSideFactor
        (zetaCompletedExplicitFormulaTopPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
          x)‖ :=
  zetaSideFactor_norm_pos_of_ne_zero_owner
    (zetaCompletedExplicitFormulaAutocorrelationTopPath_zetaSideFactor_ne_zero_of_inputs
      f u x hTopCompleted hTopGamma)

theorem zetaCompletedExplicitFormulaAutocorrelationBottomPath_zetaSideFactor_norm_pos_of_inputs
    (f : ZetaAdmissibleFunction) (u x : ℝ)
    (hBottomCompleted :
      completedRiemannZeta
          (zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x) ≠ 0)
    (hBottomGamma :
      Complex.Gammaℝ
          (zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x) ≠ 0) :
    0 < ‖zetaSideFactor
        (zetaCompletedExplicitFormulaBottomPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
          x)‖ :=
  zetaSideFactor_norm_pos_of_ne_zero_owner
    (zetaCompletedExplicitFormulaAutocorrelationBottomPath_zetaSideFactor_ne_zero_of_inputs
      f u x hBottomCompleted hBottomGamma)

theorem zetaCompletedExplicitFormulaAutocorrelationTopPath_completedZero_separation
    (f : ZetaAdmissibleFunction) (u x : ℝ)
    (hx :
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        δ ≤
          ‖zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x - ((1 / 2 : ℂ) + (ρ : ℂ))‖ :=
  ExplicitFormulaCofinalHeightSchedule.topPath_completedZero_separation
    (zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f)
    u x hx

theorem zetaCompletedExplicitFormulaAutocorrelationTopPath_gammaPole_separation
    (f : ZetaAdmissibleFunction) (u x : ℝ)
    (hx :
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ n : ℕ,
        δ ≤
          ‖zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x - (-(2 * (n : ℂ)))‖ :=
  ExplicitFormulaCofinalHeightSchedule.topPath_gammaPole_separation
    (zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f)
    u x hx

theorem zetaCompletedExplicitFormulaAutocorrelationBottomPath_completedZero_separation
    (f : ZetaAdmissibleFunction) (u x : ℝ)
    (hx :
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        δ ≤
          ‖zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x - ((1 / 2 : ℂ) + (ρ : ℂ))‖ :=
  ExplicitFormulaCofinalHeightSchedule.bottomPath_completedZero_separation
    (zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f)
    u x hx

theorem zetaCompletedExplicitFormulaAutocorrelationBottomPath_gammaPole_separation
    (f : ZetaAdmissibleFunction) (u x : ℝ)
    (hx :
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ n : ℕ,
        δ ≤
          ‖zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x - (-(2 * (n : ℂ)))‖ :=
  ExplicitFormulaCofinalHeightSchedule.bottomPath_gammaPole_separation
    (zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f)
    u x hx

theorem zetaCompletedExplicitFormulaAutocorrelationTopPath_singletonFactorBoundedCarrier
    (f : ZetaAdmissibleFunction) (u x : ℝ)
    (hx :
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    ∃ boundedCarrier :
        CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
          (min (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
          (max (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)),
      zetaCompletedExplicitFormulaTopPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
          x ∈ boundedCarrier.carrier.carrier :=
  ExplicitFormulaCofinalHeightSchedule.topPath_singletonFactorBoundedCarrier
    (zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f)
    u x hx

theorem zetaCompletedExplicitFormulaAutocorrelationBottomPath_singletonFactorBoundedCarrier
    (f : ZetaAdmissibleFunction) (u x : ℝ)
    (hx :
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    ∃ boundedCarrier :
        CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
          (min (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
          (max (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)),
      zetaCompletedExplicitFormulaBottomPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
          x ∈ boundedCarrier.carrier.carrier :=
  ExplicitFormulaCofinalHeightSchedule.bottomPath_singletonFactorBoundedCarrier
    (zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f)
    u x hx

theorem zetaCompletedExplicitFormulaAutocorrelationHorizontalPair_factorBoundedCarrier
    (f : ZetaAdmissibleFunction) (u x : ℝ)
    (hx :
      x ∈ Set.uIcc
        (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
        (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    ∃ boundedCarrier :
        CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
          (min (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
          (max (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)),
      zetaCompletedExplicitFormulaTopPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
          x ∈ boundedCarrier.carrier.carrier ∧
      zetaCompletedExplicitFormulaBottomPath
          ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
            ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
          x ∈ boundedCarrier.carrier.carrier :=
  ExplicitFormulaCofinalHeightSchedule.horizontalPairFactorBoundedCarrier
    (zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f)
    u x hx

theorem zetaCompletedExplicitFormulaAutocorrelationHorizontalFiniteWindow_factorBoundedCarrier
    (f : ZetaAdmissibleFunction) (u : ℝ) (xs : List ℝ)
    (hx :
      ∀ x : ℝ, x ∈ xs →
        x ∈ Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    ∃ boundedCarrier :
        CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
          (min (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
          (max (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)),
      (∀ x : ℝ, x ∈ xs →
        zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x ∈ boundedCarrier.carrier.carrier) ∧
      (∀ x : ℝ, x ∈ xs →
        zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x ∈ boundedCarrier.carrier.carrier) :=
  List.rec
    (motive := fun ys =>
      (∀ x : ℝ, x ∈ ys →
        x ∈ Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) →
      ∃ boundedCarrier :
          CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
            (min (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
              (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
            (max (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
              (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)),
        (∀ x : ℝ, x ∈ ys →
          zetaCompletedExplicitFormulaTopPath
              ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
              x ∈ boundedCarrier.carrier.carrier) ∧
        (∀ x : ℝ, x ∈ ys →
          zetaCompletedExplicitFormulaBottomPath
              ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
              x ∈ boundedCarrier.carrier.carrier))
    (fun emptyWindow =>
      Exists.intro
        (CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.empty
          (min (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
          (max (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)))
        (And.intro
          (fun x hxmem => False.elim (List.not_mem_nil x hxmem))
          (fun x hxmem => False.elim (List.not_mem_nil x hxmem))))
    (fun x ys ih consWindow =>
      let tailWindow :
          ∀ y : ℝ, y ∈ ys →
            y ∈ Set.uIcc
              (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
              (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) :=
        fun y hy => consWindow y (List.mem_cons_of_mem x hy)
      match
        zetaCompletedExplicitFormulaAutocorrelationHorizontalPair_factorBoundedCarrier
          f u x (consWindow x (List.mem_cons_self x ys)),
        ih tailWindow with
      | ⟨headCarrier, headTop, headBottom⟩,
        ⟨tailCarrier, tailTop, tailBottom⟩ =>
          let combinedCarrier :
              CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
                (min (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
                  (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
                (max (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
                  (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :=
            CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.union
              headCarrier tailCarrier
          Exists.intro combinedCarrier
            (And.intro
              (fun y hymem =>
                match List.mem_cons.mp hymem with
                | Or.inl hyx =>
                    Eq.subst
                      (motive := fun w : ℝ =>
                        zetaCompletedExplicitFormulaTopPath
                            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
                            w ∈ combinedCarrier.carrier.carrier)
                      hyx.symm
                      (CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.mem_union_left
                        headCarrier tailCarrier headTop)
                | Or.inr hytail =>
                    CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.mem_union_right
                      headCarrier tailCarrier (tailTop y hytail))
              (fun y hymem =>
                match List.mem_cons.mp hymem with
                | Or.inl hyx =>
                    Eq.subst
                      (motive := fun w : ℝ =>
                        zetaCompletedExplicitFormulaBottomPath
                            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
                            w ∈ combinedCarrier.carrier.carrier)
                      hyx.symm
                      (CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.mem_union_left
                        headCarrier tailCarrier headBottom)
                | Or.inr hytail =>
                    CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.mem_union_right
                      headCarrier tailCarrier (tailBottom y hytail))))
    xs hx

theorem zetaCompletedExplicitFormulaAutocorrelationHorizontalFiniteSample_factorBoundedCarrier
    (f : ZetaAdmissibleFunction) (samples : List (ℝ × ℝ))
    (hx :
      ∀ p : ℝ × ℝ, p ∈ samples →
        p.2 ∈ Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    ∃ boundedCarrier :
        CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
          (min (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
          (max (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)),
      (∀ p : ℝ × ℝ, p ∈ samples →
        zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height p.1))
            p.2 ∈ boundedCarrier.carrier.carrier) ∧
      (∀ p : ℝ × ℝ, p ∈ samples →
        zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height p.1))
            p.2 ∈ boundedCarrier.carrier.carrier) :=
  List.rec
    (motive := fun sampleList =>
      (∀ p : ℝ × ℝ, p ∈ sampleList →
        p.2 ∈ Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) →
      ∃ boundedCarrier :
          CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
            (min (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
              (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
            (max (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
              (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)),
        (∀ p : ℝ × ℝ, p ∈ sampleList →
          zetaCompletedExplicitFormulaTopPath
              ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height p.1))
              p.2 ∈ boundedCarrier.carrier.carrier) ∧
        (∀ p : ℝ × ℝ, p ∈ sampleList →
          zetaCompletedExplicitFormulaBottomPath
              ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height p.1))
              p.2 ∈ boundedCarrier.carrier.carrier))
    (fun emptySamples =>
      Exists.intro
        (CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.empty
          (min (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
          (max (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
            (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)))
        (And.intro
          (fun p hpmem => False.elim (List.not_mem_nil p hpmem))
          (fun p hpmem => False.elim (List.not_mem_nil p hpmem))))
    (fun p sampleList ih consSamples =>
      let tailSamples :
          ∀ q : ℝ × ℝ, q ∈ sampleList →
            q.2 ∈ Set.uIcc
              (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
              (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c) :=
        fun q hq => consSamples q (List.mem_cons_of_mem p hq)
      match
        zetaCompletedExplicitFormulaAutocorrelationHorizontalPair_factorBoundedCarrier
          f p.1 p.2 (consSamples p (List.mem_cons_self p sampleList)),
        ih tailSamples with
      | ⟨headCarrier, headTop, headBottom⟩,
        ⟨tailCarrier, tailTop, tailBottom⟩ =>
          let combinedCarrier :
              CompletedZetaZeroExcisedStrip.FactorBoundedCarrier
                (min (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
                  (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c))
                (max (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
                  (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :=
            CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.union
              headCarrier tailCarrier
          Exists.intro combinedCarrier
            (And.intro
              (fun q hqmem =>
                match List.mem_cons.mp hqmem with
                | Or.inl hqp =>
                    Eq.subst
                      (motive := fun r : ℝ × ℝ =>
                        zetaCompletedExplicitFormulaTopPath
                            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height r.1))
                            r.2 ∈ combinedCarrier.carrier.carrier)
                      hqp.symm
                      (CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.mem_union_left
                        headCarrier tailCarrier headTop)
                | Or.inr hqtail =>
                    CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.mem_union_right
                      headCarrier tailCarrier (tailTop q hqtail))
              (fun q hqmem =>
                match List.mem_cons.mp hqmem with
                | Or.inl hqp =>
                    Eq.subst
                      (motive := fun r : ℝ × ℝ =>
                        zetaCompletedExplicitFormulaBottomPath
                            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height r.1))
                            r.2 ∈ combinedCarrier.carrier.carrier)
                      hqp.symm
                      (CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.mem_union_left
                        headCarrier tailCarrier headBottom)
                | Or.inr hqtail =>
                    CompletedZetaZeroExcisedStrip.FactorBoundedCarrier.mem_union_right
                      headCarrier tailCarrier (tailBottom q hqtail))))
    samples hx

theorem zetaCompletedExplicitFormulaAutocorrelationHorizontalFiniteWindow_logDerivBound
    (f : ZetaAdmissibleFunction) (u : ℝ) (xs : List ℝ) (N : ℕ)
    (hx :
      ∀ x : ℝ, x ∈ xs →
        x ∈ Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    ∃ C : ℝ, 0 < C ∧
      (∀ x : ℝ, x ∈ xs →
        ‖completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)‖ ≤
          C *
            (1 +
              ‖(zetaCompletedExplicitFormulaTopPath
                ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                  ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
                x).im‖) ^ N) ∧
      (∀ x : ℝ, x ∈ xs →
        ‖completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)‖ ≤
          C *
            (1 +
              ‖(zetaCompletedExplicitFormulaBottomPath
                ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                  ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
                x).im‖) ^ N) :=
  match
    zetaCompletedExplicitFormulaAutocorrelationHorizontalFiniteWindow_factorBoundedCarrier
      f u xs hx with
  | ⟨boundedCarrier, topMem, bottomMem⟩ =>
      let C : ℝ :=
        boundedCarrier.factorBound.zetaSide.constant N +
          boundedCarrier.factorBound.inverseGamma.constant N
      let C_pos : 0 < C :=
        add_pos
          (boundedCarrier.factorBound.zetaSide.constant_pos N)
          (boundedCarrier.factorBound.inverseGamma.constant_pos N)
      Exists.intro C
        (And.intro
          C_pos
          (And.intro
            (fun x hxmem =>
              completedZetaNegLogDeriv_bound_of_separated_factorBoundData
                boundedCarrier.carrier
                boundedCarrier.factorBound.zetaSide
                boundedCarrier.factorBound.inverseGamma
                N
                (zetaCompletedExplicitFormulaTopPath
                  ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                    ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
                  x)
                (topMem x hxmem))
            (fun x hxmem =>
              completedZetaNegLogDeriv_bound_of_separated_factorBoundData
                boundedCarrier.carrier
                boundedCarrier.factorBound.zetaSide
                boundedCarrier.factorBound.inverseGamma
                N
                (zetaCompletedExplicitFormulaBottomPath
                  ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                    ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
                  x)
                (bottomMem x hxmem))))

theorem zetaCompletedExplicitFormulaAutocorrelationHorizontalFiniteSample_logDerivBound
    (f : ZetaAdmissibleFunction) (samples : List (ℝ × ℝ)) (N : ℕ)
    (hx :
      ∀ p : ℝ × ℝ, p ∈ samples →
        p.2 ∈ Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    ∃ C : ℝ, 0 < C ∧
      (∀ p : ℝ × ℝ, p ∈ samples →
        ‖completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height p.1))
            p.2)‖ ≤
          C *
            (1 +
              ‖(zetaCompletedExplicitFormulaTopPath
                ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                  ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height p.1))
                p.2).im‖) ^ N) ∧
      (∀ p : ℝ × ℝ, p ∈ samples →
        ‖completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height p.1))
            p.2)‖ ≤
          C *
            (1 +
              ‖(zetaCompletedExplicitFormulaBottomPath
                ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                  ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height p.1))
                p.2).im‖) ^ N) :=
  match
    zetaCompletedExplicitFormulaAutocorrelationHorizontalFiniteSample_factorBoundedCarrier
      f samples hx with
  | ⟨boundedCarrier, topMem, bottomMem⟩ =>
      let C : ℝ :=
        boundedCarrier.factorBound.zetaSide.constant N +
          boundedCarrier.factorBound.inverseGamma.constant N
      let C_pos : 0 < C :=
        add_pos
          (boundedCarrier.factorBound.zetaSide.constant_pos N)
          (boundedCarrier.factorBound.inverseGamma.constant_pos N)
      Exists.intro C
        (And.intro
          C_pos
          (And.intro
            (fun p hpmem =>
              completedZetaNegLogDeriv_bound_of_separated_factorBoundData
                boundedCarrier.carrier
                boundedCarrier.factorBound.zetaSide
                boundedCarrier.factorBound.inverseGamma
                N
                (zetaCompletedExplicitFormulaTopPath
                  ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                    ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height p.1))
                  p.2)
                (topMem p hpmem))
            (fun p hpmem =>
              completedZetaNegLogDeriv_bound_of_separated_factorBoundData
                boundedCarrier.carrier
                boundedCarrier.factorBound.zetaSide
                boundedCarrier.factorBound.inverseGamma
                N
                (zetaCompletedExplicitFormulaBottomPath
                  ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                    ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height p.1))
                  p.2)
                (bottomMem p hpmem))))

theorem zetaCompletedExplicitFormulaAutocorrelationHorizontalFiniteWindow_logDerivHeightBound
    (f : ZetaAdmissibleFunction) (u : ℝ) (xs : List ℝ) (N : ℕ)
    (hx :
      ∀ x : ℝ, x ∈ xs →
        x ∈ Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    ∃ C : ℝ, 0 < C ∧
      (∀ x : ℝ, x ∈ xs →
        ‖completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)‖ ≤
          C *
            (1 +
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ N) ∧
      (∀ x : ℝ, x ∈ xs →
        ‖completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
            x)‖ ≤
          C *
            (1 +
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ N) :=
  match
    zetaCompletedExplicitFormulaAutocorrelationHorizontalFiniteWindow_logDerivBound
      f u xs N hx with
  | ⟨C, C_pos, topRaw, bottomRaw⟩ =>
      Exists.intro C
        (And.intro
          C_pos
          (And.intro
            (fun x hxmem =>
              let z : ℂ :=
                zetaCompletedExplicitFormulaTopPath
                  ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                    ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
                  x
              let him :
                  ‖z.im‖ =
                    ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖ :=
                zetaCompletedExplicitFormulaTopPath_im_norm
                  ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                    ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
                  x
              let htarget :
                  C * (1 + ‖z.im‖) ^ N =
                    C *
                      (1 +
                        ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ N :=
                congrArg
                  (fun value : ℝ => C * (1 + value) ^ N)
                  him
              (topRaw x hxmem).trans_eq htarget)
            (fun x hxmem =>
              let z : ℂ :=
                zetaCompletedExplicitFormulaBottomPath
                  ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                    ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
                  x
              let him :
                  ‖z.im‖ =
                    ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖ :=
                zetaCompletedExplicitFormulaBottomPath_im_norm
                  ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                    ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u))
                  x
              let htarget :
                  C * (1 + ‖z.im‖) ^ N =
                    C *
                      (1 +
                        ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height u‖) ^ N :=
                congrArg
                  (fun value : ℝ => C * (1 + value) ^ N)
                  him
              (bottomRaw x hxmem).trans_eq htarget)))

theorem zetaCompletedExplicitFormulaAutocorrelationHorizontalFiniteSample_logDerivHeightBound
    (f : ZetaAdmissibleFunction) (samples : List (ℝ × ℝ)) (N : ℕ)
    (hx :
      ∀ p : ℝ × ℝ, p ∈ samples →
        p.2 ∈ Set.uIcc
          (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c
          (1 - (zetaCompletedExplicitFormula_autocorrelation_contourFamily f).c)) :
    ∃ C : ℝ, 0 < C ∧
      (∀ p : ℝ × ℝ, p ∈ samples →
        ‖completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaTopPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height p.1))
            p.2)‖ ≤
          C *
            (1 +
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height p.1‖) ^ N) ∧
      (∀ p : ℝ × ℝ, p ∈ samples →
        ‖completedZetaNegLogDeriv
          (zetaCompletedExplicitFormulaBottomPath
            ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
              ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height p.1))
            p.2)‖ ≤
          C *
            (1 +
              ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height p.1‖) ^ N) :=
  match
    zetaCompletedExplicitFormulaAutocorrelationHorizontalFiniteSample_logDerivBound
      f samples N hx with
  | ⟨C, C_pos, topRaw, bottomRaw⟩ =>
      Exists.intro C
        (And.intro
          C_pos
          (And.intro
            (fun p hpmem =>
              let z : ℂ :=
                zetaCompletedExplicitFormulaTopPath
                  ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                    ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height p.1))
                  p.2
              let him :
                  ‖z.im‖ =
                    ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height p.1‖ :=
                zetaCompletedExplicitFormulaTopPath_im_norm
                  ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                    ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height p.1))
                  p.2
              let htarget :
                  C * (1 + ‖z.im‖) ^ N =
                    C *
                      (1 +
                        ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height p.1‖) ^ N :=
                congrArg
                  (fun value : ℝ => C * (1 + value) ^ N)
                  him
              (topRaw p hpmem).trans_eq htarget)
            (fun p hpmem =>
              let z : ℂ :=
                zetaCompletedExplicitFormulaBottomPath
                  ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                    ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height p.1))
                  p.2
              let him :
                  ‖z.im‖ =
                    ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height p.1‖ :=
                zetaCompletedExplicitFormulaBottomPath_im_norm
                  ((zetaCompletedExplicitFormula_autocorrelation_contourFamily f).rectangle
                    ((zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height p.1))
                  p.2
              let htarget :
                  C * (1 + ‖z.im‖) ^ N =
                    C *
                      (1 +
                        ‖(zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f).height p.1‖) ^ N :=
                congrArg
                  (fun value : ℝ => C * (1 + value) ^ N)
                  him
              (bottomRaw p hpmem).trans_eq htarget)))

/-! The carrier is the union of scheduled top and bottom path images.  The
pointwise bound below records that ownership explicitly for later carrier-data
assembly. -/
theorem zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_completedLogDeriv_pointwise_bound_owner
    (f : ZetaAdmissibleFunction) {z : ℂ}
    (hz : z ∈
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier) :
    ∃ B : ℝ, 0 ≤ B ∧ ‖completedZetaNegLogDeriv z‖ ≤ B := by
  have hcases :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_mem_cases
      f z hz
  exact Or.elim hcases
    (fun htop =>
      Exists.elim htop (fun u htop_u =>
        Exists.elim htop_u (fun x htop_x =>
          Exists.elim
            (zetaCompletedExplicitFormulaAutocorrelationScheduledTopPath_completedLogDeriv_uniform_bound_owner
              f u)
            (fun B hB hbound =>
              ⟨B, hB,
                Eq.subst
                  (motive := fun w : ℂ => ‖completedZetaNegLogDeriv w‖ ≤ B)
                  htop_x.2.symm
                  (hbound x htop_x.1))))))
    (fun hbottom =>
      Exists.elim hbottom (fun u hbottom_u =>
        Exists.elim hbottom_u (fun x hbottom_x =>
          Exists.elim
            (zetaCompletedExplicitFormulaAutocorrelationScheduledBottomPath_completedLogDeriv_uniform_bound_owner
              f u)
            (fun B hB hbound =>
              ⟨B, hB,
                Eq.subst
                  (motive := fun w : ℂ => ‖completedZetaNegLogDeriv w‖ ≤ B)
                  hbottom_x.2.symm
                (hbound x hbottom_x.1))))))

theorem zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_zetaSideLogDeriv_pointwise_bound_owner
    (f : ZetaAdmissibleFunction) {z : ℂ}
    (hz : z ∈
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier) :
    ∃ B : ℝ, 0 ≤ B ∧ ‖zetaSideNegLogDeriv z‖ ≤ B := by
  have hcases :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_mem_cases
      f z hz
  exact Or.elim hcases
    (fun htop =>
      Exists.elim htop (fun u htop_u =>
        Exists.elim htop_u (fun x htop_x =>
          Exists.elim
            (zetaCompletedExplicitFormulaAutocorrelationScheduledTopPath_zetaSideLogDeriv_uniform_bound_owner
              f u)
            (fun B hB hbound =>
              ⟨B, hB,
                Eq.subst
                  (motive := fun w : ℂ => ‖zetaSideNegLogDeriv w‖ ≤ B)
                  htop_x.2.symm
                  (hbound x htop_x.1))))))
    (fun hbottom =>
      Exists.elim hbottom (fun u hbottom_u =>
        Exists.elim hbottom_u (fun x hbottom_x =>
          Exists.elim
            (zetaCompletedExplicitFormulaAutocorrelationScheduledBottomPath_zetaSideLogDeriv_uniform_bound_owner
              f u)
            (fun B hB hbound =>
              ⟨B, hB,
                Eq.subst
                  (motive := fun w : ℂ => ‖zetaSideNegLogDeriv w‖ ≤ B)
                  hbottom_x.2.symm
                  (hbound x hbottom_x.1))))))

theorem zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_inverseGammaLogDeriv_pointwise_bound_owner
    (f : ZetaAdmissibleFunction) {z : ℂ}
    (hz : z ∈
      (zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier f).carrier) :
    ∃ B : ℝ, 0 ≤ B ∧
      ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) z /
        (Complex.Gammaℝ z)⁻¹‖ ≤ B := by
  have hcases :=
    zetaCompletedExplicitFormulaAutocorrelationScheduledHorizontalCarrier_mem_cases
      f z hz
  exact Or.elim hcases
    (fun htop =>
      Exists.elim htop (fun u htop_u =>
        Exists.elim htop_u (fun x htop_x =>
          Exists.elim
            (ExplicitFormulaCofinalHeightSchedule.topPath_inverseGamma_logDeriv_uniform_bound
              (zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f) u)
            (fun B hB hbound =>
              ⟨B, hB,
                Eq.subst
                  (motive := fun w : ℂ =>
                    ‖deriv (fun ξ : ℂ => (Complex.Gammaℝ ξ)⁻¹) w /
                      (Complex.Gammaℝ w)⁻¹‖ ≤ B)
                  htop_x.2.symm
                  (hbound x htop_x.1))))))
    (fun hbottom =>
      Exists.elim hbottom (fun u hbottom_u =>
        Exists.elim hbottom_u (fun x hbottom_x =>
          Exists.elim
            (ExplicitFormulaCofinalHeightSchedule.bottomPath_inverseGamma_logDeriv_uniform_bound
              (zetaCompletedExplicitFormulaAutocorrelationCofinalHeightSchedule f) u)
            (fun B hB hbound =>
              ⟨B, hB,
                Eq.subst
                  (motive := fun w : ℂ =>
                    ‖deriv (fun ξ : ℂ => (Complex.Gammaℝ ξ)⁻¹) w /
                      (Complex.Gammaℝ w)⁻¹‖ ≤ B)
                  hbottom_x.2.symm
                  (hbound x hbottom_x.1))))))

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
