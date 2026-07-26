import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CanonicalScheduledPolynomialPackageParts.VariableCauchyPathBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaCompletedLogDerivativeControl.CauchyBoundData
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaZeroKreinGram.WeilCriterion.OwnerParts.CauchyPathCarrierDataPackage
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.OwnerParts.CanonicalCarrierSeparationConstantBoundsParts.Structures

/-!
# Canonical carrier separation and constant bounds

This file owns the finite-local Cauchy/separation constant construction for the
canonical scheduled horizontal paths.  The constants are local in the path
point and are assembled into the variable Cauchy path data consumed by the
final RH lane.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

namespace ZetaAdmissibleFunction

/- The quantitative reciprocal step used by both carrier constructors.  It is
   separated from the geometric choice of radius so that the latter only has
   to provide a positive lower bound for Gammaℝ. -/
theorem inverseGamma_norm_le_of_Gammaℝ_norm_lower_bound
    {w : ℂ} {m : ℝ}
    (hm : 0 < m)
    (hlower : m ≤ ‖Complex.Gammaℝ w‖) :
    ‖(Complex.Gammaℝ w)⁻¹‖ ≤ m⁻¹ := by
  calc
    ‖(Complex.Gammaℝ w)⁻¹‖ = ‖Complex.Gammaℝ w‖⁻¹ := norm_inv _
    _ = 1 / ‖Complex.Gammaℝ w‖ := by rfl
    _ ≤ 1 / m := one_div_le_one_div_of_le hm hlower
    _ = m⁻¹ := by rfl

/- A right-half-plane Gamma ball therefore has a genuine positive inverse-Gamma
   lower bound.  This is the compactness bridge used when choosing scheduled
   carrier radii. -/
theorem exists_inverseGamma_positive_norm_lower_bound_on_rightHalfPlane_closedBall
    (z : ℂ) (R : ℝ) (hR : 0 < R) (hcenter : R < z.re) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ w : ℂ, w ∈ Metric.closedBall z R →
        δ ≤ ‖(Complex.Gammaℝ w)⁻¹‖ := by
  exact exists_inverseGamma_positive_norm_lower_bound_of_isCompact_of_continuousOn
    isCompact_closedBall
    ⟨z, Metric.mem_closedBall_self (le_of_lt hR)⟩
    Complex.differentiable_Gammaℝ_inv.continuous.continuousOn
    (inverseGamma_ne_zero_on_closedBall_of_center_re_gt_radius_owner z R hcenter)

/- The same compact carrier also supplies a finite upper norm bound.  Keeping
   both bounds together is the local analytic package used by the Cauchy
   quotient estimates. -/
theorem exists_inverseGamma_two_sided_norm_bounds_on_rightHalfPlane_closedBall
    (z : ℂ) (R : ℝ) (hR : 0 < R) (hcenter : R < z.re) :
    ∃ δ A : ℝ, 0 < δ ∧ 0 ≤ A ∧
      (∀ w : ℂ, w ∈ Metric.closedBall z R →
        δ ≤ ‖(Complex.Gammaℝ w)⁻¹‖) ∧
      (∀ w : ℂ, w ∈ Metric.closedBall z R →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤ A) := by
  obtain ⟨δ, hδ, hδ_bound⟩ :=
    exists_inverseGamma_positive_norm_lower_bound_on_rightHalfPlane_closedBall
      z R hR hcenter
  obtain ⟨A, hA, hA_bound⟩ :=
    exists_inverseGamma_norm_upper_bound_of_isCompact_of_continuousOn
      (s := Metric.closedBall z R)
      isCompact_closedBall
      Complex.differentiable_Gammaℝ_inv.continuous.continuousOn
  exact ⟨δ, A, hδ, hA, hδ_bound, hA_bound⟩

/- Complete local analytic package for a positive-radius right-half-plane
   carrier ball.  This is the first constructor-level Gamma input used by the
   scheduled carrier proof. -/
theorem inverseGamma_rightHalfPlane_closedBall_analytic_package_owner
    (z : ℂ) (R : ℝ) (hR : 0 < R) (hcenter : R < z.re) :
    DiffContOnCl ℂ (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (Metric.ball z R) ∧
      (∀ w : ℂ, w ∈ Metric.closedBall z R →
        (Complex.Gammaℝ w)⁻¹ ≠ 0) ∧
      (∃ δ A : ℝ, 0 < δ ∧ 0 ≤ A ∧
        (∀ w : ℂ, w ∈ Metric.closedBall z R →
          δ ≤ ‖(Complex.Gammaℝ w)⁻¹‖) ∧
        (∀ w : ℂ, w ∈ Metric.closedBall z R →
          ‖(Complex.Gammaℝ w)⁻¹‖ ≤ A)) := by
  exact ⟨
    inverseGamma_diffContOnCl_on_ball_owner z R,
    inverseGamma_ne_zero_on_closedBall_of_center_re_gt_radius_owner z R
      hcenter,
      exists_inverseGamma_two_sided_norm_bounds_on_rightHalfPlane_closedBall
      z R hR hcenter⟩

theorem gamma_zero_loci_avoid_rightHalfPlane_closedBall_owner
    (z : ℂ) (R : ℝ) (hR : 0 < R) (hcenter : R < z.re) :
    (∀ w : ℂ, w ∈ Metric.closedBall z R → Complex.Gammaℝ w ≠ 0) ∧
      (∀ w : ℂ, w ∈ Metric.closedBall z R →
        Complex.Gammaℝ (w / 2) ≠ 0) := by
  have hreal : ∀ w : ℂ, w ∈ Metric.closedBall z R → 0 < w.re := by
    intro w hw
    have hdist : ‖w - z‖ ≤ R := by
      exact hw
    have hcoord : z.re - R ≤ w.re := by
      have hnorm : ‖(w - z).re‖ ≤ ‖w - z‖ := norm_re_le_norm (w - z)
      have hsub : -R ≤ (w - z).re := by
        have habs : ‖(w - z).re‖ ≤ R := hnorm.trans hdist
        exact neg_le_of_abs_le habs
      have hadd := add_le_add_left hsub z.re
      calc
        z.re - R = z.re + -R := sub_eq_add_neg z.re R
        _ ≤ z.re + (w - z).re := hadd
        _ = w.re := by
          exact Eq.trans (congrArg (fun x : ℝ => z.re + x) (Complex.sub_re w z))
            (Eq.trans (add_comm z.re (w.re - z.re)) (sub_add_cancel w.re z.re))
    exact lt_of_lt_of_le (sub_pos.mpr hcenter) hcoord
  constructor
  · intro w hw
    exact Complex.Gammaℝ_ne_zero_of_re_pos (hreal w hw)
  · intro w hw
    apply Complex.Gammaℝ_ne_zero_of_re_pos
    have hwpos := hreal w hw
    exact
      (Eq.trans (div_pos hwpos zero_lt_two)
        (Complex.div_ofReal_re w 2).symm)

theorem not_explicitFormulaContourSingularPoint_of_rightHalfPlane_closedBall_owner
    (z : ℂ) (R : ℝ) (hR : 0 < R) (hcenter : R < z.re)
    (hzero : ∀ w : ℂ, w ∈ Metric.closedBall z R → w ≠ 0)
    (hone : ∀ w : ℂ, w ∈ Metric.closedBall z R → w ≠ 1)
    (hcompleted : ∀ w : ℂ, w ∈ Metric.closedBall z R →
      completedRiemannZeta w ≠ 0) :
    ∀ w : ℂ, w ∈ Metric.closedBall z R →
      ¬ explicitFormulaContourSingularPoint w := by
  obtain ⟨hgamma, hgammaHalf⟩ :=
    gamma_zero_loci_avoid_rightHalfPlane_closedBall_owner
      z R hR hcenter
  intro w hw hsingular
  rcases hsingular with hzero' | hone' | hgamma' | hgammaHalf' | hcompleted'
  · exact hzero w hw hzero'
  · exact hone w hw hone'
  · exact hgamma w hw hgamma'
  · exact hgammaHalf w hw hgammaHalf'
  · exact hcompleted w hw hcompleted'.2.2

theorem zetaSideFactor_rightHalfPlane_closedBall_regular_package_owner
    (z : ℂ) (R : ℝ) (hR : 0 < R) (hcenter : R < z.re)
    (hzero : ∀ w : ℂ, w ∈ Metric.closedBall z R → w ≠ 0)
    (hone : ∀ w : ℂ, w ∈ Metric.closedBall z R → w ≠ 1)
    (hcompleted : ∀ w : ℂ, w ∈ Metric.closedBall z R →
      completedRiemannZeta w ≠ 0) :
    DiffContOnCl ℂ zetaSideFactor (Metric.ball z R) ∧
      (∀ w : ℂ, w ∈ Metric.closedBall z R → zetaSideFactor w ≠ 0) := by
  have hregular : ∀ w : ℂ, w ∈ Metric.closedBall z R →
      ¬ explicitFormulaContourSingularPoint w :=
    not_explicitFormulaContourSingularPoint_of_rightHalfPlane_closedBall_owner
      z R hR hcenter hzero hone hcompleted
  have hdiff : DiffContOnCl ℂ zetaSideFactor (Metric.ball z R) :=
    zetaSideFactor_diffContOnCl_of_closedBall_nonsingular
      z R hregular
  have hne : ∀ w : ℂ, w ∈ Metric.closedBall z R → zetaSideFactor w ≠ 0 := by
    intro w hw
    exact zetaSideFactor_ne_zero
      (explicitFormulaContourSingularPoint.completedRiemannZeta_ne_zero_of_not
        (hregular w hw))
      (explicitFormulaContourSingularPoint.gamma_ne_zero_of_not
        (hregular w hw))
  exact ⟨hdiff, hne⟩

/- The zeta-side factor has the same compact-carrier two-sided norm package
   once the carrier is zero-excised. -/
theorem exists_zetaSideFactor_two_sided_norm_bounds_on_compact_carrier
    {a b : ℝ}
    (E : CompletedZetaZeroExcisedStrip a b)
    (hcompact : IsCompact E.carrier)
    (hcarrier_nonempty : E.carrier.Nonempty)
    (hcontinuous : ContinuousOn zetaSideFactor E.carrier) :
    ∃ δ A : ℝ, 0 < δ ∧ 0 ≤ A ∧
      (∀ z : ℂ, z ∈ E.carrier → δ ≤ ‖zetaSideFactor z‖) ∧
      (∀ z : ℂ, z ∈ E.carrier → ‖zetaSideFactor z‖ ≤ A) := by
  obtain ⟨δ, hδ, hδ_bound⟩ :=
    exists_zetaSideFactor_positive_lower_bound_of_compact_carrier
      E hcompact hcarrier_nonempty hcontinuous
  obtain ⟨A, hA, hA_bound⟩ :=
    exists_norm_upper_bound_of_isCompact_of_continuousOn
      (s := E.carrier) hcompact hcontinuous
  exact ⟨δ, A, hδ, hA, hδ_bound, hA_bound⟩

def rightHalfPlaneClosedBallZeroExcisedStrip
    (z : ℂ) (R : ℝ)
    (hzero : ∀ w : ℂ, w ∈ Metric.closedBall z R → w ≠ 0)
    (hone : ∀ w : ℂ, w ∈ Metric.closedBall z R → w ≠ 1)
    (hcompleted : ∀ w : ℂ, w ∈ Metric.closedBall z R →
      completedRiemannZeta w ≠ 0)
    (hgamma : ∀ w : ℂ, w ∈ Metric.closedBall z R → Complex.Gammaℝ w ≠ 0) :
    CompletedZetaZeroExcisedStrip (z.re - R) (z.re + R) :=
  { carrier := Metric.closedBall z R
    in_strip := by
      intro w hw
      have hdist : ‖w - z‖ ≤ R := hw
      have hcoord : ‖(w - z).re‖ ≤ R :=
        (norm_re_le_norm (w - z)).trans hdist
      have hbounds := abs_le.mp hcoord
      constructor
      · have hadd := add_le_add_left hbounds.1 z.re
        calc
          z.re - R = z.re + -R := sub_eq_add_neg z.re R
          _ ≤ z.re + (w - z).re := hadd
          _ = w.re := by
            exact Eq.trans (congrArg (fun x : ℝ => z.re + x) (Complex.sub_re w z))
              (Eq.trans (add_comm z.re (w.re - z.re)) (sub_add_cancel w.re z.re))
      · have hadd := add_le_add_left hbounds.2 z.re
        calc
          w.re = z.re + (w - z).re := by
            exact Eq.trans
              (Eq.trans (add_comm z.re (w.re - z.re)) (sub_add_cancel w.re z.re)).symm
              (congrArg (fun x : ℝ => z.re + x) (Complex.sub_re w z)).symm
          _ ≤ z.re + R := hadd
    ne_zero := hzero
    ne_one := hone
    zeta_ne_zero := hcompleted
    gamma_ne_zero := hgamma }

theorem zetaSideFactor_rightHalfPlane_closedBall_two_sided_bounds_owner
    (z : ℂ) (R : ℝ) (hR : 0 < R) (hcenter : R < z.re)
    (hzero : ∀ w : ℂ, w ∈ Metric.closedBall z R → w ≠ 0)
    (hone : ∀ w : ℂ, w ∈ Metric.closedBall z R → w ≠ 1)
    (hcompleted : ∀ w : ℂ, w ∈ Metric.closedBall z R →
      completedRiemannZeta w ≠ 0)
    (hgamma : ∀ w : ℂ, w ∈ Metric.closedBall z R → Complex.Gammaℝ w ≠ 0) :
    ∃ lower upper : ℝ,
      0 < lower ∧ 0 ≤ upper ∧
        (∀ w : ℂ, w ∈ Metric.closedBall z R →
          lower ≤ ‖zetaSideFactor w‖) ∧
        (∀ w : ℂ, w ∈ Metric.closedBall z R →
          ‖zetaSideFactor w‖ ≤ upper) := by
  let E := rightHalfPlaneClosedBallZeroExcisedStrip
    z R hzero hone hcompleted hgamma
  have hregular := zetaSideFactor_rightHalfPlane_closedBall_regular_package_owner
    z R hR hcenter hzero hone hcompleted
  have hcontinuous : ContinuousOn zetaSideFactor E.carrier := by
    exact closedBall_continuousOn_of_diffContOnCl z R hR hregular.1
  obtain ⟨lower, hlower, hlower_bound⟩ :=
    exists_positive_norm_lower_bound_of_isCompact_of_continuousOn
      (s := E.carrier) isCompact_closedBall
      ⟨z, Metric.mem_closedBall_self (le_of_lt hR)⟩
      hcontinuous E.zeta_ne_zero
  obtain ⟨upper, hupper, hupper_bound⟩ :=
    exists_norm_upper_bound_of_isCompact_of_continuousOn
      (s := E.carrier) isCompact_closedBall hcontinuous
  exact ⟨lower, upper, hlower, hupper, hlower_bound, hupper_bound⟩

theorem zetaSideFactor_two_sided_norm_bounds_on_pair_balls_owner
    (zTop zBottom : ℂ) (R : ℝ)
    (hR : 0 < R) (hTopCenter : R < zTop.re)
    (hBottomCenter : R < zBottom.re)
    (hTopZero : ∀ w : ℂ, w ∈ Metric.closedBall zTop R → w ≠ 0)
    (hTopOne : ∀ w : ℂ, w ∈ Metric.closedBall zTop R → w ≠ 1)
    (hTopCompleted : ∀ w : ℂ, w ∈ Metric.closedBall zTop R →
      completedRiemannZeta w ≠ 0)
    (hTopGamma : ∀ w : ℂ, w ∈ Metric.closedBall zTop R →
      Complex.Gammaℝ w ≠ 0)
    (hBottomZero : ∀ w : ℂ, w ∈ Metric.closedBall zBottom R → w ≠ 0)
    (hBottomOne : ∀ w : ℂ, w ∈ Metric.closedBall zBottom R → w ≠ 1)
    (hBottomCompleted : ∀ w : ℂ, w ∈ Metric.closedBall zBottom R →
      completedRiemannZeta w ≠ 0)
    (hBottomGamma : ∀ w : ℂ, w ∈ Metric.closedBall zBottom R →
      Complex.Gammaℝ w ≠ 0) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 ≤ upper ∧
      (∀ w : ℂ, w ∈ Metric.closedBall zTop R →
        lower ≤ ‖zetaSideFactor w‖) ∧
      (∀ w : ℂ, w ∈ Metric.closedBall zTop R →
        ‖zetaSideFactor w‖ ≤ upper) ∧
      (∀ w : ℂ, w ∈ Metric.closedBall zBottom R →
        lower ≤ ‖zetaSideFactor w‖) ∧
      (∀ w : ℂ, w ∈ Metric.closedBall zBottom R →
        ‖zetaSideFactor w‖ ≤ upper) := by
  obtain ⟨lowerTop, upperTop, hlt, hut, hlt_bound, hut_bound⟩ :=
    zetaSideFactor_rightHalfPlane_closedBall_two_sided_bounds_owner
      zTop R hR hTopCenter hTopZero hTopOne hTopCompleted hTopGamma
  obtain ⟨lowerBottom, upperBottom, hlb, hub, hlb_bound, hub_bound⟩ :=
    zetaSideFactor_rightHalfPlane_closedBall_two_sided_bounds_owner
      zBottom R hR hBottomCenter hBottomZero hBottomOne hBottomCompleted
      hBottomGamma
  refine ⟨min lowerTop lowerBottom, max upperTop upperBottom,
    lt_min hlt hlb, le_max_left upperTop upperBottom, ?_, ?_, ?_, ?_⟩
  · intro w hw
    exact (min_le_left lowerTop lowerBottom).trans (hlt_bound w hw)
  · intro w hw
    exact (hut_bound w hw).trans (le_max_left upperTop upperBottom)
  · intro w hw
    exact (min_le_right lowerTop lowerBottom).trans (hlb_bound w hw)
  · intro w hw
    exact (hub_bound w hw).trans (le_max_right upperTop upperBottom)

theorem zetaSideFactor_cauchy_log_derivative_bound_on_pair_balls_owner
    (zTop zBottom : ℂ) (RTop RBottom : ℝ) (N : ℕ)
    (hTopRadius : 0 < RTop)
    (hBottomRadius : 0 < RBottom)
    (hTopDiff : DiffContOnCl ℂ zetaSideFactor
      (Metric.ball zTop RTop))
    (hBottomDiff : DiffContOnCl ℂ zetaSideFactor
      (Metric.ball zBottom RBottom))
    (hTopSphere : ∀ w : ℂ, w ∈ Metric.sphere zTop RTop →
      ‖zetaSideFactor w‖ ≤ 1 * (1 + ‖zTop.im‖) ^ N)
    (hBottomSphere : ∀ w : ℂ, w ∈ Metric.sphere zBottom RBottom →
      ‖zetaSideFactor w‖ ≤ 1 * (1 + ‖zBottom.im‖) ^ N)
    (hTopLower : 0 < ‖zetaSideFactor zTop‖)
    (hBottomLower : 0 < ‖zetaSideFactor zBottom‖) :
    ‖deriv zetaSideFactor zTop / zetaSideFactor zTop‖ ≤
        (1 / RTop) / ‖zetaSideFactor zTop‖ *
          (1 + ‖zTop.im‖) ^ N ∧
      ‖deriv zetaSideFactor zBottom / zetaSideFactor zBottom‖ ≤
        (1 / RBottom) / ‖zetaSideFactor zBottom‖ *
          (1 + ‖zBottom.im‖) ^ N := by
  constructor
  · exact zetaSideFactor_cauchy_log_derivative_bound_owner
      zTop N RTop 1 ‖zetaSideFactor zTop‖ hTopRadius hTopDiff
      hTopSphere hTopLower hTopLower.le
  · exact zetaSideFactor_cauchy_log_derivative_bound_owner
      zBottom N RBottom 1 ‖zetaSideFactor zBottom‖ hBottomRadius hBottomDiff
      hBottomSphere hBottomLower hBottomLower.le

/- This is the owner-level zeta construction used by the scheduled carrier
   layer: regularity supplies continuity, zero/pole separation supplies
   nonvanishing, and compactness turns those facts into quantitative bounds. -/
theorem zetaSideFactor_compact_carrier_analytic_package_owner
    {a b : ℝ}
    (E : CompletedZetaZeroExcisedStrip a b)
    (hcompact : IsCompact E.carrier)
    (hcarrier_nonempty : E.carrier.Nonempty)
    (hcontinuous : ContinuousOn zetaSideFactor E.carrier) :
    (∀ z : ℂ, z ∈ E.carrier → zetaSideFactor z ≠ 0) ∧
      ∃ lower upper : ℝ,
        0 < lower ∧ 0 ≤ upper ∧
          (∀ z : ℂ, z ∈ E.carrier → lower ≤ ‖zetaSideFactor z‖) ∧
          (∀ z : ℂ, z ∈ E.carrier → ‖zetaSideFactor z‖ ≤ upper) := by
  have hne : ∀ z : ℂ, z ∈ E.carrier → zetaSideFactor z ≠ 0 :=
    E.zeta_ne_zero
  obtain ⟨lower, upper, hlower, hupper, hlower_bound, hupper_bound⟩ :=
    exists_zetaSideFactor_two_sided_norm_bounds_on_compact_carrier
      E hcompact hcarrier_nonempty hcontinuous
  exact ⟨hne, lower, upper, hlower, hupper, hlower_bound, hupper_bound⟩

/- The two horizontal faces share one inverse-Gamma package.  The radius
   condition is exactly the geometric right-half-plane condition for both
   path centers, so the constants are obtained by taking minima/maxima of the
   two compact-ball bounds. -/
theorem inverseGamma_two_sided_norm_bounds_on_horizontal_pair_balls_owner
    (r : ExplicitFormulaRectangle) (x R : ℝ)
    (hcx : r.c ≤ x) (hR_pos : 0 < R) (hR : R < r.c) :
    ∃ lower upper : ℝ, 0 < lower ∧ 0 ≤ upper ∧
      (∀ w : ℂ, w ∈ Metric.closedBall
          (zetaCompletedExplicitFormulaTopPath r x) R →
        lower ≤ ‖(Complex.Gammaℝ w)⁻¹‖) ∧
      (∀ w : ℂ, w ∈ Metric.closedBall
          (zetaCompletedExplicitFormulaTopPath r x) R →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤ upper) ∧
      (∀ w : ℂ, w ∈ Metric.closedBall
          (zetaCompletedExplicitFormulaBottomPath r x) R →
        lower ≤ ‖(Complex.Gammaℝ w)⁻¹‖) ∧
      (∀ w : ℂ, w ∈ Metric.closedBall
          (zetaCompletedExplicitFormulaBottomPath r x) R →
        ‖(Complex.Gammaℝ w)⁻¹‖ ≤ upper) := by
  have htop_center : R < (zetaCompletedExplicitFormulaTopPath r x).re := by
    calc
      R < r.c := hR
      _ ≤ x := hcx
      _ = (zetaCompletedExplicitFormulaTopPath r x).re :=
        (zetaCompletedExplicitFormulaTopPath_re_eq r x).symm
  have hbottom_center : R < (zetaCompletedExplicitFormulaBottomPath r x).re := by
    calc
      R < r.c := hR
      _ ≤ x := hcx
      _ = (zetaCompletedExplicitFormulaBottomPath r x).re :=
        (zetaCompletedExplicitFormulaBottomPath_re_eq r x).symm
  obtain ⟨lowerTop, upperTop, hlt, hut, hlt_bound, hut_bound⟩ :=
    exists_inverseGamma_two_sided_norm_bounds_on_rightHalfPlane_closedBall
      (zetaCompletedExplicitFormulaTopPath r x) R hR_pos htop_center
  obtain ⟨lowerBottom, upperBottom, hlb, hub, hlb_bound, hub_bound⟩ :=
    exists_inverseGamma_two_sided_norm_bounds_on_rightHalfPlane_closedBall
      (zetaCompletedExplicitFormulaBottomPath r x) R hR_pos hbottom_center
  refine ⟨min lowerTop lowerBottom, max upperTop upperBottom,
    lt_min hlt hlb, le_max_left upperTop upperBottom, ?_, ?_, ?_, ?_⟩
  · intro w hw
    exact (min_le_left lowerTop lowerBottom).trans (hlt_bound w hw)
  · intro w hw
    exact (hut_bound w hw).trans (le_max_left upperTop upperBottom)
  · intro w hw
    exact (min_le_right lowerTop lowerBottom).trans (hlb_bound w hw)
  · intro w hw
    exact (hub_bound w hw).trans (le_max_right upperTop upperBottom)

theorem inverseGamma_diffContOnCl_on_horizontal_pair_balls_owner
    (r : ExplicitFormulaRectangle) (x R : ℝ) (hR_pos : 0 < R) :
    DiffContOnCl ℂ (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (Metric.ball (zetaCompletedExplicitFormulaTopPath r x) R) ∧
      DiffContOnCl ℂ (fun w : ℂ => (Complex.Gammaℝ w)⁻¹)
        (Metric.ball (zetaCompletedExplicitFormulaBottomPath r x) R) := by
  exact ⟨
    inverseGamma_diffContOnCl_on_ball_owner
      (zetaCompletedExplicitFormulaTopPath r x) R,
    inverseGamma_diffContOnCl_on_ball_owner
      (zetaCompletedExplicitFormulaBottomPath r x) R⟩

theorem inverseGamma_cauchy_log_derivative_bound_on_pair_balls_owner
    (zTop zBottom : ℂ) (R : ℝ) (hR : 0 < R)
    (hTopNe : ∀ w : ℂ, w ∈ Metric.closedBall zTop R →
      (Complex.Gammaℝ w)⁻¹ ≠ 0)
    (hBottomNe : ∀ w : ℂ, w ∈ Metric.closedBall zBottom R →
      (Complex.Gammaℝ w)⁻¹ ≠ 0) :
    (∃ BTop : ℝ, 0 < BTop ∧
      ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) zTop /
          (Complex.Gammaℝ zTop)⁻¹‖ ≤ BTop) ∧
    (∃ BBottom : ℝ, 0 < BBottom ∧
      ‖deriv (fun w : ℂ => (Complex.Gammaℝ w)⁻¹) zBottom /
          (Complex.Gammaℝ zBottom)⁻¹‖ ≤ BBottom) := by
  constructor
  · exact inverseGamma_cauchy_log_derivative_bound_on_closedBall_owner
      zTop R hR hTopNe
  · exact inverseGamma_cauchy_log_derivative_bound_on_closedBall_owner
      zBottom R hR hBottomNe

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
