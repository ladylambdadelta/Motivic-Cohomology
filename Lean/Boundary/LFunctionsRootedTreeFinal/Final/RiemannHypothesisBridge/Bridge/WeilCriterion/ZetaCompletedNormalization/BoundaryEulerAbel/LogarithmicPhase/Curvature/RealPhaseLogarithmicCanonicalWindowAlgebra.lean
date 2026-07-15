import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicModeRangeCardinality

/-!
# Algebra of canonical logarithmic stationary windows

For a negative mode, write `x` for its stationary center and `r = sqrt x`.
The canonical central interval is `[x-r,x+r]`.  This owner records all exact
normalizations used to simplify the stationary packet majorant before any
inequality is applied.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.center_sub_center_sub_radius
    (center radius : ℝ) :
    center - (center - radius) = radius := by
  exact sub_sub_self center radius

theorem Real.center_add_radius_sub_center
    (center radius : ℝ) :
    center + radius - center = radius := by
  exact add_sub_cancel_left center radius

theorem Real.center_add_radius_sub_center_sub_radius
    (center radius : ℝ) :
    (center + radius) - (center - radius) = 2 * radius := by
  have hfirst :
      (center + radius) - (center - radius) = radius + radius := by
    exact Eq.trans
      (congrArg (fun value : ℝ => center + radius - value)
        (sub_eq_add_neg center radius))
      (Eq.trans
        (sub_sub (center + radius) center (-radius)).symm
        (Eq.trans
          (sub_neg_eq_add
            ((center + radius) - center) radius)
          (congrArg (fun value : ℝ => value + radius)
            (add_sub_cancel_left center radius))))
  exact Eq.trans hfirst (two_mul radius).symm

theorem Complex.logarithmicPhaseCanonical_center_sub_left_eq_radius
    (t : ℝ) (m : ℤ) :
    Complex.logarithmicPhaseFourierStationaryPoint t m -
        (Complex.logarithmicPhaseFourierStationaryPoint t m -
          Complex.logarithmicPhasePoissonCanonicalRadius t m) =
      Complex.logarithmicPhasePoissonCanonicalRadius t m := by
  exact Real.center_sub_center_sub_radius _ _

theorem Complex.logarithmicPhaseCanonical_right_sub_center_eq_radius
    (t : ℝ) (m : ℤ) :
    (Complex.logarithmicPhaseFourierStationaryPoint t m +
        Complex.logarithmicPhasePoissonCanonicalRadius t m) -
      Complex.logarithmicPhaseFourierStationaryPoint t m =
      Complex.logarithmicPhasePoissonCanonicalRadius t m := by
  exact Real.center_add_radius_sub_center _ _

theorem Complex.logarithmicPhaseCanonical_centralLength_eq_twoRadius
    (t : ℝ) (m : ℤ) :
    (Complex.logarithmicPhaseFourierStationaryPoint t m +
        Complex.logarithmicPhasePoissonCanonicalRadius t m) -
      (Complex.logarithmicPhaseFourierStationaryPoint t m -
        Complex.logarithmicPhasePoissonCanonicalRadius t m) =
      2 * Complex.logarithmicPhasePoissonCanonicalRadius t m := by
  exact Real.center_add_radius_sub_center_sub_radius _ _

theorem Complex.logarithmicPhaseCanonical_leftGap_eq
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    (2 * Real.pi * (-(m : ℝ))) *
        (Complex.logarithmicPhaseFourierStationaryPoint t m -
          (Complex.logarithmicPhaseFourierStationaryPoint t m -
            Complex.logarithmicPhasePoissonCanonicalRadius t m)) /
        (Complex.logarithmicPhaseFourierStationaryPoint t m -
          Complex.logarithmicPhasePoissonCanonicalRadius t m) =
      (‖t‖ /
        Complex.logarithmicPhaseFourierStationaryPoint t m) *
        Complex.logarithmicPhasePoissonCanonicalRadius t m /
        (Complex.logarithmicPhaseFourierStationaryPoint t m -
          Complex.logarithmicPhasePoissonCanonicalRadius t m) := by
  have hangular := Complex.logarithmicPhaseAngular_eq_norm_div_center
    t ht hm
  have hdistance :=
    Complex.logarithmicPhaseCanonical_center_sub_left_eq_radius t m
  exact congrArg₂
    (fun angular distance : ℝ =>
      angular * distance /
        (Complex.logarithmicPhaseFourierStationaryPoint t m -
          Complex.logarithmicPhasePoissonCanonicalRadius t m))
    hangular hdistance

theorem Complex.logarithmicPhaseCanonical_rightGap_eq
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) (b : ℤ) :
    (2 * Real.pi * (-(m : ℝ))) *
        ((Complex.logarithmicPhaseFourierStationaryPoint t m +
          Complex.logarithmicPhasePoissonCanonicalRadius t m) -
          Complex.logarithmicPhaseFourierStationaryPoint t m) /
        (b : ℝ) =
      (‖t‖ /
        Complex.logarithmicPhaseFourierStationaryPoint t m) *
        Complex.logarithmicPhasePoissonCanonicalRadius t m /
        (b : ℝ) := by
  have hangular := Complex.logarithmicPhaseAngular_eq_norm_div_center
    t ht hm
  have hdistance :=
    Complex.logarithmicPhaseCanonical_right_sub_center_eq_radius t m
  exact congrArg₂
    (fun angular distance : ℝ =>
      angular * distance / (b : ℝ))
    hangular hdistance

theorem Complex.logarithmicPhaseCanonical_norm_mul_radius_eq_norm_div_radius
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) :
    (‖t‖ / Complex.logarithmicPhaseFourierStationaryPoint t m) *
        Complex.logarithmicPhasePoissonCanonicalRadius t m =
      ‖t‖ / Complex.logarithmicPhasePoissonCanonicalRadius t m := by
  have hradius :=
    Complex.logarithmicPhasePoissonCanonicalRadius_pos t ht hm
  have hsquare :=
    Complex.logarithmicPhasePoissonCanonicalRadius_sq t ht hm
  have hcenter :=
    Complex.logarithmicPhaseFourierStationaryPoint_pos t ht hm
  have hdivision :
      (‖t‖ / Complex.logarithmicPhaseFourierStationaryPoint t m) *
          Complex.logarithmicPhasePoissonCanonicalRadius t m =
        ‖t‖ * Complex.logarithmicPhasePoissonCanonicalRadius t m /
          Complex.logarithmicPhaseFourierStationaryPoint t m :=
    div_mul_eq_mul_div ‖t‖
      (Complex.logarithmicPhasePoissonCanonicalRadius t m)
      (Complex.logarithmicPhaseFourierStationaryPoint t m)
  have hcancel :
      ‖t‖ * Complex.logarithmicPhasePoissonCanonicalRadius t m /
          Complex.logarithmicPhaseFourierStationaryPoint t m =
        ‖t‖ / Complex.logarithmicPhasePoissonCanonicalRadius t m := by
    have hradiusNe :
        Complex.logarithmicPhasePoissonCanonicalRadius t m ≠ 0 :=
      ne_of_gt hradius
    have hradiusCancel :
        (‖t‖ / Complex.logarithmicPhasePoissonCanonicalRadius t m) *
            Complex.logarithmicPhasePoissonCanonicalRadius t m = ‖t‖ :=
      div_mul_cancel₀ ‖t‖ hradiusNe
    have hright :
        (‖t‖ / Complex.logarithmicPhasePoissonCanonicalRadius t m) *
            Complex.logarithmicPhaseFourierStationaryPoint t m =
          ‖t‖ * Complex.logarithmicPhasePoissonCanonicalRadius t m := by
      exact Eq.trans
        (congrArg
          (fun value : ℝ =>
            (‖t‖ /
              Complex.logarithmicPhasePoissonCanonicalRadius t m) * value)
          hsquare.symm)
        (Eq.trans
          (mul_assoc
            (‖t‖ / Complex.logarithmicPhasePoissonCanonicalRadius t m)
            (Complex.logarithmicPhasePoissonCanonicalRadius t m)
            (Complex.logarithmicPhasePoissonCanonicalRadius t m)).symm
          (congrArg
            (fun value : ℝ =>
              value * Complex.logarithmicPhasePoissonCanonicalRadius t m)
            hradiusCancel))
    exact (div_eq_iff (ne_of_gt hcenter)).mpr hright.symm
  exact Eq.trans hdivision hcancel

theorem Complex.logarithmicPhaseCanonical_radius_le_sqrt_b
    (t : ℝ) {a b m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b)
    (hb : 0 ≤ b) :
    Complex.logarithmicPhasePoissonCanonicalRadius t m ≤
      Real.sqrt (b : ℝ) := by
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonCanonicalInteriorModes_iff
      t a b m).mp hm
  have hradiusNonneg :=
    Complex.logarithmicPhasePoissonCanonicalRadius_nonneg t m
  have hcenterLe :
      Complex.logarithmicPhaseFourierStationaryPoint t m ≤ (b : ℝ) := by
    exact le_trans
      (le_add_of_nonneg_right hradiusNonneg)
      hmem.2.2.2
  unfold Complex.logarithmicPhasePoissonCanonicalRadius
  exact Real.sqrt_le_sqrt hcenterLe

theorem Complex.logarithmicPhaseCanonical_radius_ge_sqrt_a
    (t : ℝ) {a b m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b)
    (ha : 0 ≤ a) :
    Real.sqrt (a : ℝ) ≤
      Complex.logarithmicPhasePoissonCanonicalRadius t m := by
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonCanonicalInteriorModes_iff
      t a b m).mp hm
  have hradiusNonneg :=
    Complex.logarithmicPhasePoissonCanonicalRadius_nonneg t m
  have haCenter : (a : ℝ) ≤
      Complex.logarithmicPhaseFourierStationaryPoint t m := by
    exact le_trans hmem.2.2.1
      (sub_le_self _ hradiusNonneg)
  unfold Complex.logarithmicPhasePoissonCanonicalRadius
  exact Real.sqrt_le_sqrt haCenter

theorem Complex.logarithmicPhaseCanonical_centralLength_le_two_sqrt_b
    (t : ℝ) {a b m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b)
    (hb : 0 ≤ b) :
    (Complex.logarithmicPhaseFourierStationaryPoint t m +
        Complex.logarithmicPhasePoissonCanonicalRadius t m) -
      (Complex.logarithmicPhaseFourierStationaryPoint t m -
        Complex.logarithmicPhasePoissonCanonicalRadius t m) ≤
      2 * Real.sqrt (b : ℝ) := by
  have hradius :=
    Complex.logarithmicPhaseCanonical_radius_le_sqrt_b t hm hb
  have hscaled := mul_le_mul_of_nonneg_left hradius (Nat.cast_nonneg 2)
  exact Eq.subst
    (motive := fun value : ℝ => value ≤ 2 * Real.sqrt (b : ℝ))
    (Complex.logarithmicPhaseCanonical_centralLength_eq_twoRadius t m).symm
    hscaled

end
end LFunctions
end Boundary
