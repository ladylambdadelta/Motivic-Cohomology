import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactiveGeometry

/-!
# Deterministic derivative gaps for finite inactive modes

The stationary identity rewrites each endpoint derivative gap as a reciprocal
center difference.  The one-third center separation then yields explicit
curvature-scale lower bounds, uniformly over each finite inactive class.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.logarithmicPhaseLeftInactiveGap_eq_center_fraction
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) {x : ℝ}
    (hx : 0 < x) :
    Complex.logarithmicPhaseLeftInactiveGap t m x =
      ‖t‖ *
        (x - Complex.logarithmicPhaseFourierStationaryPoint t m) /
          (Complex.logarithmicPhaseFourierStationaryPoint t m * x) := by
  have hcenterPos :=
    Complex.logarithmicPhaseFourierStationaryPoint_pos t ht hm
  have hangular :=
    Complex.logarithmicPhaseAngular_eq_norm_div_center t ht hm
  unfold Complex.logarithmicPhaseLeftInactiveGap
  exact Eq.trans
    (congrArg (fun value : ℝ => value - ‖t‖ / x) hangular)
    (Real.div_sub_div_eq_mul_sub_div_mul
      ‖t‖
      (Complex.logarithmicPhaseFourierStationaryPoint t m) x
      (ne_of_gt hcenterPos) (ne_of_gt hx))

theorem Complex.logarithmicPhaseRightInactiveGap_eq_center_fraction
    (t : ℝ) (ht : 1 ≤ ‖t‖) {m : ℤ} (hm : m < 0) {x : ℝ}
    (hx : 0 < x) :
    Complex.logarithmicPhaseRightInactiveGap t m x =
      ‖t‖ *
        (Complex.logarithmicPhaseFourierStationaryPoint t m - x) /
          (x * Complex.logarithmicPhaseFourierStationaryPoint t m) := by
  have hcenterPos :=
    Complex.logarithmicPhaseFourierStationaryPoint_pos t ht hm
  have hangular :=
    Complex.logarithmicPhaseAngular_eq_norm_div_center t ht hm
  unfold Complex.logarithmicPhaseRightInactiveGap
  have hsub := Real.div_sub_div_eq_mul_sub_div_mul
    ‖t‖ x (Complex.logarithmicPhaseFourierStationaryPoint t m)
    (ne_of_gt hx) (ne_of_gt hcenterPos)
  exact Eq.trans
    (congrArg (fun value : ℝ => ‖t‖ / x - value) hangular)
    hsub

theorem Real.center_fraction_left_lower
    {center x d : ℝ}
    (hcenter : 0 < center) (hcenterX : center ≤ x)
    (hd : 0 ≤ d) (hgap : d ≤ x - center) :
    d / x ^ 2 ≤ (x - center) / (center * x) := by
  have hx : 0 < x := lt_of_lt_of_le hcenter hcenterX
  have hgapNonneg : 0 ≤ x - center := sub_nonneg.mpr hcenterX
  have hdenominator : center * x ≤ x ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hcenterX hx.le
    exact Eq.subst (motive := fun value : ℝ => center * x ≤ value)
      (pow_two x).symm hmul
  have hfirst : d / x ^ 2 ≤ (x - center) / x ^ 2 :=
    div_le_div_of_nonneg_right hgap (sq_nonneg x)
  have hsecond :
      (x - center) / x ^ 2 ≤ (x - center) / (center * x) :=
    div_le_div_of_nonneg_left hgapNonneg (mul_pos hcenter hx) hdenominator
  exact le_trans hfirst hsecond

theorem Real.center_fraction_right_lower
    {x center d : ℝ}
    (hx : 0 < x) (hd : 0 < d)
    (hgap : x + d ≤ center) :
    d / (x * (x + d)) ≤ (center - x) / (x * center) := by
  have hxd : 0 < x + d := add_pos hx hd
  have hcenter : 0 < center := lt_of_lt_of_le hxd hgap
  have hgapNonneg : 0 ≤ center - x :=
    sub_nonneg.mpr (le_trans (le_add_of_nonneg_right hd.le) hgap)
  have hratioNumerator :
      d * center ≤ (center - x) * (x + d) := by
    have hgapComm : d + x ≤ center :=
      Eq.subst (motive := fun value : ℝ => value ≤ center)
        (add_comm x d) hgap
    have hdLe : d ≤ center - x := (le_sub_iff_add_le).mpr hgapComm
    have hdx : d * x ≤ (center - x) * x :=
      mul_le_mul_of_nonneg_right hdLe hx.le
    have hadd := add_le_add_right hdx (d * (center - x))
    have hleft : d * center = d * x + d * (center - x) := by
      have hcenterSplit : x + (center - x) = center :=
        Eq.trans (add_comm x (center - x))
          (sub_add_cancel center x)
      exact Eq.trans
        (congrArg (fun value : ℝ => d * value) hcenterSplit.symm)
        (mul_add d x (center - x))
    have hright :
        (center - x) * x + d * (center - x) =
          (center - x) * (x + d) := by
      exact Eq.trans
        (congrArg
          (fun value : ℝ => (center - x) * x + value)
          (mul_comm d (center - x)))
        (mul_add (center - x) x d).symm
    exact Eq.subst (motive := fun value : ℝ => value ≤ _)
      hleft.symm
      (Eq.subst (motive := fun value : ℝ =>
          d * x + d * (center - x) ≤ value)
        hright hadd)
  have hdivideCenter :
      d / (x + d) ≤ (center - x) / center :=
    (div_le_div_iff₀ hxd hcenter).mpr hratioNumerator
  have hdivideX := div_le_div_of_nonneg_right hdivideCenter hx.le
  have hleft : (d / (x + d)) / x = d / (x * (x + d)) := by
    exact (div_div d (x + d) x).trans
      (congrArg (fun value : ℝ => d / value) (mul_comm (x + d) x))
  have hright : ((center - x) / center) / x =
      (center - x) / (x * center) := by
    exact (div_div (center - x) center x).trans
      (congrArg (fun value : ℝ => (center - x) / value)
        (mul_comm center x))
  exact Eq.subst (motive := fun value : ℝ => value ≤
      (center - x) / (x * center)) hleft
    (Eq.subst (motive := fun value : ℝ => d / (x + d) / x ≤ value)
      hright hdivideX)

theorem Complex.logarithmicPhaseLeftInactiveGap_ge_curvature_third
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b) :
    ‖t‖ * ((1 : ℝ) / 3) /
        (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2 ≤
      Complex.logarithmicPhaseLeftInactiveGap t m
        (Complex.logarithmicPhaseQuantitativeSupportLeft a) := by
  have hmNeg :=
    ((Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
      t a b m).mp hm).2.1
  have hx := Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha
  have hcenter := Complex.logarithmicPhaseFourierStationaryPoint_pos t ht hmNeg
  have hgap :=
    Complex.logarithmicPhasePoissonLeftInactive_one_third_center_gap
      t a b hab hm
  have honeThirdPos : (0 : ℝ) < 1 / 3 :=
    div_pos zero_lt_one (Nat.cast_pos.mpr (Nat.succ_pos 2))
  have hgapPos : 0 <
      Complex.logarithmicPhaseQuantitativeSupportLeft a -
        Complex.logarithmicPhaseFourierStationaryPoint t m :=
    lt_trans honeThirdPos hgap
  have hfraction := Real.center_fraction_left_lower
    hcenter (le_of_lt (lt_of_sub_pos hgapPos))
    (div_nonneg zero_le_one (Nat.cast_nonneg 3)) hgap.le
  have hscaled := mul_le_mul_of_nonneg_left hfraction (norm_nonneg t)
  have hleftNormalize :
      ‖t‖ * (((1 : ℝ) / 3) /
        (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2) =
      ‖t‖ * ((1 : ℝ) / 3) /
        (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2 :=
    (mul_div_assoc ‖t‖ ((1 : ℝ) / 3) _).symm
  have hrightNormalize :
      ‖t‖ *
          ((Complex.logarithmicPhaseQuantitativeSupportLeft a -
              Complex.logarithmicPhaseFourierStationaryPoint t m) /
            (Complex.logarithmicPhaseFourierStationaryPoint t m *
              Complex.logarithmicPhaseQuantitativeSupportLeft a)) =
        ‖t‖ *
            (Complex.logarithmicPhaseQuantitativeSupportLeft a -
              Complex.logarithmicPhaseFourierStationaryPoint t m) /
          (Complex.logarithmicPhaseFourierStationaryPoint t m *
            Complex.logarithmicPhaseQuantitativeSupportLeft a) :=
    (mul_div_assoc ‖t‖
      (Complex.logarithmicPhaseQuantitativeSupportLeft a -
        Complex.logarithmicPhaseFourierStationaryPoint t m)
      (Complex.logarithmicPhaseFourierStationaryPoint t m *
        Complex.logarithmicPhaseQuantitativeSupportLeft a)).symm
  have hscaledRight :
      ‖t‖ * (((1 : ℝ) / 3) /
          (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2) ≤
        ‖t‖ *
            (Complex.logarithmicPhaseQuantitativeSupportLeft a -
              Complex.logarithmicPhaseFourierStationaryPoint t m) /
          (Complex.logarithmicPhaseFourierStationaryPoint t m *
            Complex.logarithmicPhaseQuantitativeSupportLeft a) :=
    Eq.subst
      (motive := fun value : ℝ =>
        ‖t‖ * (((1 : ℝ) / 3) /
          (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2) ≤ value)
      hrightNormalize hscaled
  have hscaledNormalized :
      ‖t‖ * ((1 : ℝ) / 3) /
          (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2 ≤
        ‖t‖ *
            (Complex.logarithmicPhaseQuantitativeSupportLeft a -
              Complex.logarithmicPhaseFourierStationaryPoint t m) /
          (Complex.logarithmicPhaseFourierStationaryPoint t m *
            Complex.logarithmicPhaseQuantitativeSupportLeft a) :=
    Eq.subst
      (motive := fun value : ℝ => value ≤
        ‖t‖ *
            (Complex.logarithmicPhaseQuantitativeSupportLeft a -
              Complex.logarithmicPhaseFourierStationaryPoint t m) /
          (Complex.logarithmicPhaseFourierStationaryPoint t m *
            Complex.logarithmicPhaseQuantitativeSupportLeft a))
      hleftNormalize hscaledRight
  exact Eq.subst
    (motive := fun value : ℝ =>
      ‖t‖ * ((1 : ℝ) / 3) /
          (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2 ≤ value)
    (Complex.logarithmicPhaseLeftInactiveGap_eq_center_fraction
      t ht hmNeg hx).symm
    hscaledNormalized

end

end LFunctions
end Boundary
