import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactiveFarCrossingArithmetic

/-!
# Balanced separation geometry for finite far reciprocal gaps

Far membership says that the balanced stationary window misses the principal
block.  This owner translates that statement into strict center-distance,
derivative-gap, and reciprocal inequalities at the nearest endpoint.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.logarithmicPhaseFiniteLeftFar_radius_lt_endpoint_sub_center
    {t : ℝ} {a b m : ℤ}
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftFarModes t a b) :
    Complex.logarithmicPhaseBProcessRadius t m <
      (a : ℝ) - Complex.logarithmicPhaseFourierStationaryPoint t m := by
  have hfar :=
    ((Complex.mem_logarithmicPhaseFiniteLeftFarModes_iff
      t a b m).mp hm).2
  unfold Complex.logarithmicPhaseBProcessWindowRight at hfar
  have hcommuted :
      Complex.logarithmicPhaseBProcessRadius t m +
          Complex.logarithmicPhaseFourierStationaryPoint t m < (a : ℝ) :=
    Eq.subst
      (motive := fun value : ℝ => value < (a : ℝ))
      (add_comm
        (Complex.logarithmicPhaseFourierStationaryPoint t m)
        (Complex.logarithmicPhaseBProcessRadius t m))
      hfar
  exact (lt_sub_iff_add_lt).mpr hcommuted

theorem Complex.logarithmicPhaseFiniteRightFar_radius_lt_center_sub_endpoint
    {t : ℝ} {a b m : ℤ}
    (hm : m ∈ Complex.logarithmicPhaseFiniteRightFarModes t a b) :
    Complex.logarithmicPhaseBProcessRadius t m <
      Complex.logarithmicPhaseFourierStationaryPoint t m - (b : ℝ) := by
  have hfar :=
    ((Complex.mem_logarithmicPhaseFiniteRightFarModes_iff
      t a b m).mp hm).2
  unfold Complex.logarithmicPhaseBProcessWindowLeft at hfar
  have hendpointAddRadius :
      (b : ℝ) + Complex.logarithmicPhaseBProcessRadius t m <
        Complex.logarithmicPhaseFourierStationaryPoint t m :=
    (lt_sub_iff_add_lt).mp hfar
  have hradiusAddEndpoint :
      Complex.logarithmicPhaseBProcessRadius t m + (b : ℝ) <
        Complex.logarithmicPhaseFourierStationaryPoint t m :=
    Eq.subst
      (motive := fun value : ℝ =>
        value < Complex.logarithmicPhaseFourierStationaryPoint t m)
      (add_comm (b : ℝ)
        (Complex.logarithmicPhaseBProcessRadius t m))
      hendpointAddRadius
  exact (lt_sub_iff_add_lt).mpr hradiusAddEndpoint

theorem Complex.logarithmicPhaseFiniteLeftFar_center_lt_endpoint
    {t : ℝ} {a b m : ℤ}
    (ht : 1 ≤ ‖t‖)
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftFarModes t a b) :
    Complex.logarithmicPhaseFourierStationaryPoint t m < (a : ℝ) := by
  have hbase :=
    ((Complex.mem_logarithmicPhaseFiniteLeftFarModes_iff
      t a b m).mp hm).1
  exact
    ((Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
      t a b m).mp hbase).2.2

theorem Complex.logarithmicPhaseFiniteRightFar_endpoint_lt_center
    {t : ℝ} {a b m : ℤ}
    (hm : m ∈ Complex.logarithmicPhaseFiniteRightFarModes t a b) :
    (b : ℝ) < Complex.logarithmicPhaseFourierStationaryPoint t m := by
  have hbase :=
    ((Complex.mem_logarithmicPhaseFiniteRightFarModes_iff
      t a b m).mp hm).1
  exact
    ((Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff
      t a b m).mp hbase).2.2

theorem Complex.logarithmicPhaseFiniteLeftFar_mode_neg
    {t : ℝ} {a b m : ℤ}
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftFarModes t a b) :
    m < 0 := by
  have hbase :=
    ((Complex.mem_logarithmicPhaseFiniteLeftFarModes_iff
      t a b m).mp hm).1
  exact
    ((Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
      t a b m).mp hbase).2.1

theorem Complex.logarithmicPhaseFiniteRightFar_mode_neg
    {t : ℝ} {a b m : ℤ}
    (hm : m ∈ Complex.logarithmicPhaseFiniteRightFarModes t a b) :
    m < 0 := by
  have hbase :=
    ((Complex.mem_logarithmicPhaseFiniteRightFarModes_iff
      t a b m).mp hm).1
  exact
    ((Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff
      t a b m).mp hbase).2.1

theorem Complex.logarithmicPhaseFiniteLeftFar_radius_pos
    {t : ℝ} {a b m : ℤ}
    (ht : 1 ≤ ‖t‖)
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftFarModes t a b) :
    0 < Complex.logarithmicPhaseBProcessRadius t m := by
  unfold Complex.logarithmicPhaseBProcessRadius
  exact div_pos
    (Complex.logarithmicPhaseFourierStationaryPoint_pos t ht
      (Complex.logarithmicPhaseFiniteLeftFar_mode_neg hm))
    (Complex.logarithmicPhaseBProcessScale_pos t)

theorem Complex.logarithmicPhaseFiniteRightFar_radius_pos
    {t : ℝ} {a b m : ℤ}
    (ht : 1 ≤ ‖t‖)
    (hm : m ∈ Complex.logarithmicPhaseFiniteRightFarModes t a b) :
    0 < Complex.logarithmicPhaseBProcessRadius t m := by
  unfold Complex.logarithmicPhaseBProcessRadius
  exact div_pos
    (Complex.logarithmicPhaseFourierStationaryPoint_pos t ht
      (Complex.logarithmicPhaseFiniteRightFar_mode_neg hm))
    (Complex.logarithmicPhaseBProcessScale_pos t)

theorem Complex.logarithmicPhaseFiniteLeftFar_endpoint_sub_center_pos
    {t : ℝ} {a b m : ℤ}
    (ht : 1 ≤ ‖t‖)
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftFarModes t a b) :
    0 < (a : ℝ) - Complex.logarithmicPhaseFourierStationaryPoint t m := by
  exact sub_pos.mpr
    (Complex.logarithmicPhaseFiniteLeftFar_center_lt_endpoint ht hm)

theorem Complex.logarithmicPhaseFiniteRightFar_center_sub_endpoint_pos
    {t : ℝ} {a b m : ℤ}
    (hm : m ∈ Complex.logarithmicPhaseFiniteRightFarModes t a b) :
    0 < Complex.logarithmicPhaseFourierStationaryPoint t m - (b : ℝ) := by
  exact sub_pos.mpr
    (Complex.logarithmicPhaseFiniteRightFar_endpoint_lt_center hm)

theorem Real.inv_le_inv_of_pos_le
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    y⁻¹ ≤ x⁻¹ := by
  have hy : 0 < y := lt_of_lt_of_le hx hxy
  exact (inv_le_inv₀ hy hx).mpr hxy

theorem Real.two_inv_le_two_inv_of_pos_le
    {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    y⁻¹ + y⁻¹ ≤ x⁻¹ + x⁻¹ := by
  have hinv := Real.inv_le_inv_of_pos_le hx hxy
  exact add_le_add hinv hinv

theorem Real.mul_div_distance_mono
    {coefficient distance₁ distance₂ endpoint : ℝ}
    (hcoefficient : 0 ≤ coefficient)
    (hendpoint : 0 < endpoint)
    (hdistance : distance₁ ≤ distance₂) :
    coefficient * distance₁ / endpoint ≤
      coefficient * distance₂ / endpoint := by
  have hmul := mul_le_mul_of_nonneg_left hdistance hcoefficient
  exact div_le_div_of_nonneg_right hmul hendpoint.le

theorem Real.neg_mul_sub_div_eq_mul_sub_div
    (coefficient left right denominator : ℝ) :
    -(coefficient * (left - right) / denominator) =
      coefficient * (right - left) / denominator := by
  have hdivision :
      -(coefficient * (left - right) / denominator) =
        (-(coefficient * (left - right))) / denominator :=
    neg_div' denominator (coefficient * (left - right))
  have hproduct :
      -(coefficient * (left - right)) =
        coefficient * (-(left - right)) :=
    neg_mul_eq_mul_neg coefficient (left - right)
  have hproductTransport :
      (-(coefficient * (left - right))) / denominator =
        coefficient * (-(left - right)) / denominator :=
    congrArg (fun value : ℝ => value / denominator) hproduct
  have hsubtraction : -(left - right) = right - left :=
    neg_sub left right
  have hsubtractionTransport :
      coefficient * (-(left - right)) / denominator =
        coefficient * (right - left) / denominator :=
    congrArg
      (fun value : ℝ => coefficient * value / denominator)
      hsubtraction
  exact Eq.trans hdivision
    (Eq.trans hproductTransport hsubtractionTransport)

theorem Complex.logarithmicPhaseFiniteLeftFar_derivativeGap_ge_radiusGap
    {t : ℝ} {a b m : ℤ}
    (ht : 1 ≤ ‖t‖) (ha : 1 ≤ a)
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftFarModes t a b) :
    (2 * Real.pi * (-(m : ℝ))) *
          Complex.logarithmicPhaseBProcessRadius t m / (a : ℝ) ≤
      Complex.logarithmicPhaseFourierTwistedDerivative t m (a : ℝ) := by
  have hmNeg := Complex.logarithmicPhaseFiniteLeftFar_mode_neg hm
  have haPos : 0 < (a : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one ha)
  have hdistance :=
    (Complex.logarithmicPhaseFiniteLeftFar_radius_lt_endpoint_sub_center
      hm).le
  have hangularNonneg :
      0 ≤ 2 * Real.pi * (-(m : ℝ)) :=
    mul_nonneg Complex.two_mul_pi_pos.le
      (neg_nonneg.mpr (Int.cast_nonpos.mpr hmNeg.le))
  have hmono := Real.mul_div_distance_mono
    hangularNonneg haPos hdistance
  have hfraction :
      (2 * Real.pi * (-(m : ℝ))) *
          ((a : ℝ) -
            Complex.logarithmicPhaseFourierStationaryPoint t m) / (a : ℝ) =
        Complex.logarithmicPhaseFourierTwistedDerivative t m (a : ℝ) := by
    exact
      (Complex.logarithmicPhaseFourierTwistedDerivative_eq_frequencyGap_mul_stationaryDistance_div
        t hmNeg haPos).symm
  exact le_trans hmono (le_of_eq hfraction)

theorem Complex.logarithmicPhaseFiniteRightFar_negDerivativeGap_ge_radiusGap
    {t : ℝ} {a b m : ℤ}
    (ht : 1 ≤ ‖t‖) (hb : 1 ≤ b)
    (hm : m ∈ Complex.logarithmicPhaseFiniteRightFarModes t a b) :
    (2 * Real.pi * (-(m : ℝ))) *
          Complex.logarithmicPhaseBProcessRadius t m / (b : ℝ) ≤
      -Complex.logarithmicPhaseFourierTwistedDerivative t m (b : ℝ) := by
  have hmNeg := Complex.logarithmicPhaseFiniteRightFar_mode_neg hm
  have hbPos : 0 < (b : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one hb)
  have hdistance :=
    (Complex.logarithmicPhaseFiniteRightFar_radius_lt_center_sub_endpoint
      hm).le
  have hangularNonneg :
      0 ≤ 2 * Real.pi * (-(m : ℝ)) :=
    mul_nonneg Complex.two_mul_pi_pos.le
      (neg_nonneg.mpr (Int.cast_nonpos.mpr hmNeg.le))
  have hmono := Real.mul_div_distance_mono
    hangularNonneg hbPos hdistance
  have hfraction :
      (2 * Real.pi * (-(m : ℝ))) *
          (Complex.logarithmicPhaseFourierStationaryPoint t m - (b : ℝ)) /
            (b : ℝ) =
        -Complex.logarithmicPhaseFourierTwistedDerivative t m (b : ℝ) := by
    have hderivative :=
      Complex.logarithmicPhaseFourierTwistedDerivative_eq_frequencyGap_mul_stationaryDistance_div
        t hmNeg hbPos
    have hnegDerivative := congrArg Neg.neg hderivative
    have hnormalize :
        -((2 * Real.pi * (-(m : ℝ))) *
            ((b : ℝ) -
              Complex.logarithmicPhaseFourierStationaryPoint t m) /
                (b : ℝ)) =
          (2 * Real.pi * (-(m : ℝ))) *
            (Complex.logarithmicPhaseFourierStationaryPoint t m - (b : ℝ)) /
              (b : ℝ) := by
      exact Real.neg_mul_sub_div_eq_mul_sub_div
        (2 * Real.pi * (-(m : ℝ)))
        (b : ℝ)
        (Complex.logarithmicPhaseFourierStationaryPoint t m)
        (b : ℝ)
    exact Eq.trans hnormalize.symm hnegDerivative.symm
  exact le_trans hmono (le_of_eq hfraction)

end

end LFunctions
end Boundary
