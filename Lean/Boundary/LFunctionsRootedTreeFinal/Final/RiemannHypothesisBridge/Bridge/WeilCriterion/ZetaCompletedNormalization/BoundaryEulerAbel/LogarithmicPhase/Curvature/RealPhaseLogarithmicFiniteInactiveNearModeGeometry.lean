import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactiveNearCardinality

/-!
# Endpoint size supplied by a near inactive mode

The positive frequency coordinate of a negative integer mode is at least one.
Since `2*pi > 6`, its stationary center is at most `norm t / 6`.  Near-center
lower bounds then force the dyadic block endpoints to be controlled by
`norm t`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.logarithmicPhaseFourierStationaryPoint_le_norm_div_six
    (t : ℝ) {m : ℤ} (hm : m < 0) :
    Complex.logarithmicPhaseFourierStationaryPoint t m ≤ ‖t‖ / 6 := by
  unfold Complex.logarithmicPhaseFourierStationaryPoint
  have hmOne := Real.one_le_neg_intCast_of_neg hm
  have hsix := Real.two_mul_pi_ge_six.le
  have hmNonneg : 0 ≤ -(m : ℝ) := le_trans zero_le_one hmOne
  have honeScaled : (6 : ℝ) * 1 ≤ 6 * (-(m : ℝ)) :=
    mul_le_mul_of_nonneg_left hmOne (Nat.cast_nonneg 6)
  have hpiScaled : (6 : ℝ) * (-(m : ℝ)) ≤
      (2 * Real.pi) * (-(m : ℝ)) :=
    mul_le_mul_of_nonneg_right hsix hmNonneg
  have hdenominator : (6 : ℝ) ≤ (2 * Real.pi) * (-(m : ℝ)) :=
    Eq.subst (motive := fun value : ℝ => value ≤ _)
      (mul_one (6 : ℝ)) (le_trans honeScaled hpiScaled)
  have hsixPos : (0 : ℝ) < 6 :=
    Nat.cast_pos.mpr (Nat.succ_pos 5)
  exact div_le_div_of_nonneg_left (norm_nonneg t) hsixPos hdenominator

theorem Complex.logarithmicPhaseFiniteLeftNear_four_sevenths_a_le_norm_div_six
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftNearEndpointModes
      t (a : ℤ) (b : ℤ)) :
    (4 / 7 : ℝ) * (a : ℝ) ≤ ‖t‖ / 6 := by
  have hbase :=
    (Complex.mem_logarithmicPhaseFiniteLeftNearEndpointModes_iff
      t (a : ℤ) (b : ℤ) m).mp hm
  have hmNeg :=
    ((Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
      t (a : ℤ) (b : ℤ) m).mp hbase.1).2.1
  have hlower :=
    Complex.logarithmicPhaseFiniteLeftNearCenterLower_ge_four_sevenths_a
      t ht a
  have hcenter :=
    Complex.logarithmicPhaseFiniteLeftNear_centerLower_le_center
      t ht (a : ℤ) (b : ℤ)
      (Int.ofNat_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry)) hm
  have hupper :=
    Complex.logarithmicPhaseFourierStationaryPoint_le_norm_div_six t hmNeg
  exact le_trans hlower (le_trans hcenter hupper)

theorem Complex.logarithmicPhaseFiniteLeftNear_twenty_four_a_le_seven_norm
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftNearEndpointModes
      t (a : ℤ) (b : ℤ)) :
    24 * (a : ℝ) ≤ 7 * ‖t‖ := by
  have hbase :=
    Complex.logarithmicPhaseFiniteLeftNear_four_sevenths_a_le_norm_div_six
      ht hgeometry hm
  have hfortyTwo : (0 : ℝ) ≤ 42 := Nat.cast_nonneg 42
  have hscaled := mul_le_mul_of_nonneg_left hbase hfortyTwo
  have hsevenNe : (7 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 6))
  have hsixNe : (6 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 5))
  have hleft : 42 * ((4 / 7 : ℝ) * (a : ℝ)) = 24 * (a : ℝ) := by
    have hcoefficient : (42 : ℝ) * (4 / 7) = 24 := by
      have hleftProduct : (42 : ℝ) * 4 = 168 :=
        Real.endpoint_nat_cast_mul 42 4 168 rfl
      have hrightProduct : (24 : ℝ) * 7 = 168 :=
        Real.endpoint_nat_cast_mul 24 7 168 rfl
      calc
        (42 : ℝ) * (4 / 7) = (42 * 4) / 7 :=
          (mul_div_assoc (42 : ℝ) 4 7).symm
        _ = 24 :=
          (div_eq_iff hsevenNe).mpr
            (Eq.trans hleftProduct hrightProduct.symm)
    exact Eq.trans (mul_assoc 42 (4 / 7) (a : ℝ)).symm
      (congrArg (fun coefficient : ℝ => coefficient * (a : ℝ))
        hcoefficient)
  have hright : 42 * (‖t‖ / 6) = 7 * ‖t‖ := by
    have hcoefficient : (42 : ℝ) / 6 = 7 :=
      (div_eq_iff hsixNe).mpr
        (Real.endpoint_nat_cast_mul 7 6 42 rfl).symm
    calc
      (42 : ℝ) * (‖t‖ / 6) = (42 * ‖t‖) / 6 :=
        (mul_div_assoc (42 : ℝ) ‖t‖ 6).symm
      _ = (42 / 6) * ‖t‖ :=
        (div_mul_eq_mul_div 42 6 ‖t‖).symm
      _ = 7 * ‖t‖ :=
        congrArg (fun coefficient : ℝ => coefficient * ‖t‖)
          hcoefficient
  exact Eq.subst (motive := fun value : ℝ => value ≤ _)
    hleft
    (Eq.subst (motive := fun value : ℝ => _ ≤ value)
      hright hscaled)

theorem Complex.logarithmicPhaseFiniteLeftNear_blockRight_le_seven_twelfths_norm
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b)
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftNearEndpointModes
      t (a : ℤ) (b : ℤ)) :
    (b : ℝ) ≤ (7 / 12 : ℝ) * ‖t‖ := by
  have hba := Real.natCast_blockRight_le_two_mul_blockLeft
    (Real.logarithmicPhaseLongBranchGeometry_comparable hgeometry)
  have ha :=
    Complex.logarithmicPhaseFiniteLeftNear_twenty_four_a_le_seven_norm
      ht hgeometry hm
  have haBound : (a : ℝ) ≤ (7 / 24 : ℝ) * ‖t‖ := by
    have hcommute : (24 : ℝ) * (a : ℝ) = (a : ℝ) * 24 :=
      mul_comm 24 (a : ℝ)
    have hdivide : (a : ℝ) ≤ (7 * ‖t‖) / 24 :=
      (le_div_iff₀ (Nat.cast_pos.mpr (Nat.succ_pos 23))).mpr
        (Eq.subst (motive := fun value : ℝ => value ≤ 7 * ‖t‖)
          hcommute ha)
    have hnormalize : (7 * ‖t‖) / 24 = (7 / 24 : ℝ) * ‖t‖ := by
      exact (div_mul_eq_mul_div 7 24 ‖t‖).symm
    exact le_trans hdivide (le_of_eq hnormalize)
  have hscaled := mul_le_mul_of_nonneg_left haBound (Nat.cast_nonneg 2)
  have hnormalize :
      2 * ((7 / 24 : ℝ) * ‖t‖) = (7 / 12 : ℝ) * ‖t‖ := by
    have htwentyFourNe : (24 : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 23))
    have htwelveNe : (12 : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 11))
    have hcoefficient : (2 : ℝ) * (7 / 24) = 7 / 12 := by
      have hfourteenTwelve : (14 : ℝ) * 12 = 168 :=
        Real.endpoint_nat_cast_mul 14 12 168 rfl
      have hsevenTwentyFour : (7 : ℝ) * 24 = 168 :=
        Real.endpoint_nat_cast_mul 7 24 168 rfl
      calc
        (2 : ℝ) * (7 / 24) = (2 * 7) / 24 :=
          (mul_div_assoc (2 : ℝ) 7 24).symm
        _ = 14 / 24 :=
          congrArg (fun numerator : ℝ => numerator / 24)
            (Real.endpoint_nat_cast_mul 2 7 14 rfl)
        _ = 7 / 12 :=
          (div_eq_div_iff htwentyFourNe htwelveNe).mpr
            (Eq.trans hfourteenTwelve hsevenTwentyFour.symm)
    exact Eq.trans (mul_assoc 2 (7 / 24) ‖t‖).symm
      (congrArg (fun coefficient : ℝ => coefficient * ‖t‖)
        hcoefficient)
  exact le_trans hba (le_trans hscaled (le_of_eq hnormalize))

theorem Complex.logarithmicPhaseFiniteRightNear_blockRight_le_norm_div_six
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (hm : m ∈ Complex.logarithmicPhaseFiniteRightNearEndpointModes
      t (a : ℤ) (b : ℤ)) :
    (b : ℝ) ≤ ‖t‖ / 6 := by
  have hbase :=
    (Complex.mem_logarithmicPhaseFiniteRightNearEndpointModes_iff
      t (a : ℤ) (b : ℤ) m).mp hm
  have hdata :=
    (Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff
      t (a : ℤ) (b : ℤ) m).mp hbase.1
  have hcenter := hdata.2.2
  have hupper :=
    Complex.logarithmicPhaseFourierStationaryPoint_le_norm_div_six
      t hdata.2.1
  exact le_trans hcenter.le hupper

end

end LFunctions
end Boundary
