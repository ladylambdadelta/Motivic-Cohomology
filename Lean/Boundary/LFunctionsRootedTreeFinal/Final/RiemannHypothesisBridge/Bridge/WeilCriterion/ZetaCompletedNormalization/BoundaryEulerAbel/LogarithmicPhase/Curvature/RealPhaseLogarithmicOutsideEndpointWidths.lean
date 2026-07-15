import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.CenterFrequencyWidth
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicBProcessSharpActiveClosure

/-!
# Short frequency widths for outside-center endpoint modes

The two outside-center classes occupy cutoff collars of width `2/3`.  Their
frequency widths retain the angular denominator `2π`; on a long block they are
strictly less than one.
-/

namespace Boundary
namespace LFunctions

noncomputable section

private theorem realOfNat_add_eq_of_nat_eq
    (a b c : ℕ) (h : a + b = c) :
    (a : ℝ) + (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_add a b).symm
    (congrArg (fun value : ℕ => (value : ℝ)) h)

private theorem realOfNat_mul_eq_of_nat_eq
    (a b c : ℕ) (h : a * b = c) :
    (a : ℝ) * (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_mul a b).symm
    (congrArg (fun value : ℕ => (value : ℝ)) h)

theorem Real.six_lt_two_mul_pi :
    (6 : ℝ) < 2 * Real.pi := by
  have hpi : (3 : ℝ) < Real.pi := Real.pi_gt_three
  have hscaled := mul_lt_mul_of_pos_left hpi zero_lt_two
  have hproduct : (2 : ℝ) * 3 = 6 :=
    realOfNat_mul_eq_of_nat_eq 2 3 6 rfl
  exact Eq.subst
    (motive := fun value : ℝ => value < 2 * Real.pi)
    hproduct
    hscaled

theorem Real.two_mul_pi_gt_one :
    (1 : ℝ) < 2 * Real.pi :=
  lt_trans (Nat.one_lt_ofNat : (1 : ℝ) < 6)
    Real.six_lt_two_mul_pi

theorem Real.two_thirds_mul_a_le_a_sub_two_thirds
    {a : ℕ} (ha : 2 ≤ a) :
    (2 / 3 : ℝ) * (a : ℝ) ≤ (a : ℝ) - 2 / 3 := by
  have hthreePos : (0 : ℝ) < 3 :=
    Nat.cast_pos.mpr (Nat.succ_pos 2)
  have haReal : (2 : ℝ) ≤ (a : ℝ) := Nat.cast_le.mpr ha
  have htarget :
      2 * (a : ℝ) ≤ 3 * (a : ℝ) - 2 := by
    have hadd := add_le_add_left haReal (2 * (a : ℝ) - 2)
    have hleft : 2 * (a : ℝ) - 2 + 2 = 2 * (a : ℝ) :=
      sub_add_cancel (2 * (a : ℝ)) 2
    have hright : 2 * (a : ℝ) - 2 + (a : ℝ) =
        3 * (a : ℝ) - 2 := by
      calc
        2 * (a : ℝ) - 2 + (a : ℝ) =
            (2 * (a : ℝ) + (a : ℝ)) - 2 := by
          exact sub_add_eq_add_sub (2 * (a : ℝ)) 2 (a : ℝ)
        _ = 3 * (a : ℝ) - 2 := by
          exact congrArg (fun value : ℝ => value - 2)
            (calc
              2 * (a : ℝ) + (a : ℝ) =
                  2 * (a : ℝ) + 1 * (a : ℝ) := by
                exact congrArg (fun value : ℝ => 2 * (a : ℝ) + value)
                  (one_mul (a : ℝ)).symm
              _ = (2 + 1) * (a : ℝ) :=
                (add_mul 2 1 (a : ℝ)).symm
              _ = 3 * (a : ℝ) := by
                have hsum : (2 : ℝ) + 1 = 3 := two_add_one_eq_three
                exact congrArg (fun value : ℝ => value * (a : ℝ)) hsum)
    calc
      2 * (a : ℝ) = 2 * (a : ℝ) - 2 + 2 := hleft.symm
      _ ≤ 2 * (a : ℝ) - 2 + (a : ℝ) := hadd
      _ = 3 * (a : ℝ) - 2 := hright
  have hquotient : (2 * (a : ℝ)) / 3 ≤ (a : ℝ) - 2 / 3 := by
    have hthreeNe : (3 : ℝ) ≠ 0 := ne_of_gt hthreePos
    have hright :
        3 * (a : ℝ) - 2 = ((a : ℝ) - 2 / 3) * 3 := by
      calc
        3 * (a : ℝ) - 2 =
            (a : ℝ) * 3 - (2 / 3) * 3 := by
          exact congrArg₂ (fun left right : ℝ => left - right)
            (mul_comm 3 (a : ℝ))
            (div_mul_cancel₀ 2 hthreeNe).symm
        _ = ((a : ℝ) - 2 / 3) * 3 :=
          (sub_mul (a : ℝ) (2 / 3) 3).symm
    exact (div_le_iff₀ hthreePos).mpr
      (le_trans htarget (le_of_eq hright))
  have hform : (2 / 3 : ℝ) * (a : ℝ) = (2 * (a : ℝ)) / 3 :=
    div_mul_eq_mul_div 2 3 (a : ℝ)
  exact Eq.subst (motive := fun value : ℝ => value ≤ (a : ℝ) - 2 / 3)
    hform.symm hquotient

theorem Real.longGeometry_norm_lt_a_sq
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    ‖t‖ < (a : ℝ) ^ 2 := by
  have hscaleA := Real.longGeometry_scale_lt_a hgeometry
  have hscaleNonneg := Complex.logarithmicPhaseBProcessScale_nonneg t
  have haPos : 0 < (a : ℝ) :=
    Nat.cast_pos.mpr
      (Real.logarithmicPhaseLongBranchGeometry_zero_lt_a hgeometry)
  have hscalePos := Complex.logarithmicPhaseBProcessScale_pos t
  have hfirst := mul_lt_mul_of_pos_right hscaleA hscalePos
  have hsecond := mul_lt_mul_of_pos_left hscaleA haPos
  have hsquareStrict := lt_trans hfirst hsecond
  have hnormScale := Complex.logarithmicPhaseBProcess_norm_le_scale_sq t
  have hscaleSquare :
      Complex.logarithmicPhaseBProcessScale t *
          Complex.logarithmicPhaseBProcessScale t =
        Complex.logarithmicPhaseBProcessScale t ^ 2 :=
    (pow_two _).symm
  have haSquare : (a : ℝ) * (a : ℝ) = (a : ℝ) ^ 2 :=
    (pow_two _).symm
  have hstrict : Complex.logarithmicPhaseBProcessScale t ^ 2 <
      (a : ℝ) ^ 2 :=
    (lt_of_eq_of_lt hscaleSquare.symm hsquareStrict).trans_eq haSquare
  exact lt_of_le_of_lt hnormScale hstrict

theorem Complex.leftOutsideFrequencyWidth_lt_one
    {t : ℝ} {a b : ℕ}
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseBProcessLeftOutsideFrequencyUpper t (a : ℤ) -
        Complex.logarithmicPhaseBProcessLeftOutsideFrequencyLower t (a : ℤ) < 1 := by
  let left := Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ)
  let right := (a : ℝ)
  have haTwo := Real.logarithmicPhaseLongBranchGeometry_two_le_a hgeometry
  have hleftPos := Complex.integerBlockCutoffSupportLeftEndpoint_pos
    (Int.ofNat_le.mpr
      (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry))
  have hleftRight : left ≤ right := by
    unfold left Real.integerBlockCutoffSupportLeftEndpoint
    exact sub_le_self _
      (div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3))
  have hformula :=
    Complex.logarithmicPhaseCenterFrequencyCoordinate_sub
      t left right (ne_of_gt hleftPos)
      (ne_of_gt
        (Nat.cast_pos.mpr
          (Real.logarithmicPhaseLongBranchGeometry_zero_lt_a hgeometry)))
  have hnormASq := Real.longGeometry_norm_lt_a_sq hgeometry
  have hleftLower := Real.two_thirds_mul_a_le_a_sub_two_thirds haTwo
  have htwoPi := Real.six_lt_two_mul_pi
  have hpositiveFactors :
      0 < 2 * Real.pi * (left * right) := by
    exact mul_pos Complex.two_mul_pi_pos
      (mul_pos hleftPos
        (Nat.cast_pos.mpr
          (Real.logarithmicPhaseLongBranchGeometry_zero_lt_a hgeometry)))
  have htarget :
      (‖t‖ / (2 * Real.pi)) *
          ((right - left) / (left * right)) < 1 := by
    have hgap : right - left = (2 / 3 : ℝ) := by
      unfold left right Real.integerBlockCutoffSupportLeftEndpoint
      exact sub_sub_cancel (a : ℝ) (2 / 3)
    have hdenominatorLower :
        (a : ℝ) ^ 2 < 2 * Real.pi * (left * right) := by
      have hleftProduct :
          (2 / 3 : ℝ) * (a : ℝ) * (a : ℝ) ≤ left * right := by
        exact mul_le_mul_of_nonneg_right hleftLower (Nat.cast_nonneg a)
      have hcoarse : (a : ℝ) ^ 2 ≤
          6 * (((2 / 3 : ℝ) * (a : ℝ)) * (a : ℝ)) := by
        have hsquareNonneg : 0 ≤ (a : ℝ) ^ 2 := sq_nonneg (a : ℝ)
        have hfour : (1 : ℝ) ≤ 4 := by
          have hnat : (1 : ℕ) ≤ 4 := Nat.le_add_right 1 3
          have hcast : (((1 : ℕ) : ℝ)) ≤ ((4 : ℕ) : ℝ) :=
            Nat.cast_le.mpr hnat
          exact Eq.subst (motive := fun value : ℝ => value ≤ 4)
            Nat.cast_one hcast
        have hscaled := mul_le_mul_of_nonneg_right hfour hsquareNonneg
        have hleftIdentity : 1 * (a : ℝ) ^ 2 = (a : ℝ) ^ 2 := one_mul _
        have hsixTwoThirds : (6 : ℝ) * (2 / 3) = 4 := by
          have hthreeNe : (3 : ℝ) ≠ 0 :=
            ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
          have hsixTwo : (6 : ℝ) * 2 = 12 :=
            realOfNat_mul_eq_of_nat_eq 6 2 12 rfl
          have hfourThree : (4 : ℝ) * 3 = 12 :=
            realOfNat_mul_eq_of_nat_eq 4 3 12 rfl
          have htwelveThirds : (12 / 3 : ℝ) = 4 :=
            (div_eq_iff hthreeNe).mpr hfourThree.symm
          exact Eq.trans (mul_div_assoc 6 2 3).symm
            (Eq.trans
              (congrArg (fun value : ℝ => value / 3) hsixTwo)
              htwelveThirds)
        have hrightIdentity :
            6 * (((2 / 3 : ℝ) * (a : ℝ)) * (a : ℝ)) =
              4 * (a : ℝ) ^ 2 := by
          calc
            6 * (((2 / 3 : ℝ) * (a : ℝ)) * (a : ℝ)) =
                (6 * (2 / 3)) * ((a : ℝ) * (a : ℝ)) := by
              exact Eq.trans
                (mul_assoc 6 ((2 / 3) * (a : ℝ)) (a : ℝ)).symm
                (Eq.trans
                  (congrArg (fun value : ℝ => value * (a : ℝ))
                    (mul_assoc 6 (2 / 3) (a : ℝ)).symm)
                  (mul_assoc (6 * (2 / 3)) (a : ℝ) (a : ℝ)))
            _ = 4 * ((a : ℝ) * (a : ℝ)) :=
              congrArg (fun value : ℝ => value * ((a : ℝ) * (a : ℝ)))
                hsixTwoThirds
            _ = 4 * (a : ℝ) ^ 2 :=
              congrArg (fun value : ℝ => 4 * value) (pow_two (a : ℝ)).symm
        exact Eq.subst (motive := fun value : ℝ => value ≤ _)
          hleftIdentity hscaled |>.trans_eq hrightIdentity.symm
      have hangularProduct :
          6 * (((2 / 3 : ℝ) * (a : ℝ)) * (a : ℝ)) <
            2 * Real.pi * (((2 / 3 : ℝ) * (a : ℝ)) * (a : ℝ)) :=
        mul_lt_mul_of_pos_right htwoPi
          (mul_pos
            (mul_pos (div_pos zero_lt_two
              (Nat.cast_pos.mpr (Nat.succ_pos 2)))
              (Nat.cast_pos.mpr
                (Real.logarithmicPhaseLongBranchGeometry_zero_lt_a hgeometry)))
            (Nat.cast_pos.mpr
              (Real.logarithmicPhaseLongBranchGeometry_zero_lt_a hgeometry)))
      have hlast := mul_le_mul_of_nonneg_left hleftProduct Complex.two_mul_pi_pos.le
      exact lt_of_le_of_lt hcoarse
        (lt_of_lt_of_le hangularProduct hlast)
    have hratio :
        ‖t‖ * (right - left) <
          2 * Real.pi * (left * right) := by
      have hgapLe : right - left ≤ 1 := by
        exact Eq.subst (motive := fun value : ℝ => value ≤ 1) hgap.symm
          ((div_le_one (Nat.cast_pos.mpr (Nat.succ_pos 2))).mpr
            (show (2 : ℝ) ≤ 3 from
              Nat.cast_le.mpr (Nat.le_succ 2)))
      have hmulGap := mul_le_mul_of_nonneg_left hgapLe (norm_nonneg t)
      exact lt_of_le_of_lt
        (le_trans hmulGap (le_of_eq (mul_one ‖t‖)))
        (lt_trans hnormASq hdenominatorLower)
    have hquotientIdentity :=
      Real.div_mul_div_eq_mul_div_mul
        ‖t‖ (2 * Real.pi) (right - left) (left * right)
    have hcombined := (div_lt_one hpositiveFactors).mpr hratio
    exact Eq.subst (motive := fun value : ℝ => value < 1)
      hquotientIdentity.symm hcombined
  exact Eq.subst
    (motive := fun value : ℝ => value < 1)
    hformula.symm htarget

end

end LFunctions
end Boundary
