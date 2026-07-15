import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.CanonicalActiveBudget
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFarNegativeBudgetAssembly

/-!
# Cardinality of the logarithmic Poisson mode range

The enclosing frequency range is an integer interval from the floor of a
negative real frequency to zero.  This owner computes its cardinality and
bounds it by an explicit real frequency length.  Canonical interior, endpoint,
active, and finite inactive families all inherit the same majorant.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseModeRangeRealLower
    (t : ℝ) (a : ℤ) : ℝ :=
  (-‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a) /
    (2 * Real.pi)

def Complex.logarithmicPhaseModeRangeCardMajorant
    (t : ℝ) (a : ℤ) : ℝ :=
  2 + ‖t‖ /
    (2 * Real.pi * Real.integerBlockCutoffSupportLeftEndpoint a)

theorem Complex.logarithmicPhasePoissonModeRange_eq_Icc_floor
    (t : ℝ) (a : ℤ) :
    Complex.logarithmicPhasePoissonModeRange t a =
      Finset.Icc
        (Int.floor (Complex.logarithmicPhaseModeRangeRealLower t a)) 0 := by
  rfl

theorem Complex.logarithmicPhaseModeRangeRealLower_nonpos
    (t : ℝ) (a : ℤ) (ha : 1 ≤ a) :
    Complex.logarithmicPhaseModeRangeRealLower t a ≤ 0 := by
  unfold Complex.logarithmicPhaseModeRangeRealLower
  have hleft := Complex.integerBlockCutoffSupportLeftEndpoint_pos ha
  have hnumerator : -‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (norm_nonneg t)) hleft.le
  exact div_nonpos_of_nonpos_of_nonneg hnumerator Complex.two_mul_pi_pos.le

theorem Complex.logarithmicPhaseModeRange_floor_le_zero
    (t : ℝ) (a : ℤ) (ha : 1 ≤ a) :
    Int.floor (Complex.logarithmicPhaseModeRangeRealLower t a) ≤ 0 := by
  have hfloor := Int.floor_le
    (Complex.logarithmicPhaseModeRangeRealLower t a)
  have hnonpos :=
    Complex.logarithmicPhaseModeRangeRealLower_nonpos t a ha
  have hzeroCast : ((0 : ℤ) : ℝ) = 0 := Int.cast_zero
  exact Int.cast_le.mp
    (le_trans hfloor (Eq.subst hzeroCast.symm hnonpos))

theorem Complex.logarithmicPhasePoissonModeRange_card_int
    (t : ℝ) (a : ℤ) (ha : 1 ≤ a) :
    ((Complex.logarithmicPhasePoissonModeRange t a).card : ℤ) =
      1 - Int.floor (Complex.logarithmicPhaseModeRangeRealLower t a) := by
  have hfloor := Complex.logarithmicPhaseModeRange_floor_le_zero t a ha
  have hcondition :
      Int.floor (Complex.logarithmicPhaseModeRangeRealLower t a) ≤ 0 + 1 :=
    le_trans hfloor (show (0 : ℤ) ≤ 0 + 1 from zero_le_one)
  unfold Complex.logarithmicPhasePoissonModeRange
  unfold Complex.logarithmicPhaseModeRangeRealLower
  have hcard := Int.card_Icc_of_le
    (a := Int.floor
      ((-‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a) /
        (2 * Real.pi)))
    (b := 0) hcondition
  have hzeroOne : (0 : ℤ) + 1 = 1 := zero_add 1
  exact Eq.trans hcard
    (congrArg
      (fun endpoint : ℤ =>
        endpoint - Int.floor
          ((-‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a) /
            (2 * Real.pi))) hzeroOne)

theorem Real.neg_floor_le_one_sub
    (x : ℝ) :
    -(Int.floor x : ℝ) ≤ 1 - x := by
  have hlt := Int.lt_floor_add_one x
  have hle : x ≤ (Int.floor x : ℝ) + 1 := le_of_lt hlt
  have hneg := neg_le_neg hle
  have hleft : -((Int.floor x : ℝ) + 1) =
      -(Int.floor x : ℝ) - 1 := by
    exact Eq.trans (neg_add (Int.floor x : ℝ) 1)
      (sub_eq_add_neg (-(Int.floor x : ℝ)) 1).symm
  have hright : -x + 1 = 1 - x := by
    exact Eq.trans (add_comm (-x) 1) (sub_eq_add_neg 1 x).symm
  have hadd := add_le_add_right hneg 1
  have hnormalize :
      -((Int.floor x : ℝ) + 1) + 1 = -(Int.floor x : ℝ) := by
    exact Eq.trans
      (congrArg (fun value : ℝ => value + 1) hleft)
      (Eq.trans (add_assoc (-(Int.floor x : ℝ)) (-1) 1)
        (Eq.trans
          (congrArg (fun value : ℝ => -(Int.floor x : ℝ) + value)
            (neg_add_cancel 1))
          (add_zero _)))
  exact le_trans (le_of_eq hnormalize.symm)
    (le_trans hadd (le_of_eq hright))

theorem Complex.logarithmicPhaseModeRange_card_real_le_two_sub_lower
    (t : ℝ) (a : ℤ) (ha : 1 ≤ a) :
    ((Complex.logarithmicPhasePoissonModeRange t a).card : ℝ) ≤
      2 - Complex.logarithmicPhaseModeRangeRealLower t a := by
  have hcardInt :=
    Complex.logarithmicPhasePoissonModeRange_card_int t a ha
  have hcast := congrArg (fun value : ℤ => (value : ℝ)) hcardInt
  have hcastCard :
      ((((Complex.logarithmicPhasePoissonModeRange t a).card : ℤ) : ℝ)) =
        ((Complex.logarithmicPhasePoissonModeRange t a).card : ℝ) :=
    Int.cast_natCast
      (Complex.logarithmicPhasePoissonModeRange t a).card
  have hnormalize :
      (((1 - Int.floor
        (Complex.logarithmicPhaseModeRangeRealLower t a) : ℤ) : ℝ)) =
      1 - (Int.floor
        (Complex.logarithmicPhaseModeRangeRealLower t a) : ℝ) :=
    Eq.trans (Int.cast_sub 1 _)
      (congrArg
        (fun value : ℝ => value -
          (Int.floor
            (Complex.logarithmicPhaseModeRangeRealLower t a) : ℝ))
        Int.cast_one)
  have hcardReal :
      ((Complex.logarithmicPhasePoissonModeRange t a).card : ℝ) =
        1 - (Int.floor
          (Complex.logarithmicPhaseModeRangeRealLower t a) : ℝ) :=
    Eq.trans hcastCard.symm (Eq.trans hcast hnormalize)
  have hfloor := Real.neg_floor_le_one_sub
    (Complex.logarithmicPhaseModeRangeRealLower t a)
  have hadd := add_le_add_left hfloor 1
  have honeAddOne : (1 : ℝ) + 1 = 2 := one_add_one_eq_two
  have hright :
      1 + (1 - Complex.logarithmicPhaseModeRangeRealLower t a) =
        2 - Complex.logarithmicPhaseModeRangeRealLower t a := by
    exact Eq.trans
      (add_assoc 1 1
        (-Complex.logarithmicPhaseModeRangeRealLower t a)).symm
      (congrArg (fun value : ℝ => value -
        Complex.logarithmicPhaseModeRangeRealLower t a)
        honeAddOne)
  have hleft :
      1 - (Int.floor
          (Complex.logarithmicPhaseModeRangeRealLower t a) : ℝ) =
        1 + -(Int.floor
          (Complex.logarithmicPhaseModeRangeRealLower t a) : ℝ) :=
    sub_eq_add_neg 1 _
  exact le_trans (le_of_eq hcardReal)
    (le_trans (le_of_eq hleft)
      (le_trans hadd (le_of_eq hright)))

theorem Complex.neg_modeRangeRealLower_eq_positive_frequency
    (t : ℝ) (a : ℤ) (ha : 1 ≤ a) :
    -Complex.logarithmicPhaseModeRangeRealLower t a =
      ‖t‖ /
        (2 * Real.pi * Real.integerBlockCutoffSupportLeftEndpoint a) := by
  unfold Complex.logarithmicPhaseModeRangeRealLower
  have hnegative :
      -((-‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a) /
          (2 * Real.pi)) =
        (‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a) /
          (2 * Real.pi) := by
    exact Eq.trans
      (neg_div' (2 * Real.pi)
        (-‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a))
      (congrArg (fun numerator : ℝ => numerator / (2 * Real.pi))
        (Eq.trans
          (neg_div'
            (Real.integerBlockCutoffSupportLeftEndpoint a) (-‖t‖))
          (congrArg (fun numerator : ℝ => numerator /
            Real.integerBlockCutoffSupportLeftEndpoint a) (neg_neg ‖t‖))))
  have hdivision :
      (‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a) /
          (2 * Real.pi) =
        ‖t‖ /
          (2 * Real.pi * Real.integerBlockCutoffSupportLeftEndpoint a) := by
    exact Eq.trans (div_div ‖t‖
      (Real.integerBlockCutoffSupportLeftEndpoint a) (2 * Real.pi))
      (congrArg (fun denominator : ℝ => ‖t‖ / denominator)
        (mul_comm
          (Real.integerBlockCutoffSupportLeftEndpoint a) (2 * Real.pi)))
  exact Eq.trans hnegative hdivision

theorem Complex.logarithmicPhasePoissonModeRange_card_real_le_majorant
    (t : ℝ) (a : ℤ) (ha : 1 ≤ a) :
    ((Complex.logarithmicPhasePoissonModeRange t a).card : ℝ) ≤
      Complex.logarithmicPhaseModeRangeCardMajorant t a := by
  have hcard :=
    Complex.logarithmicPhaseModeRange_card_real_le_two_sub_lower t a ha
  have hnormalize :=
    Complex.neg_modeRangeRealLower_eq_positive_frequency t a ha
  unfold Complex.logarithmicPhaseModeRangeCardMajorant
  have hsub :
      2 - Complex.logarithmicPhaseModeRangeRealLower t a =
        2 + -Complex.logarithmicPhaseModeRangeRealLower t a :=
    sub_eq_add_neg 2 _
  have htarget :
      2 - Complex.logarithmicPhaseModeRangeRealLower t a =
        2 + ‖t‖ /
          (2 * Real.pi * Real.integerBlockCutoffSupportLeftEndpoint a) :=
    Eq.trans hsub (congrArg (fun value : ℝ => 2 + value) hnormalize)
  exact le_trans hcard
    (le_of_eq htarget)

theorem Complex.logarithmicPhaseCanonicalInterior_card_real_le_majorant
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) :
    ((Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b).card : ℝ) ≤
      Complex.logarithmicPhaseModeRangeCardMajorant t a := by
  have hcard :
      ((Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b).card : ℝ) ≤
        ((Complex.logarithmicPhasePoissonModeRange t a).card : ℝ) :=
    Nat.cast_le.mpr
      (Complex.logarithmicPhasePoissonCanonicalInteriorModes_card_le_modeRange_card
        t a b)
  exact le_trans hcard
    (Complex.logarithmicPhasePoissonModeRange_card_real_le_majorant t a ha)

theorem Complex.logarithmicPhaseCanonicalEndpoint_card_real_le_majorant
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) :
    ((Complex.logarithmicPhasePoissonCanonicalEndpointModes t a b).card : ℝ) ≤
      Complex.logarithmicPhaseModeRangeCardMajorant t a := by
  have hcard :
      ((Complex.logarithmicPhasePoissonCanonicalEndpointModes t a b).card : ℝ) ≤
        ((Complex.logarithmicPhasePoissonModeRange t a).card : ℝ) :=
    Nat.cast_le.mpr
      (Complex.logarithmicPhasePoissonCanonicalEndpointModes_card_le_modeRange_card
        t a b)
  exact le_trans hcard
    (Complex.logarithmicPhasePoissonModeRange_card_real_le_majorant t a ha)

theorem Complex.logarithmicPhaseInRangeInactive_card_real_le_majorant
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) :
    ((Complex.logarithmicPhasePoissonInRangeInactiveModes t a b).card : ℝ) ≤
      Complex.logarithmicPhaseModeRangeCardMajorant t a := by
  have hcard :
      ((Complex.logarithmicPhasePoissonInRangeInactiveModes t a b).card : ℝ) ≤
        ((Complex.logarithmicPhasePoissonModeRange t a).card : ℝ) :=
    Nat.cast_le.mpr
      (Complex.logarithmicPhasePoissonInRangeInactive_card_le_modeRange_card
        t a b)
  exact le_trans hcard
    (Complex.logarithmicPhasePoissonModeRange_card_real_le_majorant t a ha)

end
end LFunctions
end Boundary
