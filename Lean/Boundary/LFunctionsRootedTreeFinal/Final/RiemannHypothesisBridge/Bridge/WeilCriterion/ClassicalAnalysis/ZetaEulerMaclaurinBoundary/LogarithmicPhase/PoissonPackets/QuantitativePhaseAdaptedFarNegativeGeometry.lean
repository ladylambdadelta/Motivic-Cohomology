import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedOutsideSplit

/-!
# Far-negative phase-gap geometry

Modes below the floor-defined lower endpoint have angular frequency strictly
beyond the wide support threshold.  Since the quantitative cutoff starts at a
larger positive endpoint, they have a strict left-inactive phase gap there.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.cast_lt_modeRangeLower_quotient
    (t : ℝ) (a m : ℤ)
    (hm : m < Complex.logarithmicPhasePoissonModeRangeLower t a) :
    (m : ℝ) <
      (-‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a) /
        (2 * Real.pi) := by
  unfold Complex.logarithmicPhasePoissonModeRangeLower at hm
  have hcast : (m : ℝ) <
      (Int.floor
        ((-‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a) /
          (2 * Real.pi)) : ℝ) := Int.cast_lt.mpr hm
  have hfloor := Int.floor_le
    ((-‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a) /
      (2 * Real.pi))
  exact lt_of_lt_of_le hcast hfloor

theorem Complex.modeRangeLower_angular_frequency_lt
    (t : ℝ) (a m : ℤ)
    (hm : m < Complex.logarithmicPhasePoissonModeRangeLower t a) :
    ‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a <
      2 * Real.pi * (-(m : ℝ)) := by
  have hcast := Complex.cast_lt_modeRangeLower_quotient t a m hm
  have htwoPiPos := Complex.two_mul_pi_pos
  have hmul := (lt_div_iff₀ htwoPiPos).mp hcast
  have hnormalizeLeft :
      (m : ℝ) * (2 * Real.pi) = 2 * Real.pi * (m : ℝ) :=
    mul_comm _ _
  have hnegative := neg_lt_neg hmul
  have hleft :
      -(-‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a) =
        ‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a := by
    have hnegativeDivision :
        -‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a =
          -(‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a) :=
      neg_div (Real.integerBlockCutoffSupportLeftEndpoint a) ‖t‖
    exact Eq.trans (congrArg Neg.neg hnegativeDivision)
      (neg_neg (‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a))
  have hright :
      -((m : ℝ) * (2 * Real.pi)) =
        2 * Real.pi * (-(m : ℝ)) := by
    exact Eq.trans (congrArg Neg.neg hnormalizeLeft)
      (mul_neg (2 * Real.pi) (m : ℝ)).symm
  calc
    ‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a =
        -(-‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a) := hleft.symm
    _ < -((m : ℝ) * (2 * Real.pi)) := hnegative
    _ = 2 * Real.pi * (-(m : ℝ)) := hright

theorem Complex.integerBlockWideSupportLeft_lt_quantitativeSupportLeft
    (a : ℤ) :
    Real.integerBlockCutoffSupportLeftEndpoint a <
      Complex.logarithmicPhaseQuantitativeSupportLeft a := by
  unfold Real.integerBlockCutoffSupportLeftEndpoint
  unfold Complex.logarithmicPhaseQuantitativeSupportLeft
  have hthird : (1 / 3 : ℝ) < 2 / 3 := by
    have hthreePos : (0 : ℝ) < 3 := zero_lt_three
    exact (div_lt_div_iff_of_pos_right hthreePos).mpr one_lt_two
  exact sub_lt_sub_left hthird (a : ℝ)

theorem Complex.div_wideSupport_ge_div_quantitativeSupport
    (t : ℝ) (a : ℤ) (ha : 1 ≤ a) :
    ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a ≤
      ‖t‖ / Real.integerBlockCutoffSupportLeftEndpoint a := by
  have hwidePos := Complex.integerBlockCutoffSupportLeftEndpoint_pos ha
  have horder :=
    Complex.integerBlockWideSupportLeft_lt_quantitativeSupportLeft a
  exact Real.div_antitone_on_pos (norm_nonneg t) hwidePos horder.le

theorem Complex.logarithmicPhaseFarNegative_strict_left_gap
    (t : ℝ) (a m : ℤ)
    (ha : 1 ≤ a)
    (hm : m ∈ Complex.logarithmicPhasePoissonFarNegativeModes t a) :
    ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a <
      2 * Real.pi * (-(m : ℝ)) := by
  have hwide := Complex.modeRangeLower_angular_frequency_lt t a m hm
  have hnarrow :=
    Complex.div_wideSupport_ge_div_quantitativeSupport t a ha
  exact lt_of_le_of_lt hnarrow hwide

theorem Complex.logarithmicPhaseFarNegative_leftGap_pos
    (t : ℝ) (a m : ℤ)
    (ha : 1 ≤ a)
    (hm : m ∈ Complex.logarithmicPhasePoissonFarNegativeModes t a) :
    0 < Complex.logarithmicPhaseLeftInactiveGap t m
      (Complex.logarithmicPhaseQuantitativeSupportLeft a) := by
  exact Complex.logarithmicPhaseLeftInactiveGap_pos_of_strict t m _
    (Complex.logarithmicPhaseFarNegative_strict_left_gap t a m ha hm)

theorem Complex.norm_logarithmicPhaseFarNegativeModePacket_le
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : Complex.logarithmicPhasePoissonFarNegativeModes t a) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket (‖t‖) a b m‖ ≤
      Complex.logarithmicPhaseLeftInactiveClosedMajorant t a b m := by
  exact Complex.norm_logarithmicPhaseLeftInactiveModePacket_le
    t a b m ha hab
    (Complex.logarithmicPhaseFarNegative_strict_left_gap
      t a m ha m.property)

end
end LFunctions
end Boundary
