import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFiniteInactiveFarRegimeClosure

/-!
# Low-frequency closure of the finite left-far family

When `‖t‖ ≤ 3a`, the enclosing negative frequency interval contains at most
the first negative integer.  Its angular derivative gap is at least three,
so the complete left-far reciprocal family costs at most `2/3`, hence at most
`(2/3) * BProcessScale`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.three_mul_a_lt_six_mul_a_sub_two_thirds
    {a : ℕ} (ha : 2 ≤ a) :
    3 * (a : ℝ) <
      6 * ((a : ℝ) - 2 / 3) := by
  have haReal : (2 : ℝ) ≤ (a : ℝ) := Nat.cast_le.mpr ha
  have hfourLtSix : (4 : ℝ) < 6 := by
    have h := lt_add_of_pos_right (4 : ℝ) (show (0 : ℝ) < 2 from zero_lt_two)
    have heq : (4 : ℝ) + 2 = 6 := by
      exact (Nat.cast_add 4 2).symm.trans
        (congrArg Nat.cast (show (4 : ℕ) + 2 = 6 from rfl))
    exact Eq.subst heq h
  have hthreeTwo : (6 : ℝ) = 3 * 2 := by
    exact (congrArg Nat.cast (show (6 : ℕ) = 3 * 2 from rfl)).trans
      (Eq.trans (Nat.cast_mul 3 2) (show ((3 : ℕ) : ℝ) * 2 = 3 * 2 from rfl))
  have hfourLtThreeA : (4 : ℝ) < 3 * (a : ℝ) :=
    lt_of_lt_of_le hfourLtSix
      (hthreeTwo ▸ mul_le_mul_of_nonneg_left haReal (Nat.cast_nonneg 3))
  have hadd := add_lt_add_left hfourLtThreeA (3 * (a : ℝ))
  have htwoThree : (2 : ℝ) * 3 = 6 := by
    exact (mul_comm 2 3).trans hthreeTwo.symm
  have hmul : 2 * (3 * (a : ℝ)) = 6 * (a : ℝ) := by
    exact (mul_assoc 2 3 (a : ℝ)).symm.trans
      (congrArg (fun z : ℝ => z * (a : ℝ)) htwoThree)
  have haddEq : 3 * (a : ℝ) + 3 * (a : ℝ) = 6 * (a : ℝ) :=
    (two_mul (3 * (a : ℝ))).symm.trans hmul
  have hleft : 3 * (a : ℝ) + 4 < 6 * (a : ℝ) := by
    exact Eq.subst (motive := fun value : ℝ => 3 * (a : ℝ) + 4 < value)
      haddEq hadd
  have hsubtract := (lt_sub_iff_add_lt).mpr hleft
  have hnormalize :
      6 * ((a : ℝ) - 2 / 3) = 6 * (a : ℝ) - 4 := by
    have hthree : (3 : ℝ) ≠ 0 :=
      ne_of_gt (show (0 : ℝ) < 3 from zero_lt_three)
    have hfrac : (2 / 3 : ℝ) * 6 = 4 := by
      exact (div_mul_eq_mul_div (2 : ℝ) 3 6).trans
        ((div_eq_iff hthree).mpr (by
          exact Eq.trans
            (show (2 : ℝ) * 6 = 12 from by
              exact (Nat.cast_mul 2 6).symm.trans
                (congrArg Nat.cast (show (2 : ℕ) * 6 = 12 from rfl)))
            (show (12 : ℝ) = 4 * 3 from by
              exact Eq.trans (show (12 : ℝ) = ((12 : ℕ) : ℝ) from rfl)
                (Eq.trans
                  (congrArg Nat.cast (show (12 : ℕ) = 4 * 3 from rfl))
                  (Nat.cast_mul 4 3)))))
    exact Eq.trans (mul_sub 6 (a : ℝ) (2 / 3))
      (congrArg (fun value : ℝ => 6 * (a : ℝ) - value)
        (show 6 * (2 / 3 : ℝ) = 4 from (mul_comm 6 (2 / 3)).trans hfrac))
  exact Eq.subst (motive := fun value : ℝ => 3 * (a : ℝ) < value)
    hnormalize.symm hsubtract

theorem Real.three_mul_a_lt_two_pi_mul_cutoffSupportLeft
    {a : ℕ} (ha : 2 ≤ a) :
    3 * (a : ℝ) <
      2 * Real.pi *
        Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ) := by
  have hbase :=
    Real.three_mul_a_lt_six_mul_a_sub_two_thirds ha
  have hsupport :
      Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ) =
        (a : ℝ) - 2 / 3 := by
    rfl
  have hsupportPos : 0 < (a : ℝ) - 2 / 3 := by
    have htwoThirdLtTwo : (2 / 3 : ℝ) < 2 := by
      have hthree : (3 : ℝ) > 0 := zero_lt_three
      have htwoLtThree : (2 : ℝ) < 3 := by
        have h := lt_add_of_pos_right (2 : ℝ) (show (0 : ℝ) < 1 from zero_lt_one)
        exact Eq.subst (show (2 : ℝ) + 1 = 3 from by
          have h2 : ((2 : ℕ) : ℝ) = 2 := rfl
          have h1 : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
          have h3 : ((3 : ℕ) : ℝ) = 3 := rfl
          exact Eq.trans (congrArg₂ (· + ·) h2.symm h1.symm)
            (Eq.trans (Nat.cast_add 2 1).symm h3)) h
      have hfrac : (2 / 3 : ℝ) < 1 :=
        (div_lt_iff₀ hthree).mpr (by
          exact Eq.subst (one_mul 3).symm htwoLtThree)
      have h := lt_add_of_pos_right (1 : ℝ) (show (0 : ℝ) < 1 from zero_lt_one)
      exact lt_trans hfrac
        (Eq.subst (show (1 : ℝ) + 1 = 2 from one_add_one_eq_two) h)
    exact sub_pos.mpr (lt_of_lt_of_le htwoThirdLtTwo
      (Nat.cast_le.mpr ha))
  have hpi := mul_lt_mul_of_pos_right Real.six_lt_two_mul_pi hsupportPos
  exact Eq.subst
    (motive := fun value : ℝ => 3 * (a : ℝ) < value)
    (congrArg (fun support : ℝ => 2 * Real.pi * support) hsupport).symm
    (lt_trans hbase hpi)

theorem Complex.logarithmicPhaseFiniteLeftFarLowFrequency_ratio_lt_one
    {t : ℝ} {a : ℕ}
    (ha : 2 ≤ a)
    (hlow : Complex.logarithmicPhaseFiniteLeftFarLowFrequency t a) :
    ‖t‖ /
        (2 * Real.pi *
          Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ)) < 1 := by
  unfold Complex.logarithmicPhaseFiniteLeftFarLowFrequency at hlow
  have hdenom :=
    Real.three_mul_a_lt_two_pi_mul_cutoffSupportLeft ha
  have hnormDenom := lt_of_le_of_lt hlow hdenom
  have hdenomPos := lt_of_le_of_lt
    (mul_nonneg (Nat.cast_nonneg 3) (Nat.cast_nonneg a)) hdenom
  exact (div_lt_one hdenomPos).mpr hnormDenom

theorem Complex.logarithmicPhaseFiniteLeftFarLowFrequency_modeRangeRealLower_gt_neg_one
    {t : ℝ} {a : ℕ}
    (ha : 2 ≤ a)
    (hlow : Complex.logarithmicPhaseFiniteLeftFarLowFrequency t a) :
    (-1 : ℝ) < Complex.logarithmicPhaseModeRangeRealLower t (a : ℤ) := by
  have hratio :=
    Complex.logarithmicPhaseFiniteLeftFarLowFrequency_ratio_lt_one ha hlow
  have hidentity :=
    Complex.neg_modeRangeRealLower_eq_positive_frequency
      t (a : ℤ) (Int.ofNat_le.mpr (le_trans
        (show (1 : ℕ) ≤ 2 from Nat.succ_le_succ (Nat.zero_le 1)) ha))
  have hnegative := neg_lt_neg hratio
  have hnegIdentity := congrArg Neg.neg hidentity
  have hlowerEq :
      Complex.logarithmicPhaseModeRangeRealLower t (a : ℤ) =
        -(‖t‖ /
          (2 * Real.pi *
            Real.integerBlockCutoffSupportLeftEndpoint (a : ℤ))) :=
    (neg_neg
      (Complex.logarithmicPhaseModeRangeRealLower t (a : ℤ))).symm.trans
      hnegIdentity
  exact Eq.subst (motive := fun value : ℝ => (-1 : ℝ) < value)
    hlowerEq.symm hnegative

theorem Complex.logarithmicPhaseFiniteLeftFarLowFrequency_mode_eq_neg_one
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (ha : 2 ≤ a)
    (hlow : Complex.logarithmicPhaseFiniteLeftFarLowFrequency t a)
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftFarModes
      t (a : ℤ) (b : ℤ)) :
    m = -1 := by
  have hbase :=
    ((Complex.mem_logarithmicPhaseFiniteLeftFarModes_iff
      t (a : ℤ) (b : ℤ) m).mp hm).1
  have hinactive :=
    ((Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
      t (a : ℤ) (b : ℤ) m).mp hbase)
  have hdiff := Finset.mem_sdiff.mp hinactive.1
  have hinRange := hdiff.1
  have hmodeRange :=
    (Complex.mem_logarithmicPhasePoissonModeRange_iff
      t (a : ℤ) m).mp hinRange
  have hfloorCast := Int.floor_le
    (Complex.logarithmicPhaseModeRangeRealLower t (a : ℤ))
  have hlower :=
    Complex.logarithmicPhaseFiniteLeftFarLowFrequency_modeRangeRealLower_gt_neg_one
      ha hlow
  have hmNeg := hinactive.2.1
  have hmLe : m ≤ -1 := Int.le_sub_one_of_lt hmNeg
  have hnotLt : ¬ m < -1 := by
    intro hmStrict
    have hmSucc : (m : ℝ) + 1 ≤ -1 := by
      have hcast : ((m + 1 : ℤ) : ℝ) ≤ ((-1 : ℤ) : ℝ) :=
        Int.cast_le.mpr (Int.add_one_le_iff.mpr hmStrict)
      have hneg : ((-1 : ℤ) : ℝ) = (-1 : ℝ) := by
        exact Eq.trans (Int.cast_neg 1)
          (congrArg Neg.neg Int.cast_one)
      exact Eq.subst (motive := fun value : ℝ => (m : ℝ) + 1 ≤ value)
        hneg
        (Eq.subst (motive := fun value : ℝ => value ≤ ((-1 : ℤ) : ℝ))
          (show ((m + 1 : ℤ) : ℝ) = (m : ℝ) + 1 from by
            exact (Int.cast_add m 1).trans
              (congrArg₂ (· + ·) rfl Int.cast_one)) hcast)
    have hfloorPlus := Int.lt_floor_add_one
      (Complex.logarithmicPhaseModeRangeRealLower t (a : ℤ))
    have hfloorToMode :
        (Int.floor
          (Complex.logarithmicPhaseModeRangeRealLower t (a : ℤ)) : ℝ) ≤
          (m : ℝ) := Int.cast_le.mpr hmodeRange.1
    have hrealToModeSucc := lt_of_lt_of_le hfloorPlus
      (add_le_add_right hfloorToMode 1)
    exact (not_lt_of_ge hmSucc)
      (lt_trans hlower hrealToModeSucc)
  exact le_antisymm hmLe (not_lt.mp hnotLt)

theorem Complex.logarithmicPhaseFiniteLeftFarLowFrequency_card_le_one
    {t : ℝ} {a b : ℕ}
    (ha : 2 ≤ a)
    (hlow : Complex.logarithmicPhaseFiniteLeftFarLowFrequency t a) :
    (Complex.logarithmicPhaseFiniteLeftFarModes
      t (a : ℤ) (b : ℤ)).card ≤ 1 := by
  exact Finset.card_le_one.mpr (fun m hm n hn =>
    (Complex.logarithmicPhaseFiniteLeftFarLowFrequency_mode_eq_neg_one
      ha hlow hm).trans
      (Complex.logarithmicPhaseFiniteLeftFarLowFrequency_mode_eq_neg_one
        ha hlow hn).symm)

theorem Complex.logarithmicPhaseFiniteLeftFarLowFrequency_norm_div_a_le_three
    {t : ℝ} {a : ℕ}
    (ha : 2 ≤ a)
    (hlow : Complex.logarithmicPhaseFiniteLeftFarLowFrequency t a) :
    ‖t‖ / (a : ℝ) ≤ 3 := by
  unfold Complex.logarithmicPhaseFiniteLeftFarLowFrequency at hlow
  have haPos : 0 < (a : ℝ) :=
    Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one
      (le_trans (show (1 : ℕ) ≤ 2 from Nat.succ_le_succ (Nat.zero_le 1)) ha))
  have hdivide := (div_le_iff₀ haPos).mpr hlow
  exact hdivide

theorem Complex.logarithmicPhaseFiniteLeftFarLowFrequency_derivative_ge_three
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (ha : 2 ≤ a)
    (hlow : Complex.logarithmicPhaseFiniteLeftFarLowFrequency t a)
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftFarModes
      t (a : ℤ) (b : ℤ)) :
    3 ≤ Complex.logarithmicPhaseFourierTwistedDerivative t m (a : ℝ) := by
  have hmEq :=
    Complex.logarithmicPhaseFiniteLeftFarLowFrequency_mode_eq_neg_one
      ha hlow hm
  have hnormDiv :=
    Complex.logarithmicPhaseFiniteLeftFarLowFrequency_norm_div_a_le_three
      ha hlow
  have hpi : (6 : ℝ) ≤ 2 * Real.pi := le_of_lt Real.two_mul_pi_ge_six
  have hsub := sub_le_sub hpi hnormDiv
  have hthree : (6 : ℝ) - 3 = 3 := by
    exact (sub_eq_iff_eq_add).mpr
      (Eq.trans (show (6 : ℝ) = (6 : ℕ) from rfl)
        (Eq.trans (congrArg Nat.cast (show (6 : ℕ) = 3 + 3 from rfl))
          (Nat.cast_add 3 3)))
  have hgap :
      3 ≤ 2 * Real.pi - ‖t‖ / (a : ℝ) :=
    Eq.subst (motive := fun value : ℝ => value ≤ _)
      hthree hsub
  have hderivative :
      Complex.logarithmicPhaseFourierTwistedDerivative t (-1) (a : ℝ) =
        2 * Real.pi - ‖t‖ / (a : ℝ) := by
    unfold Complex.logarithmicPhaseFourierTwistedDerivative
    have hmcast : ((-1 : ℤ) : ℝ) = -1 := by
      exact Eq.trans (Int.cast_neg 1)
        (congrArg Neg.neg Int.cast_one)
    have hterm :
        2 * Real.pi * ((-1 : ℤ) : ℝ) = -(2 * Real.pi) := by
      exact Eq.trans
        (congrArg (fun value : ℝ => 2 * Real.pi * value) hmcast)
        (Eq.trans (mul_neg (2 * Real.pi) 1)
          (congrArg Neg.neg (mul_one (2 * Real.pi))))
    exact Eq.trans
      (congrArg (fun value : ℝ => -‖t‖ / (a : ℝ) - value) hterm)
      (Eq.trans (sub_neg_eq_add _ _)
        ((add_comm (-‖t‖ / (a : ℝ)) (2 * Real.pi)).trans
          ((congrArg (fun z : ℝ => 2 * Real.pi + z)
            (show -‖t‖ / (a : ℝ) = -(‖t‖ / (a : ℝ)) from neg_div _ _)).trans
            (sub_eq_add_neg (2 * Real.pi) (‖t‖ / (a : ℝ))).symm)))
  exact Eq.subst (motive := fun value : ℤ =>
      3 ≤ Complex.logarithmicPhaseFourierTwistedDerivative t value (a : ℝ))
    hmEq.symm
    (Eq.subst (motive := fun value : ℝ => 3 ≤ value)
      hderivative.symm hgap)

theorem Complex.logarithmicPhaseFiniteLeftFarLowFrequency_reciprocalGap_le_one_third
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (ha : 2 ≤ a)
    (hlow : Complex.logarithmicPhaseFiniteLeftFarLowFrequency t a)
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftFarModes
      t (a : ℤ) (b : ℤ)) :
    Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ) ≤ 1 / 3 := by
  have hgap :=
    Complex.logarithmicPhaseFiniteLeftFarLowFrequency_derivative_ge_three
      ha hlow hm
  have hinverse := Real.inv_le_inv_of_pos_le
    (Nat.cast_pos.mpr (Nat.succ_pos 2)) hgap
  unfold Complex.logarithmicPhaseRightReciprocalGap
  exact Eq.subst (motive := fun value : ℝ => _ ≤ value)
    (one_div 3).symm hinverse

theorem Complex.logarithmicPhaseFiniteLeftFarLowFrequency_twoGaps_le_two_thirds
    {t : ℝ} {a b : ℕ} {m : ℤ}
    (ha : 2 ≤ a)
    (hlow : Complex.logarithmicPhaseFiniteLeftFarLowFrequency t a)
    (hm : m ∈ Complex.logarithmicPhaseFiniteLeftFarModes
      t (a : ℤ) (b : ℤ)) :
    Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ) +
        Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ) ≤
      2 / 3 := by
  have hsingle :=
    Complex.logarithmicPhaseFiniteLeftFarLowFrequency_reciprocalGap_le_one_third
      ha hlow hm
  have hsum := add_le_add hsingle hsingle
  exact le_trans hsum
    (le_of_eq (show (1 / 3 : ℝ) + 1 / 3 = 2 / 3 from by
      have hthree : (3 : ℝ) ≠ 0 :=
        ne_of_gt (show (0 : ℝ) < 3 from zero_lt_three)
      apply (eq_div_iff hthree).mpr
      exact Eq.trans (add_mul (1 / 3 : ℝ) (1 / 3 : ℝ) 3)
        (Eq.trans (congrArg₂ (· + ·) (div_mul_cancel₀ 1 hthree)
          (div_mul_cancel₀ 1 hthree))
          (one_add_one_eq_two))))

theorem Complex.logarithmicPhaseFiniteLeftFarLowFrequency_budget_le_two_thirds
    {t : ℝ} {a b : ℕ}
    (ha : 2 ≤ a)
    (hlow : Complex.logarithmicPhaseFiniteLeftFarLowFrequency t a) :
    Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget
        t (a : ℤ) (b : ℤ) ≤ 2 / 3 := by
  unfold Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget
  exact Finset.sum_le_one_mul_of_card_le_one
    (Complex.logarithmicPhaseFiniteLeftFarModes
      t (a : ℤ) (b : ℤ))
    (fun m =>
      Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ) +
        Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ))
    (2 / 3 : ℝ)
    (Complex.logarithmicPhaseFiniteLeftFarLowFrequency_card_le_one ha hlow)
    (div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3))
    (fun m hm =>
      Complex.logarithmicPhaseFiniteLeftFarLowFrequency_twoGaps_le_two_thirds
        ha hlow hm)

theorem Complex.logarithmicPhaseFiniteLeftFarLowFrequency_budget_le_two_thirds_scale
    {t : ℝ} {a b : ℕ}
    (ha : 2 ≤ a)
    (hlow : Complex.logarithmicPhaseFiniteLeftFarLowFrequency t a) :
    Complex.logarithmicPhaseFiniteLeftFarReciprocalBudget
        t (a : ℤ) (b : ℤ) ≤
      (2 / 3 : ℝ) * Complex.logarithmicPhaseBProcessScale t := by
  exact le_trans
    (Complex.logarithmicPhaseFiniteLeftFarLowFrequency_budget_le_two_thirds
      ha hlow)
    (Complex.logarithmicPhaseFiniteNear_crossing_le_two_thirds_scale t)

end

end LFunctions
end Boundary
