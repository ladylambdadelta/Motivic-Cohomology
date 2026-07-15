import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.ShiftedReciprocalPositiveQuarticTransport

/-!
# Residual-weighted shifted reciprocal cubic series

The nonstationary cubic coefficients occurring on a negative-frequency tail
carry one factor of the residual endpoint gap.  This owner keeps that factor
attached to the complete shifted series.  The discrete first term and the
integral remainder are bounded separately by `1 / (4 * c ^ 2)` and
`1 / (8 * c ^ 2)`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.shift_mul_shiftedCubeTerm_zero_le_quarter_inverseSquare
    (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) :
    A * Real.shiftedInverseCubeTerm A c 0 ≤
      1 / (4 * c ^ 2) := by
  have hbase : 0 < A + c := add_pos_of_nonneg_of_pos hA hc
  have hfourAc : 4 * A * c ≤ (A + c) ^ 2 :=
    four_mul_le_sq_add A c
  have hcLeBase : c ≤ A + c := le_add_of_nonneg_left hA
  have hproduct := mul_le_mul hfourAc hcLeBase hc.le
    (pow_nonneg hbase.le 2)
  have hleftProduct :
      (4 * A * c) * c = A * (4 * c ^ 2) := by
    have hshuffle :
        ((4 : ℝ) * A * c) * c = (4 * A) * (c * c) :=
      mul_assoc (4 * A) c c
    have hcommute :
        ((4 : ℝ) * A) * (c * c) = A * (4 * (c * c)) := by
      exact Eq.trans
        (congrArg (fun value : ℝ => value * (c * c)) (mul_comm 4 A))
        (mul_assoc A 4 (c * c))
    exact Eq.trans hshuffle
      (Eq.trans hcommute
        (congrArg (fun value : ℝ => A * (4 * value))
          (pow_two c).symm))
  have hrightProduct :
      (A + c) ^ 2 * (A + c) = (A + c) ^ 3 :=
    (pow_succ (A + c) 2).symm
  have hcross :
      A * (4 * c ^ 2) ≤ (A + c) ^ 3 :=
    Eq.mp
      (congrArg₂ (fun left right : ℝ => left ≤ right)
        hleftProduct hrightProduct)
      hproduct
  have hleftDenominator : 0 < (A + c) ^ 3 := pow_pos hbase 3
  have hrightDenominator : 0 < 4 * c ^ 2 :=
    mul_pos (Nat.cast_pos.mpr (Nat.zero_lt_succ 3)) (pow_pos hc 2)
  have hquotient :
      A / (A + c) ^ 3 ≤ 1 / (4 * c ^ 2) :=
    (div_le_div_iff₀ hleftDenominator hrightDenominator).mpr
      (le_trans hcross
        (le_of_eq (one_mul ((A + c) ^ 3)).symm))
  have hterm := Real.shiftedInverseCubeTerm_zero_eq_base A c
  have hleftForm :
      A * Real.shiftedInverseCubeTerm A c 0 = A / (A + c) ^ 3 :=
    Eq.trans (congrArg (fun value : ℝ => A * value) hterm)
      (mul_one_div A ((A + c) ^ 3))
  exact le_trans (le_of_eq hleftForm) hquotient

theorem Real.shift_mul_shiftedCubeBudget_le
    (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) :
    A * Real.shiftedInverseCubeBudget A c ≤
      1 / (8 * c ^ 2) := by
  have hbudget := Real.shiftedInverseCubeBudget_eq_base hA hc
  have hbase : 0 < A + c := add_pos_of_nonneg_of_pos hA hc
  have hfourAc : 4 * A * c ≤ (A + c) ^ 2 :=
    four_mul_le_sq_add A c
  have hscaleNonneg : 0 ≤ (2 : ℝ) * c :=
    mul_nonneg zero_le_two hc.le
  have hscaled := mul_le_mul_of_nonneg_left hfourAc hscaleNonneg
  have hleftScaled :
      ((2 : ℝ) * c) * (4 * A * c) = A * (8 * c ^ 2) := by
    have hshuffle :
        ((2 : ℝ) * c) * ((4 * A) * c) =
          (2 * (4 * A)) * (c * c) :=
      mul_mul_mul_comm 2 c (4 * A) c
    have hcoefficient : (2 : ℝ) * (4 * A) = 8 * A := by
      exact Eq.trans (mul_assoc 2 4 A).symm
        (congrArg (fun value : ℝ => value * A)
          (Eq.trans (Nat.cast_mul 2 4).symm Nat.cast_ofNat))
    have hcommuteCoefficient :
        (8 : ℝ) * A * (c * c) = A * (8 * (c * c)) := by
      exact Eq.trans
        (congrArg (fun value : ℝ => value * (c * c)) (mul_comm 8 A))
        (mul_assoc A 8 (c * c))
    exact Eq.trans hshuffle
      (Eq.trans
        (congrArg (fun value : ℝ => value * (c * c)) hcoefficient)
        (Eq.trans hcommuteCoefficient
          (congrArg (fun value : ℝ => A * (8 * value))
            (pow_two c).symm)))
  have hrightScaled :
      ((2 : ℝ) * c) * (A + c) ^ 2 =
        1 * (((2 : ℝ) * c) * (A + c) ^ 2) :=
    (one_mul (((2 : ℝ) * c) * (A + c) ^ 2)).symm
  have hcross :
      A * (8 * c ^ 2) ≤
        1 * (((2 : ℝ) * c) * (A + c) ^ 2) :=
    Eq.mp
      (congrArg₂ (fun left right : ℝ => left ≤ right)
        hleftScaled hrightScaled)
      hscaled
  have hdenominatorLeft : 0 < ((2 : ℝ) * c) * (A + c) ^ 2 :=
    mul_pos (mul_pos zero_lt_two hc) (pow_pos hbase 2)
  have hdenominatorRight : 0 < 8 * c ^ 2 :=
    mul_pos (Nat.cast_pos.mpr (Nat.zero_lt_succ 7)) (pow_pos hc 2)
  have hcore :
      A / (((2 : ℝ) * c) * (A + c) ^ 2) ≤
        1 / (8 * c ^ 2) :=
    (div_le_div_iff₀ hdenominatorLeft hdenominatorRight).mpr hcross
  have hleftForm :
      A * Real.shiftedInverseCubeBudget A c =
        A / (((2 : ℝ) * c) * (A + c) ^ 2) := by
    exact Eq.trans (congrArg (fun value : ℝ => A * value) hbudget)
      (Eq.trans
        (congrArg (fun value : ℝ => A * value)
          (one_div (((2 : ℝ) * c) * (A + c) ^ 2)))
        (div_eq_mul_inv A (((2 : ℝ) * c) * (A + c) ^ 2)).symm)
  exact le_trans (le_of_eq hleftForm) hcore

theorem Real.shift_mul_shiftedCubeSeriesBudget_le_split
    (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) :
    A * Real.shiftedInverseCubeSeriesBudget A c ≤
      1 / (4 * c ^ 2) + 1 / (8 * c ^ 2) := by
  have hterm :=
    Real.shift_mul_shiftedCubeTerm_zero_le_quarter_inverseSquare A c hA hc
  have htail := Real.shift_mul_shiftedCubeBudget_le A c hA hc
  have hsum := add_le_add hterm htail
  have hexpand :
      A * Real.shiftedInverseCubeSeriesBudget A c =
        A * Real.shiftedInverseCubeTerm A c 0 +
          A * Real.shiftedInverseCubeBudget A c := by
    unfold Real.shiftedInverseCubeSeriesBudget
    exact mul_add A _ _
  exact le_trans (le_of_eq hexpand) hsum

theorem Real.square_ge_thirty_six_of_six_le_generic
    {c : ℝ} (hc : (6 : ℝ) ≤ c) :
    (36 : ℝ) ≤ c ^ 2 := by
  have hsquare := mul_self_le_mul_self (Nat.cast_nonneg 6) hc
  have hsixSquare : (6 : ℝ) ^ 2 = 36 := by
    have hnat : (6 ^ 2 : ℕ) = 36 := rfl
    exact Eq.trans (Nat.cast_pow 6 2).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  exact le_trans (le_of_eq hsixSquare.symm)
    (le_trans (le_of_eq (pow_two (6 : ℝ)))
      (le_trans hsquare (le_of_eq (pow_two c).symm)))

theorem Real.inverse_four_square_le_one_hundred_forty_four_of_six_le
    {c : ℝ} (hc : (6 : ℝ) ≤ c) :
    1 / (4 * c ^ 2) ≤ (1 : ℝ) / 144 := by
  have hsquare := Real.square_ge_thirty_six_of_six_le_generic hc
  have hscaled := mul_le_mul_of_nonneg_left hsquare (Nat.cast_nonneg 4)
  have hfourTimesThirtySix : (4 : ℝ) * 36 = 144 := by
    have hnat : (4 * 36 : ℕ) = 144 := rfl
    exact Eq.trans (Nat.cast_mul 4 36).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have hdenominator : (144 : ℝ) ≤ 4 * c ^ 2 :=
    le_trans (le_of_eq hfourTimesThirtySix.symm) hscaled
  exact one_div_le_one_div_of_le
    (Nat.cast_pos.mpr (Nat.zero_lt_succ 143)) hdenominator

theorem Real.inverse_eight_square_le_one_two_hundred_eighty_eight_of_six_le
    {c : ℝ} (hc : (6 : ℝ) ≤ c) :
    1 / (8 * c ^ 2) ≤ (1 : ℝ) / 288 := by
  have hsquare := Real.square_ge_thirty_six_of_six_le_generic hc
  have hscaled := mul_le_mul_of_nonneg_left hsquare (Nat.cast_nonneg 8)
  have heightTimesThirtySix : (8 : ℝ) * 36 = 288 := by
    have hnat : (8 * 36 : ℕ) = 288 := rfl
    exact Eq.trans (Nat.cast_mul 8 36).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have hdenominator : (288 : ℝ) ≤ 8 * c ^ 2 :=
    le_trans (le_of_eq heightTimesThirtySix.symm) hscaled
  exact one_div_le_one_div_of_le
    (Nat.cast_pos.mpr (Nat.zero_lt_succ 287)) hdenominator

theorem Real.eighteen_mul_one_one_hundred_forty_four_eq_one_eighth :
    (18 : ℝ) * (1 / 144) = 1 / 8 := by
  have h144Ne : (144 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 143))
  have h8Ne : (8 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 7))
  have hleft : (18 : ℝ) * 8 = 144 := by
    have hnat : (18 * 8 : ℕ) = 144 := rfl
    exact Eq.trans (Nat.cast_mul 18 8).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have hright : (1 : ℝ) * 144 = 144 := one_mul 144
  have hfraction : (18 / 144 : ℝ) = 1 / 8 :=
    (div_eq_div_iff h144Ne h8Ne).mpr (Eq.trans hleft hright.symm)
  exact Eq.trans (mul_one_div 18 144) hfraction

theorem Real.eighteen_mul_one_two_hundred_eighty_eight_eq_one_sixteenth :
    (18 : ℝ) * (1 / 288) = 1 / 16 := by
  have h288Ne : (288 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 287))
  have h16Ne : (16 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 15))
  have hleft : (18 : ℝ) * 16 = 288 := by
    have hnat : (18 * 16 : ℕ) = 288 := rfl
    exact Eq.trans (Nat.cast_mul 18 16).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have hright : (1 : ℝ) * 288 = 288 := one_mul 288
  have hfraction : (18 / 288 : ℝ) = 1 / 16 :=
    (div_eq_div_iff h288Ne h16Ne).mpr (Eq.trans hleft hright.symm)
  exact Eq.trans (mul_one_div 18 288) hfraction

theorem Real.one_eighth_add_one_sixteenth_le_one_fourth :
    (1 / 8 : ℝ) + 1 / 16 ≤ 1 / 4 := by
  have h8Ne : (8 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 7))
  have h16Ne : (16 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 15))
  have h4Ne : (4 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 3))
  have honeEighth : (1 / 8 : ℝ) = 2 / 16 := by
    have hleft : (1 : ℝ) * 16 = 16 := one_mul 16
    have hright : (2 : ℝ) * 8 = 16 := by
      have hnat : (2 * 8 : ℕ) = 16 := rfl
      exact Eq.trans (Nat.cast_mul 2 8).symm
        (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
          Nat.cast_ofNat)
    exact (div_eq_div_iff h8Ne h16Ne).mpr
      (Eq.trans hleft hright.symm)
  have hsum : (2 / 16 : ℝ) + 1 / 16 = 3 / 16 :=
    Eq.trans (div_add_div_same 2 1 16)
      (congrArg (fun value : ℝ => value / 16)
        (show (2 : ℝ) + 1 = 3 from two_add_one_eq_three))
  have hthreeLeFour : (3 : ℝ) ≤ 4 := by
    have hadd : (3 : ℝ) ≤ 3 + 1 := le_add_of_nonneg_right zero_le_one
    exact le_trans hadd (le_of_eq three_add_one_eq_four)
  have hthreeSixteenthsLeFourSixteenths :
      (3 / 16 : ℝ) ≤ 4 / 16 :=
    div_le_div_of_nonneg_right hthreeLeFour
      (Nat.cast_nonneg 16)
  have hfourSixteenths : (4 / 16 : ℝ) = 1 / 4 := by
    have hleft : (4 : ℝ) * 4 = 16 := by
      have hnat : (4 * 4 : ℕ) = 16 := rfl
      exact Eq.trans (Nat.cast_mul 4 4).symm
        (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
          Nat.cast_ofNat)
    have hright : (1 : ℝ) * 16 = 16 := one_mul 16
    exact (div_eq_div_iff h16Ne h4Ne).mpr
      (Eq.trans hleft hright.symm)
  exact le_trans
    (le_of_eq
      (Eq.trans
        (congrArg (fun value : ℝ => value + 1 / 16) honeEighth)
        hsum))
    (le_trans hthreeSixteenthsLeFourSixteenths
      (le_of_eq hfourSixteenths))

theorem Real.eighteen_mul_shiftedCubeSeriesBudget_le_one_fourth
    (A c : ℝ) (hA : 0 ≤ A) (hc : (6 : ℝ) ≤ c) :
    18 * A * Real.shiftedInverseCubeSeriesBudget A c ≤ 1 / 4 := by
  have hcPos : 0 < c :=
    lt_of_lt_of_le (Nat.cast_pos.mpr (Nat.zero_lt_succ 5)) hc
  have hsplit := Real.shift_mul_shiftedCubeSeriesBudget_le_split A c hA hcPos
  have hscaled := mul_le_mul_of_nonneg_left hsplit (Nat.cast_nonneg 18)
  have hterm := mul_le_mul_of_nonneg_left
    (Real.inverse_four_square_le_one_hundred_forty_four_of_six_le hc)
    (Nat.cast_nonneg 18)
  have htail := mul_le_mul_of_nonneg_left
    (Real.inverse_eight_square_le_one_two_hundred_eighty_eight_of_six_le hc)
    (Nat.cast_nonneg 18)
  have hparts := add_le_add
    (le_trans hterm
      (le_of_eq Real.eighteen_mul_one_one_hundred_forty_four_eq_one_eighth))
    (le_trans htail
      (le_of_eq
        Real.eighteen_mul_one_two_hundred_eighty_eight_eq_one_sixteenth))
  have hdistribute :
      18 * (1 / (4 * c ^ 2) + 1 / (8 * c ^ 2)) =
        18 * (1 / (4 * c ^ 2)) + 18 * (1 / (8 * c ^ 2)) :=
    mul_add 18 _ _
  have hreassociate :
      18 * A * Real.shiftedInverseCubeSeriesBudget A c =
        18 * (A * Real.shiftedInverseCubeSeriesBudget A c) :=
    mul_assoc 18 A _
  exact le_trans (le_of_eq hreassociate)
    (le_trans hscaled
      (le_trans (le_of_eq hdistribute)
        (le_trans hparts
          Real.one_eighth_add_one_sixteenth_le_one_fourth)))

end

end LFunctions
end Boundary
