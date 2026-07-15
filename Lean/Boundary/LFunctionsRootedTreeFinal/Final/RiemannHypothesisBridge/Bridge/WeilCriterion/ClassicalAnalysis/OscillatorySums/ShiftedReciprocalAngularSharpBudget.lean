import Mathlib.Data.Real.Pi.Bounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.ShiftedReciprocalNegativeCubicBudget

/-!
# Sharp angular-step reciprocal budgets

The decimal lower bound `3.14 < π` gives a rational lower bound for the
angular lattice step.  This owner combines that bound with the complete
shifted inverse-square series, including its first discrete term.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.one_hundred_fifty_seven_twenty_fifths_lt_two_pi :
    (157 / 25 : ℝ) < 2 * Real.pi := by
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  have htwice := mul_lt_mul_of_pos_left hpi zero_lt_two
  have hscientific : (3.14 : ℝ) = 157 / 50 := by
    have hscientificCast := Rat.cast_ofScientific (K := ℝ) 314 true 2
    have hscientificRat :
        (3.14 : ℚ) = mkRat 314 (10 ^ 2) :=
      Eq.trans
        (Rat.ofScientific_eq_ofScientific 314 true 2).symm
        Rat.ofScientific_true_def
    have hhundred : (10 ^ 2 : ℕ) = 100 := rfl
    have hscientificRatHundred :
        (3.14 : ℚ) = mkRat 314 100 :=
      Eq.trans hscientificRat
        (congrArg (mkRat 314) hhundred)
    have hcastRatHundred :=
      congrArg (fun value : ℚ => (value : ℝ)) hscientificRatHundred
    have hhundredNe : (100 : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 99))
    have hmkCast : ((mkRat 314 100 : ℚ) : ℝ) = 314 / 100 :=
      Rat.cast_mkRat_of_ne_zero 314 hhundredNe
    have hfiftyNe : (50 : ℝ) ≠ 0 :=
      ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 49))
    have hreduceCross : (314 : ℝ) * 50 = 157 * 100 := by
      have hnat : (314 * 50 : ℕ) = 157 * 100 := rfl
      exact Eq.trans (Nat.cast_mul 314 50).symm
        (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
          (Nat.cast_mul 157 100))
    have hreduce : (314 / 100 : ℝ) = 157 / 50 :=
      (div_eq_div_iff hhundredNe hfiftyNe).mpr hreduceCross
    exact Eq.trans hscientificCast.symm
      (Eq.trans hcastRatHundred (Eq.trans hmkCast hreduce))
  have htwoTimesNumerator : (2 : ℝ) * 157 = 314 := by
    have hnat : (2 * 157 : ℕ) = 314 := rfl
    exact Eq.trans (Nat.cast_mul 2 157).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have hcross : (314 : ℝ) * 25 = 157 * 50 := by
    have hnat : (314 * 25 : ℕ) = 157 * 50 := rfl
    exact Eq.trans (Nat.cast_mul 314 25).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        (Nat.cast_mul 157 50))
  have hfraction : (314 / 50 : ℝ) = 157 / 25 :=
    (div_eq_div_iff
      (ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 49)))
      (ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 24)))).mpr hcross
  have hdecimal : (2 : ℝ) * 3.14 = 157 / 25 := by
    exact Eq.trans
      (congrArg (fun value : ℝ => 2 * value) hscientific)
      (Eq.trans
        (mul_div_assoc (2 : ℝ) 157 50).symm
        (Eq.trans
          (congrArg (fun value : ℝ => value / 50) htwoTimesNumerator)
          hfraction))
  exact Eq.subst (motive := fun value : ℝ => value < 2 * Real.pi)
    hdecimal htwice

theorem Real.one_hundred_fifty_seven_twenty_fifths_le_two_pi :
    (157 / 25 : ℝ) ≤ 2 * Real.pi :=
  le_of_lt Real.one_hundred_fifty_seven_twenty_fifths_lt_two_pi

theorem Real.one_hundred_fifty_seven_twenty_fifths_pos :
    (0 : ℝ) < 157 / 25 :=
  div_pos
    (Nat.cast_pos.mpr (Nat.succ_pos 156))
    (Nat.cast_pos.mpr (Nat.succ_pos 24))

theorem Real.one_hundred_fifty_seven_twenty_fifths_square :
    (157 / 25 : ℝ) ^ 2 = 24649 / 625 := by
  have hnumerator : (157 : ℝ) * 157 = 24649 := by
    have hnat : (157 * 157 : ℕ) = 24649 := rfl
    exact Eq.trans (Nat.cast_mul 157 157).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have hdenominator : (25 : ℝ) * 25 = 625 := by
    have hnat : (25 * 25 : ℕ) = 625 := rfl
    exact Eq.trans (Nat.cast_mul 25 25).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  exact Eq.trans (pow_two (157 / 25 : ℝ))
    (Eq.trans (div_mul_div_comm 157 25 157 25)
      (congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
        hnumerator hdenominator))

theorem Real.two_pi_square_ge_twenty_four_thousand_six_hundred_forty_nine_over_six_hundred_twenty_five :
    (24649 / 625 : ℝ) ≤ (2 * Real.pi) ^ 2 := by
  have hsquare := pow_le_pow_left₀
    Real.one_hundred_fifty_seven_twenty_fifths_pos.le
    Real.one_hundred_fifty_seven_twenty_fifths_le_two_pi 2
  exact Eq.subst
    (motive := fun value : ℝ => value ≤ (2 * Real.pi) ^ 2)
    Real.one_hundred_fifty_seven_twenty_fifths_square hsquare

theorem Real.reciprocal_two_pi_square_le_six_hundred_twenty_five_over_twenty_four_thousand_six_hundred_forty_nine :
    1 / (2 * Real.pi) ^ 2 ≤ (625 / 24649 : ℝ) := by
  have hlowerPos : (0 : ℝ) < 24649 / 625 :=
    div_pos
      (Nat.cast_pos.mpr (Nat.succ_pos 24648))
      (Nat.cast_pos.mpr (Nat.succ_pos 624))
  have hinverse := one_div_le_one_div_of_le hlowerPos
    Real.two_pi_square_ge_twenty_four_thousand_six_hundred_forty_nine_over_six_hundred_twenty_five
  have hnormalize : 1 / (24649 / 625 : ℝ) = 625 / 24649 :=
    one_div_div 24649 625
  exact le_trans hinverse (le_of_eq hnormalize)

theorem Real.shiftedInverseSquareSeriesBudget_le_two_inverseSquare
    (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) :
    Real.shiftedInverseSquareSeriesBudget A c ≤ 2 * (1 / c ^ 2) := by
  have hbaseOrder : c ≤ A + c := le_add_of_nonneg_left hA
  have hpowerOrder : c ^ 2 ≤ (A + c) ^ 2 :=
    pow_le_pow_left₀ hc.le hbaseOrder 2
  have htermInverse := one_div_le_one_div_of_le (pow_pos hc 2) hpowerOrder
  have hterm :
      Real.shiftedInverseSquareTerm A c 0 ≤ 1 / c ^ 2 :=
    le_trans
      (le_of_eq (Real.shiftedInverseSquareTerm_zero_eq_base A c))
      htermInverse
  have hbudgetDrop :=
    Real.shiftedInverseSquareBudget_le_zeroShift A c hA hc
  have hbudgetBase := Real.shiftedInverseSquareBudget_eq_base
    (A := 0) (c := c) (le_refl 0) hc
  have hzeroAdd : (0 : ℝ) + c = c := zero_add c
  have hdenominator : c * ((0 : ℝ) + c) = c ^ 2 :=
    Eq.trans
      (congrArg (fun value : ℝ => c * value) hzeroAdd)
      (pow_two c).symm
  have hbudgetNormalize :
      1 / (c * ((0 : ℝ) + c)) = 1 / c ^ 2 :=
    congrArg (fun value : ℝ => 1 / value) hdenominator
  have hbudgetZero :
      Real.shiftedInverseSquareBudget 0 c = 1 / c ^ 2 :=
    Eq.trans hbudgetBase hbudgetNormalize
  have hbudget :
      Real.shiftedInverseSquareBudget A c ≤ 1 / c ^ 2 :=
    le_trans hbudgetDrop (le_of_eq hbudgetZero)
  have hsum := add_le_add hterm hbudget
  have hcollect : (1 / c ^ 2) + (1 / c ^ 2) = 2 * (1 / c ^ 2) := by
    exact Eq.trans
      (congrArg₂ (fun left right : ℝ => left + right)
        (one_mul (1 / c ^ 2)).symm
        (one_mul (1 / c ^ 2)).symm)
      (Eq.trans (add_mul 1 1 (1 / c ^ 2)).symm
        (congrArg (fun value : ℝ => value * (1 / c ^ 2))
          one_add_one_eq_two))
  unfold Real.shiftedInverseSquareSeriesBudget
  exact le_trans hsum (le_of_eq hcollect)

theorem Real.forty_eight_mul_shiftedSquareSeriesBudget_le_five_halves_two_pi
    (A : ℝ) (hA : 0 ≤ A) :
    48 * Real.shiftedInverseSquareSeriesBudget A (2 * Real.pi) ≤
      5 / 2 := by
  have hseries := Real.shiftedInverseSquareSeriesBudget_le_two_inverseSquare
    A (2 * Real.pi) hA (mul_pos zero_lt_two Real.pi_pos)
  have hfortyEightNonneg : (0 : ℝ) ≤ 48 := Nat.cast_nonneg 48
  have hscaled := mul_le_mul_of_nonneg_left hseries hfortyEightNonneg
  have hcoefficient : (48 : ℝ) * 2 = 96 := by
    have hnat : (48 * 2 : ℕ) = 96 := rfl
    exact Eq.trans (Nat.cast_mul 48 2).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have hreassociate :
      48 * (2 * (1 / (2 * Real.pi) ^ 2)) =
        96 * (1 / (2 * Real.pi) ^ 2) :=
    Eq.trans (mul_assoc 48 2 _).symm
      (congrArg (fun value : ℝ => value * (1 / (2 * Real.pi) ^ 2))
        hcoefficient)
  have hninetySixNonneg : (0 : ℝ) ≤ 96 := Nat.cast_nonneg 96
  have hinverseScaled := mul_le_mul_of_nonneg_left
    Real.reciprocal_two_pi_square_le_six_hundred_twenty_five_over_twenty_four_thousand_six_hundred_forty_nine
    hninetySixNonneg
  have hproduct : (96 : ℝ) * 625 = 60000 := by
    have hnat : (96 * 625 : ℕ) = 60000 := rfl
    exact Eq.trans (Nat.cast_mul 96 625).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have hfraction : (96 : ℝ) * (625 / 24649) = 60000 / 24649 :=
    Eq.trans (mul_div_assoc (96 : ℝ) 625 24649).symm
      (congrArg (fun value : ℝ => value / 24649) hproduct)
  have hdenominatorPos : (0 : ℝ) < 24649 :=
    Nat.cast_pos.mpr (Nat.succ_pos 24648)
  have htarget : (60000 / 24649 : ℝ) ≤ 5 / 2 := by
    have htwoPos : (0 : ℝ) < 2 := zero_lt_two
    have hcrossLeft : (60000 : ℝ) * 2 = 120000 := by
      have hnat : (60000 * 2 : ℕ) = 120000 := rfl
      exact Eq.trans (Nat.cast_mul 60000 2).symm
        (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
          Nat.cast_ofNat)
    have hcrossRight : (5 : ℝ) * 24649 = 123245 := by
      have hnat : (5 * 24649 : ℕ) = 123245 := rfl
      exact Eq.trans (Nat.cast_mul 5 24649).symm
        (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
          Nat.cast_ofNat)
    have hnatLe : (120000 : ℕ) ≤ 123245 := by
      exact Eq.subst (motive := fun value : ℕ => 120000 ≤ value)
        (show 120000 + 3245 = 123245 from rfl)
        (Nat.le_add_right 120000 3245)
    have hrealLe : (120000 : ℝ) ≤ 123245 := Nat.cast_le.mpr hnatLe
    exact (div_le_div_iff₀ hdenominatorPos htwoPos).mpr
      (le_trans (le_of_eq hcrossLeft)
        (le_trans hrealLe (le_of_eq hcrossRight.symm)))
  exact le_trans hscaled
    (le_trans (le_of_eq hreassociate)
      (le_trans hinverseScaled
        (le_trans (le_of_eq hfraction) htarget)))

end

end LFunctions
end Boundary
