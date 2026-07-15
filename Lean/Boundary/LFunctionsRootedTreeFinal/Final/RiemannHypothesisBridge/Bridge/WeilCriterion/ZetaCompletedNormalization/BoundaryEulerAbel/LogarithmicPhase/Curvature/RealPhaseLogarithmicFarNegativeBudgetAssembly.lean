import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicSquareRootTransport

/-!
# Assembly of the far-negative refined-scale budget

The square term is bounded by a fixed constant.  Both cubic terms are bounded
using one residual power, while the fourth term is bounded by the square-root
scale after dropping its nonnegative residual shift.  The resulting constants
fit comfortably inside sixteen refined-scale units.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.logarithmicPhaseFarNegative_curvatureCubeCoefficient_le
    (t : ℝ) (a : ℕ)
    (ha : 2 ≤ a) :
    Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t (a : ℤ) ≤
      18 * Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ) := by
  unfold Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient
  have hcurvature :=
    Complex.curvature_le_three_mul_farNegativeResidual t a ha
  have hscaled := mul_le_mul_of_nonneg_left hcurvature (Nat.cast_nonneg 6)
  have hnormalize :
      6 * (3 * Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ)) =
        18 * Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ) := by
    exact Eq.trans (mul_assoc 6 3 _).symm
      (congrArg (fun coefficient : ℝ => coefficient *
        Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
        (Real.transition_nat_cast_mul 6 3 18 rfl))
  exact le_trans hscaled (le_of_eq hnormalize)

theorem Complex.logarithmicPhaseFarNegative_thirdCubeCoefficient_le
    (t : ℝ) (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseAdaptedThirdCubeCoefficient
        t (a : ℤ) (b : ℤ) ≤
      (21 / 2 : ℝ) *
        Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ) := by
  unfold Complex.logarithmicPhaseAdaptedThirdCubeCoefficient
  unfold Complex.logarithmicPhaseAdaptedThirdDerivativeUpper
  have ha := Real.logarithmicPhaseLongBranchGeometry_two_le_a hgeometry
  have hleft := Complex.quantitativeSupportLeft_pos_of_two_le a ha
  have hlengthRatio := (Complex.longGeometry_sharp_support_ratios hgeometry).2
  have hcurvature :=
    Complex.curvature_le_three_mul_farNegativeResidual t a ha
  have habInt : (a : ℤ) ≤ (b : ℤ) := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_order hgeometry)
  have hlengthNonneg :=
    Complex.logarithmicPhaseQuantitativeSupportLength_nonneg
      (a : ℤ) (b : ℤ) habInt
  have hlengthDiv :
      Complex.logarithmicPhaseQuantitativeSupportLength (a : ℤ) (b : ℤ) /
          Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ) ≤
        (7 / 4 : ℝ) := by
    exact (div_le_iff₀ hleft).mpr hlengthRatio
  have hlengthDivNonneg : 0 ≤
      Complex.logarithmicPhaseQuantitativeSupportLength (a : ℤ) (b : ℤ) /
        Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ) :=
    div_nonneg hlengthNonneg hleft.le
  have hproduct := mul_le_mul hlengthDiv hcurvature
    (Complex.logarithmicPhaseAdaptedCurvatureUpper_nonneg t _ hleft.le)
    (div_nonneg (Nat.cast_nonneg 7) (Nat.cast_nonneg 4))
  have hcurvatureFormula :
      Complex.logarithmicPhaseAdaptedCurvatureUpper t
          (Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ)) =
        ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ) ^ 2 :=
    rfl
  have hproductFormula :
      (Complex.logarithmicPhaseQuantitativeSupportLength (a : ℤ) (b : ℤ) /
          Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ)) *
        (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ) ^ 2) ≤
      (7 / 4 : ℝ) *
        (3 * Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ)) :=
    Eq.subst
      (motive := fun value : ℝ =>
        (Complex.logarithmicPhaseQuantitativeSupportLength (a : ℤ) (b : ℤ) /
          Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ)) * value ≤
            (7 / 4 : ℝ) *
              (3 * Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ)))
      hcurvatureFormula hproduct
  have hleftNormalize :
      Complex.logarithmicPhaseQuantitativeSupportLength (a : ℤ) (b : ℤ) *
          (2 * ‖t‖ /
            Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ) ^ 3) =
        2 *
          (Complex.logarithmicPhaseQuantitativeSupportLength (a : ℤ) (b : ℤ) /
            Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ)) *
          (‖t‖ /
            Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ) ^ 2) := by
    let L := Complex.logarithmicPhaseQuantitativeSupportLength (a : ℤ) (b : ℤ)
    let left := Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ)
    let T := ‖t‖
    have hnumerator : L * (2 * T) = (2 * L) * T := by
      exact Eq.trans (mul_assoc L 2 T).symm
        (congrArg (fun value : ℝ => value * T) (mul_comm L 2))
    have hdenominator : left ^ 3 = left * left ^ 2 := pow_succ' left 2
    have horiginal :
        L * (2 * T / left ^ 3) = (L * (2 * T)) / left ^ 3 :=
      (mul_div_assoc L (2 * T) (left ^ 3)).symm
    have hsplit :
        2 * (L / left) * (T / left ^ 2) =
          ((2 * L) * T) / (left * left ^ 2) := by
      have hfirst : 2 * (L / left) = (2 * L) / left :=
        (mul_div_assoc 2 L left).symm
      exact Eq.trans
        (congrArg (fun value : ℝ => value * (T / left ^ 2)) hfirst)
        (div_mul_div_comm (2 * L) left T (left ^ 2))
    exact Eq.trans horiginal
      (Eq.trans
        (congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
          hnumerator hdenominator)
        hsplit.symm)
  have hrightNormalize :
      2 * ((7 / 4 : ℝ) *
        (3 * Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))) =
      (21 / 2 : ℝ) *
        Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ) := by
    have hsevenTimesThree : (7 : ℝ) * 3 = 21 :=
      Real.transition_nat_cast_mul 7 3 21 rfl
    have htwoTimesTwentyOne : (2 : ℝ) * 21 = 42 :=
      Real.transition_nat_cast_mul 2 21 42 rfl
    have hcross : (42 : ℝ) * 2 = 21 * 4 := by
      have hleftProduct : (42 : ℝ) * 2 = 84 :=
        Real.transition_nat_cast_mul 42 2 84 rfl
      have hrightProduct : (21 : ℝ) * 4 = 84 :=
        Real.transition_nat_cast_mul 21 4 84 rfl
      exact Eq.trans hleftProduct hrightProduct.symm
    have hfraction : (42 / 4 : ℝ) = 21 / 2 :=
      (div_eq_div_iff (ne_of_gt zero_lt_four) (ne_of_gt zero_lt_two)).mpr hcross
    have hcoefficient : (2 : ℝ) * ((7 / 4) * 3) = 21 / 2 := by
      exact Eq.trans
        (congrArg (fun value : ℝ => 2 * value)
          (Eq.trans (div_mul_eq_mul_div 7 4 3)
            (congrArg (fun value : ℝ => value / 4) hsevenTimesThree)))
        (Eq.trans (mul_div_assoc (2 : ℝ) 21 4).symm
          (Eq.trans
            (congrArg (fun value : ℝ => value / 4) htwoTimesTwentyOne)
            hfraction))
    exact Eq.trans
      (congrArg (fun value : ℝ => 2 * value)
        (mul_assoc (7 / 4 : ℝ) 3 _).symm)
      (Eq.trans (mul_assoc 2 ((7 / 4 : ℝ) * 3) _).symm
        (congrArg (fun coefficient : ℝ => coefficient *
          Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
          hcoefficient))
  have htwice := mul_le_mul_of_nonneg_left hproductFormula (Nat.cast_nonneg 2)
  have htwiceAssociated :
      2 *
          (Complex.logarithmicPhaseQuantitativeSupportLength (a : ℤ) (b : ℤ) /
            Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ)) *
          (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ) ^ 2) ≤
        2 * ((7 / 4 : ℝ) *
          (3 * Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))) :=
    le_trans
      (le_of_eq
        (mul_assoc 2
          (Complex.logarithmicPhaseQuantitativeSupportLength (a : ℤ) (b : ℤ) /
            Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ))
          (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ) ^ 2)))
      htwice
  exact le_trans (le_of_eq hleftNormalize)
    (le_trans htwiceAssociated (le_of_eq hrightNormalize))

theorem Real.eighteen_mul_shiftedCubeBudget_le_one
    (A c : ℝ) (hA : 0 ≤ A)
    (hc : (6 : ℝ) ≤ c) :
    18 * A * Real.shiftedInverseCubeBudget A c ≤ 1 := by
  have hcPos : 0 < c := lt_of_lt_of_le
    (Nat.cast_pos.mpr (Nat.zero_lt_succ 5)) hc
  have habsorb := Real.shift_mul_shiftedCubeBudget_le A c hA hcPos
  have hscaled := mul_le_mul_of_nonneg_left habsorb (Nat.cast_nonneg 18)
  have hcSquare : (36 : ℝ) ≤ c ^ 2 := by
    have hsquare := Real.square_le_square_of_nonneg
      (Nat.cast_nonneg 6) hc
    have hsixSquare : (6 : ℝ) ^ 2 = 36 :=
      Eq.trans (pow_two 6) (Real.transition_nat_cast_mul 6 6 36 rfl)
    exact le_trans (le_of_eq hsixSquare.symm) hsquare
  have hdenominator : (288 : ℝ) ≤ 8 * c ^ 2 := by
    have hscaled := mul_le_mul_of_nonneg_left hcSquare (Nat.cast_nonneg 8)
    have hproduct : (8 : ℝ) * 36 = 288 :=
      Real.transition_nat_cast_mul 8 36 288 rfl
    exact le_trans (le_of_eq hproduct.symm) hscaled
  have hfraction : (18 : ℝ) / (8 * c ^ 2) ≤ 1 :=
    (div_le_one (mul_pos
      (Nat.cast_pos.mpr (Nat.zero_lt_succ 7)) (pow_pos hcPos 2))).mpr
      (le_trans (by
        have hsum : (18 : ℝ) + 270 = 288 :=
          Real.transition_nat_cast_add 18 270 288 rfl
        exact (le_add_of_nonneg_right (Nat.cast_nonneg 270)).trans_eq hsum)
        hdenominator)
  have hright :
      18 * (1 / (8 * c ^ 2)) = 18 / (8 * c ^ 2) := by
    exact Eq.trans (mul_div_assoc (18 : ℝ) 1 (8 * c ^ 2)).symm
      (congrArg (fun value : ℝ => value / (8 * c ^ 2)) (mul_one 18))
  exact le_trans (le_of_eq (mul_assoc 18 A _))
    (le_trans hscaled (le_trans (le_of_eq hright) hfraction))

theorem Real.twenty_one_halves_mul_shiftedCubeBudget_le_one
    (A c : ℝ) (hA : 0 ≤ A)
    (hc : (6 : ℝ) ≤ c) :
    (21 / 2 : ℝ) * A * Real.shiftedInverseCubeBudget A c ≤ 1 := by
  have hcPos : 0 < c := lt_of_lt_of_le
    (Nat.cast_pos.mpr (Nat.zero_lt_succ 5)) hc
  have habsorb := Real.shift_mul_shiftedCubeBudget_le A c hA hcPos
  have hcoefficient : (0 : ℝ) ≤ 21 / 2 :=
    div_nonneg (Nat.cast_nonneg 21) (Nat.cast_nonneg 2)
  have hscaled := mul_le_mul_of_nonneg_left habsorb hcoefficient
  have hcSquare : (36 : ℝ) ≤ c ^ 2 := by
    have hsquare := Real.square_le_square_of_nonneg
      (Nat.cast_nonneg 6) hc
    have hsixSquare : (6 : ℝ) ^ 2 = 36 :=
      Eq.trans (pow_two 6) (Real.transition_nat_cast_mul 6 6 36 rfl)
    exact le_trans (le_of_eq hsixSquare.symm) hsquare
  have hdenominator : (288 : ℝ) ≤ 8 * c ^ 2 := by
    have hscaled := mul_le_mul_of_nonneg_left hcSquare (Nat.cast_nonneg 8)
    have hproduct : (8 : ℝ) * 36 = 288 :=
      Real.transition_nat_cast_mul 8 36 288 rfl
    exact le_trans (le_of_eq hproduct.symm) hscaled
  have hnumerator : (21 / 2 : ℝ) ≤ 288 := by
    have htwoPos : (0 : ℝ) < 2 := zero_lt_two
    have hsum : (21 : ℝ) + 555 = 576 :=
      Real.transition_nat_cast_add 21 555 576 rfl
    have hproduct : (288 : ℝ) * 2 = 576 :=
      Real.transition_nat_cast_mul 288 2 576 rfl
    exact (div_le_iff₀ htwoPos).mpr
      ((le_add_of_nonneg_right (Nat.cast_nonneg 555)).trans_eq
        (Eq.trans hsum hproduct.symm))
  have hfraction : (21 / 2 : ℝ) / (8 * c ^ 2) ≤ 1 :=
    (div_le_one (mul_pos
      (Nat.cast_pos.mpr (Nat.zero_lt_succ 7)) (pow_pos hcPos 2))).mpr
      (le_trans hnumerator hdenominator)
  have hright :
      (21 / 2 : ℝ) * (1 / (8 * c ^ 2)) =
        (21 / 2 : ℝ) / (8 * c ^ 2) := by
    exact Eq.trans (mul_div_assoc (21 / 2 : ℝ) 1 (8 * c ^ 2)).symm
      (congrArg (fun value : ℝ => value / (8 * c ^ 2))
        (mul_one (21 / 2 : ℝ)))
  exact le_trans (le_of_eq (mul_assoc (21 / 2 : ℝ) A _))
    (le_trans hscaled (le_trans (le_of_eq hright) hfraction))

theorem Real.shiftedInverseSquareBudget_zero_eq
    (c : ℝ) (hc : 0 < c) :
    Real.shiftedInverseSquareBudget 0 c = 1 / c ^ 2 := by
  have hbase := Real.shiftedInverseSquareBudget_eq_base
    (A := (0 : ℝ)) (c := c) (le_refl 0) hc
  have hdenominator : c * ((0 : ℝ) + c) = c ^ 2 := by
    exact Eq.trans (congrArg (fun value : ℝ => c * value) (zero_add c))
      (pow_two c).symm
  exact Eq.trans hbase
    (congrArg (fun denominator : ℝ => 1 / denominator) hdenominator)

theorem Real.shiftedInverseFourthBudget_zero_eq
    (c : ℝ) (hc : 0 < c) :
    Real.shiftedInverseFourthBudget 0 c = 1 / (3 * c ^ 4) := by
  have hbase := Real.shiftedInverseFourthBudget_eq_base
    (A := (0 : ℝ)) (c := c) (le_refl 0) hc
  have hpower : c ^ 4 = c * c ^ 3 := pow_succ' c 3
  have hdenominator :
      ((3 : ℝ) * c) * ((0 : ℝ) + c) ^ 3 = 3 * c ^ 4 := by
    exact Eq.trans
      (congrArg (fun value : ℝ => ((3 : ℝ) * c) * value)
        (congrArg (fun value : ℝ => value ^ 3) (zero_add c)))
      (Eq.trans (mul_assoc 3 c (c ^ 3))
        (congrArg (fun value : ℝ => 3 * value) hpower.symm))
  exact Eq.trans hbase
    (congrArg (fun denominator : ℝ => 1 / denominator) hdenominator)

theorem Real.square_ge_thirty_six_of_six_le
    {c : ℝ} (hc : (6 : ℝ) ≤ c) :
    (36 : ℝ) ≤ c ^ 2 := by
  have hsquare := Real.square_le_square_of_nonneg (Nat.cast_nonneg 6) hc
  have hsixSquare : (6 : ℝ) ^ 2 = 36 :=
    Eq.trans (pow_two 6) (Real.transition_nat_cast_mul 6 6 36 rfl)
  exact le_trans (le_of_eq hsixSquare.symm) hsquare

theorem Real.one_div_square_le_one_thirty_six_of_six_le
    {c : ℝ} (hc : (6 : ℝ) ≤ c) :
    1 / c ^ 2 ≤ 1 / 36 := by
  exact one_div_le_one_div_of_le
    (Nat.cast_pos.mpr (Nat.zero_lt_succ 35))
    (Real.square_ge_thirty_six_of_six_le hc)

theorem Real.forty_eight_mul_one_thirty_six_eq_four_thirds :
    (48 : ℝ) * (1 / 36) = 4 / 3 := by
  have hcross : (48 : ℝ) * 3 = 4 * 36 := by
    have hleft : (48 : ℝ) * 3 = 144 :=
      Real.transition_nat_cast_mul 48 3 144 rfl
    have hright : (4 : ℝ) * 36 = 144 :=
      Real.transition_nat_cast_mul 4 36 144 rfl
    exact Eq.trans hleft hright.symm
  have hfraction : (48 / 36 : ℝ) = 4 / 3 :=
    (div_eq_div_iff
      (ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 35)))
      (ne_of_gt zero_lt_three)).mpr hcross
  exact Eq.trans (mul_one_div 48 36) hfraction

theorem Real.four_thirds_add_four_thirds_eq_eight_thirds :
    (4 / 3 : ℝ) + 4 / 3 = 8 / 3 := by
  have hsum : (4 : ℝ) + 4 = 8 :=
    Real.transition_nat_cast_add 4 4 8 rfl
  exact Eq.trans (div_add_div_same 4 4 3)
    (congrArg (fun numerator : ℝ => numerator / 3) hsum)

theorem Real.shiftedInverseSquareTerm_zero_le_inverseSquare
    (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) :
    Real.shiftedInverseSquareTerm A c 0 ≤ 1 / c ^ 2 := by
  have hbaseOrder : c ≤ A + c := le_add_of_nonneg_left hA
  have hpowerOrder : c ^ 2 ≤ (A + c) ^ 2 :=
    pow_le_pow_left₀ hc.le hbaseOrder 2
  have hinverse := one_div_le_one_div_of_le (pow_pos hc 2) hpowerOrder
  exact le_trans
    (le_of_eq (Real.shiftedInverseSquareTerm_zero_eq_base A c))
    hinverse

theorem Real.forty_eight_mul_shiftedSquareSeriesBudget_le_eight_thirds
    (A c : ℝ) (hA : 0 ≤ A) (hc : (6 : ℝ) ≤ c) :
    48 * Real.shiftedInverseSquareSeriesBudget A c ≤ 8 / 3 := by
  have hcPos : 0 < c := lt_of_lt_of_le
    (Nat.cast_pos.mpr (Nat.zero_lt_succ 5)) hc
  have hinverse := Real.one_div_square_le_one_thirty_six_of_six_le hc
  have hsingle : (48 : ℝ) * (1 / c ^ 2) ≤ 4 / 3 :=
    le_trans
      (mul_le_mul_of_nonneg_left hinverse (Nat.cast_nonneg 48))
      (le_of_eq Real.forty_eight_mul_one_thirty_six_eq_four_thirds)
  have hterm := Real.shiftedInverseSquareTerm_zero_le_inverseSquare
    A c hA hcPos
  have hbudgetDrop := Real.shiftedInverseSquareBudget_le_zeroShift
    A c hA hcPos
  have hbudgetZero := Real.shiftedInverseSquareBudget_zero_eq c hcPos
  have hbudget : Real.shiftedInverseSquareBudget A c ≤ 1 / c ^ 2 :=
    le_trans hbudgetDrop (le_of_eq hbudgetZero)
  have htermScaled :
      48 * Real.shiftedInverseSquareTerm A c 0 ≤ 4 / 3 :=
    le_trans (mul_le_mul_of_nonneg_left hterm (Nat.cast_nonneg 48)) hsingle
  have hbudgetScaled :
      48 * Real.shiftedInverseSquareBudget A c ≤ 4 / 3 :=
    le_trans (mul_le_mul_of_nonneg_left hbudget (Nat.cast_nonneg 48)) hsingle
  have hsum := add_le_add htermScaled hbudgetScaled
  have hexpand :
      48 * Real.shiftedInverseSquareSeriesBudget A c =
        48 * Real.shiftedInverseSquareTerm A c 0 +
          48 * Real.shiftedInverseSquareBudget A c := by
    unfold Real.shiftedInverseSquareSeriesBudget
    exact mul_add 48 _ _
  exact le_trans (le_of_eq hexpand)
    (le_trans hsum
      (le_of_eq Real.four_thirds_add_four_thirds_eq_eight_thirds))

theorem Real.shift_mul_shiftedCubeTerm_zero_le_inverseSquare
    (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) :
    A * Real.shiftedInverseCubeTerm A c 0 ≤ 1 / c ^ 2 := by
  have hbasePos : 0 < A + c := add_pos_of_nonneg_of_pos hA hc
  have hbaseOrder : c ≤ A + c := le_add_of_nonneg_left hA
  have hshiftOrder : A ≤ A + c := le_add_of_nonneg_right hc.le
  have hleft :
      A * Real.shiftedInverseCubeTerm A c 0 = A / (A + c) ^ 3 := by
    exact Eq.trans
      (congrArg (fun value : ℝ => A * value)
        (Real.shiftedInverseCubeTerm_zero_eq_base A c))
      (mul_one_div A ((A + c) ^ 3))
  have hfraction : A / (A + c) ^ 3 ≤ (A + c) / (A + c) ^ 3 :=
    div_le_div_of_nonneg_right hshiftOrder (pow_nonneg hbasePos.le 3)
  have hpower : (A + c) ^ 3 = (A + c) ^ 2 * (A + c) :=
    pow_succ (A + c) 2
  have hcancel :
      (A + c) / ((A + c) ^ 2 * (A + c)) = 1 / (A + c) ^ 2 :=
    Eq.trans
      (div_mul_cancel_right₀ (ne_of_gt hbasePos) ((A + c) ^ 2))
      (one_div ((A + c) ^ 2)).symm
  have hright : (A + c) / (A + c) ^ 3 = 1 / (A + c) ^ 2 :=
    Eq.trans
      (congrArg (fun denominator : ℝ => (A + c) / denominator) hpower)
      hcancel
  have hbaseBound :
      A * Real.shiftedInverseCubeTerm A c 0 ≤ 1 / (A + c) ^ 2 :=
    le_trans (le_of_eq hleft)
      (le_trans hfraction (le_of_eq hright))
  have hpowerOrder : c ^ 2 ≤ (A + c) ^ 2 :=
    pow_le_pow_left₀ hc.le hbaseOrder 2
  exact le_trans hbaseBound
    (one_div_le_one_div_of_le (pow_pos hc 2) hpowerOrder)

theorem Real.eighteen_mul_one_thirty_six_eq_one_half :
    (18 : ℝ) * (1 / 36) = 1 / 2 := by
  have hcross : (18 : ℝ) * 2 = 1 * 36 := by
    exact Eq.trans (Real.transition_nat_cast_mul 18 2 36 rfl)
      (one_mul (36 : ℝ)).symm
  have hfraction : (18 / 36 : ℝ) = 1 / 2 :=
    (div_eq_div_iff
      (ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 35)))
      (ne_of_gt zero_lt_two)).mpr hcross
  exact Eq.trans (mul_one_div 18 36) hfraction

theorem Real.one_half_add_one_sixth_eq_two_thirds :
    (1 / 2 : ℝ) + 1 / 6 = 2 / 3 := by
  have hhalf : (1 / 2 : ℝ) = 3 / 6 := by
    have hcross : (1 : ℝ) * 6 = 3 * 2 := by
      exact Eq.trans (one_mul (6 : ℝ))
        (Real.transition_nat_cast_mul 3 2 6 rfl).symm
    exact (div_eq_div_iff
      (ne_of_gt zero_lt_two)
      (ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 5)))).mpr hcross
  have hsum : (3 / 6 : ℝ) + 1 / 6 = 4 / 6 := by
    exact Eq.trans (div_add_div_same 3 1 6)
      (congrArg (fun numerator : ℝ => numerator / 6)
        three_add_one_eq_four)
  have hfourSixths : (4 / 6 : ℝ) = 2 / 3 := by
    have hcross : (4 : ℝ) * 3 = 2 * 6 := by
      exact Eq.trans (Real.transition_nat_cast_mul 4 3 12 rfl)
        (Real.transition_nat_cast_mul 2 6 12 rfl).symm
    exact (div_eq_div_iff
      (ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 5)))
      (ne_of_gt zero_lt_three)).mpr hcross
  exact Eq.trans (congrArg (fun value : ℝ => value + 1 / 6) hhalf)
    (Eq.trans hsum hfourSixths)

theorem Real.eighteen_mul_shiftedCubeSeriesBudget_le_two_thirds
    (A c : ℝ) (hA : 0 ≤ A) (hc : (6 : ℝ) ≤ c) :
    18 * A * Real.shiftedInverseCubeSeriesBudget A c ≤ 2 / 3 := by
  have hcPos : 0 < c := lt_of_lt_of_le
    (Nat.cast_pos.mpr (Nat.zero_lt_succ 5)) hc
  have hinverse := Real.one_div_square_le_one_thirty_six_of_six_le hc
  have htermBase := Real.shift_mul_shiftedCubeTerm_zero_le_inverseSquare
    A c hA hcPos
  have htermConstant : (18 : ℝ) * (1 / c ^ 2) ≤ 1 / 2 :=
    le_trans
      (mul_le_mul_of_nonneg_left hinverse (Nat.cast_nonneg 18))
      (le_of_eq Real.eighteen_mul_one_thirty_six_eq_one_half)
  have htermContribution :
      18 * (A * Real.shiftedInverseCubeTerm A c 0) ≤ 1 / 2 :=
    le_trans
      (mul_le_mul_of_nonneg_left htermBase (Nat.cast_nonneg 18))
      htermConstant
  have hbudgetBase := Real.shift_mul_shiftedCubeBudget_le A c hA hcPos
  have hdenominatorOrder : (288 : ℝ) ≤ 8 * c ^ 2 := by
    have hscaled := mul_le_mul_of_nonneg_left
      (Real.square_ge_thirty_six_of_six_le hc) (Nat.cast_nonneg 8)
    have hproduct : (8 : ℝ) * 36 = 288 :=
      Real.transition_nat_cast_mul 8 36 288 rfl
    exact le_trans (le_of_eq hproduct.symm) hscaled
  have hintegralInverse : 1 / (8 * c ^ 2) ≤ 1 / 288 :=
    one_div_le_one_div_of_le
      (Nat.cast_pos.mpr (Nat.zero_lt_succ 287)) hdenominatorOrder
  have hconstant : (18 : ℝ) * (1 / 288) = 1 / 16 := by
    have hcross : (18 : ℝ) * 16 = 1 * 288 := by
      exact Eq.trans (Real.transition_nat_cast_mul 18 16 288 rfl)
        (one_mul (288 : ℝ)).symm
    have hfraction : (18 / 288 : ℝ) = 1 / 16 :=
      (div_eq_div_iff
        (ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 287)))
        (ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 15)))).mpr hcross
    exact Eq.trans (mul_one_div 18 288) hfraction
  have hsixLeSixteen : (6 : ℝ) ≤ 16 := by
    have hsum : (6 : ℝ) + 10 = 16 :=
      Real.transition_nat_cast_add 6 10 16 rfl
    exact (le_add_of_nonneg_right (Nat.cast_nonneg 10)).trans_eq hsum
  have honeSixteenLeOneSixth : (1 / 16 : ℝ) ≤ 1 / 6 :=
    one_div_le_one_div_of_le
      (Nat.cast_pos.mpr (Nat.zero_lt_succ 5)) hsixLeSixteen
  have hbudgetContribution :
      18 * (A * Real.shiftedInverseCubeBudget A c) ≤ 1 / 6 :=
    le_trans
      (mul_le_mul_of_nonneg_left hbudgetBase (Nat.cast_nonneg 18))
      (le_trans
        (mul_le_mul_of_nonneg_left hintegralInverse (Nat.cast_nonneg 18))
        (le_trans (le_of_eq hconstant) honeSixteenLeOneSixth))
  have hcomponents := add_le_add htermContribution hbudgetContribution
  have hexpand :
      18 * A * Real.shiftedInverseCubeSeriesBudget A c =
        18 * (A * Real.shiftedInverseCubeTerm A c 0) +
          18 * (A * Real.shiftedInverseCubeBudget A c) := by
    unfold Real.shiftedInverseCubeSeriesBudget
    exact Eq.trans
      (mul_add (18 * A) _ _)
      (congrArg₂ (fun left right : ℝ => left + right)
        (mul_assoc 18 A _)
        (mul_assoc 18 A _))
  exact le_trans (le_of_eq hexpand)
    (le_trans hcomponents
      (le_of_eq Real.one_half_add_one_sixth_eq_two_thirds))

theorem Real.forty_eight_mul_shiftedSquareBudget_le_two
    (A c : ℝ) (hA : 0 ≤ A) (hc : (6 : ℝ) ≤ c) :
    48 * Real.shiftedInverseSquareBudget A c ≤ 2 := by
  have hcPos : 0 < c := lt_of_lt_of_le
    (Nat.cast_pos.mpr (Nat.zero_lt_succ 5)) hc
  have hdrop := Real.shiftedInverseSquareBudget_le_zeroShift A c hA hcPos
  have hscaled := mul_le_mul_of_nonneg_left hdrop (Nat.cast_nonneg 48)
  have hzero := Real.shiftedInverseSquareBudget_zero_eq c hcPos
  have hcSquare : (36 : ℝ) ≤ c ^ 2 := by
    have hsquare := Real.square_le_square_of_nonneg
      (Nat.cast_nonneg 6) hc
    have hsixSquare : (6 : ℝ) ^ 2 = 36 :=
      Eq.trans (pow_two 6) (Real.transition_nat_cast_mul 6 6 36 rfl)
    exact le_trans (le_of_eq hsixSquare.symm) hsquare
  have honeDiv : 1 / c ^ 2 ≤ 1 / 36 :=
    one_div_le_one_div_of_le
      (Nat.cast_pos.mpr (Nat.zero_lt_succ 35)) hcSquare
  have hfinal : 48 * (1 / c ^ 2) ≤ 2 := by
    have hmul := mul_le_mul_of_nonneg_left honeDiv (Nat.cast_nonneg 48)
    have hconstant : 48 * ((1 : ℝ) / 36) ≤ 2 := by
      have hthirtySixPos : (0 : ℝ) < 36 :=
        Nat.cast_pos.mpr (Nat.zero_lt_succ 35)
      have hsum : (48 : ℝ) + 24 = 72 :=
        Real.transition_nat_cast_add 48 24 72 rfl
      have hproduct : (2 : ℝ) * 36 = 72 :=
        Real.transition_nat_cast_mul 2 36 72 rfl
      have hdivision : (48 / 36 : ℝ) ≤ 2 :=
        (div_le_iff₀ hthirtySixPos).mpr
          ((le_add_of_nonneg_right (Nat.cast_nonneg 24)).trans_eq
            (Eq.trans hsum hproduct.symm))
      exact le_trans (le_of_eq (mul_one_div 48 36)) hdivision
    exact le_trans hmul hconstant
  have hzeroScaled :
      48 * Real.shiftedInverseSquareBudget 0 c = 48 * (1 / c ^ 2) :=
    congrArg (fun value : ℝ => 48 * value) hzero
  exact le_trans hscaled
    (le_trans (le_of_eq hzeroScaled) hfinal)

theorem Real.three_mul_scale_fourth_mul_zeroFourthBudget_le_one
    (s c : ℝ)
    (hs : 0 ≤ s) (hc : 0 < c) (hsc : s ≤ c) :
    3 * s ^ 4 * Real.shiftedInverseFourthBudget 0 c ≤ 1 := by
  have hzero := Real.shiftedInverseFourthBudget_zero_eq c hc
  have hpower := Real.square_le_square_of_nonneg hs hsc
  have hfourth : s ^ 4 ≤ c ^ 4 := by
    have hsquareNonneg : 0 ≤ s ^ 2 := sq_nonneg s
    have hsecond := Real.square_le_square_of_nonneg hsquareNonneg hpower
    have hsPower : (s ^ 2) ^ 2 = s ^ 4 := (pow_mul s 2 2).symm
    have hcPower : (c ^ 2) ^ 2 = c ^ 4 := (pow_mul c 2 2).symm
    exact le_trans (le_of_eq hsPower.symm)
      (le_trans hsecond (le_of_eq hcPower))
  have hdenominatorPos : 0 < 3 * c ^ 4 :=
    mul_pos zero_lt_three (pow_pos hc 4)
  have hfraction : (3 * s ^ 4) / (3 * c ^ 4) ≤ 1 :=
    (div_le_one hdenominatorPos).mpr
      (mul_le_mul_of_nonneg_left hfourth (Nat.cast_nonneg 3))
  have hnormalize :
      3 * s ^ 4 * (1 / (3 * c ^ 4)) =
        (3 * s ^ 4) / (3 * c ^ 4) := by
    exact Eq.trans
      (congrArg (fun factor : ℝ => 3 * s ^ 4 * factor)
        (one_div (3 * c ^ 4)))
      (div_eq_mul_inv (3 * s ^ 4) (3 * c ^ 4)).symm
  have hzeroScaled :
      3 * s ^ 4 * Real.shiftedInverseFourthBudget 0 c =
        3 * s ^ 4 * (1 / (3 * c ^ 4)) :=
    congrArg (fun value : ℝ => 3 * s ^ 4 * value) hzero
  exact le_trans (le_of_eq hzeroScaled)
    (le_trans (le_of_eq hnormalize) hfraction)

theorem Real.shiftedInverseFourthTerm_zero_le_inverseFourth
    (A c : ℝ) (hA : 0 ≤ A) (hc : 0 < c) :
    Real.shiftedInverseFourthTerm A c 0 ≤ 1 / c ^ 4 := by
  have hbaseOrder : c ≤ A + c := le_add_of_nonneg_left hA
  have hpowerOrder : c ^ 4 ≤ (A + c) ^ 4 :=
    pow_le_pow_left₀ hc.le hbaseOrder 4
  have hinverse := one_div_le_one_div_of_le (pow_pos hc 4) hpowerOrder
  exact le_trans
    (le_of_eq (Real.shiftedInverseFourthTerm_zero_eq_base A c))
    hinverse

theorem Real.three_mul_scale_fourth_mul_shiftedFourthSeriesBudget_le_one
    (A s c : ℝ) (hA : 0 ≤ A) (hs : 0 ≤ s) (hc : 0 < c)
    (hsc : 2 * s ≤ c) :
    3 * s ^ 4 * Real.shiftedInverseFourthSeriesBudget A c ≤ 1 := by
  have hterm := Real.shiftedInverseFourthTerm_zero_le_inverseFourth
    A c hA hc
  have hbudgetDrop := Real.shiftedInverseFourthBudget_le_zeroShift
    A c hA hc
  have hzero := Real.shiftedInverseFourthBudget_zero_eq c hc
  have hthree : (3 : ℝ) ≠ 0 := ne_of_gt zero_lt_three
  have hthreeZeroBudget :
      3 * Real.shiftedInverseFourthBudget 0 c = 1 / c ^ 4 := by
    exact Eq.trans
      (congrArg (fun value : ℝ => 3 * value) hzero)
      (Eq.trans (mul_one_div 3 (3 * c ^ 4))
        (Eq.trans (div_mul_cancel_left₀ hthree (c ^ 4))
          (one_div (c ^ 4)).symm))
  have htermToZeroBudget :
      Real.shiftedInverseFourthTerm A c 0 ≤
        3 * Real.shiftedInverseFourthBudget 0 c :=
    le_trans hterm (le_of_eq hthreeZeroBudget.symm)
  have hsum := add_le_add htermToZeroBudget hbudgetDrop
  have hcollect :
      3 * Real.shiftedInverseFourthBudget 0 c +
          Real.shiftedInverseFourthBudget 0 c =
        4 * Real.shiftedInverseFourthBudget 0 c := by
    exact Eq.trans
      (congrArg
        (fun value : ℝ =>
          3 * Real.shiftedInverseFourthBudget 0 c + value)
        (one_mul (Real.shiftedInverseFourthBudget 0 c)).symm)
      (Eq.trans (add_mul 3 1 _).symm
        (congrArg
          (fun coefficient : ℝ => coefficient *
            Real.shiftedInverseFourthBudget 0 c)
          three_add_one_eq_four))
  have hseries : Real.shiftedInverseFourthSeriesBudget A c ≤
      4 * Real.shiftedInverseFourthBudget 0 c := by
    unfold Real.shiftedInverseFourthSeriesBudget
    exact le_trans hsum (le_of_eq hcollect)
  have hcoefficientNonneg : 0 ≤ 3 * s ^ 4 :=
    mul_nonneg (Nat.cast_nonneg 3) (pow_nonneg hs 4)
  have hscaled := mul_le_mul_of_nonneg_left hseries hcoefficientNonneg
  have htwoPow : (2 : ℝ) ^ 4 = 16 := by
    have hnat : (2 ^ 4 : ℕ) = 16 := rfl
    exact Eq.trans (Nat.cast_pow 2 4).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have hfourLeSixteen : (4 : ℝ) ≤ 16 := by
    have hsum : (4 : ℝ) + 12 = 16 :=
      Real.transition_nat_cast_add 4 12 16 rfl
    exact (le_add_of_nonneg_right (Nat.cast_nonneg 12)).trans_eq hsum
  have hpowerRaw : 4 * s ^ 4 ≤ 16 * s ^ 4 :=
    mul_le_mul_of_nonneg_right hfourLeSixteen (pow_nonneg hs 4)
  have htwoScalePower : (2 * s) ^ 4 = 16 * s ^ 4 :=
    Eq.trans (mul_pow 2 s 4)
      (congrArg (fun coefficient : ℝ => coefficient * s ^ 4) htwoPow)
  have hpower : 4 * s ^ 4 ≤ (2 * s) ^ 4 :=
    le_trans hpowerRaw (le_of_eq htwoScalePower.symm)
  have hcoefficient := mul_le_mul_of_nonneg_left hpower
    (Nat.cast_nonneg 3)
  have hzeroBudgetNonneg := Real.shiftedInverseFourthBudget_nonneg
    0 c (le_refl 0) hc
  have hcoefficientBudget := mul_le_mul_of_nonneg_right hcoefficient
    hzeroBudgetNonneg
  have hnormalize :
      3 * s ^ 4 * (4 * Real.shiftedInverseFourthBudget 0 c) =
        (3 * (4 * s ^ 4)) * Real.shiftedInverseFourthBudget 0 c := by
    exact Eq.trans
      (mul_assoc (3 * s ^ 4) 4
        (Real.shiftedInverseFourthBudget 0 c)).symm
      (congrArg
        (fun coefficient : ℝ => coefficient *
          Real.shiftedInverseFourthBudget 0 c)
        (Eq.trans (mul_assoc 3 (s ^ 4) 4)
          (congrArg (fun value : ℝ => 3 * value)
            (mul_comm (s ^ 4) 4))))
  have htwoScaleNonneg : 0 ≤ 2 * s :=
    mul_nonneg (Nat.cast_nonneg 2) hs
  have hconstant :=
    Real.three_mul_scale_fourth_mul_zeroFourthBudget_le_one
      (2 * s) c htwoScaleNonneg hc hsc
  exact le_trans hscaled
    (le_trans (le_of_eq hnormalize)
      (le_trans hcoefficientBudget hconstant))

theorem Complex.logarithmicPhaseFarNegative_fourthContribution_le_sqrt
    (t : ℝ) (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient
        t (a : ℤ) (b : ℤ) *
      Real.shiftedInverseFourthBudget
        (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
        Complex.logarithmicPhaseAngularStep ≤
      Real.sqrt (1 + ‖t‖) := by
  have hcoefficient :=
    Complex.logarithmicPhase_curvatureFourthCoefficient_le_sqrtScale
      t a b hgeometry
  have hresidual :=
    Complex.logarithmicPhaseFarNegativeResidualGap_nonneg
      t (a : ℤ)
      (Int.ofNat_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry))
  have hstep := Complex.logarithmicPhaseAngularStep_pos
  have hdrop := Real.shiftedInverseFourthBudget_le_zeroShift
    _ _ hresidual hstep
  have hcoefficientNonneg :=
    Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient_nonneg
      t (a : ℤ) (b : ℤ)
      (Int.ofNat_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_order hgeometry))
      (Complex.quantitativeSupportLeft_pos_of_two_le a
        (Real.logarithmicPhaseLongBranchGeometry_two_le_a hgeometry)).le
  have hfirst := mul_le_mul_of_nonneg_left hdrop hcoefficientNonneg
  have hzeroNonneg := Real.shiftedInverseFourthBudget_nonneg
    0 Complex.logarithmicPhaseAngularStep (le_refl 0) hstep
  have hsecond := mul_le_mul_of_nonneg_right hcoefficient hzeroNonneg
  have hangular : (7 / 4 : ℝ) ≤ Complex.logarithmicPhaseAngularStep :=
    le_trans
      (by
        have hfourPos : (0 : ℝ) < 4 := zero_lt_four
        have hsum : (7 : ℝ) + 17 = 24 :=
          Real.transition_nat_cast_add 7 17 24 rfl
        have hproduct : (6 : ℝ) * 4 = 24 :=
          Real.transition_nat_cast_mul 6 4 24 rfl
        exact (div_le_iff₀ hfourPos).mpr
          ((le_add_of_nonneg_right (Nat.cast_nonneg 17)).trans_eq
            (Eq.trans hsum hproduct.symm)))
      Real.two_mul_pi_ge_six.le
  have hconstant := Real.three_mul_scale_fourth_mul_zeroFourthBudget_le_one
    (7 / 4 : ℝ) Complex.logarithmicPhaseAngularStep
    (div_nonneg (Nat.cast_nonneg 7) (Nat.cast_nonneg 4)) hstep hangular
  have hsqrtNonneg := Real.sqrt_nonneg (1 + ‖t‖)
  have hlast := mul_le_mul_of_nonneg_right hconstant hsqrtNonneg
  let K : ℝ := 3 * (7 / 4 : ℝ) ^ 4
  let S : ℝ := Real.sqrt (1 + ‖t‖)
  let B : ℝ := Real.shiftedInverseFourthBudget
    0 Complex.logarithmicPhaseAngularStep
  have hmiddleNormalize : (K * S) * B = (K * B) * S := by
    exact Eq.trans (mul_assoc K S B)
      (Eq.trans
        (congrArg (fun value : ℝ => K * value) (mul_comm S B))
        (mul_assoc K B S).symm)
  have hlastNormalize : (1 : ℝ) * S = S := one_mul S
  exact le_trans hfirst
    (le_trans hsecond
      (le_trans (le_of_eq hmiddleNormalize)
        (le_trans hlast (le_of_eq hlastNormalize))))

theorem Real.two_mul_seven_fourths_le_six :
    (2 : ℝ) * (7 / 4) ≤ 6 := by
  have htwoTimesSeven : (2 : ℝ) * 7 = 14 :=
    Real.transition_nat_cast_mul 2 7 14 rfl
  have hnormalize : (2 : ℝ) * (7 / 4) = 14 / 4 :=
    Eq.trans (mul_div_assoc' 2 7 4)
      (congrArg (fun numerator : ℝ => numerator / 4) htwoTimesSeven)
  have hsum : (14 : ℝ) + 10 = 24 :=
    Real.transition_nat_cast_add 14 10 24 rfl
  have hproduct : (6 : ℝ) * 4 = 24 :=
    Real.transition_nat_cast_mul 6 4 24 rfl
  have hfraction : (14 / 4 : ℝ) ≤ 6 :=
    (div_le_iff₀ zero_lt_four).mpr
      ((le_add_of_nonneg_right (Nat.cast_nonneg 10)).trans_eq
        (Eq.trans hsum hproduct.symm))
  exact le_trans (le_of_eq hnormalize) hfraction

theorem Complex.logarithmicPhaseFarNegative_fourthSeriesContribution_le_sqrt
    (t : ℝ) (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient
        t (a : ℤ) (b : ℤ) *
      Real.shiftedInverseFourthSeriesBudget
        (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
        Complex.logarithmicPhaseAngularStep ≤
      Real.sqrt (1 + ‖t‖) := by
  have hcoefficient :=
    Complex.logarithmicPhase_curvatureFourthCoefficient_le_sqrtScale
      t a b hgeometry
  have hresidual :=
    Complex.logarithmicPhaseFarNegativeResidualGap_nonneg
      t (a : ℤ)
      (Int.ofNat_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry))
  have hstep := Complex.logarithmicPhaseAngularStep_pos
  have hseriesNonneg := Real.shiftedInverseFourthSeriesBudget_nonneg
    hresidual hstep
  have hfirst := mul_le_mul_of_nonneg_right hcoefficient hseriesNonneg
  have hscaleNonneg : (0 : ℝ) ≤ 7 / 4 :=
    div_nonneg (Nat.cast_nonneg 7) (Nat.cast_nonneg 4)
  have hangular : (2 : ℝ) * (7 / 4) ≤
      Complex.logarithmicPhaseAngularStep :=
    le_trans Real.two_mul_seven_fourths_le_six Real.two_mul_pi_ge_six.le
  have hconstant :=
    Real.three_mul_scale_fourth_mul_shiftedFourthSeriesBudget_le_one
      (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
      (7 / 4 : ℝ) Complex.logarithmicPhaseAngularStep
      hresidual hscaleNonneg hstep hangular
  let K : ℝ := 3 * (7 / 4 : ℝ) ^ 4
  let S : ℝ := Real.sqrt (1 + ‖t‖)
  let B : ℝ := Real.shiftedInverseFourthSeriesBudget
    (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
    Complex.logarithmicPhaseAngularStep
  have hmiddle : (K * S) * B = (K * B) * S := by
    exact Eq.trans (mul_assoc K S B)
      (Eq.trans
        (congrArg (fun value : ℝ => K * value) (mul_comm S B))
        (mul_assoc K B S).symm)
  have hsqrtNonneg := Real.sqrt_nonneg (1 + ‖t‖)
  have hlast := mul_le_mul_of_nonneg_right hconstant hsqrtNonneg
  exact le_trans hfirst
    (le_trans (le_of_eq hmiddle)
      (le_trans hlast (le_of_eq (one_mul S))))

theorem Real.twenty_one_halves_le_eighteen :
    (21 / 2 : ℝ) ≤ 18 := by
  have hsum : (21 : ℝ) + 15 = 36 :=
    Real.transition_nat_cast_add 21 15 36 rfl
  have hproduct : (18 : ℝ) * 2 = 36 :=
    Real.transition_nat_cast_mul 18 2 36 rfl
  exact (div_le_iff₀ zero_lt_two).mpr
    ((le_add_of_nonneg_right (Nat.cast_nonneg 15)).trans_eq
      (Eq.trans hsum hproduct.symm))

theorem Real.eight_thirds_add_two_thirds_add_two_thirds_eq_four :
    (8 / 3 : ℝ) + 2 / 3 + 2 / 3 = 4 := by
  have hfirst : (8 / 3 : ℝ) + 2 / 3 = (8 + 2) / 3 :=
    div_add_div_same 8 2 3
  have hsecond : ((8 + 2 : ℝ) / 3) + 2 / 3 = ((8 + 2) + 2) / 3 :=
    div_add_div_same (8 + 2) 2 3
  have heightTen : (8 : ℝ) + 2 = 10 :=
    Real.transition_nat_cast_add 8 2 10 rfl
  have htenTwelve : (10 : ℝ) + 2 = 12 :=
    Real.transition_nat_cast_add 10 2 12 rfl
  have hnumerator : (8 + 2 : ℝ) + 2 = 12 :=
    Eq.trans (congrArg (fun value : ℝ => value + 2) heightTen) htenTwelve
  have htwelveDivThree : (12 / 3 : ℝ) = 4 :=
    (div_eq_iff (ne_of_gt zero_lt_three)).mpr
      (Real.transition_nat_cast_mul 4 3 12 rfl).symm
  exact Eq.trans
    (congrArg (fun value : ℝ => value + 2 / 3) hfirst)
    (Eq.trans hsecond
      (Eq.trans
        (congrArg (fun numerator : ℝ => numerator / 3) hnumerator)
        htwelveDivThree))

theorem Complex.logarithmicPhaseEnhancedFarNegativeSeriesBudget_le_five_refined
    (t : ℝ) (a b : ℕ)
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseEnhancedFarNegativeSeriesBudget
        t (a : ℤ) (b : ℤ) ≤
      5 * Real.logarithmicPhaseRefinedScale t (b : ℤ) := by
  have hresidual :=
    Complex.logarithmicPhaseFarNegativeResidualGap_nonneg
      t (a : ℤ)
      (Int.ofNat_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry))
  have hangular : (6 : ℝ) ≤ Complex.logarithmicPhaseAngularStep :=
    Real.two_mul_pi_ge_six.le
  have hsquare :
      Complex.logarithmicPhaseAdaptedSquareCoefficient *
          Real.shiftedInverseSquareSeriesBudget
            (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
            Complex.logarithmicPhaseAngularStep ≤ 8 / 3 := by
    unfold Complex.logarithmicPhaseAdaptedSquareCoefficient
    exact Real.forty_eight_mul_shiftedSquareSeriesBudget_le_eight_thirds
      _ _ hresidual hangular
  have hcurvatureCoefficient :=
    Complex.logarithmicPhaseFarNegative_curvatureCubeCoefficient_le
      t a (Real.logarithmicPhaseLongBranchGeometry_two_le_a hgeometry)
  have hcubeNonneg := Real.shiftedInverseCubeSeriesBudget_nonneg
    hresidual Complex.logarithmicPhaseAngularStep_pos
  have hcurvatureFirst := mul_le_mul_of_nonneg_right
    hcurvatureCoefficient hcubeNonneg
  have hcurvatureLast := Real.eighteen_mul_shiftedCubeSeriesBudget_le_two_thirds
    (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
    Complex.logarithmicPhaseAngularStep hresidual hangular
  have hcurvature := le_trans hcurvatureFirst hcurvatureLast
  have hthirdCoefficient :=
    Complex.logarithmicPhaseFarNegative_thirdCubeCoefficient_le
      t a b hgeometry
  have hthirdCoefficientEighteen :
      Complex.logarithmicPhaseAdaptedThirdCubeCoefficient
          t (a : ℤ) (b : ℤ) ≤
        18 * Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ) :=
    le_trans hthirdCoefficient
      (mul_le_mul_of_nonneg_right Real.twenty_one_halves_le_eighteen
        hresidual)
  have hthirdFirst := mul_le_mul_of_nonneg_right
    hthirdCoefficientEighteen hcubeNonneg
  have hthirdLast := Real.eighteen_mul_shiftedCubeSeriesBudget_le_two_thirds
    (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
    Complex.logarithmicPhaseAngularStep hresidual hangular
  have hthird := le_trans hthirdFirst hthirdLast
  have hfourth :=
    Complex.logarithmicPhaseFarNegative_fourthSeriesContribution_le_sqrt
      t a b hgeometry
  unfold Complex.logarithmicPhaseEnhancedFarNegativeSeriesBudget
  unfold Real.shiftedReciprocalPacketSeriesBudget
  have hcomponents := add_le_add
    (add_le_add (add_le_add hsquare hcurvature) hthird) hfourth
  have hsumNormalize :
      (8 / 3 : ℝ) + 2 / 3 + 2 / 3 + Real.sqrt (1 + ‖t‖) =
        4 + Real.sqrt (1 + ‖t‖) := by
    exact congrArg (fun constant : ℝ => constant + Real.sqrt (1 + ‖t‖))
      Real.eight_thirds_add_two_thirds_add_two_thirds_eq_four
  have hb : (0 : ℤ) ≤ (b : ℤ) := Int.ofNat_zero_le b
  have hone := Real.one_le_logarithmicPhaseRefinedScale t (b : ℤ) ht hb
  have hfourConstant := mul_le_mul_of_nonneg_left hone (Nat.cast_nonneg 4)
  have hsqrt := Real.sqrt_scale_le_refinedScale t (b : ℤ) hb
  have hadd := add_le_add hfourConstant hsqrt
  have haddNormalized :
      4 + Real.sqrt (1 + ‖t‖) ≤
        4 * Real.logarithmicPhaseRefinedScale t (b : ℤ) +
          Real.logarithmicPhaseRefinedScale t (b : ℤ) :=
    le_trans
      (le_of_eq
        (congrArg (fun value : ℝ => value + Real.sqrt (1 + ‖t‖))
          (mul_one (4 : ℝ)).symm))
      hadd
  have hfiveNormalize :
      4 * Real.logarithmicPhaseRefinedScale t (b : ℤ) +
          Real.logarithmicPhaseRefinedScale t (b : ℤ) =
        5 * Real.logarithmicPhaseRefinedScale t (b : ℤ) := by
    have hfourAddOne : (4 : ℝ) + 1 = 5 := by
      have hfourCast : ((4 : ℕ) : ℝ) = (4 : ℝ) := Nat.cast_ofNat
      have honeCast : ((1 : ℕ) : ℝ) = (1 : ℝ) := Nat.cast_one
      have hfiveCast : ((5 : ℕ) : ℝ) = (5 : ℝ) := Nat.cast_ofNat
      have hcastSum : ((4 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) = ((5 : ℕ) : ℝ) :=
        Real.transition_nat_cast_add 4 1 5 rfl
      exact Eq.trans
        (congrArg₂ (fun left right : ℝ => left + right)
          hfourCast.symm honeCast.symm)
        (Eq.trans hcastSum hfiveCast)
    exact Eq.trans
      (congrArg (fun value : ℝ =>
        4 * Real.logarithmicPhaseRefinedScale t (b : ℤ) + value)
        (one_mul (Real.logarithmicPhaseRefinedScale t (b : ℤ))).symm)
      (Eq.trans (add_mul 4 1 _).symm
        (congrArg (fun coefficient : ℝ => coefficient *
          Real.logarithmicPhaseRefinedScale t (b : ℤ))
          hfourAddOne))
  exact le_trans hcomponents
    (le_trans (le_of_eq hsumNormalize)
      (le_trans haddNormalized (le_of_eq hfiveNormalize)))

theorem Complex.logarithmicPhaseEnhancedFarNegativeTailBudget_le_sixteen_refined
    (t : ℝ) (a b : ℕ)
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseEnhancedFarNegativeTailBudget
        t (a : ℤ) (b : ℤ) ≤
      16 * Real.logarithmicPhaseRefinedScale t (b : ℤ) := by
  have ha := Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry
  have hab := Real.logarithmicPhaseLongBranchGeometry_order hgeometry
  have hseries :=
    Complex.logarithmicPhaseEnhancedFarNegativeTailBudget_le_seriesBudget
      t (a : ℤ) (b : ℤ)
      (Int.ofNat_le.mpr ha) (Int.ofNat_le.mpr hab)
  have hfive :=
    Complex.logarithmicPhaseEnhancedFarNegativeSeriesBudget_le_five_refined
      t a b ht hgeometry
  have hscaleNonneg := Real.logarithmicPhaseRefinedScale_nonneg
    t (b : ℤ) (Int.ofNat_zero_le b)
  have hcoefficient : (5 : ℝ) ≤ 16 :=
    (le_add_of_nonneg_right (Nat.cast_nonneg 11)).trans_eq
      (Real.transition_nat_cast_add 5 11 16 rfl)
  have henlarge := mul_le_mul_of_nonneg_right hcoefficient hscaleNonneg
  exact le_trans hseries (le_trans hfive henlarge)

end
end LFunctions
end Boundary
