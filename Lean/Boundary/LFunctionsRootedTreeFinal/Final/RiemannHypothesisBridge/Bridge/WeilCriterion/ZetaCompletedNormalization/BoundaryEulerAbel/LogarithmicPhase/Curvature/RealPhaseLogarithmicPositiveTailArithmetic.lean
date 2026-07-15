import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicCoefficientRatios
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.ShiftedReciprocalPowerBudgetArithmetic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.ShiftedReciprocalPositiveQuarticTransport

/-!
# Numerical arithmetic for the enhanced positive tail

The positive endpoint shift is `‖t‖ / right`.  Sharp dyadic support ratios
bound each logarithmic coefficient by the matching power of this shift.  The
generic shifted-series absorption theorem then gives four fixed numerical
contributions whose sum is below sixteen.
-/

namespace Boundary
namespace LFunctions

noncomputable section

private theorem positiveTail_realOfNat_add_eq_of_nat_eq
    (a b c : ℕ) (h : a + b = c) :
    (a : ℝ) + (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_add a b).symm
    (congrArg (fun n : ℕ => (n : ℝ)) h)

private theorem positiveTail_realOfNat_mul_eq_of_nat_eq
    (a b c : ℕ) (h : a * b = c) :
    (a : ℝ) * (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_mul a b).symm
    (congrArg (fun n : ℕ => (n : ℝ)) h)

def Complex.logarithmicPhasePositiveTailShift
    (t : ℝ) (b : ℕ) : ℝ :=
  ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight (b : ℤ)

def Complex.logarithmicPhasePositiveTailSquareConstant : ℝ :=
  4 / 3

def Complex.logarithmicPhasePositiveTailCurvatureConstant : ℝ :=
  121 / 32

def Complex.logarithmicPhasePositiveTailThirdConstant : ℝ :=
  847 / 384

def Complex.logarithmicPhasePositiveTailFourthConstant : ℝ :=
  9317 / 1536

def Complex.logarithmicPhasePositiveTailTotalConstant : ℝ :=
  Complex.logarithmicPhasePositiveTailSquareConstant +
    Complex.logarithmicPhasePositiveTailCurvatureConstant +
    Complex.logarithmicPhasePositiveTailThirdConstant +
    Complex.logarithmicPhasePositiveTailFourthConstant

theorem Complex.logarithmicPhasePositiveTailShift_eq_enhancedShift
    (t : ℝ) (b : ℕ) :
    Complex.logarithmicPhasePositiveTailShift t b =
      Complex.logarithmicPhaseEnhancedPositiveShift t (b : ℤ) := by
  rfl

theorem Complex.logarithmicPhasePositiveTailShift_pos
    (t : ℝ) (a b : ℕ)
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    0 < Complex.logarithmicPhasePositiveTailShift t b := by
  unfold Complex.logarithmicPhasePositiveTailShift
  have hnorm : 0 < ‖t‖ := lt_of_lt_of_le zero_lt_one ht
  have ha : (1 : ℤ) ≤ (a : ℤ) := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry)
  have hab : (a : ℤ) ≤ (b : ℤ) := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_order hgeometry)
  have hright :=
    Complex.logarithmicPhaseQuantitativeSupportRight_pos
      (a : ℤ) (b : ℤ) ha hab
  exact div_pos hnorm hright

theorem Complex.logarithmicPhasePositiveTail_curvatureCoefficient_le_shiftSquare
    (t : ℝ) (a b : ℕ)
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseAdaptedCurvatureUpper t
        (Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ)) ≤
      (11 / 4 : ℝ) ^ 2 *
        (Complex.logarithmicPhasePositiveTailShift t b) ^ 2 := by
  unfold Complex.logarithmicPhaseAdaptedCurvatureUpper
  unfold Complex.logarithmicPhasePositiveTailShift
  have hleft := Complex.quantitativeSupportLeft_pos_of_two_le a
    (Real.logarithmicPhaseLongBranchGeometry_two_le_a hgeometry)
  have ha : (1 : ℤ) ≤ (a : ℤ) := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry)
  have hab : (a : ℤ) ≤ (b : ℤ) := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_order hgeometry)
  have hright :=
    Complex.logarithmicPhaseQuantitativeSupportRight_pos
      (a : ℤ) (b : ℤ) ha hab
  have hratio :=
    (Complex.longGeometry_sharp_support_ratios hgeometry).1
  exact Real.curvature_div_left_sq_le_ratio_sq_shift_sq
    ht hleft hright
    (div_nonneg (Nat.cast_nonneg 11) (Nat.cast_nonneg 4)) hratio

theorem Complex.logarithmicPhasePositiveTail_thirdCoefficient_le_shiftSquare
    (t : ℝ) (a b : ℕ)
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseAdaptedThirdCubeCoefficient
        t (a : ℤ) (b : ℤ) ≤
      (2 * (7 / 4 : ℝ) * (11 / 4 : ℝ) ^ 2) *
        (Complex.logarithmicPhasePositiveTailShift t b) ^ 2 := by
  unfold Complex.logarithmicPhaseAdaptedThirdCubeCoefficient
  unfold Complex.logarithmicPhaseAdaptedThirdDerivativeUpper
  unfold Complex.logarithmicPhasePositiveTailShift
  have hleft := Complex.quantitativeSupportLeft_pos_of_two_le a
    (Real.logarithmicPhaseLongBranchGeometry_two_le_a hgeometry)
  have ha : (1 : ℤ) ≤ (a : ℤ) := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry)
  have hab : (a : ℤ) ≤ (b : ℤ) := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_order hgeometry)
  have hright :=
    Complex.logarithmicPhaseQuantitativeSupportRight_pos
      (a : ℤ) (b : ℤ) ha hab
  have hlength :=
    Complex.logarithmicPhaseQuantitativeSupportLength_nonneg
      (a : ℤ) (b : ℤ) hab
  have hratios := Complex.longGeometry_sharp_support_ratios hgeometry
  exact Real.third_coefficient_le_ratio_shift_sq
    ht hleft hright hlength
    (div_nonneg (Nat.cast_nonneg 11) (Nat.cast_nonneg 4))
    (div_nonneg (Nat.cast_nonneg 7) (Nat.cast_nonneg 4))
    hratios.1 hratios.2

theorem Complex.logarithmicPhasePositiveTail_fourthCoefficient_le_shiftCube
    (t : ℝ) (a b : ℕ)
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient
        t (a : ℤ) (b : ℤ) ≤
      (3 * (7 / 4 : ℝ) * (11 / 4 : ℝ) ^ 3) *
        (Complex.logarithmicPhasePositiveTailShift t b) ^ 3 := by
  unfold Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient
  unfold Complex.logarithmicPhaseAdaptedCurvatureUpper
  unfold Complex.logarithmicPhasePositiveTailShift
  have hleft := Complex.quantitativeSupportLeft_pos_of_two_le a
    (Real.logarithmicPhaseLongBranchGeometry_two_le_a hgeometry)
  have ha : (1 : ℤ) ≤ (a : ℤ) := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry)
  have hab : (a : ℤ) ≤ (b : ℤ) := Int.ofNat_le.mpr
    (Real.logarithmicPhaseLongBranchGeometry_order hgeometry)
  have hright :=
    Complex.logarithmicPhaseQuantitativeSupportRight_pos
      (a : ℤ) (b : ℤ) ha hab
  have hlength :=
    Complex.logarithmicPhaseQuantitativeSupportLength_nonneg
      (a : ℤ) (b : ℤ) hab
  have hratios := Complex.longGeometry_sharp_support_ratios hgeometry
  exact Real.fourth_coefficient_le_ratio_shift_cube
    ht hleft hright hlength
    (div_nonneg (Nat.cast_nonneg 11) (Nat.cast_nonneg 4))
    (div_nonneg (Nat.cast_nonneg 7) (Nat.cast_nonneg 4))
    hratios.1 hratios.2

theorem Real.two_mul_pi_ge_six :
    (6 : ℝ) < 2 * Real.pi := by
  have hpi := Real.pi_gt_three
  have htwoPos : (0 : ℝ) < 2 := Nat.cast_pos.mpr (Nat.zero_lt_succ 1)
  have hmul := mul_lt_mul_of_pos_left hpi htwoPos
  have hsix : (6 : ℝ) = 2 * 3 :=
    (positiveTail_realOfNat_mul_eq_of_nat_eq 2 3 6 rfl).symm
  exact lt_of_eq_of_lt hsix hmul

theorem Real.reciprocal_two_pi_le_one_sixth :
    1 / (2 * Real.pi) ≤ (1 : ℝ) / 6 := by
  have hsixPos : (0 : ℝ) < 6 :=
    Nat.cast_pos.mpr (Nat.zero_lt_succ 5)
  have hpi := Real.two_mul_pi_ge_six.le
  exact one_div_le_one_div_of_le hsixPos hpi

theorem Complex.logarithmicPhasePositiveTailTotalConstant_le_sixteen :
    Complex.logarithmicPhasePositiveTailTotalConstant ≤ 16 := by
  unfold Complex.logarithmicPhasePositiveTailTotalConstant
  unfold Complex.logarithmicPhasePositiveTailSquareConstant
  unfold Complex.logarithmicPhasePositiveTailCurvatureConstant
  unfold Complex.logarithmicPhasePositiveTailThirdConstant
  unfold Complex.logarithmicPhasePositiveTailFourthConstant
  have hthreeDenominator : (3 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 2))
  have hthirtyTwoDenominator : (32 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 31))
  have hthreeEightyFourDenominator : (384 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 383))
  have hfifteenThirtySixDenominator : (1536 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 1535))
  have hdenominator : (0 : ℝ) < 4608 :=
    Nat.cast_pos.mpr (Nat.zero_lt_succ 4607)
  have hdenominatorNe : (4608 : ℝ) ≠ 0 := ne_of_gt hdenominator
  have hnormalize :
      (4 : ℝ) / 3 + 121 / 32 + 847 / 384 + 9317 / 1536 =
        61683 / 4608 := by
    have hthree : (4 : ℝ) / 3 = 6144 / 4608 :=
      (div_eq_div_iff hthreeDenominator hdenominatorNe).mpr
        ((positiveTail_realOfNat_mul_eq_of_nat_eq 4 4608 18432 rfl).trans
          (positiveTail_realOfNat_mul_eq_of_nat_eq 6144 3 18432 rfl).symm)
    have hthirtyTwo : (121 : ℝ) / 32 = 17424 / 4608 :=
      (div_eq_div_iff hthirtyTwoDenominator hdenominatorNe).mpr
        ((positiveTail_realOfNat_mul_eq_of_nat_eq 121 4608 557568 rfl).trans
          (positiveTail_realOfNat_mul_eq_of_nat_eq 17424 32 557568 rfl).symm)
    have hthreeEightyFour : (847 : ℝ) / 384 = 10164 / 4608 :=
      (div_eq_div_iff hthreeEightyFourDenominator hdenominatorNe).mpr
        ((positiveTail_realOfNat_mul_eq_of_nat_eq 847 4608 3902976 rfl).trans
          (positiveTail_realOfNat_mul_eq_of_nat_eq 10164 384 3902976 rfl).symm)
    have hfifteenThirtySix : (9317 : ℝ) / 1536 = 27951 / 4608 :=
      (div_eq_div_iff hfifteenThirtySixDenominator hdenominatorNe).mpr
        ((positiveTail_realOfNat_mul_eq_of_nat_eq 9317 4608 42932736 rfl).trans
          (positiveTail_realOfNat_mul_eq_of_nat_eq 27951 1536 42932736 rfl).symm)
    have hreplace :
        (4 / 3 : ℝ) + 121 / 32 + 847 / 384 + 9317 / 1536 =
          6144 / 4608 + 17424 / 4608 + 10164 / 4608 + 27951 / 4608 :=
      congrArg₂ (fun left right : ℝ => left + right)
        (congrArg₂ (fun left right : ℝ => left + right)
          (congrArg₂ (fun left right : ℝ => left + right)
            hthree hthirtyTwo)
          hthreeEightyFour)
        hfifteenThirtySix
    have hfirstSum :
        (6144 / 4608 : ℝ) + 17424 / 4608 =
          (6144 + 17424) / 4608 :=
      div_add_div_same 6144 17424 4608
    have hsecondSum :
        ((6144 + 17424 : ℝ) / 4608) + 10164 / 4608 =
          ((6144 + 17424) + 10164) / 4608 :=
      div_add_div_same (6144 + 17424) 10164 4608
    have hthirdSum :
        (((6144 + 17424 : ℝ) + 10164) / 4608) + 27951 / 4608 =
          (((6144 + 17424) + 10164) + 27951) / 4608 :=
      div_add_div_same ((6144 : ℝ) + 17424 + 10164) 27951 4608
    have h6144Add17424 : (6144 : ℝ) + 17424 = 23568 :=
      positiveTail_realOfNat_add_eq_of_nat_eq 6144 17424 23568 rfl
    have h23568Add10164 : (23568 : ℝ) + 10164 = 33732 :=
      positiveTail_realOfNat_add_eq_of_nat_eq 23568 10164 33732 rfl
    have h33732Add27951 : (33732 : ℝ) + 27951 = 61683 :=
      positiveTail_realOfNat_add_eq_of_nat_eq 33732 27951 61683 rfl
    have hnumerator :
        ((6144 + 17424 : ℝ) + 10164) + 27951 = 61683 :=
      Eq.trans
        (congrArg (fun value : ℝ => value + 27951)
          (Eq.trans
            (congrArg (fun value : ℝ => value + 10164) h6144Add17424)
            h23568Add10164))
        h33732Add27951
    exact hreplace.trans
      (Eq.trans
        (congrArg (fun value : ℝ => value + 10164 / 4608 + 27951 / 4608)
          hfirstSum)
        (Eq.trans
          (congrArg (fun value : ℝ => value + 27951 / 4608) hsecondSum)
          (Eq.trans hthirdSum
            (congrArg (fun numerator : ℝ => numerator / 4608) hnumerator))))
  have hnumerator : (61683 : ℝ) ≤ 16 * 4608 := by
    have hstep : (61683 : ℝ) ≤ 61683 + 12045 :=
      le_add_of_nonneg_right (Nat.cast_nonneg 12045)
    exact le_trans hstep
      (le_of_eq
        ((positiveTail_realOfNat_add_eq_of_nat_eq 61683 12045 73728 rfl).trans
          (positiveTail_realOfNat_mul_eq_of_nat_eq 16 4608 73728 rfl).symm))
  have hfraction : (61683 : ℝ) / 4608 ≤ 16 :=
    (div_le_iff₀ hdenominator).mpr hnumerator
  exact le_trans (le_of_eq hnormalize) hfraction

theorem Complex.logarithmicPhasePositiveTailTotalConstant_eq_quarticExactMajorant :
    Complex.logarithmicPhasePositiveTailTotalConstant =
      Real.shiftedReciprocalPositiveQuarticExactMajorant := by
  unfold Complex.logarithmicPhasePositiveTailTotalConstant
  unfold Complex.logarithmicPhasePositiveTailSquareConstant
  unfold Complex.logarithmicPhasePositiveTailCurvatureConstant
  unfold Complex.logarithmicPhasePositiveTailThirdConstant
  unfold Complex.logarithmicPhasePositiveTailFourthConstant
  unfold Real.shiftedReciprocalPositiveQuarticExactMajorant
  have hthreeDenominator : (3 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 2))
  have hthirtyTwoDenominator : (32 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 31))
  have hthreeEightyFourDenominator : (384 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 383))
  have hfifteenThirtySixDenominator : (1536 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 1535))
  have hdenominator : (4608 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.zero_lt_succ 4607))
  have hthree : (4 : ℝ) / 3 = 6144 / 4608 :=
    (div_eq_div_iff hthreeDenominator hdenominator).mpr
      ((positiveTail_realOfNat_mul_eq_of_nat_eq 4 4608 18432 rfl).trans
        (positiveTail_realOfNat_mul_eq_of_nat_eq 6144 3 18432 rfl).symm)
  have hthirtyTwo : (121 : ℝ) / 32 = 17424 / 4608 :=
    (div_eq_div_iff hthirtyTwoDenominator hdenominator).mpr
      ((positiveTail_realOfNat_mul_eq_of_nat_eq 121 4608 557568 rfl).trans
        (positiveTail_realOfNat_mul_eq_of_nat_eq 17424 32 557568 rfl).symm)
  have hthreeEightyFour : (847 : ℝ) / 384 = 10164 / 4608 :=
    (div_eq_div_iff hthreeEightyFourDenominator hdenominator).mpr
      ((positiveTail_realOfNat_mul_eq_of_nat_eq 847 4608 3902976 rfl).trans
        (positiveTail_realOfNat_mul_eq_of_nat_eq 10164 384 3902976 rfl).symm)
  have hfifteenThirtySix : (9317 : ℝ) / 1536 = 27951 / 4608 :=
    (div_eq_div_iff hfifteenThirtySixDenominator hdenominator).mpr
      ((positiveTail_realOfNat_mul_eq_of_nat_eq 9317 4608 42932736 rfl).trans
        (positiveTail_realOfNat_mul_eq_of_nat_eq 27951 1536 42932736 rfl).symm)
  have hreplace :
      (4 / 3 : ℝ) + 121 / 32 + 847 / 384 + 9317 / 1536 =
        6144 / 4608 + 17424 / 4608 + 10164 / 4608 + 27951 / 4608 :=
    congrArg₂ (fun left right : ℝ => left + right)
      (congrArg₂ (fun left right : ℝ => left + right)
        (congrArg₂ (fun left right : ℝ => left + right)
          hthree hthirtyTwo)
        hthreeEightyFour)
      hfifteenThirtySix
  have hfirstSum :
      (6144 / 4608 : ℝ) + 17424 / 4608 =
        (6144 + 17424) / 4608 :=
    div_add_div_same 6144 17424 4608
  have hsecondSum :
      ((6144 + 17424 : ℝ) / 4608) + 10164 / 4608 =
        ((6144 + 17424) + 10164) / 4608 :=
    div_add_div_same (6144 + 17424) 10164 4608
  have hthirdSum :
      (((6144 + 17424 : ℝ) + 10164) / 4608) + 27951 / 4608 =
        (((6144 + 17424) + 10164) + 27951) / 4608 :=
    div_add_div_same ((6144 : ℝ) + 17424 + 10164) 27951 4608
  have h6144Add17424 : (6144 : ℝ) + 17424 = 23568 :=
    positiveTail_realOfNat_add_eq_of_nat_eq 6144 17424 23568 rfl
  have h23568Add10164 : (23568 : ℝ) + 10164 = 33732 :=
    positiveTail_realOfNat_add_eq_of_nat_eq 23568 10164 33732 rfl
  have h33732Add27951 : (33732 : ℝ) + 27951 = 61683 :=
    positiveTail_realOfNat_add_eq_of_nat_eq 33732 27951 61683 rfl
  have hnumerator :
      ((6144 + 17424 : ℝ) + 10164) + 27951 = 61683 :=
    Eq.trans
      (congrArg (fun value : ℝ => value + 27951)
        (Eq.trans
          (congrArg (fun value : ℝ => value + 10164) h6144Add17424)
          h23568Add10164))
      h33732Add27951
  exact hreplace.trans
    (Eq.trans
      (congrArg (fun value : ℝ => value + 10164 / 4608 + 27951 / 4608)
        hfirstSum)
      (Eq.trans
        (congrArg (fun value : ℝ => value + 27951 / 4608) hsecondSum)
        (Eq.trans hthirdSum
          (congrArg (fun numerator : ℝ => numerator / 4608) hnumerator))))

theorem Complex.logarithmicPhaseEnhancedPositiveSeriesBudget_le_constant
    (t : ℝ) (a b : ℕ)
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseEnhancedPositiveSeriesBudget
        t (a : ℤ) (b : ℤ) ≤
      Complex.logarithmicPhasePositiveTailTotalConstant := by
  let A : ℝ := Complex.logarithmicPhasePositiveTailShift t b
  let c : ℝ := Complex.logarithmicPhaseAngularStep
  have hA :=
    (Complex.logarithmicPhasePositiveTailShift_pos t a b ht hgeometry).le
  have hc : (6 : ℝ) ≤ c := Real.two_mul_pi_ge_six.le
  have hcPos : 0 < c :=
    lt_of_lt_of_le (Nat.cast_pos.mpr (Nat.zero_lt_succ 5)) hc
  have hcurvatureBase :=
    Complex.logarithmicPhasePositiveTail_curvatureCoefficient_le_shiftSquare
      t a b ht hgeometry
  have hcurvature :
      Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t (a : ℤ) ≤
        6 * (11 / 4 : ℝ) ^ 2 * A ^ 2 := by
    unfold Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient
    have hscaled :=
      mul_le_mul_of_nonneg_left hcurvatureBase (Nat.cast_nonneg 6)
    have hright :
        (6 : ℝ) * ((11 / 4 : ℝ) ^ 2 * A ^ 2) =
          6 * (11 / 4 : ℝ) ^ 2 * A ^ 2 :=
      (mul_assoc (6 : ℝ) ((11 / 4 : ℝ) ^ 2) (A ^ 2)).symm
    exact Eq.mp
      (congrArg
        (fun right : ℝ =>
          6 * Complex.logarithmicPhaseAdaptedCurvatureUpper
              t (Complex.logarithmicPhaseQuantitativeSupportLeft (a : ℤ)) ≤
            right)
        hright)
      hscaled
  have hthird :=
    Complex.logarithmicPhasePositiveTail_thirdCoefficient_le_shiftSquare
      t a b ht hgeometry
  have hfourth :=
    Complex.logarithmicPhasePositiveTail_fourthCoefficient_le_shiftCube
      t a b ht hgeometry
  have hsquareBudget := Real.shiftedInverseSquareSeriesBudget_nonneg hA hcPos
  have hcubeBudget := Real.shiftedInverseCubeSeriesBudget_nonneg hA hcPos
  have hfourthBudget := Real.shiftedInverseFourthSeriesBudget_nonneg hA hcPos
  have hcurvatureScaled :=
    mul_le_mul_of_nonneg_right hcurvature hcubeBudget
  have hthirdScaled := mul_le_mul_of_nonneg_right hthird hcubeBudget
  have hfourthScaled := mul_le_mul_of_nonneg_right hfourth hfourthBudget
  have hsquareScaled :
      Complex.logarithmicPhaseAdaptedSquareCoefficient *
          Real.shiftedInverseSquareSeriesBudget A c ≤
        48 * Real.shiftedInverseSquareSeriesBudget A c := by
    unfold Complex.logarithmicPhaseAdaptedSquareCoefficient
    exact le_refl _
  have hactualToBenchmark :
      Complex.logarithmicPhaseEnhancedPositiveSeriesBudget
          t (a : ℤ) (b : ℤ) ≤
        Real.shiftedReciprocalPacketSeriesBudget
          A c 48
          (6 * (11 / 4 : ℝ) ^ 2 * A ^ 2)
          (2 * (7 / 4 : ℝ) * (11 / 4 : ℝ) ^ 2 * A ^ 2)
          (3 * (7 / 4 : ℝ) * (11 / 4 : ℝ) ^ 3 * A ^ 3) := by
    unfold Complex.logarithmicPhaseEnhancedPositiveSeriesBudget
    unfold Real.shiftedReciprocalPacketSeriesBudget
    exact add_le_add
      (add_le_add (add_le_add hsquareScaled hcurvatureScaled) hthirdScaled)
      hfourthScaled
  have hbenchmark :=
    Real.shiftedReciprocalPositiveBenchmarkSeriesBudget_le_exactMajorant hA hc
  exact le_trans hactualToBenchmark
    (le_trans hbenchmark
      (le_of_eq
        Complex.logarithmicPhasePositiveTailTotalConstant_eq_quarticExactMajorant.symm))

theorem Complex.logarithmicPhaseEnhancedPositiveTailBudget_le_sixteen
    (t : ℝ) (a b : ℕ)
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseEnhancedPositiveTailBudget
        t (a : ℤ) (b : ℤ) ≤ 16 := by
  have ha := Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry
  have hab := Real.logarithmicPhaseLongBranchGeometry_order hgeometry
  have hseries :=
    Complex.logarithmicPhaseEnhancedPositiveTailBudget_le_seriesBudget
      t (a : ℤ) (b : ℤ)
      (Int.ofNat_le.mpr ha) (Int.ofNat_le.mpr hab)
  have hconstant :=
    Complex.logarithmicPhaseEnhancedPositiveSeriesBudget_le_constant
      t a b ht hgeometry
  exact le_trans hseries
    (le_trans hconstant
      Complex.logarithmicPhasePositiveTailTotalConstant_le_sixteen)

theorem Complex.logarithmicPhaseEnhancedPositiveTailBudget_le_sixteen_refined
    (t : ℝ) (a b : ℕ)
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseEnhancedPositiveTailBudget
        t (a : ℤ) (b : ℤ) ≤
      16 * Real.logarithmicPhaseRefinedScale t (b : ℤ) := by
  have hconstant :=
    Complex.logarithmicPhaseEnhancedPositiveTailBudget_le_sixteen
      t a b ht hgeometry
  have hb := Real.logarithmicPhaseLongBranchGeometry_zero_le_b_int hgeometry
  have hone := Real.one_le_logarithmicPhaseRefinedScale t (b : ℤ) ht hb
  have hscale := mul_le_mul_of_nonneg_left hone (Nat.cast_nonneg 16)
  have hscaleNormalized :
      (16 : ℝ) ≤ 16 * Real.logarithmicPhaseRefinedScale t (b : ℤ) :=
    Eq.mp
      (congrArg
        (fun left : ℝ =>
          left ≤ 16 * Real.logarithmicPhaseRefinedScale t (b : ℤ))
        (mul_one (16 : ℝ)))
      hscale
  exact le_trans hconstant hscaleNormalized

end
end LFunctions
end Boundary
