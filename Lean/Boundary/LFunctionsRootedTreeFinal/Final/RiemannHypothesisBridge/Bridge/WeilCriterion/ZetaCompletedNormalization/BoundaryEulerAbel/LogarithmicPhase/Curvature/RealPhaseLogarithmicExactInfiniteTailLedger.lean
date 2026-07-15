import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicJointEndpointCollar
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicExactPositiveTail

/-!
# Exact infinite-tail constants

The positive tail constant is retained as `61683/4608`.  The far-negative
series is retained as four constant units plus one square-root unit.  This
avoids both integer roundings in the global constant ledger.
-/

namespace Boundary
namespace LFunctions

noncomputable section

private theorem realOfNat_add_eq_of_nat_eq
    (a b c : ℕ) (h : a + b = c) :
    (a : ℝ) + (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_add a b).symm
    (congrArg (fun n : ℕ => (n : ℝ)) h)

private theorem realOfNat_mul_eq_of_nat_eq
    (a b c : ℕ) (h : a * b = c) :
    (a : ℝ) * (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_mul a b).symm
    (congrArg (fun n : ℕ => (n : ℝ)) h)

private theorem realNatZero_add_one_eq_one :
    (((0 : ℕ) : ℝ) + 1) = 1 :=
  Eq.trans
    (congrArg (fun value : ℝ => value + 1)
      (show (((0 : ℕ) : ℝ)) = 0 from Nat.cast_zero))
    (zero_add 1)

private theorem eight_thirds_add_two_thirds_add_two_thirds_eq_four :
    (8 / 3 : ℝ) + 2 / 3 + 2 / 3 = 4 := by
  have hfirst : (8 / 3 : ℝ) + 2 / 3 = (8 + 2) / 3 :=
    div_add_div_same 8 2 3
  have hsecond : ((8 + 2 : ℝ) / 3) + 2 / 3 =
      ((8 + 2) + 2) / 3 :=
    div_add_div_same (8 + 2) 2 3
  have heightAddTwo : (8 : ℝ) + 2 = 10 :=
    realOfNat_add_eq_of_nat_eq 8 2 10 rfl
  have htenAddTwo : (10 : ℝ) + 2 = 12 :=
    realOfNat_add_eq_of_nat_eq 10 2 12 rfl
  have hnumerator : (8 + 2 : ℝ) + 2 = 12 :=
    Eq.trans
      (congrArg (fun value : ℝ => value + 2) heightAddTwo)
      htenAddTwo
  have hthree : (3 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 2))
  have htwelveDivThree : (12 / 3 : ℝ) = 4 :=
    (div_eq_iff hthree).mpr
      (realOfNat_mul_eq_of_nat_eq 4 3 12 rfl).symm
  exact Eq.trans
    (congrArg (fun value : ℝ => value + 2 / 3) hfirst)
    (Eq.trans hsecond
      (Eq.trans
        (congrArg (fun numerator : ℝ => numerator / 3) hnumerator)
        htwelveDivThree))

private theorem twenty_one_halves_le_eighteen :
    (21 / 2 : ℝ) ≤ 18 := by
  have htwoPos : (0 : ℝ) < 2 := zero_lt_two
  have hnat : (21 : ℕ) ≤ 36 :=
    Eq.subst (motive := fun value : ℕ => 21 ≤ value)
      (show 21 + 15 = 36 from rfl)
      (Nat.le_add_right 21 15)
  have hreal : (21 : ℝ) ≤ 36 := Nat.cast_le.mpr hnat
  have hproduct : (18 : ℝ) * 2 = 36 :=
    realOfNat_mul_eq_of_nat_eq 18 2 36 rfl
  exact (div_le_iff₀ htwoPos).mpr
    (Eq.subst (motive := fun value : ℝ => 21 ≤ value)
      hproduct.symm hreal)

private theorem two_mul_seven_fourths_le_six :
    (2 : ℝ) * (7 / 4) ≤ 6 := by
  have htwo : (2 : ℝ) ≠ 0 := ne_of_gt zero_lt_two
  have hfour : (4 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 3))
  have htwoMulSeven : (2 : ℝ) * 7 = 14 :=
    realOfNat_mul_eq_of_nat_eq 2 7 14 rfl
  have hfourteenDivFour : (14 / 4 : ℝ) = 7 / 2 :=
    (div_eq_div_iff hfour htwo).mpr
      ((realOfNat_mul_eq_of_nat_eq 14 2 28 rfl).trans
        (realOfNat_mul_eq_of_nat_eq 7 4 28 rfl).symm)
  have hnormalize : (2 : ℝ) * (7 / 4) = 7 / 2 :=
    Eq.trans (mul_div_assoc' 2 7 4)
      (Eq.trans
        (congrArg (fun numerator : ℝ => numerator / 4) htwoMulSeven)
        hfourteenDivFour)
  have hnat : (7 : ℕ) ≤ 12 :=
    Eq.subst (motive := fun value : ℕ => 7 ≤ value)
      (show 7 + 5 = 12 from rfl)
      (Nat.le_add_right 7 5)
  have hsevenTwelve : (7 : ℝ) ≤ 12 := Nat.cast_le.mpr hnat
  have hsixMulTwo : (6 : ℝ) * 2 = 12 :=
    realOfNat_mul_eq_of_nat_eq 6 2 12 rfl
  have hhalfLe : (7 / 2 : ℝ) ≤ 6 :=
    (div_le_iff₀ zero_lt_two).mpr
      (Eq.subst (motive := fun value : ℝ => 7 ≤ value)
        hsixMulTwo.symm hsevenTwelve)
  exact Eq.subst (motive := fun value : ℝ => value ≤ 6)
    hnormalize.symm hhalfLe

def Complex.logarithmicPhaseExactNegativeTailMajorant
    (t : ℝ) : ℝ :=
  4 + Real.sqrt (1 + ‖t‖)

def Complex.logarithmicPhaseExactInfiniteTailMajorant
    (t : ℝ) : ℝ :=
  Complex.logarithmicPhaseExactNegativeTailMajorant t +
    Complex.logarithmicPhaseExactPositiveTailConstant

theorem Real.shiftedInverseSquareTerm_zero_eq
    (A c : ℝ) :
    Real.shiftedInverseSquareTerm A c 0 = 1 / (A + c) ^ 2 := by
  unfold Real.shiftedInverseSquareTerm
  have hstep : c * ((((0 : ℕ) : ℝ) + 1)) = c :=
    Eq.trans
      (congrArg (fun value : ℝ => c * value)
        realNatZero_add_one_eq_one)
      (mul_one c)
  exact congrArg (fun base : ℝ => 1 / base ^ 2)
    (congrArg (fun offset : ℝ => A + offset) hstep)

theorem Real.shiftedInverseCubeTerm_zero_eq
    (A c : ℝ) :
    Real.shiftedInverseCubeTerm A c 0 = 1 / (A + c) ^ 3 := by
  unfold Real.shiftedInverseCubeTerm
  have hstep : c * ((((0 : ℕ) : ℝ) + 1)) = c :=
    Eq.trans
      (congrArg (fun value : ℝ => c * value)
        realNatZero_add_one_eq_one)
      (mul_one c)
  exact congrArg (fun base : ℝ => 1 / base ^ 3)
    (congrArg (fun offset : ℝ => A + offset) hstep)

theorem Real.shiftedInverseFourthTerm_zero_eq
    (A c : ℝ) :
    Real.shiftedInverseFourthTerm A c 0 = 1 / (A + c) ^ 4 := by
  unfold Real.shiftedInverseFourthTerm
  have hstep : c * ((((0 : ℕ) : ℝ) + 1)) = c :=
    Eq.trans
      (congrArg (fun value : ℝ => c * value)
        realNatZero_add_one_eq_one)
      (mul_one c)
  exact congrArg (fun base : ℝ => 1 / base ^ 4)
    (congrArg (fun offset : ℝ => A + offset) hstep)

theorem Complex.logarithmicPhaseFarNegative_curvatureContribution_le_one
    (t : ℝ) (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t (a : ℤ) *
        Real.shiftedInverseCubeBudget
          (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
          Complex.logarithmicPhaseAngularStep ≤ 1 := by
  have hresidual :=
    Complex.logarithmicPhaseFarNegativeResidualGap_nonneg
      t (a : ℤ)
      (Int.ofNat_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry))
  have hangular : (6 : ℝ) ≤ Complex.logarithmicPhaseAngularStep :=
    Real.two_mul_pi_ge_six.le
  have hcoefficient :=
    Complex.logarithmicPhaseFarNegative_curvatureCubeCoefficient_le
      t a (Real.logarithmicPhaseLongBranchGeometry_two_le_a hgeometry)
  have hbudget := Real.shiftedInverseCubeBudget_nonneg
    (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
    Complex.logarithmicPhaseAngularStep hresidual
    Complex.logarithmicPhaseAngularStep_pos
  exact le_trans
    (mul_le_mul_of_nonneg_right hcoefficient hbudget)
    (Real.eighteen_mul_shiftedCubeBudget_le_one
      (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
      Complex.logarithmicPhaseAngularStep hresidual hangular)

theorem Complex.logarithmicPhaseFarNegative_thirdContribution_le_one
    (t : ℝ) (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseAdaptedThirdCubeCoefficient
          t (a : ℤ) (b : ℤ) *
        Real.shiftedInverseCubeBudget
          (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
          Complex.logarithmicPhaseAngularStep ≤ 1 := by
  have hresidual :=
    Complex.logarithmicPhaseFarNegativeResidualGap_nonneg
      t (a : ℤ)
      (Int.ofNat_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry))
  have hangular : (6 : ℝ) ≤ Complex.logarithmicPhaseAngularStep :=
    Real.two_mul_pi_ge_six.le
  have hcoefficient :=
    Complex.logarithmicPhaseFarNegative_thirdCubeCoefficient_le
      t a b hgeometry
  have hbudget := Real.shiftedInverseCubeBudget_nonneg
    (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
    Complex.logarithmicPhaseAngularStep hresidual
    Complex.logarithmicPhaseAngularStep_pos
  exact le_trans
    (mul_le_mul_of_nonneg_right hcoefficient hbudget)
    (Real.twenty_one_halves_mul_shiftedCubeBudget_le_one
      (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
      Complex.logarithmicPhaseAngularStep hresidual hangular)

theorem Complex.logarithmicPhaseFarNegative_curvatureSeriesContribution_le_two_thirds
    (t : ℝ) (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t (a : ℤ) *
        Real.shiftedInverseCubeSeriesBudget
          (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
          Complex.logarithmicPhaseAngularStep ≤ 2 / 3 := by
  have hresidual :=
    Complex.logarithmicPhaseFarNegativeResidualGap_nonneg
      t (a : ℤ)
      (Int.ofNat_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry))
  have hangular : (6 : ℝ) ≤ Complex.logarithmicPhaseAngularStep :=
    Real.two_mul_pi_ge_six.le
  have hcoefficient :=
    Complex.logarithmicPhaseFarNegative_curvatureCubeCoefficient_le
      t a (Real.logarithmicPhaseLongBranchGeometry_two_le_a hgeometry)
  have hseriesNonneg := Real.shiftedInverseCubeSeriesBudget_nonneg
    (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
    Complex.logarithmicPhaseAngularStep hresidual
    Complex.logarithmicPhaseAngularStep_pos
  have hfirst := mul_le_mul_of_nonneg_right hcoefficient hseriesNonneg
  exact le_trans hfirst
    (Real.eighteen_mul_shiftedCubeSeriesBudget_le_two_thirds
      (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
      Complex.logarithmicPhaseAngularStep hresidual hangular)

theorem Complex.logarithmicPhaseFarNegative_thirdSeriesContribution_le_two_thirds
    (t : ℝ) (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseAdaptedThirdCubeCoefficient
          t (a : ℤ) (b : ℤ) *
        Real.shiftedInverseCubeSeriesBudget
          (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
          Complex.logarithmicPhaseAngularStep ≤ 2 / 3 := by
  have hresidual :=
    Complex.logarithmicPhaseFarNegativeResidualGap_nonneg
      t (a : ℤ)
      (Int.ofNat_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry))
  have hangular : (6 : ℝ) ≤ Complex.logarithmicPhaseAngularStep :=
    Real.two_mul_pi_ge_six.le
  have hcoefficient :=
    Complex.logarithmicPhaseFarNegative_thirdCubeCoefficient_le
      t a b hgeometry
  have hcoefficientEighteen :
      (21 / 2 : ℝ) *
          Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ) ≤
        18 * Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ) :=
    mul_le_mul_of_nonneg_right twenty_one_halves_le_eighteen hresidual
  have hcoefficientBound := le_trans hcoefficient hcoefficientEighteen
  have hseriesNonneg := Real.shiftedInverseCubeSeriesBudget_nonneg
    (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
    Complex.logarithmicPhaseAngularStep hresidual
    Complex.logarithmicPhaseAngularStep_pos
  have hfirst := mul_le_mul_of_nonneg_right hcoefficientBound hseriesNonneg
  exact le_trans hfirst
    (Real.eighteen_mul_shiftedCubeSeriesBudget_le_two_thirds
      (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
      Complex.logarithmicPhaseAngularStep hresidual hangular)

theorem Complex.logarithmicPhaseFarNegative_fourthSeriesContribution_le_sqrt
    (t : ℝ) (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient
          t (a : ℤ) (b : ℤ) *
        Real.shiftedInverseFourthSeriesBudget
          (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
          Complex.logarithmicPhaseAngularStep ≤
      Real.sqrt (1 + ‖t‖) := by
  have hresidual :=
   Complex.logarithmicPhaseFarNegativeResidualGap_nonneg
     t (a : ℤ)
     (Int.ofNat_le.mpr
       (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry))
  have hseriesNonneg := Real.shiftedInverseFourthSeriesBudget_nonneg
   (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
   Complex.logarithmicPhaseAngularStep hresidual
   Complex.logarithmicPhaseAngularStep_pos
  have hcoefficient :=
   Complex.logarithmicPhase_curvatureFourthCoefficient_le_sqrtScale
     t a b hgeometry
  have hfirst := mul_le_mul_of_nonneg_right hcoefficient hseriesNonneg
  have htwiceScale :
     2 * (7 / 4 : ℝ) ≤ Complex.logarithmicPhaseAngularStep :=
   le_trans two_mul_seven_fourths_le_six Real.two_mul_pi_ge_six.le
  have hconstant :=
   Real.three_mul_scale_fourth_mul_shiftedFourthSeriesBudget_le_one
     (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
     (7 / 4 : ℝ) Complex.logarithmicPhaseAngularStep hresidual
     (div_nonneg (Nat.cast_nonneg 7) (Nat.cast_nonneg 4))
     Complex.logarithmicPhaseAngularStep_pos htwiceScale
  have hsqrtNonneg := Real.sqrt_nonneg (1 + ‖t‖)
  have hlast := mul_le_mul_of_nonneg_right hconstant hsqrtNonneg
  have hreorder :
     (3 * (7 / 4 : ℝ) ^ 4 * Real.sqrt (1 + ‖t‖)) *
         Real.shiftedInverseFourthSeriesBudget
           (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
           Complex.logarithmicPhaseAngularStep =
       (3 * (7 / 4 : ℝ) ^ 4 *
         Real.shiftedInverseFourthSeriesBudget
           (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
           Complex.logarithmicPhaseAngularStep) *
         Real.sqrt (1 + ‖t‖) := by
    exact Eq.trans
     (mul_assoc (3 * (7 / 4 : ℝ) ^ 4) (Real.sqrt (1 + ‖t‖))
       (Real.shiftedInverseFourthSeriesBudget
         (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
         Complex.logarithmicPhaseAngularStep))
     (Eq.trans
       (congrArg
         (fun value : ℝ => (3 * (7 / 4 : ℝ) ^ 4) * value)
         (mul_comm (Real.sqrt (1 + ‖t‖))
           (Real.shiftedInverseFourthSeriesBudget
             (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
             Complex.logarithmicPhaseAngularStep)))
       (mul_assoc (3 * (7 / 4 : ℝ) ^ 4)
         (Real.shiftedInverseFourthSeriesBudget
           (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
           Complex.logarithmicPhaseAngularStep)
         (Real.sqrt (1 + ‖t‖))).symm)
  have hnormalizedFirst := le_trans hfirst (le_of_eq hreorder)
  have hnormalizedLast := le_trans hlast
    (le_of_eq (one_mul (Real.sqrt (1 + ‖t‖))))
  exact le_trans hnormalizedFirst hnormalizedLast

theorem Complex.logarithmicPhaseEnhancedFarNegativeSeriesBudget_le_exactMajorant
    (t : ℝ) (a b : ℕ)
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseEnhancedFarNegativeSeriesBudget
        t (a : ℤ) (b : ℤ) ≤
      Complex.logarithmicPhaseExactNegativeTailMajorant t := by
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
  have hcurvature :=
    Complex.logarithmicPhaseFarNegative_curvatureSeriesContribution_le_two_thirds
      t a b hgeometry
  have hthird :=
    Complex.logarithmicPhaseFarNegative_thirdSeriesContribution_le_two_thirds
      t a b hgeometry
  have hfourth :=
    Complex.logarithmicPhaseFarNegative_fourthSeriesContribution_le_sqrt
      t a b hgeometry
  unfold Complex.logarithmicPhaseEnhancedFarNegativeSeriesBudget
  unfold Real.shiftedReciprocalPacketSeriesBudget
  unfold Complex.logarithmicPhaseExactNegativeTailMajorant
  have hsum := add_le_add
    (add_le_add (add_le_add hsquare hcurvature) hthird) hfourth
  exact le_trans hsum
    (le_of_eq
      (congrArg (fun constant : ℝ => constant + Real.sqrt (1 + ‖t‖))
        eight_thirds_add_two_thirds_add_two_thirds_eq_four))

theorem Complex.logarithmicPhaseEnhancedFarNegativeTailBudget_le_exactMajorant
    (t : ℝ) (a b : ℕ)
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseEnhancedFarNegativeTailBudget
        t (a : ℤ) (b : ℤ) ≤
      Complex.logarithmicPhaseExactNegativeTailMajorant t := by
  have hseries :=
    Complex.logarithmicPhaseEnhancedFarNegativeTailBudget_le_seriesBudget
      t (a : ℤ) (b : ℤ)
      (Int.ofNat_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry))
      (Int.ofNat_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_order hgeometry))
  exact le_trans hseries
    (Complex.logarithmicPhaseEnhancedFarNegativeSeriesBudget_le_exactMajorant
      t a b ht hgeometry)

theorem Complex.logarithmicPhaseSharpOutsideTailBudget_le_exactMajorant
    (t : ℝ) (a b : ℕ)
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseSharpOutsideTailBudget
        t (a : ℤ) (b : ℤ) ≤
      Complex.logarithmicPhaseExactInfiniteTailMajorant t := by
  have hnegative :=
    Complex.logarithmicPhaseEnhancedFarNegativeTailBudget_le_exactMajorant
      t a b ht hgeometry
  have hpositive :=
    Complex.logarithmicPhaseEnhancedPositiveTailBudget_le_exactConstant
      t a b ht hgeometry
  unfold Complex.logarithmicPhaseSharpOutsideTailBudget
  unfold Complex.logarithmicPhaseExactInfiniteTailMajorant
  exact add_le_add hnegative hpositive

theorem Complex.logarithmicPhaseExactPositiveTailConstant_lt_fourteen :
    Complex.logarithmicPhaseExactPositiveTailConstant < 14 := by
  unfold Complex.logarithmicPhaseExactPositiveTailConstant
  have hsum : (61683 : ℝ) + 2829 = 64512 :=
    realOfNat_add_eq_of_nat_eq 61683 2829 64512 rfl
  have hproduct : (14 : ℝ) * 4608 = 64512 :=
    realOfNat_mul_eq_of_nat_eq 14 4608 64512 rfl
  have hstrictRaw : (61683 : ℝ) < 61683 + 2829 :=
    lt_add_of_pos_right 61683
      (Nat.cast_pos.mpr (Nat.succ_pos 2828))
  have hstrict : (61683 : ℝ) < 64512 :=
    Eq.subst (motive := fun value : ℝ => 61683 < value)
      hsum hstrictRaw
  have htarget : (61683 : ℝ) < 14 * 4608 :=
    Eq.subst (motive := fun value : ℝ => 61683 < value)
      hproduct.symm hstrict
  exact (div_lt_iff₀
    (Nat.cast_pos.mpr (Nat.succ_pos 4607))).mpr
    htarget

end

end LFunctions
end Boundary
