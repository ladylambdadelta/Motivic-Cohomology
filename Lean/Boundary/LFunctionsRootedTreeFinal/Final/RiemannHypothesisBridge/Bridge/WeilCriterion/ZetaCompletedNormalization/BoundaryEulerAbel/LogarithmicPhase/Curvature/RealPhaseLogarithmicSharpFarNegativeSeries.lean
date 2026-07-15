import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicFarNegativeBudgetAssembly
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.ShiftedReciprocalAngularSharpBudget

/-!
# Sharp complete far-negative series budget

This owner replaces the obsolete integral-only negative-tail ledger.  The
inverse-square term includes its first lattice packet, while both cubic terms
retain the residual gap supplied by their logarithmic coefficients.  The
complete negative tail costs three constant units and one square-root unit.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseSharpFarNegativeSeriesMajorant
    (t : ℝ) : ℝ :=
  3 + Real.sqrt (1 + ‖t‖)

theorem Complex.logarithmicPhaseFarNegative_squareSeriesContribution_le_five_halves
    (t : ℝ) (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseAdaptedSquareCoefficient *
        Real.shiftedInverseSquareSeriesBudget
          (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
          Complex.logarithmicPhaseAngularStep ≤
      5 / 2 := by
  have hresidual :=
    Complex.logarithmicPhaseFarNegativeResidualGap_nonneg
      t (a : ℤ)
      (Int.ofNat_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry))
  unfold Complex.logarithmicPhaseAdaptedSquareCoefficient
  unfold Complex.logarithmicPhaseAngularStep
  exact
    Real.forty_eight_mul_shiftedSquareSeriesBudget_le_five_halves_two_pi
      _ hresidual

theorem Complex.logarithmicPhaseFarNegative_curvatureSeriesContribution_le_one_fourth
    (t : ℝ) (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t (a : ℤ) *
        Real.shiftedInverseCubeSeriesBudget
          (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
          Complex.logarithmicPhaseAngularStep ≤
      1 / 4 := by
  have hresidual :=
    Complex.logarithmicPhaseFarNegativeResidualGap_nonneg
      t (a : ℤ)
      (Int.ofNat_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry))
  have hcoefficient :=
    Complex.logarithmicPhaseFarNegative_curvatureCubeCoefficient_le
      t a (Real.logarithmicPhaseLongBranchGeometry_two_le_a hgeometry)
  have hseriesNonneg := Real.shiftedInverseCubeSeriesBudget_nonneg
    hresidual Complex.logarithmicPhaseAngularStep_pos
  have hscaled := mul_le_mul_of_nonneg_right hcoefficient hseriesNonneg
  exact le_trans hscaled
    (Real.eighteen_mul_shiftedCubeSeriesBudget_le_one_fourth
      (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
      Complex.logarithmicPhaseAngularStep hresidual
      Real.two_mul_pi_ge_six.le)

theorem Complex.logarithmicPhaseFarNegative_thirdSeriesContribution_le_one_fourth
    (t : ℝ) (a b : ℕ)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseAdaptedThirdCubeCoefficient
          t (a : ℤ) (b : ℤ) *
        Real.shiftedInverseCubeSeriesBudget
          (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
          Complex.logarithmicPhaseAngularStep ≤
      1 / 4 := by
  have hresidual :=
    Complex.logarithmicPhaseFarNegativeResidualGap_nonneg
      t (a : ℤ)
      (Int.ofNat_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry))
  have hcoefficient :=
    Complex.logarithmicPhaseFarNegative_thirdCubeCoefficient_le
      t a b hgeometry
  have hcoefficientEighteen :
      (21 / 2 : ℝ) *
          Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ) ≤
        18 * Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ) :=
    mul_le_mul_of_nonneg_right Real.twenty_one_halves_le_eighteen hresidual
  have hcoefficientBound := le_trans hcoefficient hcoefficientEighteen
  have hseriesNonneg := Real.shiftedInverseCubeSeriesBudget_nonneg
    hresidual Complex.logarithmicPhaseAngularStep_pos
  have hscaled := mul_le_mul_of_nonneg_right hcoefficientBound hseriesNonneg
  exact le_trans hscaled
    (Real.eighteen_mul_shiftedCubeSeriesBudget_le_one_fourth
      (Complex.logarithmicPhaseFarNegativeResidualGap t (a : ℤ))
      Complex.logarithmicPhaseAngularStep hresidual
      Real.two_mul_pi_ge_six.le)

theorem Real.five_halves_add_one_fourth_add_one_fourth_eq_three :
    (5 / 2 : ℝ) + 1 / 4 + 1 / 4 = 3 := by
  have htwoNe : (2 : ℝ) ≠ 0 := ne_of_gt zero_lt_two
  have hfourNe : (4 : ℝ) ≠ 0 :=
    ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos 3))
  have hfiveHalves : (5 / 2 : ℝ) = 10 / 4 := by
    have hleft : (5 : ℝ) * 4 = 20 := by
      have hnat : (5 * 4 : ℕ) = 20 := rfl
      exact Eq.trans (Nat.cast_mul 5 4).symm
        (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
          Nat.cast_ofNat)
    have hright : (10 : ℝ) * 2 = 20 := by
      have hnat : (10 * 2 : ℕ) = 20 := rfl
      exact Eq.trans (Nat.cast_mul 10 2).symm
        (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
          Nat.cast_ofNat)
    exact (div_eq_div_iff htwoNe hfourNe).mpr
      (Eq.trans hleft hright.symm)
  have hfirst : (10 / 4 : ℝ) + 1 / 4 = 11 / 4 :=
    Eq.trans (div_add_div_same 10 1 4)
      (congrArg (fun value : ℝ => value / 4)
        (show (10 : ℝ) + 1 = 11 by
          have hnat : (10 + 1 : ℕ) = 11 := rfl
          have hten : ((10 : ℕ) : ℝ) = 10 := Nat.cast_ofNat
          have hone : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
          have heleven : ((11 : ℕ) : ℝ) = 11 := Nat.cast_ofNat
          have hleft :
              (10 : ℝ) + 1 = ((10 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) :=
            congrArg₂ (fun left right : ℝ => left + right) hten.symm hone.symm
          have hcastAdd :
              ((10 + 1 : ℕ) : ℝ) =
                ((10 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) :=
            Nat.cast_add 10 1
          exact Eq.trans hleft
            (Eq.trans hcastAdd.symm
              (Eq.trans
                (congrArg (fun value : ℕ => (value : ℝ)) hnat)
                heleven))))
  have hsecond : (11 / 4 : ℝ) + 1 / 4 = 12 / 4 :=
    Eq.trans (div_add_div_same 11 1 4)
      (congrArg (fun value : ℝ => value / 4)
        (show (11 : ℝ) + 1 = 12 by
          have hnat : (11 + 1 : ℕ) = 12 := rfl
          have heleven : ((11 : ℕ) : ℝ) = 11 := Nat.cast_ofNat
          have hone : ((1 : ℕ) : ℝ) = 1 := Nat.cast_one
          have htwelve : ((12 : ℕ) : ℝ) = 12 := Nat.cast_ofNat
          have hleft :
              (11 : ℝ) + 1 = ((11 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) :=
            congrArg₂ (fun left right : ℝ => left + right)
              heleven.symm hone.symm
          have hcastAdd :
              ((11 + 1 : ℕ) : ℝ) =
                ((11 : ℕ) : ℝ) + ((1 : ℕ) : ℝ) :=
            Nat.cast_add 11 1
          exact Eq.trans hleft
            (Eq.trans hcastAdd.symm
              (Eq.trans
                (congrArg (fun value : ℕ => (value : ℝ)) hnat)
                htwelve))))
  have htwelveFourths : (12 / 4 : ℝ) = 3 :=
    (div_eq_iff hfourNe).mpr
      (show (3 : ℝ) * 4 = 12 by
        have hnat : (3 * 4 : ℕ) = 12 := rfl
        exact Eq.trans (Nat.cast_mul 3 4).symm
          (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
            Nat.cast_ofNat)).symm
  exact Eq.trans (congrArg (fun value : ℝ => value + 1 / 4)
      (Eq.trans (congrArg (fun value : ℝ => value + 1 / 4) hfiveHalves)
        hfirst))
    (Eq.trans hsecond htwelveFourths)

theorem Complex.logarithmicPhaseEnhancedFarNegativeSeriesBudget_le_sharpMajorant
    (t : ℝ) (a b : ℕ)
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseEnhancedFarNegativeSeriesBudget
        t (a : ℤ) (b : ℤ) ≤
      Complex.logarithmicPhaseSharpFarNegativeSeriesMajorant t := by
  have hsquare :=
    Complex.logarithmicPhaseFarNegative_squareSeriesContribution_le_five_halves
      t a b hgeometry
  have hcurvature :=
    Complex.logarithmicPhaseFarNegative_curvatureSeriesContribution_le_one_fourth
      t a b hgeometry
  have hthird :=
    Complex.logarithmicPhaseFarNegative_thirdSeriesContribution_le_one_fourth
      t a b hgeometry
  have hfourth :=
    Complex.logarithmicPhaseFarNegative_fourthSeriesContribution_le_sqrt
      t a b hgeometry
  unfold Complex.logarithmicPhaseEnhancedFarNegativeSeriesBudget
  unfold Real.shiftedReciprocalPacketSeriesBudget
  unfold Complex.logarithmicPhaseSharpFarNegativeSeriesMajorant
  have hsum := add_le_add
    (add_le_add (add_le_add hsquare hcurvature) hthird) hfourth
  exact le_trans hsum
    (le_of_eq
      (congrArg (fun value : ℝ => value + Real.sqrt (1 + ‖t‖))
        Real.five_halves_add_one_fourth_add_one_fourth_eq_three))

theorem Complex.logarithmicPhaseEnhancedFarNegativeTailBudget_le_sharpMajorant
    (t : ℝ) (a b : ℕ)
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseEnhancedFarNegativeTailBudget
        t (a : ℤ) (b : ℤ) ≤
      Complex.logarithmicPhaseSharpFarNegativeSeriesMajorant t := by
  have hseries :=
    Complex.logarithmicPhaseEnhancedFarNegativeTailBudget_le_seriesBudget
      t (a : ℤ) (b : ℤ)
      (Int.ofNat_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry))
      (Int.ofNat_le.mpr
        (Real.logarithmicPhaseLongBranchGeometry_order hgeometry))
  exact le_trans hseries
    (Complex.logarithmicPhaseEnhancedFarNegativeSeriesBudget_le_sharpMajorant
      t a b ht hgeometry)

end

end LFunctions
end Boundary
