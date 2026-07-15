import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicSideSpecificActiveClosure
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicProtectedComplementBudget
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicExactPositiveTail

/-!
# Exact infinite-tail closure

The positive tail constant is `61683/4608`, hence below `14`; the shifted
far-negative series is below `5` times the refined scale.  Since the refined
scale is at least one, the two tails together cost at most `19` refined-scale
units.
-/

namespace Boundary
namespace LFunctions

noncomputable section

private theorem infiniteTail_realOfNat_add_eq_of_nat_eq
    (a b c : ℕ) (h : a + b = c) :
    (a : ℝ) + (b : ℝ) = (c : ℝ) :=
  Eq.trans (Nat.cast_add a b).symm
    (congrArg (fun n : ℕ => (n : ℝ)) h)

theorem Complex.logarithmicPhasePositiveTailTotalConstant_le_fourteen :
    Complex.logarithmicPhasePositiveTailTotalConstant ≤ 14 := by
  have hequality :=
    Complex.logarithmicPhasePositiveTailTotalConstant_eq_exact
  have hstrict :=
    Complex.logarithmicPhaseExactPositiveTailConstant_lt_fourteen_exact
  exact le_trans (le_of_eq hequality) (le_of_lt hstrict)

theorem Complex.logarithmicPhaseEnhancedPositiveTailBudget_le_fourteen
    (t : ℝ) (a b : ℕ)
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseEnhancedPositiveTailBudget
        t (a : ℤ) (b : ℤ) ≤ 14 := by
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
      Complex.logarithmicPhasePositiveTailTotalConstant_le_fourteen)

theorem Complex.logarithmicPhaseEnhancedPositiveTailBudget_le_fourteen_refined
    (t : ℝ) (a b : ℕ)
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseEnhancedPositiveTailBudget
        t (a : ℤ) (b : ℤ) ≤
      14 * Real.logarithmicPhaseRefinedScale t (b : ℤ) := by
  have hconstant :=
    Complex.logarithmicPhaseEnhancedPositiveTailBudget_le_fourteen
      t a b ht hgeometry
  have hb := Real.logarithmicPhaseLongBranchGeometry_zero_le_b_int hgeometry
  have hone := Real.one_le_logarithmicPhaseRefinedScale t (b : ℤ) ht hb
  have hscaled := mul_le_mul_of_nonneg_left hone (Nat.cast_nonneg 14)
  have hfourteenIdentity : (14 : ℝ) = 14 * 1 :=
    (mul_one (14 : ℝ)).symm
  exact le_trans hconstant
    (le_trans (le_of_eq hfourteenIdentity) hscaled)

theorem Complex.logarithmicPhaseInfiniteTailBudget_le_nineteen_refined
    (t : ℝ) (a b : ℕ)
    (ht : 1 ≤ ‖t‖)
    (hgeometry : Real.logarithmicPhaseLongBranchGeometry t a b) :
    Complex.logarithmicPhaseEnhancedFarNegativeTailBudget
          t (a : ℤ) (b : ℤ) +
        Complex.logarithmicPhaseEnhancedPositiveTailBudget
          t (a : ℤ) (b : ℤ) ≤
      19 * Real.logarithmicPhaseRefinedScale t (b : ℤ) := by
  have hnegative :=
    Complex.logarithmicPhaseEnhancedFarNegativeSeriesBudget_le_five_refined
      t a b ht hgeometry
  have ha := Real.logarithmicPhaseLongBranchGeometry_first_pos hgeometry
  have hab := Real.logarithmicPhaseLongBranchGeometry_order hgeometry
  have hnegativeSeries :=
    Complex.logarithmicPhaseEnhancedFarNegativeTailBudget_le_seriesBudget
      t (a : ℤ) (b : ℤ)
      (Int.ofNat_le.mpr ha) (Int.ofNat_le.mpr hab)
  have hnegativeFinal := le_trans hnegativeSeries hnegative
  have hpositive :=
    Complex.logarithmicPhaseEnhancedPositiveTailBudget_le_fourteen_refined
      t a b ht hgeometry
  have hadd := add_le_add hnegativeFinal hpositive
  have hfiveAddFourteen : (5 : ℝ) + 14 = 19 :=
    infiniteTail_realOfNat_add_eq_of_nat_eq 5 14 19 rfl
  have hnormalize :
      5 * Real.logarithmicPhaseRefinedScale t (b : ℤ) +
          14 * Real.logarithmicPhaseRefinedScale t (b : ℤ) =
        19 * Real.logarithmicPhaseRefinedScale t (b : ℤ) :=
    Eq.trans
      (add_mul 5 14
        (Real.logarithmicPhaseRefinedScale t (b : ℤ))).symm
      (congrArg
        (fun coefficient : ℝ =>
          coefficient * Real.logarithmicPhaseRefinedScale t (b : ℤ))
        hfiveAddFourteen)
  exact le_trans hadd (le_of_eq hnormalize)

end

end LFunctions
end Boundary
