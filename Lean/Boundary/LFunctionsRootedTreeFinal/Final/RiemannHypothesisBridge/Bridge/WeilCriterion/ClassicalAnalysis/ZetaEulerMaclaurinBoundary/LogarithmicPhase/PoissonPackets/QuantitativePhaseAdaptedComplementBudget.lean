import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedFarNegativeTail
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedEnhancedPositiveTail
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeThreeComponentBudget

/-!
# Phase-adapted complement budget

The complement budget consists of the finite in-range inactive family and the
two phase-adapted summable tails.  It replaces the old outside-range amplitude
second-derivative budget in the refined B-process assembly.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseAdaptedOutsideRangeBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseAdaptedFarNegativeTailBudget t a b +
    Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b

def Complex.logarithmicPhaseAdaptedComplementBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget t a b +
    Complex.logarithmicPhaseAdaptedOutsideRangeBudget t a b

theorem Complex.logarithmicPhaseAdaptedOutsideRangeBudget_nonneg
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseAdaptedOutsideRangeBudget t a b := by
  unfold Complex.logarithmicPhaseAdaptedOutsideRangeBudget
  have hleft :=
    (Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha).le
  have hnegative :=
    Complex.logarithmicPhaseAdaptedFarNegativeTailBudget_nonneg
      t a b hab hleft
  have hpositive :=
    tsum_nonneg (fun m =>
      Complex.logarithmicPhaseAdaptedClosedMajorant_nonneg
        t a b
        (Complex.logarithmicPhaseEnhancedPositiveModeGap t b m)
        hab hleft
        (Complex.logarithmicPhaseEnhancedPositiveModeGap_pos
          t a b m ha hab m.property).le)
  exact add_nonneg hnegative hpositive

theorem Complex.logarithmicPhaseAdaptedComplementBudget_nonneg
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseAdaptedComplementBudget t a b := by
  unfold Complex.logarithmicPhaseAdaptedComplementBudget
  have hinactive :=
    Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget_nonneg t a b
  have houtside :=
    Complex.logarithmicPhaseAdaptedOutsideRangeBudget_nonneg
      t a b ha hab
  exact add_nonneg hinactive houtside

def Complex.logarithmicPhaseAdaptedThreeComponentBudget
    (t : ℝ) (a b : ℤ) (radius : ℝ) : ℝ :=
  Complex.logarithmicPhaseQuantitativeActiveWindowBudget t a b radius +
    Complex.logarithmicPhaseQuantitativeCrossingBudget t a b radius +
    Complex.logarithmicPhaseAdaptedComplementBudget t a b

theorem Complex.logarithmicPhaseAdaptedThreeComponentBudget_nonneg
    (t : ℝ) (a b : ℤ) (radius : ℝ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (hactive :
      ∀ m ∈ Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius,
        0 ≤ Complex.logarithmicPhaseQuantitativeInteriorStationaryPacketBound
          t a b m radius) :
    0 ≤ Complex.logarithmicPhaseAdaptedThreeComponentBudget
      t a b radius := by
  unfold Complex.logarithmicPhaseAdaptedThreeComponentBudget
  have hactive :=
    Complex.logarithmicPhaseQuantitativeActiveWindowBudget_nonneg
      t a b radius hactive
  have hcrossing :=
    Complex.logarithmicPhaseQuantitativeCrossingBudget_nonneg t a b radius
  have hcomplement :=
    Complex.logarithmicPhaseAdaptedComplementBudget_nonneg t a b ha hab
  exact add_nonneg (add_nonneg hactive hcrossing) hcomplement

theorem Complex.logarithmicPhaseAdaptedComplementBudget_eq_finite_add_tails
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseAdaptedComplementBudget t a b =
      Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget t a b +
      Complex.logarithmicPhaseAdaptedFarNegativeTailBudget t a b +
      Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b := by
  unfold Complex.logarithmicPhaseAdaptedComplementBudget
  unfold Complex.logarithmicPhaseAdaptedOutsideRangeBudget
  exact (add_assoc _ _ _).symm

end
end LFunctions
end Boundary
