import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedEnhancedFarNegativeTail
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedEnhancedPositiveTailCore
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
  Complex.logarithmicPhaseEnhancedFarNegativeTailBudget t a b +
    Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b

def Complex.logarithmicPhaseAdaptedInRangeInactiveBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b,
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m‖

def Complex.logarithmicPhaseAdaptedComplementBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseAdaptedInRangeInactiveBudget t a b +
    Complex.logarithmicPhaseAdaptedOutsideRangeBudget t a b

theorem Complex.logarithmicPhaseAdaptedInRangeInactiveBudget_nonneg
    (t : ℝ) (a b : ℤ) :
    0 ≤ Complex.logarithmicPhaseAdaptedInRangeInactiveBudget t a b := by
  unfold Complex.logarithmicPhaseAdaptedInRangeInactiveBudget
  exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)

theorem Complex.logarithmicPhaseAdaptedOutsideRangeBudget_nonneg
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseAdaptedOutsideRangeBudget t a b := by
  have hleft :
      0 ≤ Complex.logarithmicPhaseQuantitativeSupportLeft a :=
    (Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha).le
  have hnegative :
      0 ≤ Complex.logarithmicPhaseEnhancedFarNegativeTailBudget t a b :=
    tsum_nonneg (fun m =>
      Complex.logarithmicPhaseAdaptedClosedMajorant_nonneg
        t a b
        (Complex.logarithmicPhaseLeftInactiveGap t m
          (Complex.logarithmicPhaseQuantitativeSupportLeft a))
        hab hleft
        (Complex.logarithmicPhaseFarNegative_leftGap_pos
          t a m ha m.property).le)
  have hpositive :
      0 ≤ Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b :=
    tsum_nonneg (fun m =>
      Complex.logarithmicPhaseAdaptedClosedMajorant_nonneg
        t a b
        (Complex.logarithmicPhaseEnhancedPositiveModeGap t b m)
        hab hleft
        (Complex.logarithmicPhaseEnhancedPositiveModeGap_pos
          t a b m ha hab m.property).le)
  unfold Complex.logarithmicPhaseAdaptedOutsideRangeBudget
  exact add_nonneg hnegative hpositive

theorem Complex.logarithmicPhaseAdaptedComplementBudget_nonneg
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseAdaptedComplementBudget t a b := by
  have hinactive :
      0 ≤ Complex.logarithmicPhaseAdaptedInRangeInactiveBudget t a b :=
    Complex.logarithmicPhaseAdaptedInRangeInactiveBudget_nonneg t a b
  have houtside :
      0 ≤ Complex.logarithmicPhaseAdaptedOutsideRangeBudget t a b :=
    Complex.logarithmicPhaseAdaptedOutsideRangeBudget_nonneg
      t a b ha hab
  exact add_nonneg hinactive houtside

def Complex.logarithmicPhaseAdaptedCrossingBudget
    (t : ℝ) (a b : ℤ) (radius : ℝ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius,
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m‖

theorem Complex.logarithmicPhaseAdaptedCrossingBudget_nonneg
    (t : ℝ) (a b : ℤ) (radius : ℝ) :
    0 ≤ Complex.logarithmicPhaseAdaptedCrossingBudget t a b radius := by
  unfold Complex.logarithmicPhaseAdaptedCrossingBudget
  exact Finset.sum_nonneg (fun _ _ => norm_nonneg _)

def Complex.logarithmicPhaseAdaptedThreeComponentBudget
    (t : ℝ) (a b : ℤ) (radius : ℝ) : ℝ :=
  Complex.logarithmicPhaseQuantitativeActiveWindowBudget t a b radius +
    Complex.logarithmicPhaseAdaptedCrossingBudget t a b radius +
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
  have hactiveBudget :
      0 ≤ Complex.logarithmicPhaseQuantitativeActiveWindowBudget
        t a b radius :=
    Complex.logarithmicPhaseQuantitativeActiveWindowBudget_nonneg
      t a b radius hactive
  have hcrossing :
      0 ≤ Complex.logarithmicPhaseAdaptedCrossingBudget t a b radius :=
    Complex.logarithmicPhaseAdaptedCrossingBudget_nonneg t a b radius
  have hcomplement :
      0 ≤ Complex.logarithmicPhaseAdaptedComplementBudget t a b :=
    Complex.logarithmicPhaseAdaptedComplementBudget_nonneg t a b ha hab
  exact add_nonneg (add_nonneg hactiveBudget hcrossing) hcomplement

theorem Complex.logarithmicPhaseAdaptedComplementBudget_eq_finite_add_tails
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhaseAdaptedComplementBudget t a b =
      Complex.logarithmicPhaseAdaptedInRangeInactiveBudget t a b +
      Complex.logarithmicPhaseEnhancedFarNegativeTailBudget t a b +
      Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b := by
  exact (add_assoc _ _ _).symm

end
end LFunctions
end Boundary
