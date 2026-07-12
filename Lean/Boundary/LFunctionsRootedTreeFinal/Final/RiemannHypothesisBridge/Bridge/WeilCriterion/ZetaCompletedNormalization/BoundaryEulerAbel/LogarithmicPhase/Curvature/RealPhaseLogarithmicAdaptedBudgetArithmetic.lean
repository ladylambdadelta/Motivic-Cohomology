import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedThreeComponent
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicRefinedBudgetArithmetic

/-!
# Arithmetic assembly for the phase-adapted five-part budget

The active, crossing, finite inactive, far-negative, and positive components
are each assigned sixteen units of the refined scale.  Their sum is exactly
eighty units.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Real.five_sixteen_mul_eq_eighty
    (scale : ℝ) :
    16 * scale + 16 * scale + 16 * scale + 16 * scale + 16 * scale =
      80 * scale := by
  have htwo : 16 * scale + 16 * scale = 32 * scale := by
    exact Eq.trans (add_mul 16 16 scale).symm
      (congrArg (fun value : ℝ => value * scale)
        (show (16 : ℝ) + 16 = 32 from rfl))
  have hthree : 32 * scale + 16 * scale = 48 * scale := by
    exact Eq.trans (add_mul 32 16 scale).symm
      (congrArg (fun value : ℝ => value * scale)
        (show (32 : ℝ) + 16 = 48 from rfl))
  have hfour : 48 * scale + 16 * scale = 64 * scale := by
    exact Eq.trans (add_mul 48 16 scale).symm
      (congrArg (fun value : ℝ => value * scale)
        (show (48 : ℝ) + 16 = 64 from rfl))
  have hfive : 64 * scale + 16 * scale = 80 * scale := by
    exact Eq.trans (add_mul 64 16 scale).symm
      (congrArg (fun value : ℝ => value * scale)
        (show (64 : ℝ) + 16 = 80 from rfl))
  exact Eq.trans
    (congrArg (fun value : ℝ => value + 16 * scale + 16 * scale + 16 * scale)
      htwo)
    (Eq.trans
      (congrArg (fun value : ℝ => value + 16 * scale + 16 * scale) hthree)
      (Eq.trans
        (congrArg (fun value : ℝ => value + 16 * scale) hfour)
        hfive))

theorem Complex.logarithmicPhaseAdaptedThreeComponentBudget_le_eighty
    (t : ℝ) (a b : ℤ) (radius : ℝ)
    (hactive :
      Complex.logarithmicPhaseQuantitativeActiveWindowBudget t a b radius ≤
        16 * Real.logarithmicPhaseRefinedScale t b)
    (hcrossing :
      Complex.logarithmicPhaseQuantitativeCrossingBudget t a b radius ≤
        16 * Real.logarithmicPhaseRefinedScale t b)
    (hinactive :
      Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget t a b ≤
        16 * Real.logarithmicPhaseRefinedScale t b)
    (hnegative :
      Complex.logarithmicPhaseAdaptedFarNegativeTailBudget t a b ≤
        16 * Real.logarithmicPhaseRefinedScale t b)
    (hpositive :
      Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b ≤
        16 * Real.logarithmicPhaseRefinedScale t b) :
    Complex.logarithmicPhaseAdaptedThreeComponentBudget t a b radius ≤
      80 * Real.logarithmicPhaseRefinedScale t b := by
  unfold Complex.logarithmicPhaseAdaptedThreeComponentBudget
  unfold Complex.logarithmicPhaseAdaptedComplementBudget
  unfold Complex.logarithmicPhaseAdaptedOutsideRangeBudget
  have hsum₁ := add_le_add hactive hcrossing
  have hsum₂ := add_le_add hsum₁ hinactive
  have hsum₃ := add_le_add hsum₂ hnegative
  have hsum₄ := add_le_add hsum₃ hpositive
  have harithmetic := Real.five_sixteen_mul_eq_eighty
    (Real.logarithmicPhaseRefinedScale t b)
  exact le_trans hsum₄ (le_of_eq harithmetic)

theorem Complex.logarithmicPhaseQuantitativeIntegerBlock_norm_le_eighty_adapted
    (t : ℝ)
    (ht : 1 ≤ ‖t‖) (htNonneg : 0 ≤ t)
    (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (radius : ℝ) (hradius : 0 < radius)
    (hactive :
      Complex.logarithmicPhaseQuantitativeActiveWindowBudget t a b radius ≤
        16 * Real.logarithmicPhaseRefinedScale t b)
    (hcrossing :
      Complex.logarithmicPhaseQuantitativeCrossingBudget t a b radius ≤
        16 * Real.logarithmicPhaseRefinedScale t b)
    (hinactive :
      Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget t a b ≤
        16 * Real.logarithmicPhaseRefinedScale t b)
    (hnegative :
      Complex.logarithmicPhaseAdaptedFarNegativeTailBudget t a b ≤
        16 * Real.logarithmicPhaseRefinedScale t b)
    (hpositive :
      Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b ≤
        16 * Real.logarithmicPhaseRefinedScale t b) :
    ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))‖ ≤
      80 * Real.logarithmicPhaseRefinedScale t b := by
  have hblock :=
    Complex.logarithmicPhaseQuantitativeIntegerBlock_norm_le_adaptedThreeComponent
      t ht htNonneg a b ha hab radius hradius
  have harithmetic :=
    Complex.logarithmicPhaseAdaptedThreeComponentBudget_le_eighty
      t a b radius hactive hcrossing hinactive hnegative hpositive
  exact le_trans hblock harithmetic

end
end LFunctions
end Boundary
