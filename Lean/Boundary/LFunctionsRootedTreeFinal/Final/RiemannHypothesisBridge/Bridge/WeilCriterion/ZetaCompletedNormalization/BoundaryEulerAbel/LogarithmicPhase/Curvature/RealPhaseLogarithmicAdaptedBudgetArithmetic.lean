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
  have hsixteen_add_sixteen : (16 : ℝ) + 16 = 32 := by
    have hnat : (16 + 16 : ℕ) = 32 := rfl
    exact Eq.trans (Nat.cast_add 16 16).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have hthirty_two_add_sixteen : (32 : ℝ) + 16 = 48 := by
    have hnat : (32 + 16 : ℕ) = 48 := rfl
    exact Eq.trans (Nat.cast_add 32 16).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have hforty_eight_add_sixteen : (48 : ℝ) + 16 = 64 := by
    have hnat : (48 + 16 : ℕ) = 64 := rfl
    exact Eq.trans (Nat.cast_add 48 16).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have hsixty_four_add_sixteen : (64 : ℝ) + 16 = 80 := by
    have hnat : (64 + 16 : ℕ) = 80 := rfl
    exact Eq.trans (Nat.cast_add 64 16).symm
      (Eq.trans (congrArg (fun value : ℕ => (value : ℝ)) hnat)
        Nat.cast_ofNat)
  have htwo : 16 * scale + 16 * scale = 32 * scale := by
    exact Eq.trans (add_mul 16 16 scale).symm
      (congrArg (fun value : ℝ => value * scale)
        hsixteen_add_sixteen)
  have hthree : 32 * scale + 16 * scale = 48 * scale := by
    exact Eq.trans (add_mul 32 16 scale).symm
      (congrArg (fun value : ℝ => value * scale)
        hthirty_two_add_sixteen)
  have hfour : 48 * scale + 16 * scale = 64 * scale := by
    exact Eq.trans (add_mul 48 16 scale).symm
      (congrArg (fun value : ℝ => value * scale)
        hforty_eight_add_sixteen)
  have hfive : 64 * scale + 16 * scale = 80 * scale := by
    exact Eq.trans (add_mul 64 16 scale).symm
      (congrArg (fun value : ℝ => value * scale)
        hsixty_four_add_sixteen)
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
      Complex.logarithmicPhaseAdaptedCrossingBudget t a b radius ≤
        16 * Real.logarithmicPhaseRefinedScale t b)
    (hinactive :
      Complex.logarithmicPhaseAdaptedInRangeInactiveBudget t a b ≤
        16 * Real.logarithmicPhaseRefinedScale t b)
    (hnegative :
      Complex.logarithmicPhaseEnhancedFarNegativeTailBudget t a b ≤
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
  have hreassociate :
      (Complex.logarithmicPhaseQuantitativeActiveWindowBudget t a b radius +
          Complex.logarithmicPhaseAdaptedCrossingBudget t a b radius) +
          (Complex.logarithmicPhaseAdaptedInRangeInactiveBudget t a b +
            (Complex.logarithmicPhaseEnhancedFarNegativeTailBudget t a b +
              Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b)) =
        (((Complex.logarithmicPhaseQuantitativeActiveWindowBudget t a b radius +
            Complex.logarithmicPhaseAdaptedCrossingBudget t a b radius) +
            Complex.logarithmicPhaseAdaptedInRangeInactiveBudget t a b) +
            Complex.logarithmicPhaseEnhancedFarNegativeTailBudget t a b) +
          Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b := by
    exact Eq.trans
      (add_assoc
        (Complex.logarithmicPhaseQuantitativeActiveWindowBudget t a b radius +
          Complex.logarithmicPhaseAdaptedCrossingBudget t a b radius)
        (Complex.logarithmicPhaseAdaptedInRangeInactiveBudget t a b)
        (Complex.logarithmicPhaseEnhancedFarNegativeTailBudget t a b +
          Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b)).symm
      (add_assoc
        ((Complex.logarithmicPhaseQuantitativeActiveWindowBudget t a b radius +
          Complex.logarithmicPhaseAdaptedCrossingBudget t a b radius) +
          Complex.logarithmicPhaseAdaptedInRangeInactiveBudget t a b)
        (Complex.logarithmicPhaseEnhancedFarNegativeTailBudget t a b)
        (Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b)).symm
  have hleftAssociated := le_trans hsum₄ (le_of_eq harithmetic)
  exact Eq.subst (motive := fun value : ℝ =>
      value ≤ 80 * Real.logarithmicPhaseRefinedScale t b)
    hreassociate.symm hleftAssociated

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
      Complex.logarithmicPhaseAdaptedCrossingBudget t a b radius ≤
        16 * Real.logarithmicPhaseRefinedScale t b)
    (hinactive :
      Complex.logarithmicPhaseAdaptedInRangeInactiveBudget t a b ≤
        16 * Real.logarithmicPhaseRefinedScale t b)
    (hnegative :
      Complex.logarithmicPhaseEnhancedFarNegativeTailBudget t a b ≤
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
