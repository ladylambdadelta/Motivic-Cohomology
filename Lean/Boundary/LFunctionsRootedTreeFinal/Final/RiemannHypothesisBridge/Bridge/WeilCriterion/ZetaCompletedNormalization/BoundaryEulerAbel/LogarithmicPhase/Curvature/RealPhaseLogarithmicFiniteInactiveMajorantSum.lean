import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.ZeroBasedShiftedReciprocalPower
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedEnhancedPositiveSeriesBudget

/-!
# Finite sums of the phase-adapted inactive majorant

This owner performs the algebra common to every finite inactive packet class.
The analytic input consists only of bounds for the square, cube, and fourth
reciprocal powers of the derivative gap.  The conclusion assembles those
bounds with the four nonnegative coefficients of the closed majorant.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.sum_adaptedClosedMajorant_le_fourPowerBudget
    (t : ℝ) (a b : ℤ) (modes : Finset ℤ) (gap : ℤ → ℝ)
    (B₂ B₃ B₄ : ℝ)
    (hleft : 0 ≤ Complex.logarithmicPhaseQuantitativeSupportLeft a)
    (hab : a ≤ b)
    (hsquare : (∑ m ∈ modes, 1 / (gap m) ^ 2) ≤ B₂)
    (hcube : (∑ m ∈ modes, 1 / (gap m) ^ 3) ≤ B₃)
    (hfourth : (∑ m ∈ modes, 1 / (gap m) ^ 4) ≤ B₄) :
    (∑ m ∈ modes,
      Complex.logarithmicPhaseAdaptedClosedMajorant t a b (gap m)) ≤
      Complex.logarithmicPhaseAdaptedSquareCoefficient * B₂ +
        Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a * B₃ +
        Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b * B₃ +
        Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b * B₄ := by
  let f₁ : ℤ → ℝ := fun m =>
    Complex.logarithmicPhaseAdaptedSquareCoefficient * (1 / gap m ^ 2)
  let f₂ : ℤ → ℝ := fun m =>
    Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a *
      (1 / gap m ^ 3)
  let f₃ : ℤ → ℝ := fun m =>
    Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b *
      (1 / gap m ^ 3)
  let f₄ : ℤ → ℝ := fun m =>
    Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b *
      (1 / gap m ^ 4)
  have hpoint : ∀ m ∈ modes,
      Complex.logarithmicPhaseAdaptedClosedMajorant t a b (gap m) =
        f₁ m + f₂ m + f₃ m + f₄ m :=
    fun m hm =>
      Complex.logarithmicPhaseAdaptedClosedMajorant_eq_coefficients
        t a b (gap m)
  have hpointSum := Finset.sum_congr rfl hpoint
  have hsplit := Finset.sum_four_real modes f₁ f₂ f₃ f₄
  have hscale₁ := Finset.sum_const_mul_real modes
    Complex.logarithmicPhaseAdaptedSquareCoefficient
    (fun m => 1 / gap m ^ 2)
  have hscale₂ := Finset.sum_const_mul_real modes
    (Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a)
    (fun m => 1 / gap m ^ 3)
  have hscale₃ := Finset.sum_const_mul_real modes
    (Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b)
    (fun m => 1 / gap m ^ 3)
  have hscale₄ := Finset.sum_const_mul_real modes
    (Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b)
    (fun m => 1 / gap m ^ 4)
  have hscaledPair :
      ((∑ m ∈ modes, f₁ m),
          (∑ m ∈ modes, f₂ m),
          (∑ m ∈ modes, f₃ m),
          (∑ m ∈ modes, f₄ m)) =
        (Complex.logarithmicPhaseAdaptedSquareCoefficient *
            ∑ m ∈ modes, 1 / gap m ^ 2,
          Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient t a *
            ∑ m ∈ modes, 1 / gap m ^ 3,
          Complex.logarithmicPhaseAdaptedThirdCubeCoefficient t a b *
            ∑ m ∈ modes, 1 / gap m ^ 3,
          Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient t a b *
            ∑ m ∈ modes, 1 / gap m ^ 4) :=
    Prod.ext hscale₁
      (Prod.ext hscale₂ (Prod.ext hscale₃ hscale₄))
  have hexpand := Eq.trans hpointSum
    (Eq.trans hsplit
      (congrArg
        (fun values : ℝ × ℝ × ℝ × ℝ =>
          values.1 + values.2.1 + values.2.2.1 + values.2.2.2)
        hscaledPair))
  have hc₁ := Complex.logarithmicPhaseAdaptedSquareCoefficient_nonneg
  have hc₂ :=
    Complex.logarithmicPhaseAdaptedCurvatureCubeCoefficient_nonneg t a hleft
  have hc₃ := Complex.logarithmicPhaseAdaptedThirdCubeCoefficient_nonneg
    t a b hab hleft
  have hc₄ := Complex.logarithmicPhaseAdaptedCurvatureFourthCoefficient_nonneg
    t a b hab hleft
  have hcombined := add_le_add
    (add_le_add
      (add_le_add
        (mul_le_mul_of_nonneg_left hsquare hc₁)
        (mul_le_mul_of_nonneg_left hcube hc₂))
      (mul_le_mul_of_nonneg_left hcube hc₃))
    (mul_le_mul_of_nonneg_left hfourth hc₄)
  exact Eq.subst (motive := fun value : ℝ => value ≤ _) hexpand.symm hcombined

end

end LFunctions
end Boundary
