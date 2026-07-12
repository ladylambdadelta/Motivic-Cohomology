import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedFarNegativeEquiv

/-!
# Summability of shifted far-negative inverse squares

The far-negative distance equivalence transports the canonical positive
integer inverse-square series to the shifted negative ray.  Scaling by any
fixed nonnegative packet coefficient preserves summability.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.summable_positiveIntegerInverseSquare :
    Summable (fun k : Complex.logarithmicPhasePoissonPositiveTailModes =>
      |((k : ℤ) : ℝ)| ^ (-2 : ℝ)) := by
  exact Complex.summable_scaled_integer_frequency_inverse_square_on_set
    1 Complex.logarithmicPhasePoissonPositiveTailModes

theorem Complex.summable_logarithmicPhaseFarNegativeIntegerInverseSquare
    (t : ℝ) (a : ℤ) :
    Summable (Complex.logarithmicPhaseFarNegativeIntegerInverseSquare t a) := by
  let e := Complex.logarithmicPhaseFarNegativeEquivPositive t a
  have hpositive := Complex.summable_positiveIntegerInverseSquare
  have htransport := e.summable_iff.mpr hpositive
  have hfunction :
      (fun m : Complex.logarithmicPhasePoissonFarNegativeModes t a =>
        |(((e m : Complex.logarithmicPhasePoissonPositiveTailModes) : ℤ) : ℝ)| ^
          (-2 : ℝ)) =
      Complex.logarithmicPhaseFarNegativeIntegerInverseSquare t a := by
    funext m
    exact (Complex.logarithmicPhaseFarNegativeIntegerInverseSquare_eq_positive
      t a m).symm
  exact Eq.subst
    (motive := fun function :
      Complex.logarithmicPhasePoissonFarNegativeModes t a → ℝ =>
      Summable function)
    hfunction htransport

def Complex.logarithmicPhaseFarNegativeScaledEnvelope
    (t : ℝ) (a b : ℤ)
    (m : Complex.logarithmicPhasePoissonFarNegativeModes t a) : ℝ :=
  (Complex.logarithmicPhasePositiveModeInverseSquareCoefficient t a b /
      (2 * Real.pi) ^ 2) *
    Complex.logarithmicPhaseFarNegativeIntegerInverseSquare t a m

def Complex.logarithmicPhaseAdaptedFarNegativeTailBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a,
    Complex.logarithmicPhaseFarNegativeScaledEnvelope t a b m

theorem Complex.summable_logarithmicPhaseFarNegativeScaledEnvelope
    (t : ℝ) (a b : ℤ) :
    Summable (Complex.logarithmicPhaseFarNegativeScaledEnvelope t a b) := by
  unfold Complex.logarithmicPhaseFarNegativeScaledEnvelope
  exact (Complex.summable_logarithmicPhaseFarNegativeIntegerInverseSquare
    t a).mul_left
    (Complex.logarithmicPhasePositiveModeInverseSquareCoefficient t a b /
      (2 * Real.pi) ^ 2)

theorem Complex.logarithmicPhaseFarNegativeIntegerInverseSquare_nonneg
    (t : ℝ) (a : ℤ)
    (m : Complex.logarithmicPhasePoissonFarNegativeModes t a) :
    0 ≤ Complex.logarithmicPhaseFarNegativeIntegerInverseSquare t a m := by
  unfold Complex.logarithmicPhaseFarNegativeIntegerInverseSquare
  exact Real.rpow_nonneg (abs_nonneg _) _

theorem Complex.logarithmicPhaseFarNegativeScaledEnvelope_nonneg
    (t : ℝ) (a b : ℤ)
    (hab : a ≤ b)
    (hleft : 0 ≤ Complex.logarithmicPhaseQuantitativeSupportLeft a)
    (m : Complex.logarithmicPhasePoissonFarNegativeModes t a) :
    0 ≤ Complex.logarithmicPhaseFarNegativeScaledEnvelope t a b m := by
  unfold Complex.logarithmicPhaseFarNegativeScaledEnvelope
  have hcoefficient :=
    Complex.logarithmicPhasePositiveModeInverseSquareCoefficient_nonneg
      t a b hab hleft
  have hdenominator : 0 ≤ (2 * Real.pi) ^ 2 := sq_nonneg _
  have hscaled := div_nonneg hcoefficient hdenominator
  exact mul_nonneg hscaled
    (Complex.logarithmicPhaseFarNegativeIntegerInverseSquare_nonneg t a m)

theorem Complex.logarithmicPhaseAdaptedFarNegativeTailBudget_nonneg
    (t : ℝ) (a b : ℤ)
    (hab : a ≤ b)
    (hleft : 0 ≤ Complex.logarithmicPhaseQuantitativeSupportLeft a) :
    0 ≤ Complex.logarithmicPhaseAdaptedFarNegativeTailBudget t a b := by
  unfold Complex.logarithmicPhaseAdaptedFarNegativeTailBudget
  exact tsum_nonneg (fun m =>
    Complex.logarithmicPhaseFarNegativeScaledEnvelope_nonneg
      t a b hab hleft m)

end
end LFunctions
end Boundary
