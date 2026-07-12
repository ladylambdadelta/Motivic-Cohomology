import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeSharpCutoffCurvatureMass
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeAmplitudeMassBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeSecondDerivativeClosedBound

/-!
# Sharp closed second-derivative mass

The cutoff curvature contribution is `48`; the mixed cutoff-phase variation
and pure logarithmic phase curvature retain their parameter-dependent closed
bounds.  This owner assembles the sharp mass and exports deterministic
inverse-square decay for every nonzero integer frequency.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseQuantitativeSharpSecondDerivativeMassBound
    (t : ℝ) (a b : ℤ) : ℝ :=
  48 +
    4 * (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) +
    Complex.logarithmicPhaseQuantitativeSupportLength a b *
      ((‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2 +
        ‖t‖ /
          (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2)

def Complex.logarithmicPhaseQuantitativeSharpInverseSquareCoefficient
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseQuantitativeSharpSecondDerivativeMassBound t a b /
    (2 * Real.pi) ^ 2

def Complex.logarithmicPhaseQuantitativeSharpInverseSquareMajorant
    (t : ℝ) (a b m : ℤ) : ℝ :=
  Complex.logarithmicPhaseQuantitativeSharpInverseSquareCoefficient t a b *
    |(m : ℝ)| ^ (-2 : ℝ)

theorem Complex.logarithmicPhaseQuantitativeSharpSecondDerivativeMassBound_nonneg
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseQuantitativeSharpSecondDerivativeMassBound
      t a b := by
  unfold Complex.logarithmicPhaseQuantitativeSharpSecondDerivativeMassBound
  have hleft := Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha
  have hconstant : (0 : ℝ) ≤ 48 := Nat.cast_nonneg 48
  have hmixed :
      0 ≤ 4 * (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) :=
    mul_nonneg (Nat.cast_nonneg 4)
      (div_nonneg (norm_nonneg t) hleft.le)
  have hlength :=
    Complex.logarithmicPhaseQuantitativeSupportLength_nonneg a b hab
  have hphase :
      0 ≤ (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2 +
        ‖t‖ / (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2 :=
    add_nonneg (sq_nonneg _)
      (div_nonneg (norm_nonneg t) (sq_nonneg _))
  exact add_nonneg (add_nonneg hconstant hmixed)
    (mul_nonneg hlength hphase)

theorem Complex.logarithmicPhaseQuantitativeSharpInverseSquareCoefficient_nonneg
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseQuantitativeSharpInverseSquareCoefficient
      t a b := by
  unfold Complex.logarithmicPhaseQuantitativeSharpInverseSquareCoefficient
  exact div_nonneg
    (Complex.logarithmicPhaseQuantitativeSharpSecondDerivativeMassBound_nonneg
      t a b ha hab)
    (sq_nonneg _)

theorem Complex.logarithmicPhaseQuantitativeSharpInverseSquareMajorant_nonneg
    (t : ℝ) (a b m : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseQuantitativeSharpInverseSquareMajorant
      t a b m := by
  unfold Complex.logarithmicPhaseQuantitativeSharpInverseSquareMajorant
  exact mul_nonneg
    (Complex.logarithmicPhaseQuantitativeSharpInverseSquareCoefficient_nonneg
      t a b ha hab)
    (Real.rpow_nonneg _ _)

theorem Complex.logarithmicPhaseQuantitativeMixedVariationUpper_le_sharp
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeMixedVariationUpper t a b ≤
      4 * (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) := by
  exact Complex.logarithmicPhaseQuantitativeMixedVariationUpper_le_closed
    t a b ha hab

theorem Complex.logarithmicPhaseQuantitativeSecondDerivativeMassUpper_le_sharp
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeSecondDerivativeMassUpper t a b ≤
      Complex.logarithmicPhaseQuantitativeSharpSecondDerivativeMassBound
        t a b := by
  unfold Complex.logarithmicPhaseQuantitativeSecondDerivativeMassUpper
  unfold Complex.logarithmicPhaseQuantitativeSharpSecondDerivativeMassBound
  unfold Complex.logarithmicPhaseQuantitativePhaseCurvatureUpper
  have hcutoff :=
    Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass_le_forty_eight
      a b hab
  have hmixed :=
    Complex.logarithmicPhaseQuantitativeMixedVariationUpper_le_sharp
      t a b ha hab
  exact add_le_add (add_le_add hcutoff hmixed) (le_refl _)

theorem Complex.logarithmicPhaseQuantitativeSecondDerivativeMass_le_sharp
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeSecondDerivativeMass t a b ≤
      Complex.logarithmicPhaseQuantitativeSharpSecondDerivativeMassBound
        t a b := by
  exact le_trans
    (Complex.logarithmicPhaseQuantitativeSecondDerivativeMass_le_upper
      t a b ha hab)
    (Complex.logarithmicPhaseQuantitativeSecondDerivativeMassUpper_le_sharp
      t a b ha hab)

theorem Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant_le_sharp
    (t : ℝ) (a b m : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant t a b m ≤
      Complex.logarithmicPhaseQuantitativeSharpInverseSquareMajorant
        t a b m := by
  unfold Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant
  unfold Complex.logarithmicPhaseQuantitativeSharpInverseSquareMajorant
  unfold Complex.logarithmicPhaseQuantitativeSharpInverseSquareCoefficient
  have hmass :=
    Complex.logarithmicPhaseQuantitativeSecondDerivativeMass_le_sharp
      t a b ha hab
  have hdenominator : (0 : ℝ) ≤ (2 * Real.pi) ^ 2 := sq_nonneg _
  have hdivision := div_le_div_of_nonneg_right hmass hdenominator
  have hfrequency : (0 : ℝ) ≤ |(m : ℝ)| ^ (-2 : ℝ) :=
    Real.rpow_nonneg _ _
  exact mul_le_mul_of_nonneg_right hdivision hfrequency

theorem Complex.norm_logarithmicPhaseQuantitativeBlockFourierPacket_le_sharp
    (t : ℝ) (a b m : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hm : m ≠ 0) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseQuantitativeSharpInverseSquareMajorant
        t a b m := by
  exact le_trans
    (Complex.norm_logarithmicPhaseQuantitativeBlockFourierPacket_le_integerInverseSquare
      t a b m ha hab hm)
    (Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant_le_sharp
      t a b m ha hab)

theorem Complex.summable_logarithmicPhaseQuantitativeSharpInverseSquareMajorant
    (t : ℝ) (a b : ℤ) :
    Summable
      (fun m : ℤ =>
        Complex.logarithmicPhaseQuantitativeSharpInverseSquareMajorant
          t a b m) := by
  unfold Complex.logarithmicPhaseQuantitativeSharpInverseSquareMajorant
  exact Complex.summable_scaled_integer_frequency_inverse_square
    (Complex.logarithmicPhaseQuantitativeSharpInverseSquareCoefficient t a b)

theorem Complex.summable_logarithmicPhaseQuantitativeSharpInverseSquareMajorant_on_set
    (t : ℝ) (a b : ℤ) (modes : Set ℤ) :
    Summable
      (fun m : modes =>
        Complex.logarithmicPhaseQuantitativeSharpInverseSquareMajorant
          t a b m) := by
  exact
    (Complex.summable_logarithmicPhaseQuantitativeSharpInverseSquareMajorant
      t a b).subtype modes

theorem Complex.norm_logarithmicPhaseQuantitativePacket_tsum_le_sharpMajorant
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (modes : Set ℤ)
    (hzero : ∀ m : modes, (m : ℤ) ≠ 0) :
    ‖∑' m : modes,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      ∑' m : modes,
        Complex.logarithmicPhaseQuantitativeSharpInverseSquareMajorant
          t a b m := by
  have hsummable :=
    Complex.summable_logarithmicPhaseQuantitativeSharpInverseSquareMajorant_on_set
      t a b modes
  exact tsum_norm_le hsummable
    (fun m =>
      Complex.norm_logarithmicPhaseQuantitativeBlockFourierPacket_le_sharp
        t a b m ha hab (hzero m))

end
end LFunctions
end Boundary
