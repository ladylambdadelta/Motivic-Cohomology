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
  have hleft :
      0 < Complex.logarithmicPhaseQuantitativeSupportLeft a :=
    Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha
  have hconstant : (0 : ℝ) ≤ (48 : ℝ) :=
    Nat.cast_nonneg 48
  have hnorm : (0 : ℝ) ≤ ‖t‖ :=
    norm_nonneg t
  have hratio :
      0 ≤ ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a :=
    div_nonneg hnorm hleft.le
  have hfour : (0 : ℝ) ≤ (4 : ℝ) :=
    Nat.cast_nonneg 4
  have hmixed :
      0 ≤ 4 * (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) :=
    mul_nonneg hfour hratio
  have hlength :
      0 ≤ Complex.logarithmicPhaseQuantitativeSupportLength a b :=
    Complex.logarithmicPhaseQuantitativeSupportLength_nonneg a b hab
  have hratioSquare :
      0 ≤ (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2 :=
    sq_nonneg
      (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a)
  have hleftSquare :
      0 ≤ (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2 :=
    sq_nonneg (Complex.logarithmicPhaseQuantitativeSupportLeft a)
  have hcurvatureRatio :
      0 ≤ ‖t‖ /
        (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2 :=
    div_nonneg hnorm hleftSquare
  have hphaseBracket :
      0 ≤ (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2 +
        ‖t‖ / (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2 :=
    add_nonneg hratioSquare hcurvatureRatio
  have hphaseMass :
      0 ≤ Complex.logarithmicPhaseQuantitativeSupportLength a b *
        ((‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2 +
          ‖t‖ /
            (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2) :=
    mul_nonneg hlength hphaseBracket
  have hconstantMixed :
      0 ≤ (48 : ℝ) +
        4 * (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) :=
    add_nonneg hconstant hmixed
  exact add_nonneg hconstantMixed hphaseMass

theorem Complex.logarithmicPhaseQuantitativeSharpInverseSquareCoefficient_nonneg
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseQuantitativeSharpInverseSquareCoefficient
      t a b := by
  unfold Complex.logarithmicPhaseQuantitativeSharpInverseSquareCoefficient
  have hmass :
      0 ≤ Complex.logarithmicPhaseQuantitativeSharpSecondDerivativeMassBound
        t a b :=
    Complex.logarithmicPhaseQuantitativeSharpSecondDerivativeMassBound_nonneg
      t a b ha hab
  have hdenominator : (0 : ℝ) ≤ (2 * Real.pi) ^ 2 :=
    sq_nonneg (2 * Real.pi)
  exact div_nonneg hmass hdenominator

theorem Complex.logarithmicPhaseQuantitativeSharpInverseSquareMajorant_nonneg
    (t : ℝ) (a b m : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseQuantitativeSharpInverseSquareMajorant
      t a b m := by
  unfold Complex.logarithmicPhaseQuantitativeSharpInverseSquareMajorant
  have hcoefficient :
      0 ≤ Complex.logarithmicPhaseQuantitativeSharpInverseSquareCoefficient
        t a b :=
    Complex.logarithmicPhaseQuantitativeSharpInverseSquareCoefficient_nonneg
      t a b ha hab
  have habsolute : (0 : ℝ) ≤ |(m : ℝ)| :=
    abs_nonneg (m : ℝ)
  have hfrequency : (0 : ℝ) ≤ |(m : ℝ)| ^ (-2 : ℝ) :=
    Real.rpow_nonneg habsolute (-2 : ℝ)
  exact mul_nonneg hcoefficient hfrequency

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
  have hcutoff :
      Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass a b ≤
        (48 : ℝ) :=
    Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass_le_forty_eight
      a b hab
  have hmixed :
      Complex.logarithmicPhaseQuantitativeMixedVariationUpper t a b ≤
        4 * (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) :=
    Complex.logarithmicPhaseQuantitativeMixedVariationUpper_le_sharp
      t a b ha hab
  have hcutoffMixed :
      Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass a b +
          Complex.logarithmicPhaseQuantitativeMixedVariationUpper t a b ≤
        (48 : ℝ) +
          4 * (‖t‖ /
            Complex.logarithmicPhaseQuantitativeSupportLeft a) :=
    add_le_add hcutoff hmixed
  have hphase :
      Complex.logarithmicPhaseQuantitativeSupportLength a b *
          ((‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2 +
            ‖t‖ /
              (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2) ≤
        Complex.logarithmicPhaseQuantitativeSupportLength a b *
          ((‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2 +
            ‖t‖ /
              (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2) :=
    le_refl
      (Complex.logarithmicPhaseQuantitativeSupportLength a b *
        ((‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2 +
          ‖t‖ /
            (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2))
  exact add_le_add hcutoffMixed hphase

theorem Complex.logarithmicPhaseQuantitativeSecondDerivativeMass_le_sharp
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeSecondDerivativeMass t a b ≤
      Complex.logarithmicPhaseQuantitativeSharpSecondDerivativeMassBound
        t a b := by
  have hupper :
      Complex.logarithmicPhaseQuantitativeSecondDerivativeMass t a b ≤
        Complex.logarithmicPhaseQuantitativeSecondDerivativeMassUpper
          t a b :=
    Complex.logarithmicPhaseQuantitativeSecondDerivativeMass_le_upper
      t a b ha hab
  have hsharp :
      Complex.logarithmicPhaseQuantitativeSecondDerivativeMassUpper t a b ≤
        Complex.logarithmicPhaseQuantitativeSharpSecondDerivativeMassBound
          t a b :=
    Complex.logarithmicPhaseQuantitativeSecondDerivativeMassUpper_le_sharp
      t a b ha hab
  exact le_trans hupper hsharp

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
  have hmass :
      Complex.logarithmicPhaseQuantitativeSecondDerivativeMass t a b ≤
        Complex.logarithmicPhaseQuantitativeSharpSecondDerivativeMassBound
          t a b :=
    Complex.logarithmicPhaseQuantitativeSecondDerivativeMass_le_sharp
      t a b ha hab
  have hdenominator : (0 : ℝ) ≤ (2 * Real.pi) ^ 2 :=
    sq_nonneg (2 * Real.pi)
  have hdivision :
      Complex.logarithmicPhaseQuantitativeSecondDerivativeMass t a b /
          (2 * Real.pi) ^ 2 ≤
        Complex.logarithmicPhaseQuantitativeSharpSecondDerivativeMassBound
            t a b /
          (2 * Real.pi) ^ 2 :=
    div_le_div_of_nonneg_right hmass hdenominator
  have habsolute : (0 : ℝ) ≤ |(m : ℝ)| :=
    abs_nonneg (m : ℝ)
  have hfrequency : (0 : ℝ) ≤ |(m : ℝ)| ^ (-2 : ℝ) :=
    Real.rpow_nonneg habsolute (-2 : ℝ)
  exact mul_le_mul_of_nonneg_right hdivision hfrequency

theorem Complex.norm_logarithmicPhaseQuantitativeBlockFourierPacket_le_sharp
    (t : ℝ) (a b m : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hm : m ≠ 0) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseQuantitativeSharpInverseSquareMajorant
        t a b m := by
  have hinteger :
      ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
        Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant
          t a b m :=
    Complex.norm_logarithmicPhaseQuantitativeBlockFourierPacket_le_integerInverseSquare
      t a b m ha hab hm
  have hsharp :
      Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant
          t a b m ≤
        Complex.logarithmicPhaseQuantitativeSharpInverseSquareMajorant
          t a b m :=
    Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant_le_sharp
      t a b m ha hab
  exact le_trans hinteger hsharp

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
  unfold Complex.logarithmicPhaseQuantitativeSharpInverseSquareMajorant
  exact Complex.summable_scaled_integer_frequency_inverse_square_on_set
    (Complex.logarithmicPhaseQuantitativeSharpInverseSquareCoefficient t a b)
    modes

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
  have hsummable :
      Summable
        (fun m : modes =>
          Complex.logarithmicPhaseQuantitativeSharpInverseSquareMajorant
            t a b (m : ℤ)) :=
    Complex.summable_logarithmicPhaseQuantitativeSharpInverseSquareMajorant_on_set
      t a b modes
  have hpointwise :
      ∀ m : modes,
        ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket
            t a b (m : ℤ)‖ ≤
          Complex.logarithmicPhaseQuantitativeSharpInverseSquareMajorant
            t a b (m : ℤ) :=
    fun m =>
      Complex.norm_logarithmicPhaseQuantitativeBlockFourierPacket_le_sharp
        t a b (m : ℤ) ha hab (hzero m)
  exact tsum_of_norm_bounded hsummable.hasSum hpointwise

end
end LFunctions
end Boundary
