import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeAmplitudeMassBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeCutoffCurvatureMassBound

/-!
# Closed second-derivative mass bound

This owner substitutes the universal cutoff curvature and variation estimates
into the parameter-dependent amplitude mass decomposition.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseQuantitativeClosedSecondDerivativeMassBound
    (t : ℝ) (a b : ℤ) : ℝ :=
  Real.quantitativeLogarithmicBlockCurvatureMassBound +
    4 * (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) +
    Complex.logarithmicPhaseQuantitativeSupportLength a b *
      ((‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2 +
        ‖t‖ /
          (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2)

theorem Complex.logarithmicPhaseQuantitativeMixedVariationUpper_le_closed
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeMixedVariationUpper t a b ≤
      4 * (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) := by
  unfold Complex.logarithmicPhaseQuantitativeMixedVariationUpper
  have hleftPos :=
    Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha
  have hcoefficient :
      0 ≤ 2 * (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) :=
    mul_nonneg (Nat.cast_nonneg 2)
      (div_nonneg (norm_nonneg t) hleftPos.le)
  have hvariation :=
    Complex.logarithmicPhaseQuantitativeCutoffVariationMass_le_two a b hab
  have hmul := mul_le_mul_of_nonneg_left hvariation hcoefficient
  have hnormalize :
      2 * (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) * 2 =
        4 * (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) := by
    let ratio := ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a
    have htwo_mul_two : (2 : ℝ) * 2 = 4 :=
      (Nat.cast_mul 2 2).symm.trans
        (congrArg (fun n : ℕ => (n : ℝ))
          (show 2 * 2 = 4 from rfl))
    calc
      2 * ratio * 2 = 2 * (ratio * 2) := mul_assoc 2 ratio 2
      _ = 2 * (2 * ratio) :=
        congrArg (fun value : ℝ => 2 * value) (mul_comm ratio 2)
      _ = (2 * 2) * ratio := (mul_assoc 2 2 ratio).symm
      _ = 4 * ratio :=
        congrArg (fun value : ℝ => value * ratio) htwo_mul_two
  exact le_trans hmul (le_of_eq hnormalize)

theorem Complex.logarithmicPhaseQuantitativeSecondDerivativeMassUpper_le_closed
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeSecondDerivativeMassUpper t a b ≤
      Complex.logarithmicPhaseQuantitativeClosedSecondDerivativeMassBound
        t a b := by
  unfold Complex.logarithmicPhaseQuantitativeSecondDerivativeMassUpper
  unfold Complex.logarithmicPhaseQuantitativeClosedSecondDerivativeMassBound
  unfold Complex.logarithmicPhaseQuantitativePhaseCurvatureUpper
  have hcurvature :=
    Complex.logarithmicPhaseQuantitativeCutoffCurvatureMass_le_universal
      a b hab
  have hmixed :=
    Complex.logarithmicPhaseQuantitativeMixedVariationUpper_le_closed
      t a b ha hab
  exact add_le_add
    (add_le_add hcurvature hmixed)
    (le_refl _)

theorem Complex.logarithmicPhaseQuantitativeSecondDerivativeMass_le_closed
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeSecondDerivativeMass t a b ≤
      Complex.logarithmicPhaseQuantitativeClosedSecondDerivativeMassBound
        t a b := by
  exact le_trans
    (Complex.logarithmicPhaseQuantitativeSecondDerivativeMass_le_upper
      t a b ha hab)
    (Complex.logarithmicPhaseQuantitativeSecondDerivativeMassUpper_le_closed
      t a b ha hab)

theorem Complex.logarithmicPhaseQuantitativeClosedSecondDerivativeMassBound_nonneg
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseQuantitativeClosedSecondDerivativeMassBound
      t a b := by
  unfold Complex.logarithmicPhaseQuantitativeClosedSecondDerivativeMassBound
  have hleft :=
    Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha
  have hcurvature :=
    Real.quantitativeLogarithmicBlockCurvatureMassBound_nonneg
  have hmixed :
      0 ≤ 4 * (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) :=
    mul_nonneg (Nat.cast_nonneg 4)
      (div_nonneg (norm_nonneg t) hleft.le)
  have hlength :=
    Complex.logarithmicPhaseQuantitativeSupportLength_nonneg a b hab
  have hphaseBracket :
      0 ≤ (‖t‖ / Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2 +
        ‖t‖ / (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2 :=
    add_nonneg (sq_nonneg _)
      (div_nonneg (norm_nonneg t) (sq_nonneg _))
  have hphase := mul_nonneg hlength hphaseBracket
  exact add_nonneg (add_nonneg hcurvature hmixed) hphase

theorem Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant_le_closed
    (t : ℝ) (a b m : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant t a b m ≤
      (Complex.logarithmicPhaseQuantitativeClosedSecondDerivativeMassBound
          t a b /
        (2 * Real.pi) ^ 2) * |(m : ℝ)| ^ (-2 : ℝ) := by
  unfold Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant
  have hmass :=
    Complex.logarithmicPhaseQuantitativeSecondDerivativeMass_le_closed
      t a b ha hab
  have hdenominatorNonneg : (0 : ℝ) ≤ (2 * Real.pi) ^ 2 := sq_nonneg _
  have hdivision := div_le_div_of_nonneg_right hmass hdenominatorNonneg
  have habsoluteNonneg : (0 : ℝ) ≤ |(m : ℝ)| := abs_nonneg _
  have hpower : (0 : ℝ) ≤ |(m : ℝ)| ^ (-2 : ℝ) :=
    Real.rpow_nonneg habsoluteNonneg _
  exact mul_le_mul_of_nonneg_right hdivision hpower

theorem Complex.norm_logarithmicPhaseQuantitativeBlockFourierPacket_le_closed
    (t : ℝ) (a b m : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hm : m ≠ 0) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      (Complex.logarithmicPhaseQuantitativeClosedSecondDerivativeMassBound
          t a b /
        (2 * Real.pi) ^ 2) * |(m : ℝ)| ^ (-2 : ℝ) := by
  exact le_trans
    (Complex.norm_logarithmicPhaseQuantitativeBlockFourierPacket_le_integerInverseSquare
      t a b m ha hab hm)
    (Complex.logarithmicPhaseQuantitativeIntegerInverseSquareMajorant_le_closed
      t a b m ha hab)

end
end LFunctions
end Boundary
