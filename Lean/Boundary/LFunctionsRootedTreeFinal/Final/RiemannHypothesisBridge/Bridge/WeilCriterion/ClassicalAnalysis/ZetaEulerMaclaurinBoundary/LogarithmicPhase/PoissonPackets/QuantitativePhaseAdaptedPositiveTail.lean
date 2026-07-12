import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedPositiveEnvelope

/-!
# Summable positive phase-adapted tail

The angular inverse-square envelope is normalized to the canonical integer
frequency p-series, then summed over the positive-mode subtype.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhasePositiveModeIntegerEnvelope
    (t : ℝ) (a b m : ℤ) : ℝ :=
  (Complex.logarithmicPhasePositiveModeInverseSquareCoefficient t a b /
      (2 * Real.pi) ^ 2) * |(m : ℝ)| ^ (-2 : ℝ)

def Complex.logarithmicPhaseAdaptedPositiveTailBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
    Complex.logarithmicPhasePositiveModeIntegerEnvelope t a b m

theorem Complex.logarithmicPhasePositiveModeGap_eq_angularNorm
    (m : ℤ) (hm : 0 < m) :
    Complex.logarithmicPhasePositiveModeGap m =
      ‖Complex.logarithmicPhasePoissonAngularFrequency m‖ := by
  unfold Complex.logarithmicPhasePositiveModeGap
  have hmReal : 0 ≤ (m : ℝ) := (Int.cast_nonneg.mpr (le_of_lt hm))
  have htwoPi : 0 ≤ 2 * Real.pi := Complex.two_mul_pi_pos.le
  have hproduct : 0 ≤ 2 * Real.pi * (m : ℝ) :=
    mul_nonneg htwoPi hmReal
  unfold Complex.logarithmicPhasePoissonAngularFrequency
  exact Eq.trans (Eq.symm (abs_of_nonneg hproduct))
    (Eq.trans (abs_neg _) (Real.norm_eq_abs _).symm)

theorem Complex.logarithmicPhasePositiveModeEnvelope_eq_integerEnvelope
    (t : ℝ) (a b m : ℤ) (hm : 0 < m) :
    Complex.logarithmicPhasePositiveModeInverseSquareEnvelope t a b m =
      Complex.logarithmicPhasePositiveModeIntegerEnvelope t a b m := by
  unfold Complex.logarithmicPhasePositiveModeInverseSquareEnvelope
  unfold Complex.logarithmicPhasePositiveModeIntegerEnvelope
  have hmNe : m ≠ 0 := ne_of_gt hm
  have hgap := Complex.logarithmicPhasePositiveModeGap_eq_angularNorm m hm
  have hinverse := Complex.angularInverseSquare_eq_integerInverseSquareCoefficient
    m hmNe
  have hdivision :
      Complex.logarithmicPhasePositiveModeInverseSquareCoefficient t a b /
          (Complex.logarithmicPhasePositiveModeGap m) ^ 2 =
        Complex.logarithmicPhasePositiveModeInverseSquareCoefficient t a b *
          (Complex.logarithmicPhasePositiveModeGap m)⁻¹ ^ 2 :=
    Real.div_pow_eq_mul_inv_pow _ _ 2
  have hcoefficient :
      Complex.logarithmicPhasePositiveModeInverseSquareCoefficient t a b *
          (((2 * Real.pi) ^ 2)⁻¹ * |(m : ℝ)| ^ (-2 : ℝ)) =
        (Complex.logarithmicPhasePositiveModeInverseSquareCoefficient t a b /
          (2 * Real.pi) ^ 2) * |(m : ℝ)| ^ (-2 : ℝ) := by
    exact Eq.trans (mul_assoc _ _ _).symm
      (congrArg (fun value : ℝ => value * |(m : ℝ)| ^ (-2 : ℝ))
        (div_eq_mul_inv _ _).symm)
  exact Eq.trans hdivision
    (Eq.trans
      (congrArg
        (fun value : ℝ =>
          Complex.logarithmicPhasePositiveModeInverseSquareCoefficient t a b *
            value)
        (Eq.trans
          (congrArg (fun value : ℝ => value⁻¹ ^ 2) hgap)
          hinverse))
      hcoefficient)

theorem Complex.summable_logarithmicPhasePositiveModeIntegerEnvelope_on_set
    (t : ℝ) (a b : ℤ) (modes : Set ℤ) :
    Summable (fun m : modes =>
      Complex.logarithmicPhasePositiveModeIntegerEnvelope t a b m) := by
  unfold Complex.logarithmicPhasePositiveModeIntegerEnvelope
  exact Complex.summable_scaled_integer_frequency_inverse_square_on_set
    (Complex.logarithmicPhasePositiveModeInverseSquareCoefficient t a b /
      (2 * Real.pi) ^ 2) modes

theorem Complex.summable_logarithmicPhaseAdaptedPositiveTailEnvelope
    (t : ℝ) (a b : ℤ) :
    Summable (fun m : Complex.logarithmicPhasePoissonPositiveTailModes =>
      Complex.logarithmicPhasePositiveModeIntegerEnvelope t a b m) := by
  exact Complex.summable_logarithmicPhasePositiveModeIntegerEnvelope_on_set
    t a b Complex.logarithmicPhasePoissonPositiveTailModes

theorem Complex.logarithmicPhaseAdaptedPositiveTailBudget_nonneg
    (t : ℝ) (a b : ℤ)
    (hab : a ≤ b)
    (hleft : 0 ≤ Complex.logarithmicPhaseQuantitativeSupportLeft a) :
    0 ≤ Complex.logarithmicPhaseAdaptedPositiveTailBudget t a b := by
  unfold Complex.logarithmicPhaseAdaptedPositiveTailBudget
  have hcoefficient :=
    Complex.logarithmicPhasePositiveModeInverseSquareCoefficient_nonneg
      t a b hab hleft
  have htwoPiSquare : 0 ≤ (2 * Real.pi) ^ 2 := sq_nonneg _
  have hscaled : 0 ≤
      Complex.logarithmicPhasePositiveModeInverseSquareCoefficient t a b /
        (2 * Real.pi) ^ 2 := div_nonneg hcoefficient htwoPiSquare
  exact tsum_nonneg (fun m =>
    mul_nonneg hscaled (Real.rpow_nonneg (abs_nonneg _) _))

theorem Complex.norm_logarithmicPhaseAdaptedPositiveTail_tsum_le
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseAdaptedPositiveTailBudget t a b := by
  unfold Complex.logarithmicPhaseAdaptedPositiveTailBudget
  have hleft :=
    (Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha).le
  have hpacket : ∀ m : Complex.logarithmicPhasePoissonPositiveTailModes,
      ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
        Complex.logarithmicPhasePositiveModeIntegerEnvelope t a b m := by
    intro m
    have hclosed := Complex.norm_logarithmicPhasePositiveModePacket_le
      t a b m ha hab m.property
    have henvelope :=
      Complex.logarithmicPhasePositiveModeClosedMajorant_le_envelope
        t a b m hab hleft m.property
    have hnormalize :=
      Complex.logarithmicPhasePositiveModeEnvelope_eq_integerEnvelope
        t a b m m.property
    exact le_trans hclosed
      (le_trans henvelope (le_of_eq hnormalize))
  exact tsum_norm_le
    (Complex.summable_logarithmicPhaseAdaptedPositiveTailEnvelope t a b)
    hpacket

end
end LFunctions
end Boundary
