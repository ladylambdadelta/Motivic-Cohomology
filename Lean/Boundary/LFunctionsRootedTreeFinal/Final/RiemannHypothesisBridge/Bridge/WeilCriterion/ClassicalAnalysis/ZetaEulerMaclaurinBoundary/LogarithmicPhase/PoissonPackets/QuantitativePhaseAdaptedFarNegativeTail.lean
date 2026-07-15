import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedFarNegativeGap

/-!
# Closed far-negative packet tail

Gap antitonicity reduces each far-negative packet to the positive-distance
inverse-square envelope.  The shifted p-series summability theorem then bounds
the complete far-negative packet sum.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.farNegativeDistanceGap_eq_positiveModeGap
    (t : ℝ) (a : ℤ)
    (m : Complex.logarithmicPhasePoissonFarNegativeModes t a) :
    2 * Real.pi *
        (Complex.logarithmicPhaseFarNegativeDistance t a m : ℝ) =
      Complex.logarithmicPhasePositiveModeGap
        (Complex.logarithmicPhaseFarNegativeDistance t a m) := by
  unfold Complex.logarithmicPhasePositiveModeGap
  exact rfl

theorem Complex.farNegativeDistanceGap_pos
    (t : ℝ) (a : ℤ)
    (m : Complex.logarithmicPhasePoissonFarNegativeModes t a) :
    0 < 2 * Real.pi *
      (Complex.logarithmicPhaseFarNegativeDistance t a m : ℝ) := by
  have hdistanceReal : 0 <
      (Complex.logarithmicPhaseFarNegativeDistance t a m : ℝ) :=
    Int.cast_pos.mpr (Complex.farNegativeDistance_pos t a m)
  exact mul_pos Complex.two_mul_pi_pos hdistanceReal

theorem Complex.logarithmicPhaseFarNegativeClosedMajorant_le_distanceClosed
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : Complex.logarithmicPhasePoissonFarNegativeModes t a) :
    Complex.logarithmicPhaseLeftInactiveClosedMajorant t a b m ≤
      Complex.logarithmicPhaseAdaptedClosedMajorant t a b
        (2 * Real.pi *
          (Complex.logarithmicPhaseFarNegativeDistance t a m : ℝ)) := by
  unfold Complex.logarithmicPhaseLeftInactiveClosedMajorant
  have hleft :=
    (Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha).le
  have hdistancePos := Complex.farNegativeDistanceGap_pos t a m
  have hgap := Complex.farNegative_distance_gap_le t a ha m
  exact Complex.logarithmicPhaseAdaptedClosedMajorant_gap_antitone
    t a b hab hleft hdistancePos hgap

theorem Complex.logarithmicPhaseFarNegativeDistanceClosed_le_envelope
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : Complex.logarithmicPhasePoissonFarNegativeModes t a) :
    Complex.logarithmicPhaseAdaptedClosedMajorant t a b
        (2 * Real.pi *
          (Complex.logarithmicPhaseFarNegativeDistance t a m : ℝ)) ≤
      Complex.logarithmicPhasePositiveModeInverseSquareEnvelope t a b
        (Complex.logarithmicPhaseFarNegativeDistance t a m) := by
  have hleft :=
    (Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha).le
  have hdistance := Complex.farNegativeDistance_pos t a m
  exact Complex.logarithmicPhasePositiveModeClosedMajorant_le_envelope
    t a b (Complex.logarithmicPhaseFarNegativeDistance t a m)
    hab hleft hdistance

theorem Complex.logarithmicPhaseFarNegativeEnvelope_eq_scaled
    (t : ℝ) (a b : ℤ)
    (m : Complex.logarithmicPhasePoissonFarNegativeModes t a) :
    Complex.logarithmicPhasePositiveModeInverseSquareEnvelope t a b
        (Complex.logarithmicPhaseFarNegativeDistance t a m) =
      Complex.logarithmicPhaseFarNegativeScaledEnvelope t a b m := by
  have hdistance := Complex.farNegativeDistance_pos t a m
  have hpositiveNormalize :=
    Complex.logarithmicPhasePositiveModeEnvelope_eq_integerEnvelope
      t a b (Complex.logarithmicPhaseFarNegativeDistance t a m) hdistance
  unfold Complex.logarithmicPhaseFarNegativeScaledEnvelope
  unfold Complex.logarithmicPhasePositiveModeIntegerEnvelope at hpositiveNormalize
  unfold Complex.logarithmicPhaseFarNegativeIntegerInverseSquare
  exact hpositiveNormalize

theorem Complex.norm_logarithmicPhaseFarNegativeModePacket_le_scaledEnvelope
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b)
    (m : Complex.logarithmicPhasePoissonFarNegativeModes t a) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket (‖t‖) a b m‖ ≤
      Complex.logarithmicPhaseFarNegativeScaledEnvelope t a b m := by
  have hpacket :=
    Complex.norm_logarithmicPhaseFarNegativeModePacket_le t a b ha hab m
  have hdistance :=
    Complex.logarithmicPhaseFarNegativeClosedMajorant_le_distanceClosed
      t a b ha hab m
  have henvelope :=
    Complex.logarithmicPhaseFarNegativeDistanceClosed_le_envelope
      t a b ha hab m
  have hnormalize :=
    Complex.logarithmicPhaseFarNegativeEnvelope_eq_scaled t a b m
  exact le_trans hpacket
    (le_trans hdistance
      (le_trans henvelope (le_of_eq hnormalize)))

theorem Complex.norm_logarithmicPhaseAdaptedFarNegativeTail_tsum_le
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑' m : Complex.logarithmicPhasePoissonFarNegativeModes t a,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket (‖t‖) a b m‖ ≤
      Complex.logarithmicPhaseAdaptedFarNegativeTailBudget t a b := by
  unfold Complex.logarithmicPhaseAdaptedFarNegativeTailBudget
  exact tsum_norm_le
    (Complex.summable_logarithmicPhaseFarNegativeScaledEnvelope t a b)
    (fun m =>
      Complex.norm_logarithmicPhaseFarNegativeModePacket_le_scaledEnvelope
        t a b ha hab m)

end
end LFunctions
end Boundary
