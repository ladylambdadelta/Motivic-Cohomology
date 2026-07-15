import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedEnhancedPositiveGap
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedEnhancedPositiveTailCore

/-!
# Summable endpoint-enhanced positive tail

The enhanced gap is larger than the angular-only gap, so gap antitonicity
dominates the sharper majorant by the already-summable coarse envelope.  This
establishes summability while preserving the enhanced terms for arithmetic.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.positiveModeGap_le_enhancedPositiveModeGap
    (t : ℝ) (a b m : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhasePositiveModeGap m ≤
      Complex.logarithmicPhaseEnhancedPositiveModeGap t b m := by
  unfold Complex.logarithmicPhaseEnhancedPositiveModeGap
  have hright :=
    Complex.logarithmicPhaseQuantitativeSupportRight_pos a b ha hab
  have hquotient : 0 ≤
      ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b :=
    div_nonneg (norm_nonneg t) hright.le
  exact le_add_of_nonneg_left hquotient

theorem Complex.enhancedPositiveModeClosedMajorant_le_coarse
    (t : ℝ) (a b m : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hm : 0 < m) :
    Complex.logarithmicPhaseEnhancedPositiveModeClosedMajorant t a b m ≤
      Complex.logarithmicPhasePositiveModeClosedMajorant t a b m := by
  unfold Complex.logarithmicPhaseEnhancedPositiveModeClosedMajorant
  unfold Complex.logarithmicPhasePositiveModeClosedMajorant
  have hleft :=
    (Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha).le
  have hgap := Complex.logarithmicPhasePositiveModeGap_pos m hm
  have horder :=
    Complex.positiveModeGap_le_enhancedPositiveModeGap t a b m ha hab
  exact Complex.logarithmicPhaseAdaptedClosedMajorant_gap_antitone
    t a b hab hleft hgap horder

theorem Complex.enhancedPositiveModeClosedMajorant_le_integerEnvelope
    (t : ℝ) (a b m : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hm : 0 < m) :
    Complex.logarithmicPhaseEnhancedPositiveModeClosedMajorant t a b m ≤
      Complex.logarithmicPhasePositiveModeIntegerEnvelope t a b m := by
  have hcoarse :=
    Complex.enhancedPositiveModeClosedMajorant_le_coarse
      t a b m ha hab hm
  have hleft :=
    (Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha).le
  have henvelope :=
    Complex.logarithmicPhasePositiveModeClosedMajorant_le_envelope
      t a b m hab hleft hm
  have hnormalize :=
    Complex.logarithmicPhasePositiveModeEnvelope_eq_integerEnvelope
      t a b m hm
  exact le_trans hcoarse
    (le_trans henvelope (le_of_eq hnormalize))

theorem Complex.summable_logarithmicPhaseEnhancedPositiveModeClosedMajorant
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    Summable (fun m : Complex.logarithmicPhasePoissonPositiveTailModes =>
      Complex.logarithmicPhaseEnhancedPositiveModeClosedMajorant t a b m) := by
  have hmajorant :=
    Complex.summable_logarithmicPhaseAdaptedPositiveTailEnvelope t a b
  exact Summable.of_nonneg_of_le
    (fun m =>
      Complex.logarithmicPhaseAdaptedClosedMajorant_nonneg
        t a b
        (Complex.logarithmicPhaseEnhancedPositiveModeGap t b m)
        hab
        (Complex.logarithmicPhaseQuantitativeSupportLeft_pos a ha).le
        (Complex.logarithmicPhaseEnhancedPositiveModeGap_pos
          t a b m ha hab m.property).le)
    (fun m =>
      Complex.enhancedPositiveModeClosedMajorant_le_integerEnvelope
        t a b m ha hab m.property)
    hmajorant

theorem Complex.norm_logarithmicPhaseEnhancedPositiveTail_tsum_le
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket (‖t‖) a b m‖ ≤
      Complex.logarithmicPhaseEnhancedPositiveTailBudget t a b := by
  unfold Complex.logarithmicPhaseEnhancedPositiveTailBudget
  exact tsum_norm_le
    (Complex.summable_logarithmicPhaseEnhancedPositiveModeClosedMajorant
      t a b ha hab)
    (fun m =>
      Complex.norm_logarithmicPhasePositiveModePacket_le_enhanced
        t a b m ha hab m.property)

end
end LFunctions
end Boundary
