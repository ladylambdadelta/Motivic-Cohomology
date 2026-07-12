import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.CanonicalTails
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLogarithmicStationaryWindow

/-!
# Continuous logarithmic stationary packets

This curvature-layer owner records the continuous packet itself and the exact
three-part decomposition used by the direct Poisson B-process.  The cutoff
crossings are retained separately from the principal interval.  For canonical
interior modes, the lower packet owner supplies the explicit central-window
and nonstationary-tail majorant.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

def Complex.logarithmicPhaseContinuousPacket
    (t : ℝ) (a b m : ℤ) : ℂ :=
  ∫ x : ℝ,
    Complex.phaseCutoffFrequencyTwistIntegrand
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (Real.integerBlockCutoff a b) m x

def Complex.logarithmicPhaseContinuousPacketLeftCrossing
    (t : ℝ) (a b m : ℤ) : ℂ :=
  ∫ x in ((a : ℝ) - 2 / 3)..(a : ℝ),
    Complex.phaseCutoffFrequencyTwistIntegrand
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (Real.integerBlockCutoff a b) m x

def Complex.logarithmicPhaseContinuousPacketPrincipal
    (t : ℝ) (a b m : ℤ) : ℂ :=
  ∫ x in (a : ℝ)..(b : ℝ),
    Complex.realPhaseOscillation
      (Complex.logarithmicPhasePacketTwistedPhase t m) x

def Complex.logarithmicPhaseContinuousPacketRightCrossing
    (t : ℝ) (a b m : ℤ) : ℂ :=
  ∫ x in (b : ℝ)..((b : ℝ) + 2 / 3),
    Complex.phaseCutoffFrequencyTwistIntegrand
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (Real.integerBlockCutoff a b) m x

theorem Complex.logarithmicPhaseContinuousPacket_eq_integerBlockFourierPacket
    (t : ℝ) (a b m : ℤ) :
    Complex.logarithmicPhaseContinuousPacket t a b m =
      Complex.integerBlockFourierPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m :=
  rfl

theorem Complex.logarithmicPhaseContinuousPacketPrincipal_eq
    (t : ℝ) (a b m : ℤ) :
    Complex.logarithmicPhaseContinuousPacketPrincipal t a b m =
      ∫ x in (a : ℝ)..(b : ℝ),
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x :=
  rfl

theorem Complex.logarithmicPhaseContinuousPacket_eq_three_parts
    (t : ℝ) (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhaseContinuousPacket t a b m =
      Complex.logarithmicPhaseContinuousPacketLeftCrossing t a b m +
        Complex.logarithmicPhaseContinuousPacketPrincipal t a b m +
          Complex.logarithmicPhaseContinuousPacketRightCrossing t a b m := by
  exact
    Complex.integral_logarithmicPhase_integerBlockCutoffFrequencyTwist_eq_three_parts
      t a b m ha hab

theorem Complex.norm_logarithmicPhaseContinuousPacketLeftCrossing_le_two_thirds
    (t : ℝ) (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖Complex.logarithmicPhaseContinuousPacketLeftCrossing t a b m‖ ≤ 2 / 3 := by
  exact
    Complex.norm_intervalIntegral_logarithmicPhase_leftCutoffCrossing_le
      t a b m

theorem Complex.norm_logarithmicPhaseContinuousPacketRightCrossing_le_two_thirds
    (t : ℝ) (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖Complex.logarithmicPhaseContinuousPacketRightCrossing t a b m‖ ≤ 2 / 3 := by
  exact
    Complex.norm_intervalIntegral_logarithmicPhase_rightCutoffCrossing_le
      t a b m

theorem Complex.norm_logarithmicPhaseContinuousPacketCrossings_le_four_thirds
    (t : ℝ) (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖Complex.logarithmicPhaseContinuousPacketLeftCrossing t a b m +
        Complex.logarithmicPhaseContinuousPacketRightCrossing t a b m‖ ≤
      4 / 3 := by
  exact Complex.norm_logarithmicPhase_cutoffCrossingSum_le t a b m

theorem Complex.norm_logarithmicPhaseContinuousPacketPrincipal_le_canonical_three_piece
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b) :
    ‖Complex.logarithmicPhaseContinuousPacket t a b m‖ ≤
      Complex.logarithmicPhasePoissonCanonicalStationaryMajorant t a b m := by
  exact
    Complex.norm_integerBlockFourierPacket_le_canonicalStationaryMajorant
      t ht ht_nonneg a b m ha hab hm

theorem Complex.norm_logarithmicPhaseContinuousPacketPrincipalWindow_le_width
    (t : ℝ) (a b m : ℤ)
    (hm : m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b) :
    ‖Complex.logarithmicPhasePoissonCanonicalCentralIntegral t a b m‖ ≤
      Complex.logarithmicPhasePoissonCanonicalWindowWidth t m := by
  exact
    Complex.norm_logarithmicPhasePoissonCanonicalCentralIntegral_le_width
      t a b m hm

theorem Complex.norm_logarithmicPhaseContinuousPacketCanonicalLeftTail_le
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a)
    (hm : m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b) :
    ‖Complex.logarithmicPhasePoissonCanonicalLeftTail t a b m‖ ≤
      Complex.logarithmicPhasePoissonCanonicalLeftTailMajorant t a b m := by
  exact
    Complex.norm_logarithmicPhasePoissonCanonicalLeftTail_le_majorant
      t ht ht_nonneg a b m ha hm

theorem Complex.norm_logarithmicPhaseContinuousPacketCanonicalRightTail_le
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a)
    (hm : m ∈ Complex.logarithmicPhasePoissonCanonicalInteriorModes t a b) :
    ‖Complex.logarithmicPhasePoissonCanonicalRightTail t a b m‖ ≤
      Complex.logarithmicPhasePoissonCanonicalRightTailMajorant t a b m := by
  exact
    Complex.norm_logarithmicPhasePoissonCanonicalRightTail_le_majorant
      t ht ht_nonneg a b m ha hm

end
end LFunctions
end Boundary
