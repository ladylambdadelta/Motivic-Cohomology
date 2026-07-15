import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedGap

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseEnhancedPositiveModeGap
    (t : ℝ) (b m : ℤ) : ℝ :=
  ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b +
    Complex.logarithmicPhasePositiveModeGap m

theorem Complex.logarithmicPhaseEnhancedPositiveModeGap_pos
    (t : ℝ) (a b m : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) (hm : 0 < m) :
    0 < Complex.logarithmicPhaseEnhancedPositiveModeGap t b m := by
  unfold Complex.logarithmicPhaseEnhancedPositiveModeGap
  have hright :=
    Complex.logarithmicPhaseQuantitativeSupportRight_pos a b ha hab
  have hquotient :
      0 ≤ ‖t‖ / Complex.logarithmicPhaseQuantitativeSupportRight b :=
    div_nonneg (norm_nonneg t) hright.le
  have htwoPi : 0 < 2 * Real.pi :=
    mul_pos zero_lt_two Real.pi_pos
  have hmReal : 0 < (m : ℝ) := Int.cast_pos.mpr hm
  have hmode : 0 < Complex.logarithmicPhasePositiveModeGap m := by
    unfold Complex.logarithmicPhasePositiveModeGap
    exact mul_pos htwoPi hmReal
  exact add_pos_of_nonneg_of_pos hquotient hmode

end
end LFunctions
end Boundary
