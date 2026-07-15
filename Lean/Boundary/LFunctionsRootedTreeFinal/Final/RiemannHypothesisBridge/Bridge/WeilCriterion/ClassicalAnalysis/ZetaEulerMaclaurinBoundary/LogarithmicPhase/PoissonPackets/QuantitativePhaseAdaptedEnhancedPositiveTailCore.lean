import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedEnhancedPositiveGapCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeAmplitudeMassBounds

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseEnhancedPositiveTailBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑' m : Complex.logarithmicPhasePoissonPositiveTailModes,
    (48 / (Complex.logarithmicPhaseEnhancedPositiveModeGap t b m) ^ 2 +
      6 * (‖t‖ /
        (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2) /
          (Complex.logarithmicPhaseEnhancedPositiveModeGap t b m) ^ 3 +
      Complex.logarithmicPhaseQuantitativeSupportLength a b *
        (2 * ‖t‖ /
          (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 3) /
            (Complex.logarithmicPhaseEnhancedPositiveModeGap t b m) ^ 3 +
      3 * Complex.logarithmicPhaseQuantitativeSupportLength a b *
        (‖t‖ / (Complex.logarithmicPhaseQuantitativeSupportLeft a) ^ 2) ^ 2 /
          (Complex.logarithmicPhaseEnhancedPositiveModeGap t b m) ^ 4)

end
end LFunctions
end Boundary
