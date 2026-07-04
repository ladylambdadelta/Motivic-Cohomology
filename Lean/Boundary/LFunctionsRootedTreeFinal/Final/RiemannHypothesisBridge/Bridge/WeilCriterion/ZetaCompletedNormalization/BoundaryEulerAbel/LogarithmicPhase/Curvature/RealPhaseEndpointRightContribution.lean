import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseEndpointRightZero

/-!
# Real-phase right endpoint contribution

This file owns the local reduction from a cardinality estimate for the
right-endpoint zero derivative packet to the corresponding packet contribution
budget.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- If the zero derivative-frequency packet has the right endpoint-cardinality
budget, then its packet sum satisfies the same contribution budget. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightZeroPacketContribution_le_twentyTarget_of_card
    (t : ℝ)
    {a b : ℕ}
    (hcard :
      ((Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0).card : ℝ) ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)))) :
    ‖Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0‖ ≤
      20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
  le_trans
    (Complex.realPhase_secondDerivative_vdc_packetSum_norm_le_card
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b 0)
    hcard

end

end LFunctions
end Boundary
