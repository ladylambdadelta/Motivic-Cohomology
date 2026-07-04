import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseEndpointFirstDerivative
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

/-- If the zero derivative-frequency packet is explicitly a terminal interval
and that terminal interval has the first-derivative monotonicity/separation
data, then the zero packet has the endpoint contribution budget. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightZeroPacketContribution_le_twentyTarget_of_terminalInterval
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b c : ℕ}
    (hc_one : 1 ≤ c)
    (hcb : c ≤ b)
    (hpacket :
      Complex.realPhase_secondDerivative_vdc_derivPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b 0 =
        Finset.Icc c b)
    (hinc_mono :
      Complex.realPhase_integerIncrementMonotoneOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) c b)
    (hred_mono :
      Complex.realPhase_reducedIntegerIncrementMonotoneOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) c b)
    (hsep :
      Complex.realPhase_integerIncrementSeparatedOn
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t) c b
        (‖t‖ / ((b + 1 : ℕ) : ℝ))) :
    ‖Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0‖ ≤
      20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hsum_eq :
      Complex.realPhase_secondDerivative_vdc_packetSum φ a b 0 =
        ∑ n ∈ Finset.Icc c b,
          Complex.exp (Complex.I * (φ n : ℂ)) :=
    congrArg
      (fun S : Finset ℕ =>
        ∑ n ∈ S, Complex.exp (Complex.I * (φ n : ℂ)))
      hpacket
  have hinterval :
      ‖∑ n ∈ Finset.Icc c b,
        Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
    Complex.logarithmicPhaseRealPhase_firstDerivative_subblock_le_twentyTarget
      t ht hc_one hcb le_rfl hinc_mono hred_mono hsep
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤
          20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
      hsum_eq.symm
      hinterval

end

end LFunctions
end Boundary
