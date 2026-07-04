import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhasePacketPartition

/-!
# Real-phase second-derivative packet families

This file owns the finite packet-family union construction for active
second-derivative packets.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Sample union attached to an arbitrary derivative-frequency packet family. -/
def Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
    (φ : ℝ → ℝ)
    (a b : ℕ)
    (packets : Finset ℤ) : Finset ℕ :=
  packets.biUnion
    (fun m : ℤ => Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m)

/-- A subfamily of active derivative packets inherits pairwise disjointness. -/
theorem Complex.realPhase_secondDerivative_vdc_packetFamily_pairwiseDisjoint
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {packets : Finset ℤ}
    (hpackets :
      packets ⊆ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b) :
    ∀ m₁ ∈ packets,
      ∀ m₂ ∈ packets,
        m₁ ≠ m₂ →
          Disjoint
            (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m₁)
            (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m₂) := by
  intro m₁ hm₁ m₂ hm₂ hne
  exact
    Complex.realPhase_secondDerivative_vdc_activeDerivPackets_pairwiseDisjoint
      φ a b m₁ (hpackets hm₁) m₂ (hpackets hm₂) hne

/-- The sum over a packet family expands exactly as the sample sum over its
sample union. -/
theorem Complex.realPhase_secondDerivative_vdc_packetFamilyUnion_sum_eq_packetSums
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {packets : Finset ℤ}
    (hpackets :
      packets ⊆ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b) :
    (∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion φ a b packets,
      Complex.exp (Complex.I * (φ n : ℂ))) =
    ∑ m ∈ packets,
      Complex.realPhase_secondDerivative_vdc_packetSum φ a b m := by
  exact
    Finset.sum_biUnion
      (Complex.realPhase_secondDerivative_vdc_packetFamily_pairwiseDisjoint
        φ hpackets)

end

end LFunctions
end Boundary
