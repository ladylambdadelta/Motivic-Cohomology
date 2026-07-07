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

/-- The sample count of a disjoint active packet family is the sum of its
individual packet counts. -/
theorem Complex.realPhase_secondDerivative_vdc_packetFamilyUnion_card_eq_sum_cards
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {packets : Finset ℤ}
    (hpackets :
      packets ⊆ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b) :
    (Complex.realPhase_secondDerivative_vdc_packetFamilyUnion φ a b packets).card =
      ∑ m ∈ packets,
        (Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m).card := by
  exact
    Finset.card_biUnion
      (Complex.realPhase_secondDerivative_vdc_packetFamily_pairwiseDisjoint
        φ hpackets)

/-- The sample union of an active packet subfamily is contained in the
underlying integer block. -/
theorem Complex.realPhase_secondDerivative_vdc_packetFamilyUnion_subset_block
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {packets : Finset ℤ}
    (hpackets :
      packets ⊆ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b) :
    Complex.realPhase_secondDerivative_vdc_packetFamilyUnion φ a b packets ⊆
      Finset.Icc a b := by
  intro n hn
  have hexists :
      ∃ m : ℤ,
        m ∈ packets ∧
          n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m :=
    Finset.mem_biUnion.mp hn
  match hexists with
  | Exists.intro m hm =>
      exact
        Complex.realPhase_secondDerivative_vdc_activePacket_member_mem_block
          φ (hpackets hm.1) hm.2

/-- The sample count of an active packet subfamily is bounded by the ambient
integer block count. -/
theorem Complex.realPhase_secondDerivative_vdc_packetFamilyUnion_card_le_block
    (φ : ℝ → ℝ)
    {a b : ℕ}
    {packets : Finset ℤ}
    (hpackets :
      packets ⊆ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b) :
    (Complex.realPhase_secondDerivative_vdc_packetFamilyUnion φ a b packets).card ≤
      (Finset.Icc a b).card := by
  exact
    Finset.card_le_card
      (Complex.realPhase_secondDerivative_vdc_packetFamilyUnion_subset_block
        φ hpackets)

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
