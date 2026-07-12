import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeEndpointCollars

/-!
# Internal clipped endpoint packet estimate

This owner assembles the two conditional clipped tails and the clipped central
stationary window for endpoint-active modes whose center lies in the principal
block.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped ContDiff FourierTransform Interval
open MeasureTheory

theorem Complex.norm_logarithmicPhaseQuantitativeEndpointInternalPacket_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    (a b m : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (radius : ℝ)
    (hradius : 0 < radius)
    (hm : m ∈ Complex.logarithmicPhaseQuantitativeEndpointInternalModes t a b radius) :
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      2 / 3 +
        Complex.logarithmicPhaseQuantitativeEndpointLeftTailBudget t a b m
          (Complex.logarithmicPhaseFourierStationaryPoint t m) radius +
        2 * radius +
        Complex.logarithmicPhaseQuantitativeEndpointRightTailBudget t a b m
          (Complex.logarithmicPhaseFourierStationaryPoint t m) radius := by
  have hdata :=
    (Complex.mem_logarithmicPhaseQuantitativeEndpointInternalModes_iff
      t a b m radius).mp hm
  have hactive_data := Finset.mem_sdiff.mp hdata.1
  have hmode :=
    (Complex.mem_logarithmicPhasePoissonActiveModes_iff t a b m).mp hactive_data.1
  have hcenter :
      Complex.logarithmicPhaseFourierStationaryPoint t m ∈ Set.Icc (a : ℝ) (b : ℝ) :=
    hdata.2
  let center := Complex.logarithmicPhaseFourierStationaryPoint t m
  let left := Complex.logarithmicPhaseQuantitativeEndpointWindowLeft a center radius
  let right := Complex.logarithmicPhaseQuantitativeEndpointWindowRight b center radius
  have hleft_block : (a : ℝ) ≤ left :=
    Complex.logarithmicPhaseQuantitativeEndpointWindowLeft_ge_blockLeft a center radius
  have hright_block : right ≤ (b : ℝ) :=
    Complex.logarithmicPhaseQuantitativeEndpointWindowRight_le_blockRight b center radius
  have hwindow : left ≤ right :=
    Complex.logarithmicPhaseQuantitativeEndpointWindow_nonempty
      a b center radius hcenter (le_of_lt hradius)
  have hright_tail_left : (a : ℝ) ≤ center + radius :=
    le_trans hcenter.1 (le_add_of_nonneg_right (le_of_lt hradius))
  have hleft_tail :=
    Complex.norm_logarithmicPhaseQuantitativeEndpoint_leftTail_le_budget
      t ht ht_nonneg a b m ha hab hmode.2.1 center radius rfl hradius
  have hright_tail :=
    Complex.norm_logarithmicPhaseQuantitativeEndpoint_rightTail_le_budget
      t ht ht_nonneg a b m ha hab hmode.2.1 center radius rfl hradius
      hright_tail_left
  have hcentral :=
    Complex.norm_logarithmicPhaseQuantitativeEndpointCentral_le_two_radius
      t a b m center radius hcenter (le_of_lt hradius)
  have hprincipal :=
    Complex.norm_logarithmicPhaseQuantitativeEndpoint_principal_le
      t ht_nonneg a b m left right center radius ha hleft_block hwindow hright_block
      hleft_tail hright_tail hcentral
  exact
    Complex.norm_logarithmicPhaseQuantitativePacket_le_crossings_add_principal
      t a b m ha hab hprincipal

def Complex.logarithmicPhaseQuantitativeEndpointInternalPacketBound
    (t : ℝ)
    (a b m : ℤ)
    (radius : ℝ) : ℝ :=
  2 / 3 +
    Complex.logarithmicPhaseQuantitativeEndpointLeftTailBudget t a b m
      (Complex.logarithmicPhaseFourierStationaryPoint t m) radius +
    2 * radius +
    Complex.logarithmicPhaseQuantitativeEndpointRightTailBudget t a b m
      (Complex.logarithmicPhaseFourierStationaryPoint t m) radius

theorem Complex.norm_logarithmicPhaseQuantitativeEndpointInternal_tsum_le
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (radius : ℝ)
    (hradius : 0 < radius) :
    ‖∑' m : {m : ℤ // m ∈ Complex.logarithmicPhaseQuantitativeEndpointInternalModes t a b radius},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      ∑ m ∈ Complex.logarithmicPhaseQuantitativeEndpointInternalModes t a b radius,
        Complex.logarithmicPhaseQuantitativeEndpointInternalPacketBound t a b m radius := by
  exact
    Complex.norm_logarithmicPhaseQuantitative_selectedPacket_tsum_le_finset_majorant_sum
      t a b (Complex.logarithmicPhaseQuantitativeEndpointInternalModes t a b radius)
      (fun m : ℤ =>
        Complex.logarithmicPhaseQuantitativeEndpointInternalPacketBound t a b m radius)
      (fun m hm =>
        Complex.norm_logarithmicPhaseQuantitativeEndpointInternalPacket_le
          t ht ht_nonneg a b m ha hab radius hradius hm)

end
end LFunctions
end Boundary
