import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhasePacketReconstruction
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongBudgetArithmetic
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseEndpointRightContribution

/-!
# Real-phase long-budget assembly

This file owns the finite assembly step in the long logarithmic curvature
branch: stationary packets plus endpoint packets give the final block budget.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Three endpoint-tail budgets assemble into the endpoint packet budget. -/
theorem Complex.logarithmicPhaseRealPhase_endpoint_packet_budget
    (t : ℝ)
    {a b : ℕ}
    (hab : a ≤ b)
    (hright :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
    (hleft :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
    (hfar :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)))) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b,
      Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖ ≤
      60 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  let E : ℝ :=
    (((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))
  have hsplit :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ +
      (‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ +
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖) :=
    Complex.logarithmicPhaseRealPhase_endpointPacket_norm_le_three_tail_norms
      t hab
  have htails :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ +
      (‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ +
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖) ≤
        60 * E :=
    le_trans
      (add_le_add hright (add_le_add hleft hfar))
      (Real.logarithmicPhase_three_twenty_targets_le_sixty E)
  exact le_trans hsplit htails

/-- The stationary and endpoint packet budgets assemble into the long
real-phase block estimate. -/
theorem Complex.logarithmicPhaseRealPhase_long_packet_budget
    (t : ℝ)
    {a b : ℕ}
    (hstationary :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
    (hendpoint :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
        60 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  let E : ℝ :=
    (((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))
  have hsplit :
      ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
        ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
          Complex.realPhase_secondDerivative_vdc_packetSum
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ +
        ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b,
          Complex.realPhase_secondDerivative_vdc_packetSum
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ :=
    Complex.logarithmicPhaseRealPhase_block_norm_le_stationary_endpoint_packet_norms
      t a b
  have hpacket_budget :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ +
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
        80 * E :=
    le_trans
      (add_le_add hstationary hendpoint)
      (Real.logarithmicPhase_twenty_sixty_targets_le_eighty E)
  exact le_trans hsplit hpacket_budget

/-- Stationary and three endpoint-tail packet budgets assemble into the long
real-phase block estimate. -/
theorem Complex.logarithmicPhaseRealPhase_long_packet_budget_of_tail_budgets
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hstationary :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
    (hleft :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
    (hfar :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)))) :
    ‖∑ n ∈ Finset.Icc a b,
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  have hright :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
    Complex.logarithmicPhaseRealPhase_endpointRightPacket_le_twentyTarget
      t ht ht_nonneg ha
  have hendpoint :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
        60 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
    Complex.logarithmicPhaseRealPhase_endpoint_packet_budget
      t hab hright hleft hfar
  exact
    Complex.logarithmicPhaseRealPhase_long_packet_budget
      t hstationary hendpoint

end

end LFunctions
end Boundary
