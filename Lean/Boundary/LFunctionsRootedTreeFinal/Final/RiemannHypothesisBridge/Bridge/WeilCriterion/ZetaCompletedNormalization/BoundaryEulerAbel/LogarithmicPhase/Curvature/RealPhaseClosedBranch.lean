import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseCurvatureLower
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseLongBudget

/-!
# Closed logarithmic real-phase curvature branch

This file restores the closed owner names for the resonance-safe logarithmic
long branch in the split curvature tree.  The proofs here are assembly proofs:
the packet reconstruction and endpoint/stationary contribution estimates remain
owned by their respective split files.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Positive long branch from closed stationary and endpoint contribution
budgets. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_stationary_bProcess_budget
    (t : ℝ)
    (_ht : 1 ≤ ‖t‖)
    (_ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (_ha : 1 ≤ a)
    (_hab : a ≤ b)
    (_hab_strict : a < b)
    (_hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (_hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
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
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
  exact
    Complex.logarithmicPhaseRealPhase_long_packet_budget
      t hstationary hendpoint

/-- Positive long branch from a closed stationary contribution budget and
three closed endpoint-tail contribution budgets. -/
theorem Complex.logarithmicPhaseRealPhase_long_nonneg_stationary_bProcess_budget_of_tails
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hab_strict : a < b)
    (hlong_sqrt :
      Real.sqrt (1 + ‖t‖) < (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
    (hlong_endpoint :
      (((b + 1 : ℕ) : ℝ) / ‖t‖) <
        (((b + 1 : ℕ) : ℝ) - (a : ℝ)))
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
      80 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
        Real.sqrt (1 + ‖t‖))) := by
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
    Complex.logarithmicPhaseRealPhase_long_nonneg_stationary_bProcess_budget
      t ht ht_nonneg ha hab hab_strict hlong_sqrt hlong_endpoint
      hstationary hendpoint

end

end LFunctions
end Boundary
