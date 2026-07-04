import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseEndpointPartition

/-!
# Real-phase left and far-right endpoint tail contribution reductions

This file owns the finite reduction from the singleton structure of the
left/far endpoint derivative-packet sets to pointwise packet contribution
estimates.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- The empty left endpoint-tail packet set contributes zero. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftPacketContribution_le_twentyTarget_of_empty
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (hempty :
      Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b = ∅) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hsum :
      (∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum φ a b m) = 0 :=
    Eq.trans
      (congrArg
        (fun S : Finset ℤ =>
          ∑ m ∈ S, Complex.realPhase_secondDerivative_vdc_packetSum φ a b m)
        hempty)
      Finset.sum_empty
  have htarget_nonneg :
      0 ≤ 20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
    mul_nonneg
      (Nat.cast_nonneg 20)
      (Real.logarithmicPhase_endpoint_sqrt_target_nonneg t ht b)
  have hzero :
      ‖(0 : ℂ)‖ ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
    Eq.subst
      (motive := fun left : ℝ =>
        left ≤
          20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
      (norm_zero : ‖(0 : ℂ)‖ = 0).symm
      htarget_nonneg
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤
          20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
      hsum.symm
      hzero

/-- The empty far-right endpoint-tail packet set contributes zero. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightPacketContribution_le_twentyTarget_of_empty
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (hempty :
      Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b = ∅) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hsum :
      (∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum φ a b m) = 0 :=
    Eq.trans
      (congrArg
        (fun S : Finset ℤ =>
          ∑ m ∈ S, Complex.realPhase_secondDerivative_vdc_packetSum φ a b m)
        hempty)
      Finset.sum_empty
  have htarget_nonneg :
      0 ≤ 20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
    mul_nonneg
      (Nat.cast_nonneg 20)
      (Real.logarithmicPhase_endpoint_sqrt_target_nonneg t ht b)
  have hzero :
      ‖(0 : ℂ)‖ ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
    Eq.subst
      (motive := fun left : ℝ =>
        left ≤
          20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
      (norm_zero : ‖(0 : ℂ)‖ = 0).symm
      htarget_nonneg
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤
          20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
      hsum.symm
      hzero

/-- A pointwise bound on the unique left endpoint-tail packet gives the full
left endpoint-tail contribution bound. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftPacketContribution_le_twentyTarget_of_pointwise
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hpoint :
      ∀ m : ℤ,
        m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b →
          ‖Complex.realPhase_secondDerivative_vdc_packetSum
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ ≤
          20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)))) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  match
    Complex.logarithmicPhaseRealPhase_endpointLeftActive_eq_empty_or_singleton
      t ht_nonneg (a := a) (b := b) ha with
  | Or.inl hempty =>
      exact
        Complex.logarithmicPhaseRealPhase_endpointLeftPacketContribution_le_twentyTarget_of_empty
          t ht hempty
  | Or.inr hsingleton =>
      match hsingleton with
      | ⟨m, hm_singleton⟩ =>
          have hm_mem :
              m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b :=
            Eq.subst
              (motive := fun S : Finset ℤ => m ∈ S)
              hm_singleton.symm
              (Finset.mem_singleton_self m)
          have hsum_le_packet :
              ‖∑ n ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b,
                  Complex.realPhase_secondDerivative_vdc_packetSum
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                    a b n‖ ≤
                ‖Complex.realPhase_secondDerivative_vdc_packetSum
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  a b m‖ :=
            Complex.logarithmicPhaseRealPhase_endpointLeftPacket_sum_norm_le_of_mem
              t ht_nonneg ha hm_mem
          exact le_trans hsum_le_packet (hpoint m hm_mem)

/-- A pointwise bound on the unique far-right endpoint-tail packet gives the
full far-right endpoint-tail contribution bound. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightPacketContribution_le_twentyTarget_of_pointwise
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hpoint :
      ∀ m : ℤ,
        m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b →
          ‖Complex.realPhase_secondDerivative_vdc_packetSum
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ ≤
          20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)))) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  match
    Complex.logarithmicPhaseRealPhase_endpointFarRightActive_eq_empty_or_singleton
      t ht_nonneg (a := a) (b := b) ha with
  | Or.inl hempty =>
      exact
        Complex.logarithmicPhaseRealPhase_endpointFarRightPacketContribution_le_twentyTarget_of_empty
          t ht hempty
  | Or.inr hsingleton =>
      match hsingleton with
      | ⟨m, hm_singleton⟩ =>
          have hm_mem :
              m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b :=
            Eq.subst
              (motive := fun S : Finset ℤ => m ∈ S)
              hm_singleton.symm
              (Finset.mem_singleton_self m)
          have hsum_le_packet :
              ‖∑ n ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b,
                  Complex.realPhase_secondDerivative_vdc_packetSum
                    (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                    a b n‖ ≤
                ‖Complex.realPhase_secondDerivative_vdc_packetSum
                  (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
                  a b m‖ :=
            Complex.logarithmicPhaseRealPhase_endpointFarRightPacket_sum_norm_le_of_mem
              t ht_nonneg ha hm_mem
          exact le_trans hsum_le_packet (hpoint m hm_mem)

/-- Cardinality control of each left endpoint-tail packet gives the full left
endpoint-tail contribution bound. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftPacketContribution_le_twentyTarget_of_card
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hcard :
      ∀ m : ℤ,
        m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b →
          ((Complex.realPhase_secondDerivative_vdc_derivPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m).card : ℝ) ≤
          20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)))) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  have hpoint :
      ∀ m : ℤ,
        m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b →
          ‖Complex.realPhase_secondDerivative_vdc_packetSum
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ ≤
          20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
    fun m hm =>
      le_trans
        (Complex.realPhase_secondDerivative_vdc_packetSum_norm_le_card
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m)
        (hcard m hm)
  exact
    Complex.logarithmicPhaseRealPhase_endpointLeftPacketContribution_le_twentyTarget_of_pointwise
      t ht ht_nonneg ha hpoint

/-- Cardinality control of each far-right endpoint-tail packet gives the full
far-right endpoint-tail contribution bound. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightPacketContribution_le_twentyTarget_of_card
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hcard :
      ∀ m : ℤ,
        m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b →
          ((Complex.realPhase_secondDerivative_vdc_derivPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m).card : ℝ) ≤
          20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)))) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  have hpoint :
      ∀ m : ℤ,
        m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b →
          ‖Complex.realPhase_secondDerivative_vdc_packetSum
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ ≤
          20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
    fun m hm =>
      le_trans
        (Complex.realPhase_secondDerivative_vdc_packetSum_norm_le_card
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m)
        (hcard m hm)
  exact
    Complex.logarithmicPhaseRealPhase_endpointFarRightPacketContribution_le_twentyTarget_of_pointwise
      t ht ht_nonneg ha hpoint

end

end LFunctions
end Boundary
