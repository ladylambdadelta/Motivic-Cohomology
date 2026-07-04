import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseEndpointPartition
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhasePacketFamily

/-!
# Real-phase logarithmic packet reconstruction

This file owns the finite packet-family reconstruction and endpoint-tail
triangle decompositions for the real logarithmic phase.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Stationary packet sums are the sample sum over the stationary packet
family union. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryPacketFamilyUnion_sum_eq
    (t : ℝ)
    (a b : ℕ) :
    (∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b),
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))) =
    ∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
      Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m := by
  exact
    Complex.realPhase_secondDerivative_vdc_packetFamilyUnion_sum_eq_packetSums
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (fun m hm =>
        Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_mem_active
          t hm)

/-- Right endpoint-tail packet sums are the sample sum over the right endpoint
packet-family union. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightPacketFamilyUnion_sum_eq
    (t : ℝ)
    (a b : ℕ) :
    (∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b),
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))) =
    ∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b,
      Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m := by
  exact
    Complex.realPhase_secondDerivative_vdc_packetFamilyUnion_sum_eq_packetSums
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (fun m hm =>
        Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets_mem_active
          t hm)

/-- Left endpoint-tail packet sums are the sample sum over the left endpoint
packet-family union. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftPacketFamilyUnion_sum_eq
    (t : ℝ)
    (a b : ℕ) :
    (∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b),
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))) =
    ∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b,
      Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m := by
  exact
    Complex.realPhase_secondDerivative_vdc_packetFamilyUnion_sum_eq_packetSums
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (fun m hm =>
        Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets_mem_active
          t hm)

/-- Far-right endpoint-tail packet sums are the sample sum over the far-right
endpoint packet-family union. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightPacketFamilyUnion_sum_eq
    (t : ℝ)
    (a b : ℕ) :
    (∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b),
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))) =
    ∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b,
      Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m := by
  exact
    Complex.realPhase_secondDerivative_vdc_packetFamilyUnion_sum_eq_packetSums
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (fun m hm =>
        Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets_mem_active
          t hm)

/-- Norm form of the right endpoint packet-family sample-union expansion. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightPacketFamilyUnion_norm_eq
    (t : ℝ)
    (a b : ℕ) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b,
      Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖ =
    ‖∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b),
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ := by
  exact congrArg norm
    (Complex.logarithmicPhaseRealPhase_endpointRightPacketFamilyUnion_sum_eq
      t a b).symm

/-- Norm form of the left endpoint packet-family sample-union expansion. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftPacketFamilyUnion_norm_eq
    (t : ℝ)
    (a b : ℕ) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b,
      Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖ =
    ‖∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b),
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ := by
  exact congrArg norm
    (Complex.logarithmicPhaseRealPhase_endpointLeftPacketFamilyUnion_sum_eq
      t a b).symm

/-- Norm form of the far-right endpoint packet-family sample-union expansion. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightPacketFamilyUnion_norm_eq
    (t : ℝ)
    (a b : ℕ) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b,
      Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖ =
    ‖∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b),
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ := by
  exact congrArg norm
    (Complex.logarithmicPhaseRealPhase_endpointFarRightPacketFamilyUnion_sum_eq
      t a b).symm

/-- Norm form of the stationary packet-family sample-union expansion. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryPacketFamilyUnion_norm_eq
    (t : ℝ)
    (a b : ℕ) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
      Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖ =
    ‖∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b),
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ := by
  exact congrArg norm
    (Complex.logarithmicPhaseRealPhase_stationaryPacketFamilyUnion_sum_eq
      t a b).symm

/-- The active derivative-packet reconstruction splits the logarithmic block
into its stationary and endpoint packet contributions. -/
theorem Complex.logarithmicPhaseRealPhase_block_norm_le_stationary_endpoint_packet_norms
    (t : ℝ)
    (a b : ℕ) :
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
          a b m‖ := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  let stationary : Finset ℤ :=
    Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b
  let endpoint : Finset ℤ :=
    Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b
  let packet : ℤ → ℂ :=
    fun m : ℤ => Complex.realPhase_secondDerivative_vdc_packetSum φ a b m
  have hpartition :
      Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b =
        stationary ∪ endpoint :=
    Complex.logarithmicPhaseRealPhase_activeDerivPackets_eq_stationary_union_endpoint
      t a b
  have hdisjoint : Disjoint stationary endpoint :=
    Complex.logarithmicPhaseRealPhase_stationary_endpoint_disjoint t a b
  have hpacket_sum :
      (∑ m ∈ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b,
        packet m) =
        (∑ m ∈ stationary, packet m) + ∑ m ∈ endpoint, packet m := by
    have hchange :
        (∑ m ∈ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b,
          packet m) =
          ∑ m ∈ stationary ∪ endpoint, packet m :=
      congrArg (fun s : Finset ℤ => ∑ m ∈ s, packet m) hpartition
    have hunion :
        (∑ m ∈ stationary ∪ endpoint, packet m) =
          (∑ m ∈ stationary, packet m) + ∑ m ∈ endpoint, packet m :=
      Finset.sum_union hdisjoint
    exact Eq.trans hchange hunion
  have hactive_eq_block :
      (∑ m ∈ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b,
        packet m) =
      ∑ n ∈ Finset.Icc a b,
        Complex.exp (Complex.I * (φ n : ℂ)) :=
    Complex.realPhase_secondDerivative_vdc_activePacketSums_eq_block_sum φ a b
  have hblock_eq :
      (∑ n ∈ Finset.Icc a b,
        Complex.exp (Complex.I * (φ n : ℂ))) =
        (∑ m ∈ stationary, packet m) + ∑ m ∈ endpoint, packet m :=
    Eq.trans hactive_eq_block.symm hpacket_sum
  have htriangle :
      ‖(∑ m ∈ stationary, packet m) + ∑ m ∈ endpoint, packet m‖ ≤
        ‖∑ m ∈ stationary, packet m‖ + ‖∑ m ∈ endpoint, packet m‖ :=
    norm_add_le
      (∑ m ∈ stationary, packet m)
      (∑ m ∈ endpoint, packet m)
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤
          ‖∑ m ∈ stationary, packet m‖ +
          ‖∑ m ∈ endpoint, packet m‖)
      hblock_eq.symm
      htriangle

/-- The endpoint packet contribution splits into the three endpoint tails. -/
theorem Complex.logarithmicPhaseRealPhase_endpointPacket_norm_le_three_tail_norms
    (t : ℝ)
    {a b : ℕ}
    (hab : a ≤ b) :
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
          a b m‖) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  let right : Finset ℤ :=
    Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b
  let left : Finset ℤ :=
    Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b
  let far : Finset ℤ :=
    Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b
  let packet : ℤ → ℂ :=
    fun m : ℤ => Complex.realPhase_secondDerivative_vdc_packetSum φ a b m
  have hpartition :
      Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b =
        right ∪ (left ∪ far) :=
    Complex.logarithmicPhaseRealPhase_endpointActive_eq_three_tails t a b
  have hleft_far : Disjoint left far :=
    Complex.logarithmicPhaseRealPhase_endpointLeft_farRight_disjoint t hab
  have hright_left : Disjoint right left :=
    Complex.logarithmicPhaseRealPhase_endpointRight_left_disjoint t a b
  have hright_far : Disjoint right far :=
    Complex.logarithmicPhaseRealPhase_endpointRight_farRight_disjoint t a b
  have hright_rest : Disjoint right (left ∪ far) := by
    exact Finset.disjoint_left.mpr
      (fun m hm_right hm_rest =>
        match Finset.mem_union.mp hm_rest with
        | Or.inl hm_left =>
            (Finset.disjoint_left.mp hright_left) hm_right hm_left
        | Or.inr hm_far =>
            (Finset.disjoint_left.mp hright_far) hm_right hm_far)
  have hsum_endpoint :
      (∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b,
        packet m) =
        (∑ m ∈ right, packet m) +
          ((∑ m ∈ left, packet m) + ∑ m ∈ far, packet m) := by
    have hchange :
        (∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b,
          packet m) =
          ∑ m ∈ right ∪ (left ∪ far), packet m :=
      congrArg (fun s : Finset ℤ => ∑ m ∈ s, packet m) hpartition
    have houter :
        (∑ m ∈ right ∪ (left ∪ far), packet m) =
          (∑ m ∈ right, packet m) + ∑ m ∈ left ∪ far, packet m :=
      Finset.sum_union hright_rest
    have hinner :
        (∑ m ∈ left ∪ far, packet m) =
          (∑ m ∈ left, packet m) + ∑ m ∈ far, packet m :=
      Finset.sum_union hleft_far
    exact Eq.trans hchange (Eq.trans houter
      (congrArg (fun z : ℂ => (∑ m ∈ right, packet m) + z) hinner))
  have htriangle_inner :
      ‖(∑ m ∈ left, packet m) + ∑ m ∈ far, packet m‖ ≤
        ‖∑ m ∈ left, packet m‖ + ‖∑ m ∈ far, packet m‖ :=
    norm_add_le (∑ m ∈ left, packet m) (∑ m ∈ far, packet m)
  have htriangle_outer :
      ‖(∑ m ∈ right, packet m) +
          ((∑ m ∈ left, packet m) + ∑ m ∈ far, packet m)‖ ≤
        ‖∑ m ∈ right, packet m‖ +
          ‖(∑ m ∈ left, packet m) + ∑ m ∈ far, packet m‖ :=
    norm_add_le
      (∑ m ∈ right, packet m)
      ((∑ m ∈ left, packet m) + ∑ m ∈ far, packet m)
  have hcombined :
      ‖(∑ m ∈ right, packet m) +
          ((∑ m ∈ left, packet m) + ∑ m ∈ far, packet m)‖ ≤
        ‖∑ m ∈ right, packet m‖ +
          (‖∑ m ∈ left, packet m‖ + ‖∑ m ∈ far, packet m‖) :=
    le_trans htriangle_outer
      (add_le_add_left htriangle_inner ‖∑ m ∈ right, packet m‖)
  exact
    Eq.subst
      (motive := fun z : ℂ =>
        ‖z‖ ≤
          ‖∑ m ∈ right, packet m‖ +
          (‖∑ m ∈ left, packet m‖ + ‖∑ m ∈ far, packet m‖))
      hsum_endpoint.symm
      hcombined

end

end LFunctions
end Boundary
