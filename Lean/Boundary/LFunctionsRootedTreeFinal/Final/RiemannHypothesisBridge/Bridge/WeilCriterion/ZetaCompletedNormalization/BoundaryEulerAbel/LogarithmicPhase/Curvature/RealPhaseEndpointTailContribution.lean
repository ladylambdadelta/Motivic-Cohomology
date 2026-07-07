import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseEndpointInterval
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseEndpointPartition
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseIntervalReduction
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhasePacketReconstruction

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

/-- A left reciprocal-scale cut cardinality bound gives the full left
endpoint-tail contribution bound. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftPacketContribution_le_twentyTarget_of_scaleCut
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hscale :
      (((Finset.Icc a b).filter
        (fun n : ℕ =>
          ‖t‖ / (a : ℝ) - (1 / 2 : ℝ) < ‖t‖ / (n : ℝ))).card :
          ℝ) ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)))) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  have hcard :
      ∀ m : ℤ,
        m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b →
          ((Complex.realPhase_secondDerivative_vdc_derivPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m).card : ℝ) ≤
          20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
    fun m hm =>
      have hpacket_nat :
          (Complex.realPhase_secondDerivative_vdc_derivPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m).card ≤
          ((Finset.Icc a b).filter
            (fun n : ℕ =>
              ‖t‖ / (a : ℝ) - (1 / 2 : ℝ) < ‖t‖ / (n : ℝ))).card :=
        Complex.logarithmicPhaseRealPhase_endpointLeftDerivPacket_card_le_scaleCut
          t ht ht_nonneg ha hm
      have hpacket_real :
          ((Complex.realPhase_secondDerivative_vdc_derivPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m).card : ℝ) ≤
          (((Finset.Icc a b).filter
            (fun n : ℕ =>
              ‖t‖ / (a : ℝ) - (1 / 2 : ℝ) < ‖t‖ / (n : ℝ))).card : ℝ) :=
        Nat.cast_le.mpr hpacket_nat
      le_trans hpacket_real hscale
  exact
    Complex.logarithmicPhaseRealPhase_endpointLeftPacketContribution_le_twentyTarget_of_card
      t ht ht_nonneg ha hcard

/-- A far-right reciprocal-scale cut cardinality bound gives the full
far-right endpoint-tail contribution bound. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightPacketContribution_le_twentyTarget_of_scaleCut
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hscale :
      (((Finset.Icc a b).filter
        (fun n : ℕ =>
          ‖t‖ / (n : ℝ) <
            ‖t‖ / (((b + 1 : ℕ) : ℝ)) + (1 / 2 : ℝ))).card :
          ℝ) ≤
        20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)))) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  have hcard :
      ∀ m : ℤ,
        m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b →
          ((Complex.realPhase_secondDerivative_vdc_derivPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m).card : ℝ) ≤
          20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
    fun m hm =>
      have hpacket_nat :
          (Complex.realPhase_secondDerivative_vdc_derivPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m).card ≤
          ((Finset.Icc a b).filter
            (fun n : ℕ =>
              ‖t‖ / (n : ℝ) <
                ‖t‖ / (((b + 1 : ℕ) : ℝ)) + (1 / 2 : ℝ))).card :=
        Complex.logarithmicPhaseRealPhase_endpointFarRightDerivPacket_card_le_scaleCut
          t ht_nonneg ha hm
      have hpacket_real :
          ((Complex.realPhase_secondDerivative_vdc_derivPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m).card : ℝ) ≤
          (((Finset.Icc a b).filter
            (fun n : ℕ =>
              ‖t‖ / (n : ℝ) <
                ‖t‖ / (((b + 1 : ℕ) : ℝ)) + (1 / 2 : ℝ))).card : ℝ) :=
        Nat.cast_le.mpr hpacket_nat
      le_trans hpacket_real hscale
  exact
    Complex.logarithmicPhaseRealPhase_endpointFarRightPacketContribution_le_twentyTarget_of_card
      t ht ht_nonneg ha hcard

/-- The left endpoint-tail contribution is controlled once every closed
initial subinterval has the endpoint first-derivative budget. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftPacketContribution_le_twentyTarget_of_Icc_bounds
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hIcc :
      ∀ {r : ℕ},
        a ≤ r →
        r ≤ b →
          ‖∑ n ∈ Finset.Icc a r,
            Complex.exp
              (Complex.I *
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                  t n : ℂ))‖ ≤
            20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)))) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hinterval :
      ∃ c : ℕ,
        a ≤ c ∧ c ≤ b + 1 ∧
        Complex.realPhase_secondDerivative_vdc_packetFamilyUnion φ a b
            (Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets
              t a b) =
          Finset.Ico a c :=
    Complex.logarithmicPhaseRealPhase_endpointLeftPacketFamilyUnion_eq_initialInterval
      t ht ht_nonneg ha hab
  match hinterval with
  | ⟨c, _hac, hcb, hfamily⟩ =>
      have hsample :
          ‖∑ n ∈ Finset.Ico a c,
            Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
            20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
        Complex.logarithmicPhaseRealPhase_Ico_twenty_bound_of_Icc_bounds
          t ht hcb hIcc
      have hunion_sum :
          (∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion φ a b
              (Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets
                t a b),
            Complex.exp (Complex.I * (φ n : ℂ))) =
          ∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets
              t a b,
            Complex.realPhase_secondDerivative_vdc_packetSum φ a b m :=
        Complex.logarithmicPhaseRealPhase_endpointLeftPacketFamilyUnion_sum_eq
          t a b
      have hsample_eq :
          (∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion φ a b
              (Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets
                t a b),
            Complex.exp (Complex.I * (φ n : ℂ))) =
          ∑ n ∈ Finset.Ico a c,
            Complex.exp (Complex.I * (φ n : ℂ)) :=
        congrArg
          (fun S : Finset ℕ =>
            ∑ n ∈ S, Complex.exp (Complex.I * (φ n : ℂ)))
          hfamily
      have hpacket_sum :
          (∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets
              t a b,
            Complex.realPhase_secondDerivative_vdc_packetSum φ a b m) =
          ∑ n ∈ Finset.Ico a c,
            Complex.exp (Complex.I * (φ n : ℂ)) :=
        Eq.trans hunion_sum.symm hsample_eq
      exact
        Eq.subst
          (motive := fun z : ℂ =>
            ‖z‖ ≤
              20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
          hpacket_sum.symm
          hsample

/-- The far-right endpoint-tail contribution is controlled once every closed
subinterval has the endpoint first-derivative budget. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightPacketContribution_le_twentyTarget_of_Icc_bounds
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hIcc :
      ∀ {c r : ℕ},
        a ≤ c →
        c ≤ r →
        r ≤ b →
          ‖∑ n ∈ Finset.Icc c r,
            Complex.exp
              (Complex.I *
                (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
                  t n : ℂ))‖ ≤
            20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)))) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hinterval :
      ∃ c d : ℕ,
        a ≤ c ∧ c ≤ d ∧ d ≤ b + 1 ∧
        Complex.realPhase_secondDerivative_vdc_packetFamilyUnion φ a b
            (Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets
              t a b) =
          Finset.Ico c d :=
    Complex.logarithmicPhaseRealPhase_endpointFarRightPacketFamilyUnion_eq_boundedInterval
      t ht ht_nonneg ha hab
  match hinterval with
  | ⟨c, d, hac, _hcd, hdb, hfamily⟩ =>
      have hclosed :
          ∀ {r : ℕ},
            c ≤ r →
            r ≤ b →
              ‖∑ n ∈ Finset.Icc c r,
                Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
                20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ +
                  Real.sqrt (1 + ‖t‖))) :=
        fun {r} hcr hrb =>
          hIcc hac hcr hrb
      have hsample :
          ‖∑ n ∈ Finset.Ico c d,
            Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
            20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
        Complex.logarithmicPhaseRealPhase_Ico_twenty_bound_of_Icc_bounds
          t ht hdb hclosed
      have hunion_sum :
          (∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion φ a b
              (Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets
                t a b),
            Complex.exp (Complex.I * (φ n : ℂ))) =
          ∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets
              t a b,
            Complex.realPhase_secondDerivative_vdc_packetSum φ a b m :=
        Complex.logarithmicPhaseRealPhase_endpointFarRightPacketFamilyUnion_sum_eq
          t a b
      have hsample_eq :
          (∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion φ a b
              (Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets
                t a b),
            Complex.exp (Complex.I * (φ n : ℂ))) =
          ∑ n ∈ Finset.Ico c d,
            Complex.exp (Complex.I * (φ n : ℂ)) :=
        congrArg
          (fun S : Finset ℕ =>
            ∑ n ∈ S, Complex.exp (Complex.I * (φ n : ℂ)))
          hfamily
      have hpacket_sum :
          (∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets
              t a b,
            Complex.realPhase_secondDerivative_vdc_packetSum φ a b m) =
          ∑ n ∈ Finset.Ico c d,
            Complex.exp (Complex.I * (φ n : ℂ)) :=
        Eq.trans hunion_sum.symm hsample_eq
      exact
        Eq.subst
          (motive := fun z : ℂ =>
            ‖z‖ ≤
              20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
          hpacket_sum.symm
          hsample

end

end LFunctions
end Boundary
