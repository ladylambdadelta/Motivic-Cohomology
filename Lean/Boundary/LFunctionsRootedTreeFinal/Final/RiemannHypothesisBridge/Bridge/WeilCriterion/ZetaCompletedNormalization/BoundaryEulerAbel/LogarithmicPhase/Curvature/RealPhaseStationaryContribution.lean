import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseIntervalReduction
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhasePacketCurvature
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhasePacketReconstruction
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseStationaryInterval

/-!
# Real-phase stationary packet contribution

This file owns the finite reconstruction step for stationary packets in the
long logarithmic curvature branch.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- The stationary packet-family sample count is the sum of the stationary
derivative-packet counts. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryPacketFamilyUnion_card_eq_sum_cards
    (t : ℝ)
    (a b : ℕ) :
    (Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b
      (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b)).card =
      ∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
        (Complex.realPhase_secondDerivative_vdc_derivPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m).card := by
  exact
    Complex.realPhase_secondDerivative_vdc_packetFamilyUnion_card_eq_sum_cards
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (fun m hm =>
        Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_mem_active
          t hm)

/-- The stationary packet-family sample count is bounded by the ambient
integer block count. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryPacketFamilyUnion_card_le_block
    (t : ℝ)
    (a b : ℕ) :
    (Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b
      (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b)).card ≤
      (Finset.Icc a b).card := by
  exact
    Complex.realPhase_secondDerivative_vdc_packetFamilyUnion_card_le_block
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (fun m hm =>
        Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_mem_active
          t hm)

/-- The stationary packet-family sample sum is bounded by the stationary
packet-family sample count. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryPacketFamilyUnion_norm_le_card
    (t : ℝ)
    (a b : ℕ) :
    ‖∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b),
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      ((Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b)).card :
        ℝ) := by
  exact
    Complex.realPhase_secondDerivative_vdc_packetFamilyUnion_norm_le_card
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)

/-- The stationary packet-family sample sum is bounded by the ambient integer
block count. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryPacketFamilyUnion_norm_le_block_card
    (t : ℝ)
    (a b : ℕ) :
    ‖∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b),
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      ((Finset.Icc a b).card : ℝ) := by
  exact
    Complex.realPhase_secondDerivative_vdc_packetFamilyUnion_norm_le_block_card
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      (fun m hm =>
        Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_mem_active
          t hm)

/-- A bound for the stationary packet-family sample union transfers directly
to the stationary packet contribution. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryPacketContribution_le_of_familyUnion
    (t : ℝ)
    {a b : ℕ}
    {M : ℝ}
    (hfamily :
      ‖∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b
          (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b),
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
        M) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      M := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hnorm :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum φ a b m‖ =
      ‖∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
          φ a b
          (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b),
        Complex.exp (Complex.I * (φ n : ℂ))‖ :=
    Complex.logarithmicPhaseRealPhase_stationaryPacketFamilyUnion_norm_eq
      t a b
  exact
    Eq.subst
      (motive := fun left : ℝ => left ≤ M)
      hnorm.symm
      hfamily

/-- Pointwise packet-sum control over stationary active packets controls the
whole stationary packet contribution. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryPacketContribution_le_of_pointwise
    (t : ℝ)
    {a b : ℕ}
    {M : ℝ}
    (hM : 0 ≤ M)
    (hpoint :
      ∀ m : ℤ,
        m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b →
          ‖Complex.realPhase_secondDerivative_vdc_packetSum
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ ≤
          M) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      ((Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b).card :
        ℝ) * M := by
  exact
    Complex.finite_sum_norm_le_card_mul_of_norm_le
      (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b)
      (fun m : ℤ =>
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m)
      hM
      hpoint

/-- Stationary packet contribution bound obtained from the active-packet
reciprocal-curvature scale estimate. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryPacketContribution_le_card_mul_curvatureScale_add_one_of_nonneg
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      ((Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b).card :
        ℝ) *
        ((((b + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ))) / ‖t‖ + 1) := by
  have hscale_nonneg :
      0 ≤
        ((((b + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ))) / ‖t‖ + 1) := by
    have hleft_nonneg :
        0 ≤ ((((b + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ))) / ‖t‖) := by
      have hnum_nonneg :
          0 ≤ (((b + 1 : ℕ) : ℝ) * (((b + 1 : ℕ) : ℝ))) :=
        mul_nonneg
          (Nat.cast_nonneg (b + 1))
          (Nat.cast_nonneg (b + 1))
      exact div_nonneg hnum_nonneg (norm_nonneg t)
    exact add_nonneg hleft_nonneg zero_le_one
  exact
    Complex.logarithmicPhaseRealPhase_stationaryPacketContribution_le_of_pointwise
      t hscale_nonneg
      (fun m hm =>
        Complex.logarithmicPhaseRealPhase_active_packetSum_le_curvatureScale_add_one_of_nonneg
          t ht ht_nonneg
          (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_mem_active
            t hm)
          ha hab)

/-- Stationary packet-family sample sums inherit a closed-subinterval
twentieth-budget bound through the stationary interval reconstruction. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryPacketFamilyUnion_le_twentyTarget_of_Icc_bounds
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
    ‖∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b),
      Complex.exp
        (Complex.I *
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
      20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  match
    Complex.logarithmicPhaseRealPhase_stationaryPacketFamilyUnion_eq_boundedInterval
      t ht ht_nonneg ha hab with
  | ⟨c, d, hc_left, _hcd, hd_right, hpacket_eq⟩ =>
      have hIco :
          ‖∑ n ∈ Finset.Ico c d,
            Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
            20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) :=
        Complex.logarithmicPhaseRealPhase_Ico_twenty_bound_of_Icc_bounds
          t ht hd_right
          (fun {r : ℕ} hcr hrb => hIcc hc_left hcr hrb)
      exact
        Eq.subst
          (motive := fun S : Finset ℕ =>
            ‖∑ n ∈ S, Complex.exp (Complex.I * (φ n : ℂ))‖ ≤
              20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
          hpacket_eq.symm
          hIco

/-- Stationary packet sums inherit a closed-subinterval twentieth-budget
bound after finite packet-family reconstruction. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryPacketContribution_le_twentyTarget_of_Icc_bounds
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
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hnorm :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum φ a b m‖ =
      ‖∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
          φ a b
          (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b),
        Complex.exp (Complex.I * (φ n : ℂ))‖ :=
    Complex.logarithmicPhaseRealPhase_stationaryPacketFamilyUnion_norm_eq
      t a b
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        left ≤
          20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))))
      hnorm.symm
      (Complex.logarithmicPhaseRealPhase_stationaryPacketFamilyUnion_le_twentyTarget_of_Icc_bounds
        t ht ht_nonneg ha hab hIcc)

/-- A tenth-budget stationary sample-union estimate gives a twentieth-budget
stationary packet contribution estimate. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryPacketContribution_le_twentyTarget_of_familyUnion_ten
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    (hfamily :
      ‖∑ n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b
          (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b),
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t n : ℂ))‖ ≤
        10 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖)))) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      20 * ((((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))) := by
  let E : ℝ :=
    (((b + 1 : ℕ) : ℝ) / ‖t‖ + Real.sqrt (1 + ‖t‖))
  have hpacket :
      ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
        10 * E :=
    Complex.logarithmicPhaseRealPhase_stationaryPacketContribution_le_of_familyUnion
      t hfamily
  have hten_le_twenty : 10 * E ≤ 20 * E := by
    have hconst : (10 : ℝ) ≤ 20 := by
      have hten_nonneg : 0 ≤ (10 : ℝ) :=
        Nat.cast_nonneg 10
      calc
        (10 : ℝ) ≤ 10 + 10 :=
          le_add_of_nonneg_right hten_nonneg
        _ = 20 := by
          have hnat : (10 + 10 : ℕ) = 20 :=
            rfl
          exact Eq.trans
            (Nat.cast_add 10 10).symm
            (Eq.trans
              (congrArg (fun n : ℕ => (n : ℝ)) hnat)
              Nat.cast_ofNat)
    exact mul_le_mul_of_nonneg_right hconst
      (Real.logarithmicPhase_endpoint_sqrt_target_nonneg t ht b)
  exact le_trans hpacket hten_le_twenty

end

end LFunctions
end Boundary
