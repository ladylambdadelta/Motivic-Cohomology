import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseActivePacketBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseEndpointPartition

/-!
# Real-phase right endpoint zero packet

This file owns the elementary fact that right endpoint-tail derivative packets
can only have frequency index zero.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- A right endpoint-tail packet has nonnegative packet index. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets_index_nonneg
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b) :
    0 ≤ m :=
  (Finset.mem_filter.mp hm).2

/-- A right endpoint-tail packet can exist only when the right endpoint
derivative scale is at most a half-window. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightActive_endpointScale_le_half
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b) :
    ‖t‖ / (((b + 1 : ℕ) : ℝ)) ≤ (1 / 2 : ℝ) := by
  have hm_endpoint :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b :=
    Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets_mem_endpoint
      t hm
  have hm_active :
      m ∈
        Complex.realPhase_secondDerivative_vdc_activeDerivPackets
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b :=
    Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets_mem_active
      t hm_endpoint
  have hm_nonneg : 0 ≤ m :=
    Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets_index_nonneg
      t hm
  have hm_cast_nonneg : (0 : ℝ) ≤ (m : ℝ) :=
    Int.cast_nonneg.mpr hm_nonneg
  have hupper :
      (m : ℝ) ≤
        -(‖t‖ / (((b + 1 : ℕ) : ℝ))) + (1 / 2 : ℝ) :=
    Complex.logarithmicPhaseRealPhase_activeDerivPacket_index_upper
      t ht_nonneg ha hm_active
  have hzero_le :
      (0 : ℝ) ≤ -(‖t‖ / (((b + 1 : ℕ) : ℝ))) + (1 / 2 : ℝ) :=
    le_trans hm_cast_nonneg hupper
  let scale : ℝ := ‖t‖ / (((b + 1 : ℕ) : ℝ))
  have hplus :
      scale + 0 ≤ scale + (-scale + (1 / 2 : ℝ)) :=
    add_le_add_left hzero_le scale
  have hcollapse :
      scale + (-scale + (1 / 2 : ℝ)) = (1 / 2 : ℝ) := by
    calc
      scale + (-scale + (1 / 2 : ℝ)) =
          (scale + -scale) + (1 / 2 : ℝ) :=
        (add_assoc scale (-scale) (1 / 2 : ℝ)).symm
      _ = 0 + (1 / 2 : ℝ) := by
        exact congrArg (fun r : ℝ => r + (1 / 2 : ℝ))
          (add_neg_cancel scale)
      _ = (1 / 2 : ℝ) :=
        zero_add (1 / 2 : ℝ)
  exact
    Eq.subst
      (motive := fun right : ℝ => scale ≤ right)
      hcollapse
      (Eq.subst
        (motive := fun left : ℝ =>
          left ≤ scale + (-scale + (1 / 2 : ℝ)))
        (add_zero scale)
        hplus)

/-- A right endpoint-tail packet has packet index zero. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightActive_index_eq_zero
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b) :
    m = 0 := by
  have hm_nonneg : 0 ≤ m :=
    Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets_index_nonneg
      t hm
  let scale : ℝ := ‖t‖ / (((b + 1 : ℕ) : ℝ))
  have hscale_nonneg : 0 ≤ scale := by
    show 0 ≤ ‖t‖ / (((b + 1 : ℕ) : ℝ))
    have hnorm_nonneg : 0 ≤ ‖t‖ :=
      norm_nonneg t
    have hden_nonneg : 0 ≤ (((b + 1 : ℕ) : ℝ)) :=
      Nat.cast_nonneg (b + 1)
    exact div_nonneg hnorm_nonneg hden_nonneg
  have hupper :
      (m : ℝ) ≤ -scale + (1 / 2 : ℝ) :=
    Complex.logarithmicPhaseRealPhase_activeDerivPacket_index_upper
      t ht_nonneg ha
      (Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets_mem_active
        t hm)
  have hupper_half :
      (m : ℝ) ≤ (1 / 2 : ℝ) :=
    le_trans hupper
      (add_le_of_nonpos_left (neg_nonpos.mpr hscale_nonneg))
  have hhalf_lt_one : (1 / 2 : ℝ) < 1 :=
    one_half_lt_one
  have hm_cast_lt_one : (m : ℝ) < 1 :=
    lt_of_le_of_lt hupper_half hhalf_lt_one
  have hm_lt_one : m < 1 :=
    Int.cast_lt.mp
      (show (m : ℝ) < ((1 : ℤ) : ℝ) from
        Eq.subst
          (motive := fun right : ℝ => (m : ℝ) < right)
          Int.cast_one.symm
          hm_cast_lt_one)
  have hm_le_zero : m ≤ 0 :=
    Int.lt_add_one_iff.mp hm_lt_one
  exact le_antisymm hm_le_zero hm_nonneg

/-- The right endpoint-tail packet set is contained in the singleton zero
frequency. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightActive_subset_singleton_zero
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a) :
    Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b ⊆
      ({(0 : ℤ)} : Finset ℤ) := by
  intro m hm
  have hm_zero : m = 0 :=
    Complex.logarithmicPhaseRealPhase_endpointRightActive_index_eq_zero
      t ht_nonneg ha hm
  exact
    Eq.subst
      (motive := fun z : ℤ => z ∈ ({(0 : ℤ)} : Finset ℤ))
      hm_zero.symm
      (Finset.mem_singleton_self (0 : ℤ))

/-- The right endpoint-tail packet sum is controlled by the single zero
derivative-frequency packet. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightPacket_sum_norm_le_zero_packet
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a) :
    ‖∑ m ∈ Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      ‖Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0‖ := by
  let S : Finset ℤ :=
    Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b
  let F : ℤ → ℂ :=
    fun m =>
      Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m
  have hsubset : S ⊆ ({(0 : ℤ)} : Finset ℤ) :=
    Complex.logarithmicPhaseRealPhase_endpointRightActive_subset_singleton_zero
      t ht_nonneg ha
  match Finset.subset_singleton_iff.mp hsubset with
  | Or.inl hS_empty =>
      have hsum :
          (∑ m ∈ S, F m) = 0 :=
        Eq.trans
          (congrArg (fun U : Finset ℤ => ∑ m ∈ U, F m) hS_empty)
          (Finset.sum_empty)
      have hzero_norm : ‖(0 : ℂ)‖ ≤ ‖F 0‖ :=
        Eq.subst
          (motive := fun left : ℝ => left ≤ ‖F 0‖)
          (norm_zero : ‖(0 : ℂ)‖ = 0).symm
          (norm_nonneg (F 0))
      exact
        Eq.subst
          (motive := fun z : ℂ => ‖z‖ ≤ ‖F 0‖)
          hsum.symm
          hzero_norm
  | Or.inr hS_singleton =>
      have hsum :
          (∑ m ∈ S, F m) = F 0 :=
        Eq.trans
          (congrArg (fun U : Finset ℤ => ∑ m ∈ U, F m) hS_singleton)
          (Finset.sum_singleton F 0)
      exact
        Eq.subst
          (motive := fun z : ℂ => ‖z‖ ≤ ‖F 0‖)
          hsum.symm
          (le_refl ‖F 0‖)

end

end LFunctions
end Boundary
