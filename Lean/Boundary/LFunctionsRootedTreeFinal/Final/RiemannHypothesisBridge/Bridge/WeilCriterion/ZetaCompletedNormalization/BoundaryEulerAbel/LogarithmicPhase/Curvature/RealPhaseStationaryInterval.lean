import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseDerivPacketIndex
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhasePacketFamily
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhasePacketPartition

/-!
# Real-phase stationary packet interval reconstruction

This file owns the finite interval reconstruction for the stationary packet
sample union.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- A finite subset of an integer block that is interval-convex is a bounded
half-open interval. -/
theorem Finset.exists_eq_Ico_of_subset_Icc_intervalConvex
    {S : Finset ℕ}
    {a b : ℕ}
    (hab : a ≤ b)
    (hS_block : S ⊆ Finset.Icc a b)
    (hconvex :
      ∀ n k l : ℕ,
        n ∈ S →
        l ∈ S →
        k ∈ Finset.Icc a b →
        n ≤ k →
        k ≤ l →
          k ∈ S) :
    ∃ c d : ℕ,
      a ≤ c ∧ c ≤ d ∧ d ≤ b + 1 ∧ S = Finset.Ico c d := by
  match S.eq_empty_or_nonempty with
  | Or.inl hS_empty =>
      have hIco_empty : Finset.Ico a a = (∅ : Finset ℕ) :=
        Finset.eq_empty_iff_forall_not_mem.mpr
          (fun n hn =>
            have hn_bounds : a ≤ n ∧ n < a :=
              Finset.mem_Ico.mp hn
            not_lt_of_ge hn_bounds.1 hn_bounds.2)
      exact Exists.intro a
        (Exists.intro a
          (And.intro le_rfl
            (And.intro le_rfl
              (And.intro
                (Nat.le_trans hab (Nat.le_succ b))
                (Eq.trans hS_empty hIco_empty.symm)))))
  | Or.inr hS_nonempty =>
      let c : ℕ := S.min' hS_nonempty
      let r : ℕ := S.max' hS_nonempty
      let d : ℕ := r + 1
      have hc_mem : c ∈ S :=
        Finset.min'_mem S hS_nonempty
      have hr_mem : r ∈ S :=
        Finset.max'_mem S hS_nonempty
      have hc_block : c ∈ Finset.Icc a b :=
        hS_block hc_mem
      have hr_block : r ∈ Finset.Icc a b :=
        hS_block hr_mem
      have hc_bounds : a ≤ c ∧ c ≤ b :=
        Finset.mem_Icc.mp hc_block
      have hr_bounds : a ≤ r ∧ r ≤ b :=
        Finset.mem_Icc.mp hr_block
      have hc_le_r : c ≤ r :=
        Finset.min'_le S r hr_mem
      have hc_le_d : c ≤ d :=
        Nat.le_trans hc_le_r (Nat.le_succ r)
      have hd_right : d ≤ b + 1 :=
        Nat.succ_le_succ hr_bounds.2
      have hS_eq : S = Finset.Ico c d :=
        Finset.ext
          (fun n =>
            Iff.intro
              (fun hn =>
                have hc_le_n : c ≤ n :=
                  Finset.min'_le S n hn
                have hn_le_r : n ≤ r :=
                  Finset.le_max' S n hn
                have hn_lt_d : n < d :=
                  Nat.lt_succ_of_le hn_le_r
                Finset.mem_Ico.mpr (And.intro hc_le_n hn_lt_d))
              (fun hn_interval =>
                have hn_bounds : c ≤ n ∧ n < d :=
                  Finset.mem_Ico.mp hn_interval
                have hn_le_r : n ≤ r :=
                  Nat.le_of_lt_succ hn_bounds.2
                have hn_block : n ∈ Finset.Icc a b :=
                  Finset.mem_Icc.mpr
                    (And.intro
                      (Nat.le_trans hc_bounds.1 hn_bounds.1)
                      (Nat.le_trans hn_le_r hr_bounds.2))
                hconvex c n r hc_mem hr_mem hn_block hn_bounds.1 hn_le_r))
      exact Exists.intro c
        (Exists.intro d
          (And.intro hc_bounds.1
            (And.intro hc_le_d
              (And.intro hd_right hS_eq))))

/-- The stationary packet-index set is interval-convex inside the active
packet indices. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_index_intervalConvex
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    {m j l : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b)
    (hl :
      l ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b)
    (hj_active :
      j ∈
        Complex.realPhase_secondDerivative_vdc_activeDerivPackets
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b)
    (hmj : m ≤ j)
    (hjl : j ≤ l) :
    j ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b := by
  have hm_neg :
      m < 0 :=
    Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_index_neg
      t hm
  have hl_neg :
      l < 0 :=
    Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_index_neg
      t hl
  have hpoint_m :
      Complex.logarithmicPhaseRealPhase_stationaryPoint t m ∈
        Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
    Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_point_mem_Icc
      t hm
  have hpoint_l :
      Complex.logarithmicPhaseRealPhase_stationaryPoint t l ∈
        Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
    Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_point_mem_Icc
      t hl
  have hj_neg : j < 0 :=
    lt_of_le_of_lt hjl hl_neg
  have hT_nonneg : 0 ≤ ‖t‖ :=
    le_trans zero_le_one ht
  have hm_den_pos : 0 < -(m : ℝ) :=
    Int.neg_cast_pos_of_lt_zero hm_neg
  have hj_den_pos : 0 < -(j : ℝ) :=
    Int.neg_cast_pos_of_lt_zero hj_neg
  have hl_den_pos : 0 < -(l : ℝ) :=
    Int.neg_cast_pos_of_lt_zero hl_neg
  have hm_to_j_den : -(j : ℝ) ≤ -(m : ℝ) := by
    have hcast : (m : ℝ) ≤ (j : ℝ) :=
      Int.cast_le.mpr hmj
    exact neg_le_neg hcast
  have hj_to_l_den : -(l : ℝ) ≤ -(j : ℝ) := by
    have hcast : (j : ℝ) ≤ (l : ℝ) :=
      Int.cast_le.mpr hjl
    exact neg_le_neg hcast
  have hrecip_mj :
      (-(m : ℝ))⁻¹ ≤ (-(j : ℝ))⁻¹ :=
    inv_anti₀ hj_den_pos hm_to_j_den
  have hrecip_jl :
      (-(j : ℝ))⁻¹ ≤ (-(l : ℝ))⁻¹ :=
    inv_anti₀ hl_den_pos hj_to_l_den
  have hscale_mj :
      ‖t‖ / (-(m : ℝ)) ≤ ‖t‖ / (-(j : ℝ)) := by
    have hmul :
        ‖t‖ * (-(m : ℝ))⁻¹ ≤ ‖t‖ * (-(j : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_left hrecip_mj hT_nonneg
    exact
      Eq.subst
        (motive := fun left : ℝ => left ≤ ‖t‖ / (-(j : ℝ)))
        (div_eq_mul_inv ‖t‖ (-(m : ℝ))).symm
        (Eq.subst
          (motive := fun right : ℝ => ‖t‖ * (-(m : ℝ))⁻¹ ≤ right)
          (div_eq_mul_inv ‖t‖ (-(j : ℝ))).symm
          hmul)
  have hscale_jl :
      ‖t‖ / (-(j : ℝ)) ≤ ‖t‖ / (-(l : ℝ)) := by
    have hmul :
        ‖t‖ * (-(j : ℝ))⁻¹ ≤ ‖t‖ * (-(l : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_left hrecip_jl hT_nonneg
    exact
      Eq.subst
        (motive := fun left : ℝ => left ≤ ‖t‖ / (-(l : ℝ)))
        (div_eq_mul_inv ‖t‖ (-(j : ℝ))).symm
        (Eq.subst
          (motive := fun right : ℝ => ‖t‖ * (-(j : ℝ))⁻¹ ≤ right)
          (div_eq_mul_inv ‖t‖ (-(l : ℝ))).symm
          hmul)
  have hpoint_mj :
      Complex.logarithmicPhaseRealPhase_stationaryPoint t m ≤
        Complex.logarithmicPhaseRealPhase_stationaryPoint t j := by
    show ‖t‖ / (-(m : ℝ)) ≤ ‖t‖ / (-(j : ℝ))
    exact hscale_mj
  have hpoint_jl :
      Complex.logarithmicPhaseRealPhase_stationaryPoint t j ≤
        Complex.logarithmicPhaseRealPhase_stationaryPoint t l := by
    show ‖t‖ / (-(j : ℝ)) ≤ ‖t‖ / (-(l : ℝ))
    exact hscale_jl
  have hpoint_j :
      Complex.logarithmicPhaseRealPhase_stationaryPoint t j ∈
        Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
    And.intro
      (le_trans hpoint_m.1 hpoint_mj)
      (le_trans hpoint_jl hpoint_l.2)
  exact Finset.mem_filter.mpr
    (And.intro hj_active (And.intro hj_neg hpoint_j))

/-- The stationary packet-family sample union is interval-convex in the
ambient block. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryPacketFamilyUnion_intervalConvex
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b n k l : ℕ}
    (ha : 1 ≤ a)
    (hn :
      n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b
          (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b))
    (hl :
      l ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b
          (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b))
    (hk_block : k ∈ Finset.Icc a b)
    (hnk : n ≤ k)
    (hkl : k ≤ l) :
    k ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hn_member :
      ∃ m : ℤ,
        m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b ∧
          n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m :=
    Finset.mem_biUnion.mp hn
  have hl_member :
      ∃ r : ℤ,
        r ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b ∧
          l ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b r :=
    Finset.mem_biUnion.mp hl
  match hn_member with
  | ⟨m, hm_stat, hn_packet⟩ =>
      match hl_member with
      | ⟨r, hr_stat, hl_packet⟩ =>
          have hn_block : n ∈ Finset.Icc a b :=
            Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block φ hn_packet
          have hl_block : l ∈ Finset.Icc a b :=
            Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block φ hl_packet
          let j : ℤ := Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ k
          have hj_active :
              j ∈ Complex.realPhase_secondDerivative_vdc_activeDerivPackets φ a b :=
            Complex.realPhase_secondDerivative_vdc_derivPacketIndex_mem_active φ hk_block
          have hk_packet :
              k ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b j :=
            Complex.realPhase_secondDerivative_vdc_mem_own_derivPacket φ hk_block
          have hn_index :
              Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n = m :=
            have hn_pair :
                n ∈ Finset.Icc a b ∧
                  Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n = m :=
              (Complex.mem_realPhase_secondDerivative_vdc_derivPacket_iff_index_eq φ).mp
                hn_packet
            hn_pair.2
          have hl_index :
              Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ l = r :=
            have hl_pair :
                l ∈ Finset.Icc a b ∧
                  Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ l = r :=
              (Complex.mem_realPhase_secondDerivative_vdc_derivPacket_iff_index_eq φ).mp
                hl_packet
            hl_pair.2
          have hm_le_j_raw :
              Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n ≤
                Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ k :=
            Complex.logarithmicPhaseRealPhase_derivPacketIndex_mono
              t ht_nonneg ha hn_block hk_block hnk
          have hj_le_r_raw :
              Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ k ≤
                Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ l :=
            Complex.logarithmicPhaseRealPhase_derivPacketIndex_mono
              t ht_nonneg ha hk_block hl_block hkl
          have hm_le_j : m ≤ j :=
            Eq.subst
              (motive := fun left : ℤ => left ≤ j)
              hn_index
              hm_le_j_raw
          have hj_le_r : j ≤ r :=
            Eq.subst
              (motive := fun right : ℤ => j ≤ right)
              hl_index
              hj_le_r_raw
          have hj_stat :
              j ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b :=
            Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets_index_intervalConvex
              t ht hm_stat hr_stat hj_active hm_le_j hj_le_r
          exact Finset.mem_biUnion.mpr
            (Exists.intro j (And.intro hj_stat hk_packet))

/-- The stationary packet-family sample union is a bounded natural interval
inside the ambient block. -/
theorem Complex.logarithmicPhaseRealPhase_stationaryPacketFamilyUnion_eq_boundedInterval
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    ∃ c d : ℕ,
      a ≤ c ∧ c ≤ d ∧ d ≤ b + 1 ∧
        Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b
          (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b) =
          Finset.Ico c d := by
  let S : Finset ℕ :=
    Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b
      (Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b)
  have hS_block : S ⊆ Finset.Icc a b := by
    intro n hn
    have hmember :
        ∃ m : ℤ,
          m ∈ Complex.logarithmicPhaseRealPhase_stationaryActiveDerivPackets t a b ∧
            n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              a b m :=
      Finset.mem_biUnion.mp hn
    match hmember with
    | ⟨m, hm, hn_packet⟩ =>
        exact
          Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            hn_packet
  have hconvex :
      ∀ n k l : ℕ,
        n ∈ S →
        l ∈ S →
        k ∈ Finset.Icc a b →
        n ≤ k →
        k ≤ l →
          k ∈ S :=
    fun n k l hn hl hk_block hnk hkl =>
      Complex.logarithmicPhaseRealPhase_stationaryPacketFamilyUnion_intervalConvex
        t ht ht_nonneg ha hn hl hk_block hnk hkl
  exact Finset.exists_eq_Ico_of_subset_Icc_intervalConvex hab hS_block hconvex

end

end LFunctions
end Boundary
