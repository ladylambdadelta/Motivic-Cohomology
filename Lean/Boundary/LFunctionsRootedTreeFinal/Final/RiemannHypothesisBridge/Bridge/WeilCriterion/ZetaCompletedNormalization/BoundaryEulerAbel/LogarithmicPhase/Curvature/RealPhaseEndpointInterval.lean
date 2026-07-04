import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseStationaryInterval

/-!
# Real-phase endpoint packet interval reconstruction

This file owns the finite interval shape of the left and far-right endpoint
packet-family sample unions.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- A finite subset of an integer block that is downward closed is an initial
half-open interval. -/
theorem Finset.exists_eq_Ico_of_subset_Icc_downwardClosed
    {S : Finset ℕ}
    {a b : ℕ}
    (hab : a ≤ b)
    (hS_block : S ⊆ Finset.Icc a b)
    (hdown :
      ∀ n k : ℕ,
        n ∈ S →
        k ∈ Finset.Icc a b →
        k ≤ n →
          k ∈ S) :
    ∃ c : ℕ, a ≤ c ∧ c ≤ b + 1 ∧ S = Finset.Ico a c := by
  match S.eq_empty_or_nonempty with
  | Or.inl hS_empty =>
      have hIco_empty : Finset.Ico a a = (∅ : Finset ℕ) :=
        Finset.eq_empty_iff_forall_not_mem.mpr
          (fun n hn =>
            have hn_bounds : a ≤ n ∧ n < a :=
              Finset.mem_Ico.mp hn
            not_lt_of_ge hn_bounds.1 hn_bounds.2)
      exact Exists.intro a
        (And.intro le_rfl
          (And.intro (Nat.le_trans hab (Nat.le_succ b))
            (Eq.trans hS_empty hIco_empty.symm)))
  | Or.inr hS_nonempty =>
      let m : ℕ := S.max' hS_nonempty
      let c : ℕ := m + 1
      have hm_mem : m ∈ S :=
        Finset.max'_mem S hS_nonempty
      have hm_block : m ∈ Finset.Icc a b :=
        hS_block hm_mem
      have hm_bounds : a ≤ m ∧ m ≤ b :=
        Finset.mem_Icc.mp hm_block
      have hc_left : a ≤ c :=
        Nat.le_trans hm_bounds.1 (Nat.le_succ m)
      have hc_right : c ≤ b + 1 :=
        Nat.succ_le_succ hm_bounds.2
      have hS_eq : S = Finset.Ico a c :=
        Finset.ext
          (fun n =>
            Iff.intro
              (fun hn =>
                have hn_block : n ∈ Finset.Icc a b :=
                  hS_block hn
                have hn_bounds : a ≤ n ∧ n ≤ b :=
                  Finset.mem_Icc.mp hn_block
                have hn_le_m : n ≤ m :=
                  Finset.le_max' S n hn
                have hn_lt_c : n < c :=
                  Nat.lt_succ_of_le hn_le_m
                Finset.mem_Ico.mpr (And.intro hn_bounds.1 hn_lt_c))
              (fun hn_interval =>
                have hn_bounds : a ≤ n ∧ n < c :=
                  Finset.mem_Ico.mp hn_interval
                have hn_le_m : n ≤ m :=
                  Nat.le_of_lt_succ hn_bounds.2
                have hn_block : n ∈ Finset.Icc a b :=
                  Finset.mem_Icc.mpr
                    (And.intro hn_bounds.1
                      (Nat.le_trans hn_le_m hm_bounds.2))
                hdown m n hm_mem hn_block hn_le_m))
      exact Exists.intro c
        (And.intro hc_left (And.intro hc_right hS_eq))

/-- The left endpoint packet-index set is downward closed inside the active
packet indices. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets_index_downwardClosed
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    {m j : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b)
    (hj_active :
      j ∈
        Complex.realPhase_secondDerivative_vdc_activeDerivPackets
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b)
    (hjm : j ≤ m) :
    j ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b := by
  have hm_data :
      m < 0 ∧
        Complex.logarithmicPhaseRealPhase_stationaryPoint t m < (a : ℝ) :=
    (Finset.mem_filter.mp hm).2
  have hm_neg : m < 0 :=
    hm_data.1
  have hsp_m_left :
      Complex.logarithmicPhaseRealPhase_stationaryPoint t m < (a : ℝ) :=
    hm_data.2
  have hj_neg : j < 0 :=
    lt_of_le_of_lt hjm hm_neg
  have hT_nonneg : 0 ≤ ‖t‖ :=
    le_trans zero_le_one ht
  have hm_den_pos : 0 < -(m : ℝ) :=
    Int.neg_cast_pos_of_lt_zero hm_neg
  have hj_den_pos : 0 < -(j : ℝ) :=
    Int.neg_cast_pos_of_lt_zero hj_neg
  have hden_le : -(m : ℝ) ≤ -(j : ℝ) := by
    have hcast : (j : ℝ) ≤ (m : ℝ) :=
      Int.cast_le.mpr hjm
    exact neg_le_neg hcast
  have hrecip :
      (-(j : ℝ))⁻¹ ≤ (-(m : ℝ))⁻¹ :=
    inv_anti₀ hm_den_pos hden_le
  have hscale :
      ‖t‖ / (-(j : ℝ)) ≤ ‖t‖ / (-(m : ℝ)) := by
    have hmul :
        ‖t‖ * (-(j : ℝ))⁻¹ ≤ ‖t‖ * (-(m : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_left hrecip hT_nonneg
    exact
      Eq.subst
        (motive := fun left : ℝ => left ≤ ‖t‖ / (-(m : ℝ)))
        (div_eq_mul_inv ‖t‖ (-(j : ℝ))).symm
        (Eq.subst
          (motive := fun right : ℝ => ‖t‖ * (-(j : ℝ))⁻¹ ≤ right)
          (div_eq_mul_inv ‖t‖ (-(m : ℝ))).symm
          hmul)
  have hsp_j_le_m :
      Complex.logarithmicPhaseRealPhase_stationaryPoint t j ≤
        Complex.logarithmicPhaseRealPhase_stationaryPoint t m := by
    show ‖t‖ / (-(j : ℝ)) ≤ ‖t‖ / (-(m : ℝ))
    exact hscale
  have hsp_j_left :
      Complex.logarithmicPhaseRealPhase_stationaryPoint t j < (a : ℝ) :=
    lt_of_le_of_lt hsp_j_le_m hsp_m_left
  have hj_not_stationary :
      ¬ ((j < 0) ∧
          Complex.logarithmicPhaseRealPhase_stationaryPoint t j ∈
            Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) :=
    fun hstat =>
      have hleft_bound :
          (a : ℝ) ≤ Complex.logarithmicPhaseRealPhase_stationaryPoint t j :=
        hstat.2.1
      not_lt_of_ge hleft_bound hsp_j_left
  have hj_endpoint :
      j ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b :=
    Finset.mem_filter.mpr (And.intro hj_active hj_not_stationary)
  exact Finset.mem_filter.mpr
    (And.intro hj_endpoint (And.intro hj_neg hsp_j_left))

/-- The far-right endpoint packet-index set is interval-convex inside the
active packet indices. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets_index_intervalConvex
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    {m j l : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b)
    (hl :
      l ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b)
    (hj_active :
      j ∈
        Complex.realPhase_secondDerivative_vdc_activeDerivPackets
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b)
    (hmj : m ≤ j)
    (hjl : j ≤ l) :
    j ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b := by
  have hm_data :
      m < 0 ∧
        ((b + 1 : ℕ) : ℝ) <
          Complex.logarithmicPhaseRealPhase_stationaryPoint t m :=
    (Finset.mem_filter.mp hm).2
  have hl_data :
      l < 0 ∧
        ((b + 1 : ℕ) : ℝ) <
          Complex.logarithmicPhaseRealPhase_stationaryPoint t l :=
    (Finset.mem_filter.mp hl).2
  have hm_neg : m < 0 :=
    hm_data.1
  have hl_neg : l < 0 :=
    hl_data.1
  have hsp_m_right :
      ((b + 1 : ℕ) : ℝ) <
        Complex.logarithmicPhaseRealPhase_stationaryPoint t m :=
    hm_data.2
  have hj_neg : j < 0 :=
    lt_of_le_of_lt hjl hl_neg
  have hT_nonneg : 0 ≤ ‖t‖ :=
    le_trans zero_le_one ht
  have hm_den_pos : 0 < -(m : ℝ) :=
    Int.neg_cast_pos_of_lt_zero hm_neg
  have hj_den_pos : 0 < -(j : ℝ) :=
    Int.neg_cast_pos_of_lt_zero hj_neg
  have hden_le : -(j : ℝ) ≤ -(m : ℝ) := by
    have hcast : (m : ℝ) ≤ (j : ℝ) :=
      Int.cast_le.mpr hmj
    exact neg_le_neg hcast
  have hrecip :
      (-(m : ℝ))⁻¹ ≤ (-(j : ℝ))⁻¹ :=
    inv_anti₀ hj_den_pos hden_le
  have hscale :
      ‖t‖ / (-(m : ℝ)) ≤ ‖t‖ / (-(j : ℝ)) := by
    have hmul :
        ‖t‖ * (-(m : ℝ))⁻¹ ≤ ‖t‖ * (-(j : ℝ))⁻¹ :=
      mul_le_mul_of_nonneg_left hrecip hT_nonneg
    exact
      Eq.subst
        (motive := fun left : ℝ => left ≤ ‖t‖ / (-(j : ℝ)))
        (div_eq_mul_inv ‖t‖ (-(m : ℝ))).symm
        (Eq.subst
          (motive := fun right : ℝ => ‖t‖ * (-(m : ℝ))⁻¹ ≤ right)
          (div_eq_mul_inv ‖t‖ (-(j : ℝ))).symm
          hmul)
  have hsp_m_le_j :
      Complex.logarithmicPhaseRealPhase_stationaryPoint t m ≤
        Complex.logarithmicPhaseRealPhase_stationaryPoint t j := by
    show ‖t‖ / (-(m : ℝ)) ≤ ‖t‖ / (-(j : ℝ))
    exact hscale
  have hsp_j_right :
      ((b + 1 : ℕ) : ℝ) <
        Complex.logarithmicPhaseRealPhase_stationaryPoint t j :=
    lt_of_lt_of_le hsp_m_right hsp_m_le_j
  have hj_not_stationary :
      ¬ ((j < 0) ∧
          Complex.logarithmicPhaseRealPhase_stationaryPoint t j ∈
            Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) :=
    fun hstat =>
      have hright_bound :
          Complex.logarithmicPhaseRealPhase_stationaryPoint t j ≤
            ((b + 1 : ℕ) : ℝ) :=
        hstat.2.2
      not_lt_of_ge hright_bound hsp_j_right
  have hj_endpoint :
      j ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b :=
    Finset.mem_filter.mpr (And.intro hj_active hj_not_stationary)
  exact Finset.mem_filter.mpr
    (And.intro hj_endpoint (And.intro hj_neg hsp_j_right))

/-- The left endpoint packet-family union is downward closed in the ambient
block. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftPacketFamilyUnion_downwardClosed
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b n k : ℕ}
    (ha : 1 ≤ a)
    (hn :
      n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b
          (Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b))
    (hk_block : k ∈ Finset.Icc a b)
    (hkn : k ≤ n) :
    k ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hmember :
      ∃ m : ℤ,
        m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b ∧
          n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m :=
    Finset.mem_biUnion.mp hn
  match hmember with
  | ⟨m, hm_left, hn_packet⟩ =>
      have hn_block : n ∈ Finset.Icc a b :=
        Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block φ hn_packet
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
      have hindex_le_raw :
          Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ k ≤
            Complex.realPhase_secondDerivative_vdc_derivPacketIndex φ n :=
        Complex.logarithmicPhaseRealPhase_derivPacketIndex_mono
          t ht_nonneg ha hk_block hn_block hkn
      have hj_le_m : j ≤ m :=
        Eq.subst
          (motive := fun right : ℤ => j ≤ right)
          hn_index
          hindex_le_raw
      have hj_left :
          j ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b :=
        Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets_index_downwardClosed
          t ht hm_left hj_active hj_le_m
      exact Finset.mem_biUnion.mpr
        (Exists.intro j (And.intro hj_left hk_packet))

/-- The far-right endpoint packet-family union is interval-convex in the
ambient block. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightPacketFamilyUnion_intervalConvex
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b n k l : ℕ}
    (ha : 1 ≤ a)
    (hn :
      n ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b
          (Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b))
    (hl :
      l ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b
          (Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b))
    (hk_block : k ∈ Finset.Icc a b)
    (hnk : n ≤ k)
    (hkl : k ≤ l) :
    k ∈ Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hn_member :
      ∃ m : ℤ,
        m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b ∧
          n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b m :=
    Finset.mem_biUnion.mp hn
  have hl_member :
      ∃ r : ℤ,
        r ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b ∧
          l ∈ Complex.realPhase_secondDerivative_vdc_derivPacket φ a b r :=
    Finset.mem_biUnion.mp hl
  match hn_member with
  | ⟨m, hm_far, hn_packet⟩ =>
      match hl_member with
      | ⟨r, hr_far, hl_packet⟩ =>
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
          have hj_far :
              j ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b :=
            Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets_index_intervalConvex
              t ht hm_far hr_far hj_active hm_le_j hj_le_r
          exact Finset.mem_biUnion.mpr
            (Exists.intro j (And.intro hj_far hk_packet))

/-- The left endpoint packet family is a genuine initial endpoint interval. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftPacketFamilyUnion_eq_initialInterval
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    ∃ c : ℕ,
      a ≤ c ∧ c ≤ b + 1 ∧
      Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b
          (Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b) =
        Finset.Ico a c := by
  let S : Finset ℕ :=
    Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b
      (Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b)
  have hS_block : S ⊆ Finset.Icc a b := by
    intro n hn
    have hmember :
        ∃ m : ℤ,
          m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b ∧
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
  have hdown :
      ∀ n k : ℕ,
        n ∈ S →
        k ∈ Finset.Icc a b →
        k ≤ n →
          k ∈ S :=
    fun n k hn hk_block hkn =>
      Complex.logarithmicPhaseRealPhase_endpointLeftPacketFamilyUnion_downwardClosed
        t ht ht_nonneg ha hn hk_block hkn
  exact Finset.exists_eq_Ico_of_subset_Icc_downwardClosed hab hS_block hdown

/-- The far-right endpoint packet family is a genuine bounded interval. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightPacketFamilyUnion_eq_boundedInterval
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
          (Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b) =
        Finset.Ico c d := by
  let S : Finset ℕ :=
    Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b
      (Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b)
  have hS_block : S ⊆ Finset.Icc a b := by
    intro n hn
    have hmember :
        ∃ m : ℤ,
          m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b ∧
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
      Complex.logarithmicPhaseRealPhase_endpointFarRightPacketFamilyUnion_intervalConvex
        t ht ht_nonneg ha hn hl hk_block hnk hkl
  exact Finset.exists_eq_Ico_of_subset_Icc_intervalConvex hab hS_block hconvex

/-- Left endpoint-tail packet indices lie below the left endpoint derivative
frequency. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftActive_index_lt_leftEndpoint
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b) :
    (m : ℝ) < -(‖t‖ / (a : ℝ)) := by
  have hm_data :
      m < 0 ∧
        Complex.logarithmicPhaseRealPhase_stationaryPoint t m < (a : ℝ) :=
    (Finset.mem_filter.mp hm).2
  have hm_neg : m < 0 :=
    hm_data.1
  have hsp_left :
      Complex.logarithmicPhaseRealPhase_stationaryPoint t m < (a : ℝ) :=
    hm_data.2
  have hden_pos : 0 < -(m : ℝ) :=
    Int.neg_cast_pos_of_lt_zero hm_neg
  have ha_pos : 0 < (a : ℝ) :=
    lt_trans
      (Complex.logarithmicPhaseRealPhase_stationaryPoint_pos t ht hm_neg)
      hsp_left
  have hdiv_lt :
      ‖t‖ / (-(m : ℝ)) < (a : ℝ) := by
    exact hsp_left
  have hT_lt :
      ‖t‖ < (a : ℝ) * (-(m : ℝ)) :=
    (div_lt_iff₀ hden_pos).mp hdiv_lt
  have hdiv_left :
      ‖t‖ / (a : ℝ) < -(m : ℝ) :=
    (div_lt_iff₀ ha_pos).mpr
      (Eq.subst
        (motive := fun right : ℝ => ‖t‖ < right)
        (mul_comm (a : ℝ) (-(m : ℝ)))
        hT_lt)
  have hneg :
      - (-(m : ℝ)) < -(‖t‖ / (a : ℝ)) :=
    neg_lt_neg hdiv_left
  exact
    Eq.subst
      (motive := fun left : ℝ => left < -(‖t‖ / (a : ℝ)))
      (neg_neg (m : ℝ))
      hneg

/-- A sample in a left endpoint-tail packet has reciprocal scale still above
the left endpoint scale, up to the packet half-window. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftPacket_sample_scale_lower
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b n : ℕ}
    {m : ℤ}
    (ha : 1 ≤ a)
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b)
    (hn :
      n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m) :
    ‖t‖ / (a : ℝ) - (1 / 2 : ℝ) < ‖t‖ / (n : ℝ) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hn_block : n ∈ Finset.Icc a b :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block φ hn
  have hn_one : 1 ≤ n :=
    le_trans ha (Finset.mem_Icc.mp hn_block).1
  have hn_pos : 0 < n :=
    Nat.lt_of_succ_le hn_one
  have hindex :
      (m : ℝ) < -(‖t‖ / (a : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_endpointLeftActive_index_lt_leftEndpoint
      t ht hm
  have hupper_packet :
      deriv φ n < (m : ℝ) + (1 / 2 : ℝ) :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_upper φ hn
  have hcenter_lt :
      (m : ℝ) + (1 / 2 : ℝ) <
        -(‖t‖ / (a : ℝ)) + (1 / 2 : ℝ) :=
    add_lt_add_right hindex (1 / 2 : ℝ)
  have hderiv_lt :
      deriv φ n < -(‖t‖ / (a : ℝ)) + (1 / 2 : ℝ) :=
    lt_trans hupper_packet hcenter_lt
  have hderiv :
      deriv φ n = -(‖t‖ / (n : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_deriv_eq_neg_norm_div_parenthesized
      t ht_nonneg (Nat.cast_pos.mpr hn_pos)
  have hneg_lt :
      -(‖t‖ / (n : ℝ)) < -(‖t‖ / (a : ℝ)) + (1 / 2 : ℝ) :=
    Eq.subst
      (motive := fun left : ℝ =>
        left < -(‖t‖ / (a : ℝ)) + (1 / 2 : ℝ))
      hderiv
      hderiv_lt
  have hflipped :
      - (-(‖t‖ / (a : ℝ)) + (1 / 2 : ℝ)) < - (-(‖t‖ / (n : ℝ))) :=
    neg_lt_neg hneg_lt
  have hleft :
      - (-(‖t‖ / (a : ℝ)) + (1 / 2 : ℝ)) =
        ‖t‖ / (a : ℝ) - (1 / 2 : ℝ) := by
    calc
      - (-(‖t‖ / (a : ℝ)) + (1 / 2 : ℝ)) =
          - (-(‖t‖ / (a : ℝ))) - (1 / 2 : ℝ) :=
        neg_add (-(‖t‖ / (a : ℝ))) (1 / 2 : ℝ)
      _ = ‖t‖ / (a : ℝ) - (1 / 2 : ℝ) := by
        exact congrArg (fun r : ℝ => r - (1 / 2 : ℝ))
          (neg_neg (‖t‖ / (a : ℝ)))
  have hright :
      - (-(‖t‖ / (n : ℝ))) = ‖t‖ / (n : ℝ) :=
    neg_neg (‖t‖ / (n : ℝ))
  exact
    Eq.subst
      (motive := fun left : ℝ => left < ‖t‖ / (n : ℝ))
      hleft
      (Eq.subst
        (motive := fun right : ℝ =>
          - (-(‖t‖ / (a : ℝ)) + (1 / 2 : ℝ)) < right)
        hright
        hflipped)

/-- The left endpoint packet-family union is contained in the corresponding
left reciprocal-scale cut. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftPacketFamilyUnion_subset_scaleCut
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a) :
    Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b)
      ⊆
      (Finset.Icc a b).filter
        (fun n : ℕ =>
          ‖t‖ / (a : ℝ) - (1 / 2 : ℝ) < ‖t‖ / (n : ℝ)) := by
  intro n hn
  have hmember :
      ∃ m : ℤ,
        m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b ∧
          n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m :=
    Finset.mem_biUnion.mp hn
  match hmember with
  | ⟨m, hm, hn_packet⟩ =>
      have hn_block :
          n ∈ Finset.Icc a b :=
        Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          hn_packet
      have hcut :
          ‖t‖ / (a : ℝ) - (1 / 2 : ℝ) < ‖t‖ / (n : ℝ) :=
        Complex.logarithmicPhaseRealPhase_endpointLeftPacket_sample_scale_lower
          t ht ht_nonneg ha hm hn_packet
      exact Finset.mem_filter.mpr (And.intro hn_block hcut)

/-- Far-right endpoint-tail packet indices lie above the right endpoint
derivative frequency. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightActive_rightEndpoint_lt_index
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b) :
    -(‖t‖ / (((b + 1 : ℕ) : ℝ))) < (m : ℝ) := by
  have hm_data :
      m < 0 ∧
        ((b + 1 : ℕ) : ℝ) <
          Complex.logarithmicPhaseRealPhase_stationaryPoint t m :=
    (Finset.mem_filter.mp hm).2
  have hm_neg : m < 0 :=
    hm_data.1
  have hright_sp :
      ((b + 1 : ℕ) : ℝ) <
        Complex.logarithmicPhaseRealPhase_stationaryPoint t m :=
    hm_data.2
  have hden_pos : 0 < -(m : ℝ) :=
    Int.neg_cast_pos_of_lt_zero hm_neg
  have hB_pos : 0 < (((b + 1 : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr (Nat.succ_pos b)
  have hB_lt :
      ((b + 1 : ℕ) : ℝ) < ‖t‖ / (-(m : ℝ)) := by
    exact hright_sp
  have hprod_lt :
      ((b + 1 : ℕ) : ℝ) * (-(m : ℝ)) < ‖t‖ :=
    (lt_div_iff₀ hden_pos).mp hB_lt
  have hneg_lt :
      -(m : ℝ) < ‖t‖ / (((b + 1 : ℕ) : ℝ)) :=
    (lt_div_iff₀ hB_pos).mpr
      (Eq.subst
        (motive := fun left : ℝ => left < ‖t‖)
        (mul_comm (((b + 1 : ℕ) : ℝ)) (-(m : ℝ)))
        hprod_lt)
  have hneg :
      -(‖t‖ / (((b + 1 : ℕ) : ℝ))) < -(-(m : ℝ)) :=
    neg_lt_neg hneg_lt
  exact
    Eq.subst
      (motive := fun right : ℝ =>
        -(‖t‖ / (((b + 1 : ℕ) : ℝ))) < right)
      (neg_neg (m : ℝ))
      hneg

/-- A sample in a far-right endpoint-tail packet has reciprocal scale below the
right endpoint scale, up to the packet half-window. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightPacket_sample_scale_upper
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b n : ℕ}
    {m : ℤ}
    (ha : 1 ≤ a)
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b)
    (hn :
      n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m) :
    ‖t‖ / (n : ℝ) <
      ‖t‖ / (((b + 1 : ℕ) : ℝ)) + (1 / 2 : ℝ) := by
  let φ : ℝ → ℝ :=
    Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t
  have hn_block : n ∈ Finset.Icc a b :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block φ hn
  have hn_one : 1 ≤ n :=
    le_trans ha (Finset.mem_Icc.mp hn_block).1
  have hn_pos : 0 < n :=
    Nat.lt_of_succ_le hn_one
  have hindex :
      -(‖t‖ / (((b + 1 : ℕ) : ℝ))) < (m : ℝ) :=
    Complex.logarithmicPhaseRealPhase_endpointFarRightActive_rightEndpoint_lt_index
      t hm
  have hlower_packet :
      (m : ℝ) - (1 / 2 : ℝ) ≤ deriv φ n :=
    Complex.realPhase_secondDerivative_vdc_derivPacket_lower φ hn
  have hcenter_lt :
      -(‖t‖ / (((b + 1 : ℕ) : ℝ))) - (1 / 2 : ℝ) <
        (m : ℝ) - (1 / 2 : ℝ) :=
    sub_lt_sub_right hindex (1 / 2 : ℝ)
  have hlt_deriv :
      -(‖t‖ / (((b + 1 : ℕ) : ℝ))) - (1 / 2 : ℝ) < deriv φ n :=
    lt_of_lt_of_le hcenter_lt hlower_packet
  have hderiv :
      deriv φ n = -(‖t‖ / (n : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_deriv_eq_neg_norm_div_parenthesized
      t ht_nonneg (Nat.cast_pos.mpr hn_pos)
  have hlt_neg :
      -(‖t‖ / (((b + 1 : ℕ) : ℝ))) - (1 / 2 : ℝ) <
        -(‖t‖ / (n : ℝ)) :=
    Eq.subst
      (motive := fun right : ℝ =>
        -(‖t‖ / (((b + 1 : ℕ) : ℝ))) - (1 / 2 : ℝ) < right)
      hderiv
      hlt_deriv
  have hflipped :
      - (-(‖t‖ / (n : ℝ))) <
        - (-(‖t‖ / (((b + 1 : ℕ) : ℝ))) - (1 / 2 : ℝ)) :=
    neg_lt_neg hlt_neg
  have hleft :
      - (-(‖t‖ / (n : ℝ))) = ‖t‖ / (n : ℝ) :=
    neg_neg (‖t‖ / (n : ℝ))
  have hright :
      - (-(‖t‖ / (((b + 1 : ℕ) : ℝ))) - (1 / 2 : ℝ)) =
        ‖t‖ / (((b + 1 : ℕ) : ℝ)) + (1 / 2 : ℝ) := by
    calc
      - (-(‖t‖ / (((b + 1 : ℕ) : ℝ))) - (1 / 2 : ℝ)) =
          - (-(‖t‖ / (((b + 1 : ℕ) : ℝ))) + -(1 / 2 : ℝ)) := by
        exact congrArg Neg.neg
          (sub_eq_add_neg (-(‖t‖ / (((b + 1 : ℕ) : ℝ)))) (1 / 2 : ℝ))
      _ =
          - (-(‖t‖ / (((b + 1 : ℕ) : ℝ)))) - (-(1 / 2 : ℝ)) :=
        neg_add (-(‖t‖ / (((b + 1 : ℕ) : ℝ)))) (-(1 / 2 : ℝ))
      _ =
          ‖t‖ / (((b + 1 : ℕ) : ℝ)) - (-(1 / 2 : ℝ)) := by
        exact congrArg (fun r : ℝ => r - (-(1 / 2 : ℝ)))
          (neg_neg (‖t‖ / (((b + 1 : ℕ) : ℝ))))
      _ =
          ‖t‖ / (((b + 1 : ℕ) : ℝ)) + (1 / 2 : ℝ) :=
        sub_neg_eq_add (‖t‖ / (((b + 1 : ℕ) : ℝ))) (1 / 2 : ℝ)
  exact
    Eq.subst
      (motive := fun left : ℝ =>
        left < ‖t‖ / (((b + 1 : ℕ) : ℝ)) + (1 / 2 : ℝ))
      hleft
      (Eq.subst
        (motive := fun right : ℝ =>
          - (-(‖t‖ / (n : ℝ))) < right)
        hright
        hflipped)

/-- The far-right endpoint packet-family union is contained in the
corresponding right reciprocal-scale cut. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightPacketFamilyUnion_subset_scaleCut
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a) :
    Complex.realPhase_secondDerivative_vdc_packetFamilyUnion
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b
        (Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b)
      ⊆
      (Finset.Icc a b).filter
        (fun n : ℕ =>
          ‖t‖ / (n : ℝ) <
            ‖t‖ / (((b + 1 : ℕ) : ℝ)) + (1 / 2 : ℝ)) := by
  intro n hn
  have hmember :
      ∃ m : ℤ,
        m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b ∧
          n ∈ Complex.realPhase_secondDerivative_vdc_derivPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m :=
    Finset.mem_biUnion.mp hn
  match hmember with
  | ⟨m, hm, hn_packet⟩ =>
      have hn_block :
          n ∈ Finset.Icc a b :=
        Complex.realPhase_secondDerivative_vdc_derivPacket_mem_block
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          hn_packet
      have hcut :
          ‖t‖ / (n : ℝ) <
            ‖t‖ / (((b + 1 : ℕ) : ℝ)) + (1 / 2 : ℝ) :=
        Complex.logarithmicPhaseRealPhase_endpointFarRightPacket_sample_scale_upper
          t ht_nonneg ha hm hn_packet
      exact Finset.mem_filter.mpr (And.intro hn_block hcut)

end

end LFunctions
end Boundary
