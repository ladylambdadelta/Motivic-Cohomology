import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhaseActivePacketBounds
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.BoundaryEulerAbel.LogarithmicPhase.Curvature.RealPhasePacketPartition

/-!
# Real-phase logarithmic endpoint-packet partition

This file owns the elementary endpoint-tail classification for active
derivative packets of the real logarithmic phase.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- An endpoint filtered packet is active. -/
theorem Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets_mem_active
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b) :
    m ∈
      Complex.realPhase_secondDerivative_vdc_activeDerivPackets
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b :=
  (Finset.mem_filter.mp hm).1

/-- Endpoint filtered packets are exactly the active packets that fail the
negative-frequency stationary-in-interval condition. -/
theorem Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets_not_stationary
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b) :
    ¬ ((m < 0) ∧
        Complex.logarithmicPhaseRealPhase_stationaryPoint t m ∈
          Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) :=
  (Finset.mem_filter.mp hm).2

/-- If an endpoint packet is not in the negative stationary interval class,
then either its frequency is nonnegative or its explicit stationary point lies
outside the ambient interval. -/
theorem Complex.logarithmicPhaseRealPhase_endpointActive_index_nonneg_or_stationaryPoint_outside
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b) :
    0 ≤ m ∨
      (m < 0 ∧
        Complex.logarithmicPhaseRealPhase_stationaryPoint t m < (a : ℝ)) ∨
        (m < 0 ∧
          ((b + 1 : ℕ) : ℝ) <
            Complex.logarithmicPhaseRealPhase_stationaryPoint t m) := by
  have hnot :
      ¬ ((m < 0) ∧
          Complex.logarithmicPhaseRealPhase_stationaryPoint t m ∈
            Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets_not_stationary
      t hm
  match le_or_gt 0 m with
  | Or.inl hm_nonneg =>
      exact Or.inl hm_nonneg
  | Or.inr hm_neg =>
      have hnot_mem :
          ¬ Complex.logarithmicPhaseRealPhase_stationaryPoint t m ∈
              Set.Icc (a : ℝ) ((b + 1 : ℕ) : ℝ) :=
        fun hmem => hnot (And.intro hm_neg hmem)
      match
        lt_or_ge
          (Complex.logarithmicPhaseRealPhase_stationaryPoint t m)
          (a : ℝ) with
      | Or.inl hleft =>
          exact Or.inr (Or.inl (And.intro hm_neg hleft))
      | Or.inr hleft_ge =>
          have hright_not :
              ¬ Complex.logarithmicPhaseRealPhase_stationaryPoint t m ≤
                  ((b + 1 : ℕ) : ℝ) :=
            fun hright_le =>
              hnot_mem (And.intro hleft_ge hright_le)
          exact Or.inr
            (Or.inr
              (And.intro hm_neg (lt_of_not_ge hright_not)))

/-- The three endpoint-tail classes cover all endpoint active packets. -/
theorem Complex.logarithmicPhaseRealPhase_endpointActive_eq_three_tails
    (t : ℝ)
    (a b : ℕ) :
    Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b =
      Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b ∪
        (Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b ∪
          Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b) := by
  exact Finset.ext
    (fun m =>
      Iff.intro
        (fun hm =>
          match
            Complex.logarithmicPhaseRealPhase_endpointActive_index_nonneg_or_stationaryPoint_outside
              t hm with
          | Or.inl hm_nonneg =>
              Finset.mem_union.mpr
                (Or.inl
                  (Finset.mem_filter.mpr
                    (And.intro hm hm_nonneg)))
          | Or.inr (Or.inl hleft_data) =>
              Finset.mem_union.mpr
                (Or.inr
                  (Finset.mem_union.mpr
                    (Or.inl
                      (Finset.mem_filter.mpr
                        (And.intro hm hleft_data)))))
          | Or.inr (Or.inr hright_data) =>
              Finset.mem_union.mpr
                (Or.inr
                  (Finset.mem_union.mpr
                    (Or.inr
                      (Finset.mem_filter.mpr
                        (And.intro hm hright_data))))))
        (fun hm =>
          match Finset.mem_union.mp hm with
          | Or.inl hright =>
              (Finset.mem_filter.mp hright).1
          | Or.inr hrest =>
              match Finset.mem_union.mp hrest with
              | Or.inl hleft =>
                  (Finset.mem_filter.mp hleft).1
              | Or.inr hfar =>
                  (Finset.mem_filter.mp hfar).1))

/-- The nonnegative-index endpoint tail is disjoint from the negative left
endpoint tail. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRight_left_disjoint
    (t : ℝ)
    (a b : ℕ) :
    Disjoint
      (Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b)
      (Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b) := by
  exact Finset.disjoint_left.mpr
    (fun m hm_right hm_left =>
      have hm_nonneg : 0 ≤ m :=
        (Finset.mem_filter.mp hm_right).2
      have hm_neg : m < 0 :=
        ((Finset.mem_filter.mp hm_left).2).1
      not_lt_of_ge hm_nonneg hm_neg)

/-- The nonnegative-index endpoint tail is disjoint from the negative
far-right endpoint tail. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRight_farRight_disjoint
    (t : ℝ)
    (a b : ℕ) :
    Disjoint
      (Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b)
      (Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b) := by
  exact Finset.disjoint_left.mpr
    (fun m hm_right hm_far =>
      have hm_nonneg : 0 ≤ m :=
        (Finset.mem_filter.mp hm_right).2
      have hm_neg : m < 0 :=
        ((Finset.mem_filter.mp hm_far).2).1
      not_lt_of_ge hm_nonneg hm_neg)

/-- The two negative endpoint tails are disjoint because the left endpoint is
not to the right of `b+1`. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeft_farRight_disjoint
    (t : ℝ)
    {a b : ℕ}
    (hab : a ≤ b) :
    Disjoint
      (Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b)
      (Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b) := by
  exact Finset.disjoint_left.mpr
    (fun m hm_left hm_far =>
      have hleft :
          Complex.logarithmicPhaseRealPhase_stationaryPoint t m < (a : ℝ) :=
        ((Finset.mem_filter.mp hm_left).2).2
      have hfar :
          ((b + 1 : ℕ) : ℝ) <
            Complex.logarithmicPhaseRealPhase_stationaryPoint t m :=
        ((Finset.mem_filter.mp hm_far).2).2
      have ha_le_B : (a : ℝ) ≤ ((b + 1 : ℕ) : ℝ) :=
        Nat.cast_le.mpr (Nat.le_trans hab (Nat.le_succ b))
      have hsp_lt_B :
          Complex.logarithmicPhaseRealPhase_stationaryPoint t m <
            ((b + 1 : ℕ) : ℝ) :=
        lt_of_lt_of_le hleft ha_le_B
      not_lt_of_ge (le_of_lt hsp_lt_B) hfar)

/-- A right endpoint-tail packet is endpoint active. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets_mem_endpoint
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b) :
    m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b :=
  (Finset.mem_filter.mp hm).1

/-- A left endpoint-tail packet is endpoint active. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets_mem_endpoint
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b) :
    m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b :=
  (Finset.mem_filter.mp hm).1

/-- A far-right endpoint-tail packet is endpoint active. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets_mem_endpoint
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b) :
    m ∈ Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets t a b :=
  (Finset.mem_filter.mp hm).1

/-- A right endpoint-tail packet is active. -/
theorem Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets_mem_active
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets t a b) :
    m ∈
      Complex.realPhase_secondDerivative_vdc_activeDerivPackets
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b :=
  Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets_mem_active t
    (Complex.logarithmicPhaseRealPhase_endpointRightActiveDerivPackets_mem_endpoint
      t hm)

/-- A left endpoint-tail packet is active. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets_mem_active
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b) :
    m ∈
      Complex.realPhase_secondDerivative_vdc_activeDerivPackets
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b :=
  Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets_mem_active t
    (Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets_mem_endpoint
      t hm)

/-- A far-right endpoint-tail packet is active. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets_mem_active
    (t : ℝ)
    {a b : ℕ}
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b) :
    m ∈
      Complex.realPhase_secondDerivative_vdc_activeDerivPackets
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b :=
  Complex.logarithmicPhaseRealPhase_endpointActiveDerivPackets_mem_active t
    (Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets_mem_endpoint
      t hm)

/-- A left endpoint-tail packet index lies in the half-window immediately below
the left endpoint derivative scale. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftActive_index_window
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b) :
    -(‖t‖ / (a : ℝ)) - (1 / 2 : ℝ) ≤ (m : ℝ) ∧
      (m : ℝ) < -(‖t‖ / (a : ℝ)) := by
  have hm_active :
      m ∈
        Complex.realPhase_secondDerivative_vdc_activeDerivPackets
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b :=
    Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets_mem_active
      t hm
  have hlower :
      -(‖t‖ / (a : ℝ)) - (1 / 2 : ℝ) ≤ (m : ℝ) :=
    Complex.logarithmicPhaseRealPhase_activeDerivPacket_index_lower
      t ht_nonneg ha hm_active
  have hm_data :
      m < 0 ∧
        Complex.logarithmicPhaseRealPhase_stationaryPoint t m < (a : ℝ) :=
    (Finset.mem_filter.mp hm).2
  have hden_pos : 0 < -(m : ℝ) :=
    Int.neg_cast_pos_of_lt_zero hm_data.1
  have ha_pos : (0 : ℝ) < (a : ℝ) :=
    Nat.cast_pos.mpr (Nat.lt_of_succ_le ha)
  have hmul :
      ‖t‖ < (a : ℝ) * (-(m : ℝ)) :=
    (div_lt_iff₀ hden_pos).mp hm_data.2
  have hmul_commuted :
      ‖t‖ < (-(m : ℝ)) * (a : ℝ) :=
    Eq.subst
      (motive := fun right : ℝ => ‖t‖ < right)
      (mul_comm (a : ℝ) (-(m : ℝ)))
      hmul
  have hdiv :
      ‖t‖ / (a : ℝ) < -(m : ℝ) :=
    (div_lt_iff₀ ha_pos).mpr hmul_commuted
  have hupper_neg :
      -(-(m : ℝ)) < -(‖t‖ / (a : ℝ)) :=
    neg_lt_neg hdiv
  have hupper :
      (m : ℝ) < -(‖t‖ / (a : ℝ)) :=
    Eq.subst
      (motive := fun left : ℝ => left < -(‖t‖ / (a : ℝ)))
      (neg_neg (m : ℝ))
      hupper_neg
  exact And.intro hlower hupper

/-- A far-right endpoint-tail packet index lies in the half-window immediately
above the right endpoint derivative scale. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightActive_index_window
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b) :
    -(‖t‖ / (((b + 1 : ℕ) : ℝ))) < (m : ℝ) ∧
      (m : ℝ) ≤
        -(‖t‖ / (((b + 1 : ℕ) : ℝ))) + (1 / 2 : ℝ) := by
  have hm_active :
      m ∈
        Complex.realPhase_secondDerivative_vdc_activeDerivPackets
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b :=
    Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets_mem_active
      t hm
  have hupper :
      (m : ℝ) ≤
        -(‖t‖ / (((b + 1 : ℕ) : ℝ))) + (1 / 2 : ℝ) :=
    Complex.logarithmicPhaseRealPhase_activeDerivPacket_index_upper
      t ht_nonneg ha hm_active
  have hm_data :
      m < 0 ∧
        ((b + 1 : ℕ) : ℝ) <
          Complex.logarithmicPhaseRealPhase_stationaryPoint t m :=
    (Finset.mem_filter.mp hm).2
  have hden_pos : 0 < -(m : ℝ) :=
    Int.neg_cast_pos_of_lt_zero hm_data.1
  have hb_pos : (0 : ℝ) < (((b + 1 : ℕ) : ℝ)) :=
    Nat.cast_pos.mpr (Nat.succ_pos b)
  have hmul :
      ((b + 1 : ℕ) : ℝ) * (-(m : ℝ)) < ‖t‖ :=
    (lt_div_iff₀ hden_pos).mp hm_data.2
  have hmul_commuted :
      (-(m : ℝ)) * (((b + 1 : ℕ) : ℝ)) < ‖t‖ :=
    Eq.subst
      (motive := fun left : ℝ => left < ‖t‖)
      (mul_comm (((b + 1 : ℕ) : ℝ)) (-(m : ℝ)))
      hmul
  have hdiv :
      -(m : ℝ) < ‖t‖ / (((b + 1 : ℕ) : ℝ)) :=
    (lt_div_iff₀ hb_pos).mpr hmul_commuted
  have hlower_neg :
      -(‖t‖ / (((b + 1 : ℕ) : ℝ))) < -(-(m : ℝ)) :=
    neg_lt_neg hdiv
  have hlower :
      -(‖t‖ / (((b + 1 : ℕ) : ℝ))) < (m : ℝ) :=
    Eq.subst
      (motive := fun right : ℝ =>
        -(‖t‖ / (((b + 1 : ℕ) : ℝ))) < right)
      (neg_neg (m : ℝ))
      hlower_neg
  exact And.intro hlower hupper

/-- Two integers cannot both lie in the same real half-window of length
strictly less than one. -/
theorem Int.eq_of_cast_mem_left_half_window
    {A : ℝ}
    {m n : ℤ}
    (hm_lower : A - (1 / 2 : ℝ) ≤ (m : ℝ))
    (hm_upper : (m : ℝ) < A)
    (hn_lower : A - (1 / 2 : ℝ) ≤ (n : ℝ))
    (hn_upper : (n : ℝ) < A) :
    m = n := by
  have hhalf_lt_one : (1 / 2 : ℝ) < 1 :=
    one_half_lt_one
  have hm_A_lt_succ : A < (m : ℝ) + 1 := by
    have hA_le_m_half : A ≤ (m : ℝ) + (1 / 2 : ℝ) :=
      (sub_le_iff_le_add).mp hm_lower
    have hm_half_lt_succ : (m : ℝ) + (1 / 2 : ℝ) < (m : ℝ) + 1 :=
      add_lt_add_left hhalf_lt_one (m : ℝ)
    exact lt_of_le_of_lt hA_le_m_half hm_half_lt_succ
  have hn_A_lt_succ : A < (n : ℝ) + 1 := by
    have hA_le_n_half : A ≤ (n : ℝ) + (1 / 2 : ℝ) :=
      (sub_le_iff_le_add).mp hn_lower
    have hn_half_lt_succ : (n : ℝ) + (1 / 2 : ℝ) < (n : ℝ) + 1 :=
      add_lt_add_left hhalf_lt_one (n : ℝ)
    exact lt_of_le_of_lt hA_le_n_half hn_half_lt_succ
  have hm_le_n : m ≤ n := by
    exact le_of_not_gt
      (fun hnm : n < m =>
        have hn_succ_le_m : n + 1 ≤ m :=
          Int.add_one_le_iff.mpr hnm
        have hcast_succ :
            (((n + 1 : ℤ) : ℝ)) = (n : ℝ) + 1 :=
          Eq.trans
            (Int.cast_add n 1)
            (congrArg (fun right : ℝ => (n : ℝ) + right) Int.cast_one)
        have hn_succ_le_m_cast :
            (n : ℝ) + 1 ≤ (m : ℝ) :=
          Eq.subst
            (motive := fun left : ℝ => left ≤ (m : ℝ))
            hcast_succ
            (Int.cast_le.mpr hn_succ_le_m)
        have hn_succ_lt_A : (n : ℝ) + 1 < A :=
          lt_of_le_of_lt hn_succ_le_m_cast hm_upper
        not_lt_of_ge (le_of_lt hn_A_lt_succ) hn_succ_lt_A)
  have hn_le_m : n ≤ m := by
    exact le_of_not_gt
      (fun hmn : m < n =>
        have hm_succ_le_n : m + 1 ≤ n :=
          Int.add_one_le_iff.mpr hmn
        have hcast_succ :
            (((m + 1 : ℤ) : ℝ)) = (m : ℝ) + 1 :=
          Eq.trans
            (Int.cast_add m 1)
            (congrArg (fun right : ℝ => (m : ℝ) + right) Int.cast_one)
        have hm_succ_le_n_cast :
            (m : ℝ) + 1 ≤ (n : ℝ) :=
          Eq.subst
            (motive := fun left : ℝ => left ≤ (n : ℝ))
            hcast_succ
            (Int.cast_le.mpr hm_succ_le_n)
        have hm_succ_lt_A : (m : ℝ) + 1 < A :=
          lt_of_le_of_lt hm_succ_le_n_cast hn_upper
        not_lt_of_ge (le_of_lt hm_A_lt_succ) hm_succ_lt_A)
  exact le_antisymm hm_le_n hn_le_m

/-- Two integers cannot both lie in the same right-closed real half-window of
length strictly less than one. -/
theorem Int.eq_of_cast_mem_right_half_window
    {A : ℝ}
    {m n : ℤ}
    (hm_lower : A < (m : ℝ))
    (hm_upper : (m : ℝ) ≤ A + (1 / 2 : ℝ))
    (hn_lower : A < (n : ℝ))
    (hn_upper : (n : ℝ) ≤ A + (1 / 2 : ℝ)) :
    m = n := by
  have hhalf_lt_one : (1 / 2 : ℝ) < 1 :=
    one_half_lt_one
  have hm_half_lt_succ : A + (1 / 2 : ℝ) < (m : ℝ) + 1 := by
    have hhalf_step : A + (1 / 2 : ℝ) < A + 1 :=
      add_lt_add_left hhalf_lt_one A
    have hA_one_le_m_one : A + 1 ≤ (m : ℝ) + 1 :=
      add_le_add_right (le_of_lt hm_lower) 1
    exact lt_of_lt_of_le hhalf_step hA_one_le_m_one
  have hn_half_lt_succ : A + (1 / 2 : ℝ) < (n : ℝ) + 1 := by
    have hhalf_step : A + (1 / 2 : ℝ) < A + 1 :=
      add_lt_add_left hhalf_lt_one A
    have hA_one_le_n_one : A + 1 ≤ (n : ℝ) + 1 :=
      add_le_add_right (le_of_lt hn_lower) 1
    exact lt_of_lt_of_le hhalf_step hA_one_le_n_one
  have hm_le_n : m ≤ n := by
    exact le_of_not_gt
      (fun hnm : n < m =>
        have hn_succ_le_m : n + 1 ≤ m :=
          Int.add_one_le_iff.mpr hnm
        have hcast_succ :
            (((n + 1 : ℤ) : ℝ)) = (n : ℝ) + 1 :=
          Eq.trans
            (Int.cast_add n 1)
            (congrArg (fun right : ℝ => (n : ℝ) + right) Int.cast_one)
        have hn_succ_le_m_cast :
            (n : ℝ) + 1 ≤ (m : ℝ) :=
          Eq.subst
            (motive := fun left : ℝ => left ≤ (m : ℝ))
            hcast_succ
            (Int.cast_le.mpr hn_succ_le_m)
        have hn_succ_le_half : (n : ℝ) + 1 ≤ A + (1 / 2 : ℝ) :=
          le_trans hn_succ_le_m_cast hm_upper
        not_lt_of_ge hn_succ_le_half hn_half_lt_succ)
  have hn_le_m : n ≤ m := by
    exact le_of_not_gt
      (fun hmn : m < n =>
        have hm_succ_le_n : m + 1 ≤ n :=
          Int.add_one_le_iff.mpr hmn
        have hcast_succ :
            (((m + 1 : ℤ) : ℝ)) = (m : ℝ) + 1 :=
          Eq.trans
            (Int.cast_add m 1)
            (congrArg (fun right : ℝ => (m : ℝ) + right) Int.cast_one)
        have hm_succ_le_n_cast :
            (m : ℝ) + 1 ≤ (n : ℝ) :=
          Eq.subst
            (motive := fun left : ℝ => left ≤ (n : ℝ))
            hcast_succ
            (Int.cast_le.mpr hm_succ_le_n)
        have hm_succ_le_half : (m : ℝ) + 1 ≤ A + (1 / 2 : ℝ) :=
          le_trans hm_succ_le_n_cast hn_upper
        not_lt_of_ge hm_succ_le_half hm_half_lt_succ)
  exact le_antisymm hm_le_n hn_le_m

/-- Left endpoint-tail packet indices are unique. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftActive_index_eq_of_mem
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    {m n : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b)
    (hn :
      n ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b) :
    m = n := by
  have hm_window :
      -(‖t‖ / (a : ℝ)) - (1 / 2 : ℝ) ≤ (m : ℝ) ∧
        (m : ℝ) < -(‖t‖ / (a : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_endpointLeftActive_index_window
      t ht_nonneg ha hm
  have hn_window :
      -(‖t‖ / (a : ℝ)) - (1 / 2 : ℝ) ≤ (n : ℝ) ∧
        (n : ℝ) < -(‖t‖ / (a : ℝ)) :=
    Complex.logarithmicPhaseRealPhase_endpointLeftActive_index_window
      t ht_nonneg ha hn
  exact
    Int.eq_of_cast_mem_left_half_window
      hm_window.1 hm_window.2 hn_window.1 hn_window.2

/-- Far-right endpoint-tail packet indices are unique. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightActive_index_eq_of_mem
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    {m n : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b)
    (hn :
      n ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b) :
    m = n := by
  have hm_window :
      -(‖t‖ / (((b + 1 : ℕ) : ℝ))) < (m : ℝ) ∧
        (m : ℝ) ≤
          -(‖t‖ / (((b + 1 : ℕ) : ℝ))) + (1 / 2 : ℝ) :=
    Complex.logarithmicPhaseRealPhase_endpointFarRightActive_index_window
      t ht_nonneg ha hm
  have hn_window :
      -(‖t‖ / (((b + 1 : ℕ) : ℝ))) < (n : ℝ) ∧
        (n : ℝ) ≤
          -(‖t‖ / (((b + 1 : ℕ) : ℝ))) + (1 / 2 : ℝ) :=
    Complex.logarithmicPhaseRealPhase_endpointFarRightActive_index_window
      t ht_nonneg ha hn
  exact
    Int.eq_of_cast_mem_right_half_window
      hm_window.1 hm_window.2 hn_window.1 hn_window.2

/-- A finite set whose members are all equal is either empty or a singleton. -/
theorem Finset.eq_empty_or_exists_eq_singleton_of_mem_eq
    {α : Type*}
    [DecidableEq α]
    (S : Finset α)
    (huniq : ∀ x ∈ S, ∀ y ∈ S, x = y) :
    S = ∅ ∨ ∃ x : α, S = {x} := by
  match S.eq_empty_or_nonempty with
  | Or.inl hS_empty =>
      exact Or.inl hS_empty
  | Or.inr hS_nonempty =>
      match hS_nonempty with
      | ⟨x, hx_mem⟩ =>
          have hS_singleton : S = {x} :=
            Finset.ext
              (fun y =>
                Iff.intro
                  (fun hy =>
                    have hy_eq : y = x :=
                      huniq y hy x hx_mem
                    Eq.subst
                      (motive := fun z : α => z ∈ ({x} : Finset α))
                      hy_eq.symm
                      (Finset.mem_singleton_self x))
                  (fun hy_singleton =>
                    have hy_eq : y = x :=
                      Finset.mem_singleton.mp hy_singleton
                    Eq.subst
                      (motive := fun z : α => z ∈ S)
                      hy_eq.symm
                      hx_mem))
          exact Or.inr (Exists.intro x hS_singleton)

/-- The left endpoint-tail packet set is empty or a singleton. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftActive_eq_empty_or_singleton
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a) :
    Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b = ∅ ∨
      ∃ m : ℤ,
        Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b =
          {m} := by
  exact
    Finset.eq_empty_or_exists_eq_singleton_of_mem_eq
      (Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b)
      (fun m hm n hn =>
        Complex.logarithmicPhaseRealPhase_endpointLeftActive_index_eq_of_mem
          t ht_nonneg ha hm hn)

/-- The far-right endpoint-tail packet set is empty or a singleton. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightActive_eq_empty_or_singleton
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a) :
    Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b = ∅ ∨
      ∃ m : ℤ,
        Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b =
          {m} := by
  exact
    Finset.eq_empty_or_exists_eq_singleton_of_mem_eq
      (Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b)
      (fun m hm n hn =>
        Complex.logarithmicPhaseRealPhase_endpointFarRightActive_index_eq_of_mem
          t ht_nonneg ha hm hn)

/-- The sum over an empty-or-singleton finite set is controlled by one named
entry. -/
theorem Finset.sum_norm_le_of_eq_empty_or_singleton
    {α : Type*}
    [DecidableEq α]
    {S : Finset α}
    {F : α → ℂ}
    {x : α}
    (hS : S = ∅ ∨ S = {x}) :
    ‖∑ y ∈ S, F y‖ ≤ ‖F x‖ := by
  match hS with
  | Or.inl hS_empty =>
      have hsum : (∑ y ∈ S, F y) = 0 :=
        Eq.trans
          (congrArg (fun U : Finset α => ∑ y ∈ U, F y) hS_empty)
          Finset.sum_empty
      have hzero_norm : ‖(0 : ℂ)‖ ≤ ‖F x‖ :=
        Eq.subst
          (motive := fun left : ℝ => left ≤ ‖F x‖)
          (norm_zero : ‖(0 : ℂ)‖ = 0).symm
          (norm_nonneg (F x))
      exact
        Eq.subst
          (motive := fun z : ℂ => ‖z‖ ≤ ‖F x‖)
          hsum.symm
          hzero_norm
  | Or.inr hS_singleton =>
      have hsum : (∑ y ∈ S, F y) = F x :=
        Eq.trans
          (congrArg (fun U : Finset α => ∑ y ∈ U, F y) hS_singleton)
          (Finset.sum_singleton F x)
      exact
        Eq.subst
          (motive := fun z : ℂ => ‖z‖ ≤ ‖F x‖)
          hsum.symm
          (le_refl ‖F x‖)

/-- If the left endpoint-tail packet set is nonempty, its full packet
contribution is controlled by that unique packet. -/
theorem Complex.logarithmicPhaseRealPhase_endpointLeftPacket_sum_norm_le_of_mem
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b) :
    ‖∑ n ∈ Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b n‖ ≤
      ‖Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖ := by
  let S : Finset ℤ :=
    Complex.logarithmicPhaseRealPhase_endpointLeftActiveDerivPackets t a b
  let F : ℤ → ℂ :=
    fun n : ℤ =>
      Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b n
  have hsingle :
      S = ∅ ∨ S = {m} := by
    match
      Complex.logarithmicPhaseRealPhase_endpointLeftActive_eq_empty_or_singleton
        t ht_nonneg (a := a) (b := b) ha with
    | Or.inl hS_empty =>
        exact Or.inl hS_empty
    | Or.inr hS_exists =>
        match hS_exists with
        | ⟨k, hS_singleton_k⟩ =>
            have hk_mem : k ∈ S :=
              Eq.subst
                (motive := fun U : Finset ℤ => k ∈ U)
                hS_singleton_k.symm
                (Finset.mem_singleton_self k)
            have hm_eq_k : m = k :=
              Complex.logarithmicPhaseRealPhase_endpointLeftActive_index_eq_of_mem
                t ht_nonneg ha hm hk_mem
            have hsingleton_m : ({k} : Finset ℤ) = {m} :=
              congrArg (fun z : ℤ => ({z} : Finset ℤ)) hm_eq_k.symm
            exact Or.inr (Eq.trans hS_singleton_k hsingleton_m)
  exact
    Finset.sum_norm_le_of_eq_empty_or_singleton
      (S := S)
      (F := F)
      (x := m)
      hsingle

/-- If the far-right endpoint-tail packet set is nonempty, its full packet
contribution is controlled by that unique packet. -/
theorem Complex.logarithmicPhaseRealPhase_endpointFarRightPacket_sum_norm_le_of_mem
    (t : ℝ)
    (ht_nonneg : 0 ≤ t)
    {a b : ℕ}
    (ha : 1 ≤ a)
    {m : ℤ}
    (hm :
      m ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b) :
    ‖∑ n ∈ Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b,
        Complex.realPhase_secondDerivative_vdc_packetSum
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b n‖ ≤
      ‖Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖ := by
  let S : Finset ℤ :=
    Complex.logarithmicPhaseRealPhase_endpointFarRightActiveDerivPackets t a b
  let F : ℤ → ℂ :=
    fun n : ℤ =>
      Complex.realPhase_secondDerivative_vdc_packetSum
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b n
  have hsingle :
      S = ∅ ∨ S = {m} := by
    match
      Complex.logarithmicPhaseRealPhase_endpointFarRightActive_eq_empty_or_singleton
        t ht_nonneg (a := a) (b := b) ha with
    | Or.inl hS_empty =>
        exact Or.inl hS_empty
    | Or.inr hS_exists =>
        match hS_exists with
        | ⟨k, hS_singleton_k⟩ =>
            have hk_mem : k ∈ S :=
              Eq.subst
                (motive := fun U : Finset ℤ => k ∈ U)
                hS_singleton_k.symm
                (Finset.mem_singleton_self k)
            have hm_eq_k : m = k :=
              Complex.logarithmicPhaseRealPhase_endpointFarRightActive_index_eq_of_mem
                t ht_nonneg ha hm hk_mem
            have hsingleton_m : ({k} : Finset ℤ) = {m} :=
              congrArg (fun z : ℤ => ({z} : Finset ℤ)) hm_eq_k.symm
            exact Or.inr (Eq.trans hS_singleton_k hsingleton_m)
  exact
    Finset.sum_norm_le_of_eq_empty_or_singleton
      (S := S)
      (F := F)
      (x := m)
      hsingle

end

end LFunctions
end Boundary
