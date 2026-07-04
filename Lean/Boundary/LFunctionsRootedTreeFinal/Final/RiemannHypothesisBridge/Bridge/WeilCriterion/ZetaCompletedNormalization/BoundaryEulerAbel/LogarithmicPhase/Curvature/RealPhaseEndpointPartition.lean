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

end

end LFunctions
end Boundary
