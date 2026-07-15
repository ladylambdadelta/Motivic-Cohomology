import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.BProcessClippedEndpointPackets

/-!
# Single-counted balanced endpoint budget

The four endpoint classes are not pairwise disjoint: a very short block may
clip both sides of one stationary window.  This owner defines one piecewise
budget directly on the original endpoint family.  Every mode is counted once,
while the class partition selects the appropriate outside or clipped packet
estimate.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseBProcessEndpointPacketBudget
    (t : ℝ) (a b m : ℤ) : ℝ :=
  if Complex.logarithmicPhaseFourierStationaryPoint t m < (a : ℝ) then
    Complex.logarithmicPhaseBProcessLeftOutsidePacketBudget t a m
  else if (b : ℝ) < Complex.logarithmicPhaseFourierStationaryPoint t m then
    Complex.logarithmicPhaseBProcessRightOutsidePacketBudget t b m
  else
    Complex.logarithmicPhaseBProcessClippedPacketBudget t a b m

def Complex.logarithmicPhaseBProcessEndpointBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes t a b,
    Complex.logarithmicPhaseBProcessEndpointPacketBudget t a b m

theorem Complex.logarithmicPhaseBProcessEndpointPacketBudget_eq_leftOutside
    (t : ℝ) (a b m : ℤ)
    (hcenter :
      Complex.logarithmicPhaseFourierStationaryPoint t m < (a : ℝ)) :
    Complex.logarithmicPhaseBProcessEndpointPacketBudget t a b m =
      Complex.logarithmicPhaseBProcessLeftOutsidePacketBudget t a m := by
  unfold Complex.logarithmicPhaseBProcessEndpointPacketBudget
  exact if_pos hcenter

theorem Complex.logarithmicPhaseBProcessEndpointPacketBudget_eq_rightOutside
    (t : ℝ) (a b m : ℤ)
    (hleft :
      ¬ Complex.logarithmicPhaseFourierStationaryPoint t m < (a : ℝ))
    (hcenter :
      (b : ℝ) < Complex.logarithmicPhaseFourierStationaryPoint t m) :
    Complex.logarithmicPhaseBProcessEndpointPacketBudget t a b m =
      Complex.logarithmicPhaseBProcessRightOutsidePacketBudget t b m := by
  unfold Complex.logarithmicPhaseBProcessEndpointPacketBudget
  exact (if_neg hleft).trans (if_pos hcenter)

theorem Complex.logarithmicPhaseBProcessEndpointPacketBudget_eq_clipped
    (t : ℝ) (a b m : ℤ)
    (hleft :
      ¬ Complex.logarithmicPhaseFourierStationaryPoint t m < (a : ℝ))
    (hright :
      ¬ (b : ℝ) < Complex.logarithmicPhaseFourierStationaryPoint t m) :
    Complex.logarithmicPhaseBProcessEndpointPacketBudget t a b m =
      Complex.logarithmicPhaseBProcessClippedPacketBudget t a b m := by
  unfold Complex.logarithmicPhaseBProcessEndpointPacketBudget
  exact (if_neg hleft).trans (if_neg hright)

theorem Complex.logarithmicPhaseBProcessEndpointPacketBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes t a b) :
    0 ≤ Complex.logarithmicPhaseBProcessEndpointPacketBudget t a b m := by
  have hmNeg :=
    Complex.logarithmicPhasePoissonBProcessEndpointMode_negative t a b hm
  match lt_or_ge
      (Complex.logarithmicPhaseFourierStationaryPoint t m) (a : ℝ) with
  | Or.inl hleft =>
      have hprincipal :=
        Complex.logarithmicPhaseBProcessLeftOutsidePrincipalBudget_nonneg
          t ht ha hmNeg hleft
      have hcrossing : 0 ≤ (4 / 3 : ℝ) :=
        div_nonneg zero_le_four zero_le_three
      exact Eq.subst
        (motive := fun value : ℝ => 0 ≤ value)
        (Complex.logarithmicPhaseBProcessEndpointPacketBudget_eq_leftOutside
          t a b m hleft).symm
        (add_nonneg hcrossing hprincipal)
  | Or.inr hleft =>
      match lt_or_ge
          (b : ℝ) (Complex.logarithmicPhaseFourierStationaryPoint t m) with
      | Or.inl hright =>
          have hb : 1 ≤ b := le_trans ha hab
          have hprincipal :=
            Complex.logarithmicPhaseBProcessRightOutsidePrincipalBudget_nonneg
              t ht hb hmNeg hright
          have hcrossing : 0 ≤ (4 / 3 : ℝ) :=
            div_nonneg zero_le_four zero_le_three
          exact Eq.subst
            (motive := fun value : ℝ => 0 ≤ value)
            (Complex.logarithmicPhaseBProcessEndpointPacketBudget_eq_rightOutside
              t a b m (not_lt.mpr hleft) hright).symm
            (add_nonneg hcrossing hprincipal)
      | Or.inr hright =>
          have hradius :=
            Complex.logarithmicPhaseBProcessRadius_nonneg t ht hmNeg
          have hleftTail :
              0 ≤ Complex.logarithmicPhaseBProcessClippedLeftTailBudget t a m := by
            unfold Complex.logarithmicPhaseBProcessClippedLeftTailBudget
            match Classical.em
                ((a : ℝ) ≤ Complex.logarithmicPhaseBProcessWindowLeft t m) with
            | Or.inl hraw =>
                have hleftPos :
                    0 < Complex.logarithmicPhaseBProcessWindowLeft t m :=
                  lt_of_lt_of_le
                    (Int.cast_pos.mpr
                      (lt_of_lt_of_le Int.zero_lt_one ha)) hraw
                have hcenterRaw :=
                  Complex.logarithmicPhaseBProcessWindowLeft_lt_center
                    t ht hmNeg
                have hgap :=
                  Complex.logarithmicPhaseLeftReciprocalGap_eq_coefficientNorm
                    t ht m hmNeg hleftPos hcenterRaw
                have hterm :
                    0 ≤ Complex.logarithmicPhaseLeftReciprocalGap t m
                      (Complex.logarithmicPhaseBProcessWindowLeft t m) :=
                  Eq.subst (motive := fun value : ℝ => 0 ≤ value)
                    hgap.symm (norm_nonneg _)
                have htail :
                    0 ≤ Complex.logarithmicPhaseBProcessLeftTailBudget t m :=
                  add_nonneg hterm hterm
                exact Eq.subst
                  (motive := fun value : ℝ => 0 ≤ value)
                  (if_pos hraw).symm
                  htail
            | Or.inr hraw =>
                exact Eq.subst
                  (motive := fun value : ℝ => 0 ≤ value)
                  (if_neg hraw).symm
                  (le_refl (0 : ℝ))
          have hrightTail :
              0 ≤ Complex.logarithmicPhaseBProcessClippedRightTailBudget t b m := by
            unfold Complex.logarithmicPhaseBProcessClippedRightTailBudget
            match Classical.em
                (Complex.logarithmicPhaseBProcessWindowRight t m ≤ (b : ℝ)) with
            | Or.inl hraw =>
                have hcenterPos :=
                  Complex.logarithmicPhaseFourierStationaryPoint_pos t ht hmNeg
                have hrightPos := lt_of_lt_of_le hcenterPos
                  (Complex.logarithmicPhaseBProcess_center_lt_WindowRight
                    t ht hmNeg).le
                have hcenterRaw :=
                  Complex.logarithmicPhaseBProcess_center_lt_WindowRight
                    t ht hmNeg
                have hgap :=
                  Complex.logarithmicPhaseRightReciprocalGap_eq_coefficientNorm
                    t ht m hmNeg hrightPos hcenterRaw
                have hterm :
                    0 ≤ Complex.logarithmicPhaseRightReciprocalGap t m
                      (Complex.logarithmicPhaseBProcessWindowRight t m) :=
                  Eq.subst (motive := fun value : ℝ => 0 ≤ value)
                    hgap.symm (norm_nonneg _)
                have htail :
                    0 ≤ Complex.logarithmicPhaseBProcessRightTailBudget t m :=
                  add_nonneg hterm hterm
                exact Eq.subst
                  (motive := fun value : ℝ => 0 ≤ value)
                  (if_pos hraw).symm
                  htail
            | Or.inr hraw =>
                exact Eq.subst
                  (motive := fun value : ℝ => 0 ≤ value)
                  (if_neg hraw).symm
                  (le_refl (0 : ℝ))
          have hcrossing : 0 ≤ (4 / 3 : ℝ) :=
            div_nonneg zero_le_four zero_le_three
          have hbudget :=
            add_nonneg
              (add_nonneg (add_nonneg hcrossing hleftTail)
                (mul_nonneg zero_le_two hradius))
              hrightTail
          exact Eq.subst
            (motive := fun value : ℝ => 0 ≤ value)
            (Complex.logarithmicPhaseBProcessEndpointPacketBudget_eq_clipped
              t a b m (not_lt.mpr hleft) (not_lt.mpr hright)).symm
            hbudget

theorem Complex.norm_integerBlockFourierPacket_le_BProcessEndpointPacketBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes t a b) :
    ‖Complex.integerBlockFourierPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖ ≤
      Complex.logarithmicPhaseBProcessEndpointPacketBudget t a b m := by
  have hmNeg :=
    Complex.logarithmicPhasePoissonBProcessEndpointMode_negative t a b hm
  match lt_or_ge
      (Complex.logarithmicPhaseFourierStationaryPoint t m) (a : ℝ) with
  | Or.inl hleft =>
      have hclass :
          m ∈ Complex.logarithmicPhasePoissonBProcessLeftOutsideModes t a b :=
        (Complex.mem_logarithmicPhasePoissonBProcessLeftOutsideModes_iff
          t a b m).mpr (And.intro hm hleft)
      have hpacket :=
        Complex.norm_integerBlockFourierPacket_le_BProcessLeftOutsidePacketBudget
          t ht ht_nonneg a b m ha hab hclass
      exact hpacket.trans_eq
        (Complex.logarithmicPhaseBProcessEndpointPacketBudget_eq_leftOutside
          t a b m hleft).symm
  | Or.inr hleft =>
      match lt_or_ge
          (b : ℝ) (Complex.logarithmicPhaseFourierStationaryPoint t m) with
      | Or.inl hright =>
          have hclass :
              m ∈ Complex.logarithmicPhasePoissonBProcessRightOutsideModes t a b :=
            (Complex.mem_logarithmicPhasePoissonBProcessRightOutsideModes_iff
              t a b m).mpr (And.intro hm hright)
          have hpacket :=
            Complex.norm_integerBlockFourierPacket_le_BProcessRightOutsidePacketBudget
              t ht ht_nonneg a b m ha hab hclass
          exact hpacket.trans_eq
            (Complex.logarithmicPhaseBProcessEndpointPacketBudget_eq_rightOutside
              t a b m (not_lt.mpr hleft) hright).symm
      | Or.inr hright =>
          have hcenter :
              Complex.logarithmicPhaseFourierStationaryPoint t m ∈
                Set.Icc (a : ℝ) (b : ℝ) :=
            And.intro hleft hright
          have hpacket :=
            Complex.norm_integerBlockFourierPacket_le_BProcessClippedPacketBudget
              t ht ht_nonneg a b m ha hab hmNeg hcenter
          exact hpacket.trans_eq
            (Complex.logarithmicPhaseBProcessEndpointPacketBudget_eq_clipped
              t a b m (not_lt.mpr hleft) (not_lt.mpr hright)).symm

theorem Complex.logarithmicPhaseBProcessEndpointBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseBProcessEndpointBudget t a b := by
  unfold Complex.logarithmicPhaseBProcessEndpointBudget
  exact Finset.sum_nonneg (fun m hm =>
    Complex.logarithmicPhaseBProcessEndpointPacketBudget_nonneg
      t ht a b m ha hab hm)

theorem Complex.norm_logarithmicPhaseBProcessEndpoint_packet_tsum_le_budget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonBProcessEndpointModes t a b},
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      Complex.logarithmicPhaseBProcessEndpointBudget t a b := by
  exact
    Complex.norm_logarithmicPhase_selected_packet_tsum_le_finset_majorant_sum
      t a b
      (Complex.logarithmicPhasePoissonBProcessEndpointModes t a b)
      (Complex.logarithmicPhaseBProcessEndpointPacketBudget t a b)
      (fun m hm =>
        Complex.norm_integerBlockFourierPacket_le_BProcessEndpointPacketBudget
          t ht ht_nonneg a b m ha hab hm)

end

end LFunctions
end Boundary
