import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.BProcessEndpointPartition

/-!
# Balanced endpoint packets with centers outside the principal block

When an active stationary center lies in a cutoff collar but outside `[a,b]`,
the whole principal interval is nonstationary.  Exact monotone reciprocal
variation therefore controls the principal packet by twice the reciprocal gap
at the nearest block endpoint.  Adding the two cutoff crossings gives the
complete Fourier-packet estimates below.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Complex.logarithmicPhaseBProcessLeftOutsidePrincipalBudget
    (t : ℝ) (a m : ℤ) : ℝ :=
  Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ) +
    Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ)

def Complex.logarithmicPhaseBProcessRightOutsidePrincipalBudget
    (t : ℝ) (b m : ℤ) : ℝ :=
  Complex.logarithmicPhaseLeftReciprocalGap t m (b : ℝ) +
    Complex.logarithmicPhaseLeftReciprocalGap t m (b : ℝ)

def Complex.logarithmicPhaseBProcessLeftOutsidePacketBudget
    (t : ℝ) (a m : ℤ) : ℝ :=
  4 / 3 + Complex.logarithmicPhaseBProcessLeftOutsidePrincipalBudget t a m

def Complex.logarithmicPhaseBProcessRightOutsidePacketBudget
    (t : ℝ) (b m : ℤ) : ℝ :=
  4 / 3 + Complex.logarithmicPhaseBProcessRightOutsidePrincipalBudget t b m

theorem Complex.logarithmicPhaseBProcessLeftOutsidePrincipalBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) {a m : ℤ}
    (ha : 1 ≤ a) (hm : m < 0)
    (hcenter :
      Complex.logarithmicPhaseFourierStationaryPoint t m < (a : ℝ)) :
    0 ≤ Complex.logarithmicPhaseBProcessLeftOutsidePrincipalBudget t a m := by
  have haPos : 0 < (a : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one ha)
  have hgap :=
    Complex.logarithmicPhaseRightReciprocalGap_eq_coefficientNorm
      t ht m hm haPos hcenter
  have hterm :
      0 ≤ Complex.logarithmicPhaseRightReciprocalGap t m (a : ℝ) :=
    Eq.subst
      (motive := fun value : ℝ => 0 ≤ value)
      hgap.symm (norm_nonneg _)
  exact add_nonneg hterm hterm

theorem Complex.logarithmicPhaseBProcessRightOutsidePrincipalBudget_nonneg
    (t : ℝ) (ht : 1 ≤ ‖t‖) {b m : ℤ}
    (hb : 1 ≤ b) (hm : m < 0)
    (hcenter :
      (b : ℝ) < Complex.logarithmicPhaseFourierStationaryPoint t m) :
    0 ≤ Complex.logarithmicPhaseBProcessRightOutsidePrincipalBudget t b m := by
  have hbPos : 0 < (b : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one hb)
  have hgap :=
    Complex.logarithmicPhaseLeftReciprocalGap_eq_coefficientNorm
      t ht m hm hbPos hcenter
  have hterm :
      0 ≤ Complex.logarithmicPhaseLeftReciprocalGap t m (b : ℝ) :=
    Eq.subst
      (motive := fun value : ℝ => 0 ≤ value)
      hgap.symm (norm_nonneg _)
  exact add_nonneg hterm hterm

theorem Complex.norm_logarithmicPhaseBProcessLeftOutsidePrincipal_le
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) (hm : m < 0)
    (hcenter :
      Complex.logarithmicPhaseFourierStationaryPoint t m < (a : ℝ)) :
    ‖∫ x in (a : ℝ)..(b : ℝ),
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x‖ ≤
      Complex.logarithmicPhaseBProcessLeftOutsidePrincipalBudget t a m := by
  have haPos : 0 < (a : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one ha)
  have habReal : (a : ℝ) ≤ (b : ℝ) := Int.cast_le.mpr hab
  exact
    Complex.norm_intervalIntegral_logarithmicPhase_rightOfStationary_le_twice_reciprocalGap
      t ht ht_nonneg m hm (a : ℝ) (b : ℝ)
      haPos habReal hcenter

theorem Complex.norm_logarithmicPhaseBProcessRightOutsidePrincipal_le
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) (hm : m < 0)
    (hcenter :
      (b : ℝ) < Complex.logarithmicPhaseFourierStationaryPoint t m) :
    ‖∫ x in (a : ℝ)..(b : ℝ),
        Complex.realPhaseOscillation
          (Complex.realPhaseFrequencyTwist
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            m) x‖ ≤
      Complex.logarithmicPhaseBProcessRightOutsidePrincipalBudget t b m := by
  have haPos : 0 < (a : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one ha)
  have habReal : (a : ℝ) ≤ (b : ℝ) := Int.cast_le.mpr hab
  exact
    Complex.norm_intervalIntegral_logarithmicPhase_leftOfStationary_le_twice_reciprocalGap
      t ht ht_nonneg m hm (a : ℝ) (b : ℝ)
      haPos habReal hcenter

theorem Complex.norm_integerBlockFourierPacket_le_BProcessLeftOutsidePacketBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessLeftOutsideModes t a b) :
    ‖Complex.integerBlockFourierPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖ ≤
      Complex.logarithmicPhaseBProcessLeftOutsidePacketBudget t a m := by
  have hclass :=
    (Complex.mem_logarithmicPhasePoissonBProcessLeftOutsideModes_iff
      t a b m).mp hm
  have hmNeg :=
    Complex.logarithmicPhasePoissonBProcessEndpointMode_negative
      t a b hclass.1
  have hprincipal :=
    Complex.norm_logarithmicPhaseBProcessLeftOutsidePrincipal_le
      t ht ht_nonneg a b m ha hab hmNeg hclass.2
  exact
    Complex.norm_integerBlockFourierPacket_le_crossing_add_principal
      t a b m ha hab hprincipal

theorem Complex.norm_integerBlockFourierPacket_le_BProcessRightOutsidePacketBudget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessRightOutsideModes t a b) :
    ‖Complex.integerBlockFourierPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖ ≤
      Complex.logarithmicPhaseBProcessRightOutsidePacketBudget t b m := by
  have hclass :=
    (Complex.mem_logarithmicPhasePoissonBProcessRightOutsideModes_iff
      t a b m).mp hm
  have hmNeg :=
    Complex.logarithmicPhasePoissonBProcessEndpointMode_negative
      t a b hclass.1
  have hprincipal :=
    Complex.norm_logarithmicPhaseBProcessRightOutsidePrincipal_le
      t ht ht_nonneg a b m ha hab hmNeg hclass.2
  exact
    Complex.norm_integerBlockFourierPacket_le_crossing_add_principal
      t a b m ha hab hprincipal

def Complex.logarithmicPhaseBProcessLeftOutsideBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonBProcessLeftOutsideModes t a b,
    Complex.logarithmicPhaseBProcessLeftOutsidePacketBudget t a m

def Complex.logarithmicPhaseBProcessRightOutsideBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonBProcessRightOutsideModes t a b,
    Complex.logarithmicPhaseBProcessRightOutsidePacketBudget t b m

theorem Complex.norm_logarithmicPhaseBProcessLeftOutside_packet_tsum_le_budget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonBProcessLeftOutsideModes t a b},
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      Complex.logarithmicPhaseBProcessLeftOutsideBudget t a b := by
  exact
    Complex.norm_logarithmicPhase_selected_packet_tsum_le_finset_majorant_sum
      t a b
      (Complex.logarithmicPhasePoissonBProcessLeftOutsideModes t a b)
      (Complex.logarithmicPhaseBProcessLeftOutsidePacketBudget t a)
      (fun m hm =>
        Complex.norm_integerBlockFourierPacket_le_BProcessLeftOutsidePacketBudget
          t ht ht_nonneg a b m ha hab hm)

theorem Complex.norm_logarithmicPhaseBProcessRightOutside_packet_tsum_le_budget
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonBProcessRightOutsideModes t a b},
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      Complex.logarithmicPhaseBProcessRightOutsideBudget t a b := by
  exact
    Complex.norm_logarithmicPhase_selected_packet_tsum_le_finset_majorant_sum
      t a b
      (Complex.logarithmicPhasePoissonBProcessRightOutsideModes t a b)
      (Complex.logarithmicPhaseBProcessRightOutsidePacketBudget t b)
      (fun m hm =>
        Complex.norm_integerBlockFourierPacket_le_BProcessRightOutsidePacketBudget
          t ht ht_nonneg a b m ha hab hm)

end

end LFunctions
end Boundary
