import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.BProcessStationaryWindows

/-!
# Balanced logarithmic B-process stationary packets

This file estimates a packet whose balanced stationary window remains inside
the principal block.  Both nonstationary tails use exact monotone reciprocal
variation.  The central interval is bounded by its balanced width.  Together
with the two cutoff crossings this yields the per-mode B-process majorant used
by the refined active-family arithmetic.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

def Complex.logarithmicPhaseBProcessLeftTail
    (t : ℝ) (a b m : ℤ) : ℂ :=
  ∫ x in (a : ℝ)..Complex.logarithmicPhaseBProcessWindowLeft t m,
    Complex.realPhaseOscillation
      (Complex.realPhaseFrequencyTwist
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        m) x

def Complex.logarithmicPhaseBProcessCentralIntegral
    (t : ℝ) (a b m : ℤ) : ℂ :=
  ∫ x in Complex.logarithmicPhaseBProcessWindowLeft t m..
      Complex.logarithmicPhaseBProcessWindowRight t m,
    Complex.realPhaseOscillation
      (Complex.realPhaseFrequencyTwist
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        m) x

def Complex.logarithmicPhaseBProcessRightTail
    (t : ℝ) (a b m : ℤ) : ℂ :=
  ∫ x in Complex.logarithmicPhaseBProcessWindowRight t m..(b : ℝ),
    Complex.realPhaseOscillation
      (Complex.realPhaseFrequencyTwist
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        m) x

def Complex.logarithmicPhaseBProcessLeftTailBudget
    (t : ℝ) (m : ℤ) : ℝ :=
  Complex.logarithmicPhaseLeftReciprocalGap t m
      (Complex.logarithmicPhaseBProcessWindowLeft t m) +
    Complex.logarithmicPhaseLeftReciprocalGap t m
      (Complex.logarithmicPhaseBProcessWindowLeft t m)

def Complex.logarithmicPhaseBProcessRightTailBudget
    (t : ℝ) (m : ℤ) : ℝ :=
  Complex.logarithmicPhaseRightReciprocalGap t m
      (Complex.logarithmicPhaseBProcessWindowRight t m) +
    Complex.logarithmicPhaseRightReciprocalGap t m
      (Complex.logarithmicPhaseBProcessWindowRight t m)

def Complex.logarithmicPhaseBProcessStationaryPacketMajorant
    (t : ℝ) (m : ℤ) : ℝ :=
  4 / 3 +
    Complex.logarithmicPhaseBProcessLeftTailBudget t m +
      Complex.logarithmicPhaseBProcessWindowWidth t m +
        Complex.logarithmicPhaseBProcessRightTailBudget t m

theorem Complex.logarithmicPhaseBProcessWindow_bounds_of_mem
    (t : ℝ) (a b m : ℤ)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b) :
    (a : ℝ) ≤ Complex.logarithmicPhaseBProcessWindowLeft t m ∧
      Complex.logarithmicPhaseBProcessWindowRight t m ≤ (b : ℝ) := by
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonBProcessInteriorModes_iff
      t a b m).mp hm
  exact And.intro hmem.2.2.1 hmem.2.2.2

theorem Complex.logarithmicPhaseBProcessWindowLeft_pos_of_mem
    (t : ℝ) (a b m : ℤ) (ha : 1 ≤ a)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b) :
    0 < Complex.logarithmicPhaseBProcessWindowLeft t m := by
  have hbounds :=
    Complex.logarithmicPhaseBProcessWindow_bounds_of_mem t a b m hm
  have haPos : 0 < (a : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one ha)
  exact lt_of_lt_of_le haPos hbounds.1

theorem Complex.norm_logarithmicPhaseBProcessLeftTail_le
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b) :
    ‖Complex.logarithmicPhaseBProcessLeftTail t a b m‖ ≤
      Complex.logarithmicPhaseBProcessLeftTailBudget t m := by
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonBProcessInteriorModes_iff
      t a b m).mp hm
  have hbounds :=
    Complex.logarithmicPhaseBProcessWindow_bounds_of_mem t a b m hm
  have haPos : 0 < (a : ℝ) :=
    Int.cast_pos.mpr (lt_of_lt_of_le Int.zero_lt_one ha)
  have hcenter :=
    Complex.logarithmicPhaseBProcessWindowLeft_lt_center
      t ht hmem.2.1
  exact
    Complex.norm_intervalIntegral_logarithmicPhase_leftOfStationary_le_twice_reciprocalGap
      t ht ht_nonneg m hmem.2.1
      (a : ℝ) (Complex.logarithmicPhaseBProcessWindowLeft t m)
      haPos hbounds.1 hcenter

theorem Complex.norm_logarithmicPhaseBProcessRightTail_le
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b) :
    ‖Complex.logarithmicPhaseBProcessRightTail t a b m‖ ≤
      Complex.logarithmicPhaseBProcessRightTailBudget t m := by
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonBProcessInteriorModes_iff
      t a b m).mp hm
  have hbounds :=
    Complex.logarithmicPhaseBProcessWindow_bounds_of_mem t a b m hm
  have hleftPos :=
    Complex.logarithmicPhaseBProcessWindowLeft_pos_of_mem
      t a b m ha hm
  have hrightPos :
      0 < Complex.logarithmicPhaseBProcessWindowRight t m :=
    lt_of_lt_of_le hleftPos
      (le_trans
        (Complex.logarithmicPhaseBProcessWindowLeft_lt_center
          t ht hmem.2.1).le
        (Complex.logarithmicPhaseBProcess_center_lt_WindowRight
          t ht hmem.2.1).le)
  have hcenter :=
    Complex.logarithmicPhaseBProcess_center_lt_WindowRight
      t ht hmem.2.1
  exact
    Complex.norm_intervalIntegral_logarithmicPhase_rightOfStationary_le_twice_reciprocalGap
      t ht ht_nonneg m hmem.2.1
      (Complex.logarithmicPhaseBProcessWindowRight t m) (b : ℝ)
      hrightPos hbounds.2 hcenter

theorem Complex.norm_logarithmicPhaseBProcessCentralIntegral_le_width
    (t : ℝ) (ht : 1 ≤ ‖t‖) (a b m : ℤ)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b) :
    ‖Complex.logarithmicPhaseBProcessCentralIntegral t a b m‖ ≤
      Complex.logarithmicPhaseBProcessWindowWidth t m := by
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonBProcessInteriorModes_iff
      t a b m).mp hm
  have hbounds :=
    Complex.logarithmicPhaseBProcessWindow_bounds_of_mem t a b m hm
  have hradiusNonneg :
      0 ≤ Complex.logarithmicPhaseBProcessRadius t m := by
    have hcenterNonneg :
        0 ≤ Complex.logarithmicPhaseFourierStationaryPoint t m :=
      le_of_lt
        (Complex.logarithmicPhaseFourierStationaryPoint_pos
          t ht hmem.2.1)
    exact div_nonneg hcenterNonneg
      (Complex.logarithmicPhaseBProcessScale_pos t).le
  have hcutoff :=
    Complex.norm_intervalIntegral_logarithmicPhase_packet_centralWindow_le_two_radius
      t a b m
      (Complex.logarithmicPhaseFourierStationaryPoint t m)
      (Complex.logarithmicPhaseBProcessRadius t m)
      hbounds.1 hbounds.2 hradiusNonneg
  have heq :=
    Complex.integral_logarithmicPhase_packet_eq_integral_realPhaseOscillation_on_subinterval
      t a b m
      (Complex.logarithmicPhaseBProcessWindowLeft t m)
      (Complex.logarithmicPhaseBProcessWindowRight t m)
      hbounds.1 hbounds.2
      (le_trans
        (Complex.logarithmicPhaseBProcessWindowLeft_lt_center
          t ht hmem.2.1).le
        (Complex.logarithmicPhaseBProcess_center_lt_WindowRight
          t ht hmem.2.1).le)
  exact Eq.subst
    (motive := fun value : ℂ =>
      ‖value‖ ≤ Complex.logarithmicPhaseBProcessWindowWidth t m)
    heq hcutoff

theorem Complex.norm_integerBlockFourierPacket_le_BProcessStationaryMajorant
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b)
    (hm : m ∈ Complex.logarithmicPhasePoissonBProcessInteriorModes t a b) :
    ‖Complex.integerBlockFourierPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖ ≤
      Complex.logarithmicPhaseBProcessStationaryPacketMajorant t m := by
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonBProcessInteriorModes_iff
      t a b m).mp hm
  have hbounds :=
    Complex.logarithmicPhaseBProcessWindow_bounds_of_mem t a b m hm
  have hradiusNonneg :=
    Complex.logarithmicPhaseBProcessRadius_nonneg t ht hmem.2.1
  have hwindowOrder :
      Complex.logarithmicPhaseBProcessWindowLeft t m ≤
        Complex.logarithmicPhaseBProcessWindowRight t m :=
    le_trans
      (Complex.logarithmicPhaseBProcessWindowLeft_lt_center
        t ht hmem.2.1).le
      (Complex.logarithmicPhaseBProcess_center_lt_WindowRight
        t ht hmem.2.1).le
  have hleft :=
    Complex.norm_logarithmicPhaseBProcessLeftTail_le
      t ht ht_nonneg a b m ha hm
  have hright :=
    Complex.norm_logarithmicPhaseBProcessRightTail_le
      t ht ht_nonneg a b m ha hm
  exact
    Complex.norm_integerBlockFourierPacket_le_active_three_piece
      t ht_nonneg a b m ha hab
      (Complex.logarithmicPhaseFourierStationaryPoint t m)
      (Complex.logarithmicPhaseBProcessRadius t m)
      hbounds.1 hwindowOrder hbounds.2
      hleft hright hradiusNonneg

end

end LFunctions
end Boundary
