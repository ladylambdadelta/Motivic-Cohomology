import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.DirectTails
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.ModeRangeCore

/-!
# Finite inactive logarithmic Poisson geometry

The finite complement of the active stationary family is not a homogeneous
object.  It consists of modes whose stationary centers lie strictly to the
left or right of the principal block, together with the zero mode and the two
cutoff-transition strips.  This file makes that partition exact.  The left
and right families carry the first-derivative estimates; the transition family
is deliberately retained as a finite owner object for a separate local bound.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

def Complex.logarithmicPhasePoissonLeftInactiveModes
    (t : ℝ) (a b : ℤ) : Finset ℤ :=
  (Complex.logarithmicPhasePoissonInRangeInactiveModes t a b).filter
    (fun m : ℤ =>
      m < 0 ∧
        Complex.logarithmicPhaseFourierStationaryPoint t m < (a : ℝ))

def Complex.logarithmicPhasePoissonRightInactiveModes
    (t : ℝ) (a b : ℤ) : Finset ℤ :=
  (Complex.logarithmicPhasePoissonInRangeInactiveModes t a b).filter
    (fun m : ℤ =>
      m < 0 ∧
        (b : ℝ) < Complex.logarithmicPhaseFourierStationaryPoint t m)

def Complex.logarithmicPhasePoissonTransitionModes
    (t : ℝ) (a b : ℤ) : Finset ℤ :=
  Complex.logarithmicPhasePoissonInRangeInactiveModes t a b \
    (Complex.logarithmicPhasePoissonLeftInactiveModes t a b ∪
      Complex.logarithmicPhasePoissonRightInactiveModes t a b)

def Complex.logarithmicPhasePoissonTransitionBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonTransitionModes t a b,
    ‖Complex.integerBlockFourierPacket
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m‖

def Complex.logarithmicPhasePoissonLeftInactiveBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b,
    ‖Complex.integerBlockFourierPacket
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m‖

def Complex.logarithmicPhasePoissonRightInactiveBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b,
    ‖Complex.integerBlockFourierPacket
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m‖

theorem Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
    (t : ℝ) (a b m : ℤ) :
    m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b ↔
      m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b ∧
        m < 0 ∧
          Complex.logarithmicPhaseFourierStationaryPoint t m < (a : ℝ) := by
  unfold Complex.logarithmicPhasePoissonLeftInactiveModes
  exact Finset.mem_filter

theorem Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff
    (t : ℝ) (a b m : ℤ) :
    m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b ↔
      m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b ∧
        m < 0 ∧
          (b : ℝ) < Complex.logarithmicPhaseFourierStationaryPoint t m := by
  unfold Complex.logarithmicPhasePoissonRightInactiveModes
  exact Finset.mem_filter

theorem Complex.logarithmicPhasePoissonLeftInactiveModes_subset_inRangeInactive
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhasePoissonLeftInactiveModes t a b ⊆
      Complex.logarithmicPhasePoissonInRangeInactiveModes t a b := by
  intro m hm
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff t a b m).mp hm
  exact hmem.1

theorem Complex.logarithmicPhasePoissonRightInactiveModes_subset_inRangeInactive
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhasePoissonRightInactiveModes t a b ⊆
      Complex.logarithmicPhasePoissonInRangeInactiveModes t a b := by
  intro m hm
  have hmem :=
    (Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff t a b m).mp hm
  exact hmem.1

theorem Complex.logarithmicPhasePoissonLeftRightInactive_disjoint
    (t : ℝ) (a b : ℤ) (hab : a ≤ b) :
    Disjoint
      (Complex.logarithmicPhasePoissonLeftInactiveModes t a b)
      (Complex.logarithmicPhasePoissonRightInactiveModes t a b) := by
  exact
    Finset.disjoint_left.mpr
      (fun m hmleft hmright =>
        have hleft :=
          (Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
            t a b m).mp hmleft
        have hright :=
          (Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff
            t a b m).mp hmright
        have hab_real : (a : ℝ) ≤ (b : ℝ) :=
          Int.cast_le.mpr hab
        have hcenter_lt_center :
            Complex.logarithmicPhaseFourierStationaryPoint t m <
              Complex.logarithmicPhaseFourierStationaryPoint t m :=
          lt_of_lt_of_le hleft.2.2
            (le_trans hab_real (le_of_lt hright.2.2))
        lt_irrefl _ hcenter_lt_center)

theorem Complex.logarithmicPhasePoissonLeftRightInactive_subset_inRangeInactive
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhasePoissonLeftInactiveModes t a b ∪
        Complex.logarithmicPhasePoissonRightInactiveModes t a b ⊆
      Complex.logarithmicPhasePoissonInRangeInactiveModes t a b := by
  intro m hm
  match Finset.mem_union.mp hm with
  | Or.inl hmleft =>
      exact
        Complex.logarithmicPhasePoissonLeftInactiveModes_subset_inRangeInactive
          t a b hmleft
  | Or.inr hmright =>
      exact
        Complex.logarithmicPhasePoissonRightInactiveModes_subset_inRangeInactive
          t a b hmright

theorem Complex.logarithmicPhasePoissonLeftRightTransition_union_eq_inRangeInactive
    (t : ℝ) (a b : ℤ) :
    (Complex.logarithmicPhasePoissonLeftInactiveModes t a b ∪
        Complex.logarithmicPhasePoissonRightInactiveModes t a b) ∪
      Complex.logarithmicPhasePoissonTransitionModes t a b =
        Complex.logarithmicPhasePoissonInRangeInactiveModes t a b := by
  unfold Complex.logarithmicPhasePoissonTransitionModes
  exact
    (Finset.union_comm _ _).trans
      (Finset.sdiff_union_of_subset
        (Complex.logarithmicPhasePoissonLeftRightInactive_subset_inRangeInactive
          t a b))

theorem Complex.logarithmicPhasePoissonLeftRightInactive_disjoint_transition
    (t : ℝ) (a b : ℤ) :
    Disjoint
      (Complex.logarithmicPhasePoissonLeftInactiveModes t a b ∪
        Complex.logarithmicPhasePoissonRightInactiveModes t a b)
      (Complex.logarithmicPhasePoissonTransitionModes t a b) := by
  unfold Complex.logarithmicPhasePoissonTransitionModes
  exact Finset.disjoint_sdiff

theorem Complex.logarithmicPhasePoissonTransitionModes_subset_inRangeInactive
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhasePoissonTransitionModes t a b ⊆
      Complex.logarithmicPhasePoissonInRangeInactiveModes t a b := by
  unfold Complex.logarithmicPhasePoissonTransitionModes
  exact Finset.sdiff_subset

/-- There are no negative transition modes.  A negative mode in the finite
range whose center is not strictly left or right of the principal block has
its center in that block, hence is active.  Thus the residual finite family
contains only the zero frequency. -/
theorem Complex.logarithmicPhasePoissonTransitionModes_subset_singleton_zero
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhasePoissonTransitionModes t a b ⊆ {0} := by
  intro m hm
  have htransition := Finset.mem_sdiff.mp hm
  have hinactive := htransition.1
  have hnot_left_right := htransition.2
  have hinactive_data := Finset.mem_sdiff.mp hinactive
  have hm_range := hinactive_data.1
  have hm_nonpos : m ≤ 0 :=
    ((Complex.mem_logarithmicPhasePoissonModeRange_iff t a m).mp hm_range).2
  have hnot_left : m ∉ Complex.logarithmicPhasePoissonLeftInactiveModes t a b :=
    fun hmleft => hnot_left_right (Finset.mem_union_left _ hmleft)
  have hnot_right : m ∉ Complex.logarithmicPhasePoissonRightInactiveModes t a b :=
    fun hmright => hnot_left_right (Finset.mem_union_right _ hmright)
  have hm_not_neg : ¬ m < 0 := by
    intro hm_neg
    have hcenter_not_left : ¬
        Complex.logarithmicPhaseFourierStationaryPoint t m < (a : ℝ) := by
      intro hcenter_left
      have hleft_mem :
          m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b :=
        (Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff t a b m).mpr
          (And.intro hinactive (And.intro hm_neg hcenter_left))
      exact hnot_left hleft_mem
    have hcenter_not_right : ¬
        (b : ℝ) < Complex.logarithmicPhaseFourierStationaryPoint t m := by
      intro hcenter_right
      have hright_mem :
          m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b :=
        (Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff t a b m).mpr
          (And.intro hinactive (And.intro hm_neg hcenter_right))
      exact hnot_right hright_mem
    have hcenter_left : (a : ℝ) ≤
        Complex.logarithmicPhaseFourierStationaryPoint t m :=
      le_of_not_gt hcenter_not_left
    have hcenter_right : Complex.logarithmicPhaseFourierStationaryPoint t m ≤
        (b : ℝ) :=
      le_of_not_gt hcenter_not_right
    have hmargin_nonneg : (0 : ℝ) ≤ 2 / 3 :=
      div_nonneg (Nat.cast_nonneg 2) (Nat.cast_nonneg 3)
    have hactive_center :
        Complex.logarithmicPhaseFourierStationaryPoint t m ∈
          Set.Icc
            (Real.integerBlockCutoffSupportLeftEndpoint a)
            ((b : ℝ) + 2 / 3) := by
      unfold Real.integerBlockCutoffSupportLeftEndpoint
      exact
        And.intro
          (le_trans (sub_le_self (a : ℝ) hmargin_nonneg) hcenter_left)
          (le_trans hcenter_right (le_add_of_nonneg_right hmargin_nonneg))
    have hactive :
        m ∈ Complex.logarithmicPhasePoissonActiveModes t a b :=
      (Complex.mem_logarithmicPhasePoissonActiveModes_iff t a b m).mpr
        (And.intro hm_range (And.intro hm_neg hactive_center))
    exact hinactive_data.2 hactive
  have hm_nonneg : 0 ≤ m :=
    le_of_not_gt hm_not_neg
  have hm_zero : m = 0 :=
    le_antisymm hm_nonpos hm_nonneg
  exact Finset.mem_singleton.mpr hm_zero

theorem Complex.zero_mem_logarithmicPhasePoissonTransitionModes
    (t : ℝ) {a b : ℤ} (ha : 1 ≤ a) :
    0 ∈ Complex.logarithmicPhasePoissonTransitionModes t a b := by
  have hzero_range : 0 ∈ Complex.logarithmicPhasePoissonModeRange t a :=
    Complex.zero_mem_logarithmicPhasePoissonModeRange_of_lower_le_zero t a
      (Complex.logarithmicPhasePoissonModeRangeLower_le_zero t ha)
  have hzero_not_active : 0 ∉ Complex.logarithmicPhasePoissonActiveModes t a b := by
    intro hzero_active
    have hactive_data :=
      (Complex.mem_logarithmicPhasePoissonActiveModes_iff t a b 0).mp
        hzero_active
    exact lt_irrefl 0 hactive_data.2.1
  have hzero_inactive :
      0 ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b :=
    Finset.mem_sdiff.mpr (And.intro hzero_range hzero_not_active)
  have hzero_not_left : 0 ∉ Complex.logarithmicPhasePoissonLeftInactiveModes t a b := by
    intro hzero_left
    have hleft_data :=
      (Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff t a b 0).mp
        hzero_left
    exact lt_irrefl 0 hleft_data.2.1
  have hzero_not_right : 0 ∉ Complex.logarithmicPhasePoissonRightInactiveModes t a b := by
    intro hzero_right
    have hright_data :=
      (Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff t a b 0).mp
        hzero_right
    exact lt_irrefl 0 hright_data.2.1
  exact
    Finset.mem_sdiff.mpr
      (And.intro hzero_inactive
        (fun hzero_left_right =>
          match Finset.mem_union.mp hzero_left_right with
          | Or.inl hzero_left => hzero_not_left hzero_left
          | Or.inr hzero_right => hzero_not_right hzero_right))

theorem Complex.logarithmicPhasePoissonTransitionModes_eq_singleton_zero
    (t : ℝ) {a b : ℤ} (ha : 1 ≤ a) :
    Complex.logarithmicPhasePoissonTransitionModes t a b = {0} := by
  have hsubset :
      Complex.logarithmicPhasePoissonTransitionModes t a b ⊆ {0} :=
    Complex.logarithmicPhasePoissonTransitionModes_subset_singleton_zero t a b
  have hsuperset : {0} ⊆ Complex.logarithmicPhasePoissonTransitionModes t a b := by
    intro m hm
    have hm_zero : m = 0 :=
      Finset.mem_singleton.mp hm
    exact
      Eq.subst
        (motive := fun value : ℤ =>
          value ∈ Complex.logarithmicPhasePoissonTransitionModes t a b)
        hm_zero.symm
        (Complex.zero_mem_logarithmicPhasePoissonTransitionModes t ha)
  exact Finset.Subset.antisymm hsubset hsuperset

theorem Complex.logarithmicPhasePoissonTransitionModes_card_eq_one
    (t : ℝ) {a b : ℤ} (ha : 1 ≤ a) :
    (Complex.logarithmicPhasePoissonTransitionModes t a b).card = 1 := by
  have heq :=
    Complex.logarithmicPhasePoissonTransitionModes_eq_singleton_zero
      t (b := b) ha
  exact
    Eq.trans
      (congrArg Finset.card heq)
      (by rfl)

theorem Complex.logarithmicPhasePoissonTransitionBudget_eq_zeroModePacketNorm
    (t : ℝ) {a b : ℤ} (ha : 1 ≤ a) :
    Complex.logarithmicPhasePoissonTransitionBudget t a b =
      ‖Complex.integerBlockFourierPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b 0‖ := by
  have hmodes :=
    Complex.logarithmicPhasePoissonTransitionModes_eq_singleton_zero
      t (b := b) ha
  unfold Complex.logarithmicPhasePoissonTransitionBudget
  calc
    (∑ m ∈ Complex.logarithmicPhasePoissonTransitionModes t a b,
      ‖Complex.integerBlockFourierPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖) =
        ∑ m ∈ ({0} : Finset ℤ),
          ‖Complex.integerBlockFourierPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖ :=
      congrArg
        (fun modes : Finset ℤ =>
          ∑ m ∈ modes,
            ‖Complex.integerBlockFourierPacket
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              a b m‖)
        hmodes
    _ = ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b 0‖ :=
      Finset.sum_singleton
        (fun m : ℤ =>
          ‖Complex.integerBlockFourierPacket
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            a b m‖) 0

theorem Complex.logarithmicPhasePoissonTransitionModes_card_le_modeRange_card
    (t : ℝ) (a b : ℤ) :
    (Complex.logarithmicPhasePoissonTransitionModes t a b).card ≤
      (Complex.logarithmicPhasePoissonModeRange t a).card := by
  exact
    le_trans
      (Finset.card_le_card
        (Complex.logarithmicPhasePoissonTransitionModes_subset_inRangeInactive
          t a b))
      (Complex.logarithmicPhasePoissonInRangeInactive_card_le_modeRange_card
        t a b)

theorem Complex.logarithmicPhasePoissonTransitionBudget_nonneg
    (t : ℝ) (a b : ℤ) :
    0 ≤ Complex.logarithmicPhasePoissonTransitionBudget t a b := by
  unfold Complex.logarithmicPhasePoissonTransitionBudget
  exact Finset.sum_nonneg (fun m hm => norm_nonneg _)

theorem Complex.logarithmicPhasePoissonLeftInactiveBudget_nonneg
    (t : ℝ) (a b : ℤ) :
    0 ≤ Complex.logarithmicPhasePoissonLeftInactiveBudget t a b := by
  unfold Complex.logarithmicPhasePoissonLeftInactiveBudget
  exact Finset.sum_nonneg (fun m hm => norm_nonneg _)

theorem Complex.logarithmicPhasePoissonRightInactiveBudget_nonneg
    (t : ℝ) (a b : ℤ) :
    0 ≤ Complex.logarithmicPhasePoissonRightInactiveBudget t a b := by
  unfold Complex.logarithmicPhasePoissonRightInactiveBudget
  exact Finset.sum_nonneg (fun m hm => norm_nonneg _)

theorem Complex.logarithmicPhasePoissonInRangeInactiveBudget_eq_left_add_right_add_transition
    (t : ℝ) (a b : ℤ) (hab : a ≤ b) :
    Complex.logarithmicPhasePoissonInRangeInactiveBudget t a b =
      Complex.logarithmicPhasePoissonLeftInactiveBudget t a b +
        Complex.logarithmicPhasePoissonRightInactiveBudget t a b +
          Complex.logarithmicPhasePoissonTransitionBudget t a b := by
  let left := Complex.logarithmicPhasePoissonLeftInactiveModes t a b
  let right := Complex.logarithmicPhasePoissonRightInactiveModes t a b
  let transition := Complex.logarithmicPhasePoissonTransitionModes t a b
  let inactive := Complex.logarithmicPhasePoissonInRangeInactiveModes t a b
  let packetNorm : ℤ → ℝ := fun m =>
    ‖Complex.integerBlockFourierPacket
      (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
      a b m‖
  have hleft_right : Disjoint left right :=
    Complex.logarithmicPhasePoissonLeftRightInactive_disjoint t a b hab
  have hcore_transition : Disjoint (left ∪ right) transition :=
    Complex.logarithmicPhasePoissonLeftRightInactive_disjoint_transition t a b
  have hpartition : (left ∪ right) ∪ transition = inactive :=
    Complex.logarithmicPhasePoissonLeftRightTransition_union_eq_inRangeInactive
      t a b
  have hleft_right_sum :
      (∑ m ∈ left ∪ right, packetNorm m) =
        (∑ m ∈ left, packetNorm m) + ∑ m ∈ right, packetNorm m := by
    exact Finset.sum_union hleft_right
  have hcore_transition_sum :
      (∑ m ∈ (left ∪ right) ∪ transition, packetNorm m) =
        (∑ m ∈ left ∪ right, packetNorm m) +
          ∑ m ∈ transition, packetNorm m := by
    exact Finset.sum_union hcore_transition
  change
    (∑ m ∈ inactive, packetNorm m) =
      (∑ m ∈ left, packetNorm m) +
        (∑ m ∈ right, packetNorm m) +
          ∑ m ∈ transition, packetNorm m
  calc
    (∑ m ∈ inactive, packetNorm m) =
        ∑ m ∈ (left ∪ right) ∪ transition, packetNorm m :=
      congrArg (fun modes : Finset ℤ => ∑ m ∈ modes, packetNorm m)
        hpartition.symm
    _ = (∑ m ∈ left ∪ right, packetNorm m) +
          ∑ m ∈ transition, packetNorm m :=
      hcore_transition_sum
    _ = ((∑ m ∈ left, packetNorm m) +
          ∑ m ∈ right, packetNorm m) +
          ∑ m ∈ transition, packetNorm m :=
      congrArg
        (fun value : ℝ => value + ∑ m ∈ transition, packetNorm m)
        hleft_right_sum

/-- A packet without a usable nonstationary gap is still bounded explicitly
by the principal interval length and the two compact cutoff crossings.  This
is the local bound reserved for the finite transition family. -/
theorem Complex.norm_integerBlockFourierPacket_le_crossing_add_blockLength
    (t : ℝ) (a b m : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖Complex.integerBlockFourierPacket
        (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
        a b m‖ ≤ 4 / 3 + ((b : ℝ) - (a : ℝ)) := by
  have hab_real : (a : ℝ) ≤ (b : ℝ) :=
    Int.cast_le.mpr hab
  have hcutoff :
      ‖∫ x in (a : ℝ)..(b : ℝ),
          Complex.phaseCutoffFrequencyTwistIntegrand
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            (Real.integerBlockCutoff a b) m x‖ ≤
        (b : ℝ) - (a : ℝ) :=
    Complex.norm_intervalIntegral_logarithmicPhase_packet_le_length
      t a b m (a : ℝ) (b : ℝ) hab_real
  have heq :
      (∫ x in (a : ℝ)..(b : ℝ),
          Complex.phaseCutoffFrequencyTwistIntegrand
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
            (Real.integerBlockCutoff a b) m x) =
        ∫ x in (a : ℝ)..(b : ℝ),
          Complex.realPhaseOscillation
            (Complex.realPhaseFrequencyTwist
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              m) x :=
    Complex.integral_logarithmicPhase_packet_eq_integral_realPhaseOscillation_on_subinterval
      t a b m (a : ℝ) (b : ℝ) le_rfl le_rfl hab_real
  have hprincipal :
      ‖∫ x in (a : ℝ)..(b : ℝ),
          Complex.realPhaseOscillation
            (Complex.realPhaseFrequencyTwist
              (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
              m) x‖ ≤
        (b : ℝ) - (a : ℝ) := by
    exact
      Eq.subst
        (motive := fun value : ℂ => ‖value‖ ≤ (b : ℝ) - (a : ℝ))
        heq
        hcutoff
  exact
    Complex.norm_integerBlockFourierPacket_le_crossing_add_principal
      t a b m ha hab hprincipal

theorem Complex.logarithmicPhasePoissonTransitionBudget_le_blockLength
    (t : ℝ) {a b : ℤ} (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhasePoissonTransitionBudget t a b ≤
      4 / 3 + ((b : ℝ) - (a : ℝ)) := by
  have htransition :=
    Complex.logarithmicPhasePoissonTransitionBudget_eq_zeroModePacketNorm
      t (b := b) ha
  have hpacket :=
    Complex.norm_integerBlockFourierPacket_le_crossing_add_blockLength
      t a b 0 ha hab
  exact
    Eq.subst
      (motive := fun value : ℝ =>
        value ≤ 4 / 3 + ((b : ℝ) - (a : ℝ)))
      htransition.symm
      hpacket

theorem Complex.logarithmicPhasePoissonTransitionBudget_le_card_mul_blockLength
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    Complex.logarithmicPhasePoissonTransitionBudget t a b ≤
      ((Complex.logarithmicPhasePoissonTransitionModes t a b).card : ℝ) *
        (4 / 3 + ((b : ℝ) - (a : ℝ))) := by
  unfold Complex.logarithmicPhasePoissonTransitionBudget
  have hpointwise :
      (∑ m ∈ Complex.logarithmicPhasePoissonTransitionModes t a b,
        ‖Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖) ≤
        ∑ m ∈ Complex.logarithmicPhasePoissonTransitionModes t a b,
          (4 / 3 + ((b : ℝ) - (a : ℝ))) := by
    exact
      Finset.sum_le_sum
        (fun m hm =>
          Complex.norm_integerBlockFourierPacket_le_crossing_add_blockLength
            t a b m ha hab)
  have hconstant :
      (∑ m ∈ Complex.logarithmicPhasePoissonTransitionModes t a b,
        (4 / 3 + ((b : ℝ) - (a : ℝ))) ) =
        ((Complex.logarithmicPhasePoissonTransitionModes t a b).card : ℝ) *
          (4 / 3 + ((b : ℝ) - (a : ℝ))) := by
    exact
      Finset.sum_const_real_eq_card_mul
        (Complex.logarithmicPhasePoissonTransitionModes t a b)
        (4 / 3 + ((b : ℝ) - (a : ℝ)))
  exact hpointwise.trans_eq hconstant

theorem Complex.norm_logarithmicPhasePoissonLeftInactive_packet_tsum_le_explicit_sum
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b},
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      ∑ m ∈ Complex.logarithmicPhasePoissonLeftInactiveModes t a b,
        (4 / 3 +
          2 * ((2 * Real.pi * (-(m : ℝ))) *
            ((a : ℝ) - Complex.logarithmicPhaseFourierStationaryPoint t m) /
              (b : ℝ))⁻¹ +
          ((b : ℝ) - (a : ℝ)) •
            ((‖t‖ / (a : ℝ) ^ 2) /
              ((2 * Real.pi * (-(m : ℝ))) *
                ((a : ℝ) - Complex.logarithmicPhaseFourierStationaryPoint t m) /
                  (b : ℝ)) ^ 2)) := by
  exact
    Complex.norm_logarithmicPhase_leftInactive_packet_tsum_le_explicit_sum
      t ht ht_nonneg a b ha hab
      (Complex.logarithmicPhasePoissonLeftInactiveModes t a b)
      (fun m hm =>
        have hmem :=
          (Complex.mem_logarithmicPhasePoissonLeftInactiveModes_iff
            t a b m).mp hm
        And.intro hmem.2.1 hmem.2.2)

theorem Complex.norm_logarithmicPhasePoissonRightInactive_packet_tsum_le_explicit_sum
    (t : ℝ) (ht : 1 ≤ ‖t‖) (ht_nonneg : 0 ≤ t)
    (a b : ℤ) (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b},
        Complex.integerBlockFourierPacket
          (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase t)
          a b m‖ ≤
      ∑ m ∈ Complex.logarithmicPhasePoissonRightInactiveModes t a b,
        (4 / 3 +
          2 * ((2 * Real.pi * (-(m : ℝ))) *
            (Complex.logarithmicPhaseFourierStationaryPoint t m - (b : ℝ)) /
              (b : ℝ))⁻¹ +
          ((b : ℝ) - (a : ℝ)) •
            ((‖t‖ / (a : ℝ) ^ 2) /
              ((2 * Real.pi * (-(m : ℝ))) *
                (Complex.logarithmicPhaseFourierStationaryPoint t m - (b : ℝ)) /
                  (b : ℝ)) ^ 2)) := by
  exact
    Complex.norm_logarithmicPhase_rightInactive_packet_tsum_le_explicit_sum
      t ht ht_nonneg a b ha hab
      (Complex.logarithmicPhasePoissonRightInactiveModes t a b)
      (fun m hm =>
        have hmem :=
          (Complex.mem_logarithmicPhasePoissonRightInactiveModes_iff
            t a b m).mp hm
        And.intro hmem.2.1 hmem.2.2)

end
end LFunctions
end Boundary
