import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeInactiveAndFarTail
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeBudget

/-!
# Refined quantitative logarithmic B-process budget

The exact frequency reconstruction is decomposed into four analytically
different owners: stationary interior packets, endpoint-active packets,
finite in-range inactive packets, and genuinely far packets.  The public
budget groups the first two as the active-window and crossing components and
the latter two as the complement-tail component.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory

def Complex.logarithmicPhaseQuantitativeRefinedActiveBudget
    (t : ℝ) (a b : ℤ) (radius : ℝ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius,
    Complex.logarithmicPhaseQuantitativeInteriorStationaryPacketBound
      t a b m radius

def Complex.logarithmicPhaseQuantitativeRefinedEndpointBudget
    (t : ℝ) (a b : ℤ) (radius : ℝ) : ℝ :=
  ∑ m ∈ Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius,
    ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖

def Complex.logarithmicPhaseQuantitativeRefinedTailBudget
    (t : ℝ) (a b : ℤ) : ℝ :=
  Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget t a b +
    Complex.logarithmicPhaseQuantitativeOutsideRangeClosedBudget t a b

def Complex.logarithmicPhaseQuantitativeRefinedBProcessBudget
    (t : ℝ) (a b : ℤ) (radius : ℝ) : ℝ :=
  Complex.logarithmicPhaseQuantitativeRefinedActiveBudget t a b radius +
    Complex.logarithmicPhaseQuantitativeRefinedEndpointBudget t a b radius +
      Complex.logarithmicPhaseQuantitativeRefinedTailBudget t a b

theorem Complex.logarithmicPhaseQuantitativeRefinedActiveBudget_nonneg
    (t : ℝ) (a b : ℤ) (radius : ℝ)
    (hpacket :
      ∀ m ∈ Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius,
        0 ≤ Complex.logarithmicPhaseQuantitativeInteriorStationaryPacketBound
          t a b m radius) :
    0 ≤ Complex.logarithmicPhaseQuantitativeRefinedActiveBudget
      t a b radius := by
  unfold Complex.logarithmicPhaseQuantitativeRefinedActiveBudget
  exact Finset.sum_nonneg (fun m hm => hpacket m hm)

theorem Complex.logarithmicPhaseQuantitativeRefinedEndpointBudget_nonneg
    (t : ℝ) (a b : ℤ) (radius : ℝ) :
    0 ≤ Complex.logarithmicPhaseQuantitativeRefinedEndpointBudget
      t a b radius := by
  unfold Complex.logarithmicPhaseQuantitativeRefinedEndpointBudget
  exact Finset.sum_nonneg (fun m hm => norm_nonneg _)

theorem Complex.logarithmicPhaseQuantitativeRefinedTailBudget_nonneg
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b) :
    0 ≤ Complex.logarithmicPhaseQuantitativeRefinedTailBudget t a b := by
  unfold Complex.logarithmicPhaseQuantitativeRefinedTailBudget
  exact add_nonneg
    (Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget_nonneg t a b)
    (Complex.logarithmicPhaseQuantitativeOutsideRangeClosedBudget_nonneg
      t a b ha hab)

theorem Complex.logarithmicPhaseQuantitativeRefinedBProcessBudget_nonneg
    (t : ℝ) (a b : ℤ) (radius : ℝ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (hpacket :
      ∀ m ∈ Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius,
        0 ≤ Complex.logarithmicPhaseQuantitativeInteriorStationaryPacketBound
          t a b m radius) :
    0 ≤ Complex.logarithmicPhaseQuantitativeRefinedBProcessBudget
      t a b radius := by
  unfold Complex.logarithmicPhaseQuantitativeRefinedBProcessBudget
  exact add_nonneg
    (add_nonneg
      (Complex.logarithmicPhaseQuantitativeRefinedActiveBudget_nonneg
        t a b radius hpacket)
      (Complex.logarithmicPhaseQuantitativeRefinedEndpointBudget_nonneg
        t a b radius))
    (Complex.logarithmicPhaseQuantitativeRefinedTailBudget_nonneg
      t a b ha hab)

theorem Complex.logarithmicPhaseQuantitativeModeRange_eq_active_union_inactive
    (t : ℝ) (a b : ℤ) :
    Complex.logarithmicPhasePoissonModeRange t a =
      Complex.logarithmicPhasePoissonActiveModes t a b ∪
        Complex.logarithmicPhasePoissonInRangeInactiveModes t a b := by
  exact
    (Complex.logarithmicPhasePoissonActive_union_inRangeInactive_eq_modeRange
      t a b).symm

theorem Complex.logarithmicPhaseQuantitativeActiveInactive_disjoint
    (t : ℝ) (a b : ℤ) :
    Disjoint
      (Complex.logarithmicPhasePoissonActiveModes t a b)
      (Complex.logarithmicPhasePoissonInRangeInactiveModes t a b) := by
  exact Complex.logarithmicPhasePoissonActive_disjoint_inRangeInactive t a b

theorem Complex.logarithmicPhaseQuantitativeModeRange_finset_sum_eq_active_add_inactive
    (t : ℝ) (a b : ℤ) :
    (∑ m ∈ Complex.logarithmicPhasePoissonModeRange t a,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) =
      (∑ m ∈ Complex.logarithmicPhasePoissonActiveModes t a b,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) +
      (∑ m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) := by
  have hunion :=
    Complex.logarithmicPhaseQuantitativeModeRange_eq_active_union_inactive
      t a b
  have hdisjoint :=
    Complex.logarithmicPhaseQuantitativeActiveInactive_disjoint t a b
  exact Eq.trans
    (congrArg
      (fun modes : Finset ℤ =>
        ∑ m ∈ modes,
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m)
      hunion)
    (Finset.sum_union hdisjoint)

theorem Complex.logarithmicPhaseQuantitativeModeRange_tsum_eq_active_add_inactive
    (t : ℝ) (a b : ℤ) :
    (∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonModeRange t a},
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) =
      (∑' m : {m : ℤ //
          m ∈ Complex.logarithmicPhasePoissonActiveModes t a b},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) +
      (∑' m : {m : ℤ //
          m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) := by
  let packet : ℤ → ℂ :=
    fun m => Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m
  have hrange :=
    (Complex.logarithmicPhasePoissonModeRange t a).tsum_subtype packet
  have hactive :=
    (Complex.logarithmicPhasePoissonActiveModes t a b).tsum_subtype packet
  have hinactive :=
    (Complex.logarithmicPhasePoissonInRangeInactiveModes t a b).tsum_subtype packet
  have hfinite :=
    Complex.logarithmicPhaseQuantitativeModeRange_finset_sum_eq_active_add_inactive
      t a b
  exact Eq.trans
    hrange
    (Eq.trans hfinite
      (congrArg₂ (fun first second : ℂ => first + second)
        hactive.symm hinactive.symm))

theorem Complex.logarithmicPhaseQuantitativePacket_tsum_eq_four_families
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a) :
    (∑' m : ℤ,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) =
      ((∑' m : {m : ℤ //
          m ∈ Complex.logarithmicPhasePoissonActiveModes t a b},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) +
       (∑' m : {m : ℤ //
          m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m)) +
       (∑' m : {m : ℤ //
          m ∉ Complex.logarithmicPhasePoissonModeRange t a},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) := by
  have hrangeSplit :=
    Complex.logarithmicPhaseQuantitativePacket_tsum_eq_modeRange_add_outside
      t a b ha
  have hfiniteSplit :=
    Complex.logarithmicPhaseQuantitativeModeRange_tsum_eq_active_add_inactive
      t a b
  exact Eq.trans hrangeSplit
    (congrArg
      (fun rangePart : ℂ => rangePart +
        (∑' m : {m : ℤ //
            m ∉ Complex.logarithmicPhasePoissonModeRange t a},
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m))
      hfiniteSplit)

theorem Complex.norm_logarithmicPhaseQuantitativeInRangeInactive_tsum_le_budget
    (t : ℝ) (a b : ℤ) :
    ‖∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b},
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget t a b := by
  have hfinite :=
    (Complex.logarithmicPhasePoissonInRangeInactiveModes t a b).tsum_subtype
      (fun m : ℤ =>
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m)
  unfold Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget
  exact Eq.subst
    (motive := fun packetSum : ℂ =>
      ‖packetSum‖ ≤
        ∑ m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b,
          ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖)
    hfinite.symm
    (norm_sum_le
      (Complex.logarithmicPhasePoissonInRangeInactiveModes t a b)
      (fun m : ℤ =>
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m))

theorem Complex.norm_logarithmicPhaseQuantitativePacket_tsum_le_refined_budget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (htNonneg : 0 ≤ t)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (radius : ℝ)
    (hradius : 0 < radius) :
    ‖∑' m : ℤ,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      Complex.logarithmicPhaseQuantitativeRefinedBProcessBudget
        t a b radius := by
  have hsplit :=
    Complex.logarithmicPhaseQuantitativePacket_tsum_eq_four_families
      t a b ha
  have hactive :=
    Complex.norm_logarithmicPhaseQuantitative_activePacket_tsum_le_interior_add_endpoint
      t ht htNonneg a b ha hab radius hradius
  have hinactive :=
    Complex.norm_logarithmicPhaseQuantitativeInRangeInactive_tsum_le_budget
      t a b
  have houtside :=
    Complex.norm_logarithmicPhaseQuantitativeOutsideRangePacket_tsum_le_closed
      t a b ha hab
  unfold Complex.logarithmicPhaseQuantitativeRefinedBProcessBudget
  unfold Complex.logarithmicPhaseQuantitativeRefinedActiveBudget
  unfold Complex.logarithmicPhaseQuantitativeRefinedEndpointBudget
  unfold Complex.logarithmicPhaseQuantitativeRefinedTailBudget
  calc
    ‖∑' m : ℤ,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ =
      ‖((∑' m : {m : ℤ //
          m ∈ Complex.logarithmicPhasePoissonActiveModes t a b},
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m) +
        (∑' m : {m : ℤ //
          m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b},
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m)) +
        (∑' m : {m : ℤ //
          m ∉ Complex.logarithmicPhasePoissonModeRange t a},
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m)‖ :=
      congrArg norm hsplit
    _ ≤
      (‖∑' m : {m : ℤ //
          m ∈ Complex.logarithmicPhasePoissonActiveModes t a b},
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ +
       ‖∑' m : {m : ℤ //
          m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b},
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖) +
       ‖∑' m : {m : ℤ //
          m ∉ Complex.logarithmicPhasePoissonModeRange t a},
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ :=
      le_trans
        (norm_add_le _ _)
        (add_le_add_right (norm_add_le _ _) _)
    _ ≤
      (((∑ m ∈ Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius,
          Complex.logarithmicPhaseQuantitativeInteriorStationaryPacketBound
            t a b m radius) +
       (∑ m ∈ Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius,
          ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖)) +
       Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget t a b) +
       Complex.logarithmicPhaseQuantitativeOutsideRangeClosedBudget t a b :=
      add_le_add (add_le_add hactive hinactive) houtside
    _ =
      (∑ m ∈ Complex.logarithmicPhasePoissonInteriorActiveModes t a b radius,
          Complex.logarithmicPhaseQuantitativeInteriorStationaryPacketBound
            t a b m radius) +
       (∑ m ∈ Complex.logarithmicPhasePoissonEndpointActiveModes t a b radius,
          ‖Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖) +
       (Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget t a b +
        Complex.logarithmicPhaseQuantitativeOutsideRangeClosedBudget t a b) :=
      add_assoc _ _ _

theorem Complex.logarithmicPhaseQuantitativeIntegerBlock_norm_le_refined_budget
    (t : ℝ)
    (ht : 1 ≤ ‖t‖)
    (htNonneg : 0 ≤ t)
    (a b : ℤ)
    (ha : 1 ≤ a)
    (hab : a ≤ b)
    (radius : ℝ)
    (hradius : 0 < radius) :
    ‖∑ n ∈ Finset.Icc a b,
        Complex.exp
          (Complex.I *
            (Complex.boundaryLineOnePointRealParam_logarithmicPhaseRealPhase
              t (n : ℝ) : ℂ))‖ ≤
      Complex.logarithmicPhaseQuantitativeRefinedBProcessBudget
        t a b radius := by
  have hreconstruction :=
    Complex.logarithmicPhase_quantitativeBlock_poisson_packet_reconstruction
      t a b ha hab
  have hpacket :=
    Complex.norm_logarithmicPhaseQuantitativePacket_tsum_le_refined_budget
      t ht htNonneg a b ha hab radius hradius
  exact le_trans (le_of_eq (congrArg norm hreconstruction)) hpacket

theorem Complex.logarithmicPhaseQuantitativeRefinedBudget_upper_of_components
    (t : ℝ) (a b : ℤ) (radius : ℝ)
    (active endpoint inactive outside : ℝ)
    (hactive :
      Complex.logarithmicPhaseQuantitativeRefinedActiveBudget t a b radius ≤ active)
    (hendpoint :
      Complex.logarithmicPhaseQuantitativeRefinedEndpointBudget t a b radius ≤ endpoint)
    (hinactive :
      Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget t a b ≤ inactive)
    (houtside :
      Complex.logarithmicPhaseQuantitativeOutsideRangeClosedBudget t a b ≤ outside) :
    Complex.logarithmicPhaseQuantitativeRefinedBProcessBudget t a b radius ≤
      active + endpoint + (inactive + outside) := by
  unfold Complex.logarithmicPhaseQuantitativeRefinedBProcessBudget
  unfold Complex.logarithmicPhaseQuantitativeRefinedTailBudget
  exact add_le_add (add_le_add hactive hendpoint) (add_le_add hinactive houtside)

end
end LFunctions
end Boundary
