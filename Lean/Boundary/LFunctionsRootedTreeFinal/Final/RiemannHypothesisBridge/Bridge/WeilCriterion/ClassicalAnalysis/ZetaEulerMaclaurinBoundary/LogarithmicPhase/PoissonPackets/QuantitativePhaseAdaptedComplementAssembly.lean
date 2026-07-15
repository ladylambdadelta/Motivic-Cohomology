import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativePhaseAdaptedOutsideBudgetBound
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.QuantitativeRefinedBProcessBudget

/-!
# Assembly of the phase-adapted complement estimate

The exact four-family Poisson split is bounded by the active packet norm, the
finite in-range inactive norm sum, and the new phase-adapted outside budget.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.logarithmicPhaseAdaptedModeRange_finset_sum_eq_active_add_inactive
    (t : ℝ) (a b : ℤ) :
    (∑ m ∈ Complex.logarithmicPhasePoissonModeRange t a,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m) =
      (∑ m ∈ Complex.logarithmicPhasePoissonActiveModes t a b,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m) +
      (∑ m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m) := by
  have hunion :=
    Complex.logarithmicPhaseQuantitativeModeRange_eq_active_union_inactive
      t a b
  have hdisjoint :=
    Complex.logarithmicPhaseQuantitativeActiveInactive_disjoint t a b
  have htransport := congrArg
    (fun modes : Finset ℤ =>
      ∑ m ∈ modes,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m)
    hunion
  exact Eq.trans htransport (Finset.sum_union hdisjoint)

theorem Complex.logarithmicPhaseAdaptedModeRange_tsum_eq_active_add_inactive
    (t : ℝ) (a b : ℤ) :
    (∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonModeRange t a},
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m) =
      (∑' m : {m : ℤ //
          m ∈ Complex.logarithmicPhasePoissonActiveModes t a b},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m) +
      (∑' m : {m : ℤ //
          m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m) := by
  let packet : ℤ → ℂ :=
    fun m =>
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m
  have hrange :=
    (Complex.logarithmicPhasePoissonModeRange t a).tsum_subtype packet
  have hactive :=
    (Complex.logarithmicPhasePoissonActiveModes t a b).tsum_subtype packet
  have hinactive :=
    (Complex.logarithmicPhasePoissonInRangeInactiveModes t a b).tsum_subtype
      packet
  have hfinite :=
    Complex.logarithmicPhaseAdaptedModeRange_finset_sum_eq_active_add_inactive
      t a b
  have hnormalize := congrArg₂
    (fun active inactive : ℂ => active + inactive)
    hactive.symm hinactive.symm
  exact Eq.trans hrange (Eq.trans hfinite hnormalize)

theorem Complex.logarithmicPhaseAdaptedPacket_tsum_eq_modeRange_add_outside
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) :
    (∑' m : ℤ,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m) =
      (∑' m : {m : ℤ //
          m ∈ Complex.logarithmicPhasePoissonModeRange t a},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m) +
      (∑' m : {m : ℤ //
          m ∉ Complex.logarithmicPhasePoissonModeRange t a},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m) := by
  have hsummable :=
    Complex.summable_logarithmicPhaseQuantitativeBlockFourierPacket
      ‖t‖ a b ha
  let modeSet : Set ℤ :=
    {m : ℤ | m ∈ Complex.logarithmicPhasePoissonModeRange t a}
  have hsplit :=
    tsum_subtype_add_tsum_subtype_compl hsummable modeSet
  have hcomplement :
      modeSetᶜ =
        {m : ℤ | m ∉ Complex.logarithmicPhasePoissonModeRange t a} :=
    Set.ext (fun m => Iff.rfl)
  have houtside :
      (∑' m : {m : ℤ // m ∈ modeSetᶜ},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m) =
        ∑' m : {m : ℤ //
            m ∉ Complex.logarithmicPhasePoissonModeRange t a},
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m :=
    Eq.subst
      (motive := fun modes : Set ℤ =>
        (∑' m : modes,
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m) =
          (∑' m : {m : ℤ //
              m ∉ Complex.logarithmicPhasePoissonModeRange t a},
            Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m))
      hcomplement
      rfl
  exact Eq.trans hsplit.symm
    (congrArg₂ (fun rangePart outsidePart : ℂ => rangePart + outsidePart)
      rfl houtside)

theorem Complex.logarithmicPhaseAdaptedPacket_tsum_eq_four_families
    (t : ℝ) (a b : ℤ) (ha : 1 ≤ a) :
    (∑' m : ℤ,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m) =
      ((∑' m : {m : ℤ //
          m ∈ Complex.logarithmicPhasePoissonActiveModes t a b},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m) +
       (∑' m : {m : ℤ //
          m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m)) +
       (∑' m : {m : ℤ //
          m ∉ Complex.logarithmicPhasePoissonModeRange t a},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m) := by
  have hrangeSplit :=
    Complex.logarithmicPhaseAdaptedPacket_tsum_eq_modeRange_add_outside
      t a b ha
  have hfiniteSplit :=
    Complex.logarithmicPhaseAdaptedModeRange_tsum_eq_active_add_inactive
      t a b
  exact Eq.trans hrangeSplit
    (congrArg
      (fun rangePart : ℂ => rangePart +
        (∑' m : {m : ℤ //
            m ∉ Complex.logarithmicPhasePoissonModeRange t a},
          Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m))
      hfiniteSplit)

theorem Complex.norm_logarithmicPhaseAdaptedInRangeInactive_tsum_le_budget
    (t : ℝ) (a b : ℤ) :
    ‖∑' m : {m : ℤ //
        m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b},
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m‖ ≤
      Complex.logarithmicPhaseAdaptedInRangeInactiveBudget t a b := by
  have hfinite :=
    (Complex.logarithmicPhasePoissonInRangeInactiveModes t a b).tsum_subtype
      (fun m : ℤ =>
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m)
  exact Eq.subst
    (motive := fun packetSum : ℂ =>
      ‖packetSum‖ ≤
        Complex.logarithmicPhaseAdaptedInRangeInactiveBudget t a b)
    hfinite.symm
    (norm_sum_le
      (Complex.logarithmicPhasePoissonInRangeInactiveModes t a b)
      (fun m : ℤ =>
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m))

theorem Complex.norm_logarithmicPhaseQuantitativePacket_tsum_le_active_add_adaptedComplement
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑' m : ℤ,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m‖ ≤
      ‖∑' m : {m : ℤ //
          m ∈ Complex.logarithmicPhasePoissonActiveModes t a b},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m‖ +
      Complex.logarithmicPhaseAdaptedComplementBudget t a b := by
  have hsplit :=
    Complex.logarithmicPhaseAdaptedPacket_tsum_eq_four_families
      t a b ha
  let activeSum : ℂ :=
    ∑' m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonActiveModes t a b},
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m
  let inactiveSum : ℂ :=
    ∑' m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b},
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m
  let outsideSum : ℂ :=
    ∑' m : {m : ℤ //
      m ∉ Complex.logarithmicPhasePoissonModeRange t a},
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket ‖t‖ a b m
  have houterTriangle : ‖(activeSum + inactiveSum) + outsideSum‖ ≤
      ‖activeSum + inactiveSum‖ + ‖outsideSum‖ :=
    norm_add_le (activeSum + inactiveSum) outsideSum
  have hinnerTriangle : ‖activeSum + inactiveSum‖ ≤
      ‖activeSum‖ + ‖inactiveSum‖ :=
    norm_add_le activeSum inactiveSum
  have hinactive :=
    Complex.norm_logarithmicPhaseAdaptedInRangeInactive_tsum_le_budget
      t a b
  have houtside :=
    Complex.norm_logarithmicPhaseOutsidePacket_tsum_le_adaptedBudget
      t a b ha hab
  have hcombine₁ := add_le_add_right hinnerTriangle ‖outsideSum‖
  have hcombine₂ := add_le_add_left hinactive ‖activeSum‖
  have hcombine₃ := add_le_add_left houtside
    (‖activeSum‖ +
      Complex.logarithmicPhaseAdaptedInRangeInactiveBudget t a b)
  have hnormalize :
      (‖activeSum‖ +
          Complex.logarithmicPhaseAdaptedInRangeInactiveBudget t a b) +
          Complex.logarithmicPhaseAdaptedOutsideRangeBudget t a b =
        ‖activeSum‖ +
          Complex.logarithmicPhaseAdaptedComplementBudget t a b :=
    add_assoc _ _ _
  exact le_trans (le_of_eq (congrArg norm hsplit))
    (le_trans houterTriangle
      (le_trans hcombine₁
        (le_trans
          (add_le_add_right hcombine₂ ‖outsideSum‖)
          (le_trans hcombine₃ (le_of_eq hnormalize)))))

end
end LFunctions
end Boundary
