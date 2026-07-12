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

theorem Complex.norm_logarithmicPhaseQuantitativePacket_tsum_le_active_add_adaptedComplement
    (t : ℝ) (a b : ℤ)
    (ha : 1 ≤ a) (hab : a ≤ b) :
    ‖∑' m : ℤ,
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ ≤
      ‖∑' m : {m : ℤ //
          m ∈ Complex.logarithmicPhasePoissonActiveModes t a b},
        Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m‖ +
      Complex.logarithmicPhaseAdaptedComplementBudget t a b := by
  have hsplit :=
    Complex.logarithmicPhaseQuantitativePacket_tsum_eq_four_families
      t a b ha
  let activeSum : ℂ :=
    ∑' m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonActiveModes t a b},
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m
  let inactiveSum : ℂ :=
    ∑' m : {m : ℤ //
      m ∈ Complex.logarithmicPhasePoissonInRangeInactiveModes t a b},
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m
  let outsideSum : ℂ :=
    ∑' m : {m : ℤ //
      m ∉ Complex.logarithmicPhasePoissonModeRange t a},
      Complex.logarithmicPhaseQuantitativeBlockFourierPacket t a b m
  have houterTriangle : ‖(activeSum + inactiveSum) + outsideSum‖ ≤
      ‖activeSum + inactiveSum‖ + ‖outsideSum‖ :=
    norm_add_le (activeSum + inactiveSum) outsideSum
  have hinnerTriangle : ‖activeSum + inactiveSum‖ ≤
      ‖activeSum‖ + ‖inactiveSum‖ :=
    norm_add_le activeSum inactiveSum
  have hinactive :=
    Complex.norm_logarithmicPhaseQuantitativeInRangeInactive_tsum_le_budget
      t a b
  have houtside :=
    Complex.norm_logarithmicPhaseOutsidePacket_tsum_le_adaptedBudget
      t a b ha hab
  have hcombine₁ := add_le_add_right hinnerTriangle ‖outsideSum‖
  have hcombine₂ := add_le_add_left hinactive ‖activeSum‖
  have hcombine₃ := add_le_add_left houtside
    (‖activeSum‖ +
      Complex.logarithmicPhaseQuantitativeInRangeInactiveBudget t a b)
  unfold Complex.logarithmicPhaseAdaptedComplementBudget
  unfold Complex.logarithmicPhaseAdaptedOutsideRangeBudget
  exact le_trans (le_of_eq (congrArg norm hsplit))
    (le_trans houterTriangle
      (le_trans hcombine₁
        (le_trans
          (add_le_add_right hcombine₂ ‖outsideSum‖)
          hcombine₃)))

end
end LFunctions
end Boundary
