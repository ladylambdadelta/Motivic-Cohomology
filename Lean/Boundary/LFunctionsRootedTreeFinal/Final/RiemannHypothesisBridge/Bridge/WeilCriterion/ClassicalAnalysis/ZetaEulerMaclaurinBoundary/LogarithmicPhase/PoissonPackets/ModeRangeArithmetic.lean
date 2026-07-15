import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.ModeRangeCore
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.LogarithmicPhase.PoissonPackets.CanonicalGlobalBudget

/-!
# Arithmetic of the logarithmic Poisson mode range

The direct Poisson range is an integer interval with a floor-defined lower
endpoint.  This file owns the exact interval and cardinal identities so later
analytic estimates can use them without unfolding the range definition.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem Complex.logarithmicPhasePoissonModeRange_card_eq_toNat
    (t : ℝ) (a : ℤ) :
    (Complex.logarithmicPhasePoissonModeRange t a).card =
      (0 + 1 - Complex.logarithmicPhasePoissonModeRangeLower t a).toNat := by
  unfold Complex.logarithmicPhasePoissonModeRange
  exact Int.card_Icc
    (Complex.logarithmicPhasePoissonModeRangeLower t a) 0

theorem Complex.logarithmicPhasePoissonModeRange_card_cast_eq_of_lower_le_one
    (t : ℝ) (a : ℤ)
    (hlower : Complex.logarithmicPhasePoissonModeRangeLower t a ≤ 1) :
    ((Complex.logarithmicPhasePoissonModeRange t a).card : ℤ) =
      1 - Complex.logarithmicPhasePoissonModeRangeLower t a := by
  change
    ((Finset.Icc (Complex.logarithmicPhasePoissonModeRangeLower t a) 0).card : ℤ) =
      0 + 1 - Complex.logarithmicPhasePoissonModeRangeLower t a
  exact Int.card_Icc_of_le
    (Complex.logarithmicPhasePoissonModeRangeLower t a) 0 hlower

theorem Complex.logarithmicPhasePoissonModeRange_lower_mem_of_lower_le_zero
    (t : ℝ) (a : ℤ)
    (hlower : Complex.logarithmicPhasePoissonModeRangeLower t a ≤ 0) :
    Complex.logarithmicPhasePoissonModeRangeLower t a ∈
      Complex.logarithmicPhasePoissonModeRange t a := by
  exact
    (Complex.mem_logarithmicPhasePoissonModeRange_iff t a
      (Complex.logarithmicPhasePoissonModeRangeLower t a)).mpr
      ⟨le_rfl, hlower⟩

theorem Complex.logarithmicPhasePoissonModeRange_card_cast_eq
    (t : ℝ) {a : ℤ} (ha : 1 ≤ a) :
    ((Complex.logarithmicPhasePoissonModeRange t a).card : ℤ) =
      1 - Complex.logarithmicPhasePoissonModeRangeLower t a := by
  exact
    Complex.logarithmicPhasePoissonModeRange_card_cast_eq_of_lower_le_one
      t a
      (le_trans
        (Complex.logarithmicPhasePoissonModeRangeLower_le_zero t ha)
        (show (0 : ℤ) ≤ 1 from zero_le_one))

end
end LFunctions
end Boundary
