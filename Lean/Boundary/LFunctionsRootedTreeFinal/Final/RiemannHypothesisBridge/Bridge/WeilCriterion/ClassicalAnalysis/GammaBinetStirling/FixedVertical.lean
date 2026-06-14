import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.SectorialLogNorm

/-!
# Fixed-vertical-line Gamma bounds

This file owns fixed-real-part vertical upper and reciprocal bounds for Gamma.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Fixed-real-part vertical upper bound for Gamma. -/
theorem Complex.Gamma_fixedRealPart_vertical_upper_bound_classical
    (σ : ℝ)
    (hσ : 0 < σ) :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ t : ℝ,
        ‖Complex.Gamma (σ + t * Complex.I)‖ ≤
          C * (1 + ‖t‖) ^ m := by
  sorry

/-- Fixed-real-part vertical lower reciprocal bound for Gamma. -/
theorem Complex.Gamma_fixedRealPart_vertical_lower_bound_classical
    (σ : ℝ)
    (hσ : 0 < σ) :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ t : ℝ,
        ‖(Complex.Gamma (σ + t * Complex.I))⁻¹‖ ≤
          C * (1 + ‖t‖) ^ m := by
  sorry

end

end LFunctions
end Boundary
