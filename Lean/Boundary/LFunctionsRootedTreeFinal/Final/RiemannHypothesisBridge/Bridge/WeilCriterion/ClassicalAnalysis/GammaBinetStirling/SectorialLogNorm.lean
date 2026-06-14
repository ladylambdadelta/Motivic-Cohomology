import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.SectorialFromBinet

/-!
# Sectorial logarithmic Gamma norm bounds

This file owns the right-half-plane logarithmic growth consequence of
Binet-Stirling.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Closed-sector logarithmic Gamma growth from Binet-Stirling. -/
theorem Complex.Gamma_closedRightHalfPlane_log_norm_bound_classical :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ z : ℂ,
        Complex.closedRightHalfPlaneSector z →
          Real.log ‖Complex.Gamma z‖ ≤
            C * (1 + ‖z‖) ^ m := by
  sorry

end

end LFunctions
end Boundary
