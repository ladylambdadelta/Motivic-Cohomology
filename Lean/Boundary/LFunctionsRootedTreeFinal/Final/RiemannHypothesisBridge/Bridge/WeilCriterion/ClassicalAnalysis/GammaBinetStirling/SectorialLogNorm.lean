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

/-- Open-right-half-plane logarithmic Gamma growth from the principal-log
Binet formula and the open-half-plane remainder estimates. -/
theorem Complex.Gamma_openRightHalfPlane_log_norm_bound_from_Binet :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
          Real.log ‖Complex.Gamma z‖ ≤
            C * (1 + ‖z‖) ^ m := by
  sorry

/-- Open-right-half-plane logarithmic Gamma growth from Binet-Stirling.

The literal principal-arctangent Binet remainder in this package is not a
closed-boundary kernel on the imaginary axis, so the sectorial log-norm owner
statement is intentionally open in the real part. -/
theorem Complex.Gamma_closedRightHalfPlane_log_norm_bound_classical :
    ∃ C : ℝ, ∃ m : ℕ,
      0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
          Real.log ‖Complex.Gamma z‖ ≤
            C * (1 + ‖z‖) ^ m := by
  exact
    Complex.Gamma_openRightHalfPlane_log_norm_bound_from_Binet

end

end LFunctions
end Boundary
