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

/-- The explicit Binet main term has polynomial logarithmic growth after a
large-radius cutoff in the open right half-plane. -/
theorem Complex.binetLogGammaMainTerm_log_norm_bound_large_openRightHalfPlane :
    ∃ R : ℝ, ∃ C : ℝ, ∃ m : ℕ,
      0 < R ∧ 0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
          R ≤ ‖z‖ →
            Real.log ‖Complex.binetLogGammaMainTerm z‖ ≤
              C * (1 + ‖z‖) ^ m := by
  sorry

/-- The Binet remainder has polynomial logarithmic growth after a large-radius
cutoff in the open right half-plane. -/
theorem Complex.binetSecondFormulaRemainder_log_norm_bound_large_openRightHalfPlane :
    ∃ R : ℝ, ∃ C : ℝ, ∃ m : ℕ,
      0 < R ∧ 0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
          R ≤ ‖z‖ →
            Real.log ‖Complex.binetSecondFormulaRemainder z‖ ≤
              C * (1 + ‖z‖) ^ m := by
  sorry

/-- Addition preserves polynomial logarithmic growth for the Binet main term
and remainder after a common large-radius cutoff. -/
theorem Complex.Gamma_openRightHalfPlane_log_norm_bound_from_Binet_components :
    ∃ R : ℝ, ∃ C : ℝ, ∃ m : ℕ,
      0 < R ∧ 0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
          R ≤ ‖z‖ →
            Real.log ‖Complex.Gamma z‖ ≤
              C * (1 + ‖z‖) ^ m := by
  sorry

/-- Open-right-half-plane logarithmic Gamma growth from the principal-log
Binet formula and the open-half-plane remainder estimates, away from the
origin.  A large-radius cutoff is necessary because `Gamma` has a pole at
zero. -/
theorem Complex.Gamma_openRightHalfPlane_log_norm_bound_from_Binet :
    ∃ R : ℝ, ∃ C : ℝ, ∃ m : ℕ,
      0 < R ∧ 0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
          R ≤ ‖z‖ →
            Real.log ‖Complex.Gamma z‖ ≤
              C * (1 + ‖z‖) ^ m := by
  exact
    Complex.Gamma_openRightHalfPlane_log_norm_bound_from_Binet_components

/-- Open-right-half-plane logarithmic Gamma growth from Binet-Stirling.

The literal principal-arctangent Binet remainder in this package is not a
closed-boundary kernel on the imaginary axis, so the sectorial log-norm owner
statement is intentionally open in the real part.  The large-radius cutoff is
also necessary because `Gamma` has a pole at zero. -/
theorem Complex.Gamma_closedRightHalfPlane_log_norm_bound_classical :
    ∃ R : ℝ, ∃ C : ℝ, ∃ m : ℕ,
      0 < R ∧ 0 < C ∧
      ∀ z : ℂ,
        0 < z.re →
          R ≤ ‖z‖ →
            Real.log ‖Complex.Gamma z‖ ≤
              C * (1 + ‖z‖) ^ m := by
  exact
    Complex.Gamma_openRightHalfPlane_log_norm_bound_from_Binet

end

end LFunctions
end Boundary
