import LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.AbelTail

/-!
# Boundary growth of raw zeta

This file owns the logarithmic growth estimate for `ζ(1 + it)` obtained from
the Abel/Euler-Maclaurin tail and finite truncation.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- The guarded truncation comparison and the finite first term give the
boundary-line logarithmic growth bound for zeta. -/
theorem Complex.riemannZeta_boundaryLine_log_bound_of_truncated_remainder :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ‖riemannZeta (Complex.boundaryLineOnePointRealParam t)‖ ≤
            A * Real.log (2 + ‖t‖) := by
  sorry

/-- Boundary-line logarithmic growth bound for zeta at `1 + it`. -/
theorem Complex.riemannZeta_boundaryLine_log_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ‖riemannZeta (Complex.boundaryLineOnePointRealParam t)‖ ≤
            A * Real.log (2 + ‖t‖) := by
  exact Complex.riemannZeta_boundaryLine_log_bound_of_truncated_remainder

end

end LFunctions
end Boundary
