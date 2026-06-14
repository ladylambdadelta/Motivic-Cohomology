import LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.ZetaEulerMaclaurinBoundary.BoundaryGrowth

/-!
# Pole-cleared Euler-Maclaurin boundary growth

This file owns the boundary-line polynomial growth estimate for
`(s - 1) ζ(s)` exported to completed-normalization consumers.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Pole-cleared boundary-line polynomial growth in the right critical strip,
as exported to completed normalization. -/
theorem Complex.poleClearedRiemannZeta_boundaryLine_growth_bound :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ‖((Complex.boundaryLineOnePointRealParam t - 1) *
              riemannZeta (Complex.boundaryLineOnePointRealParam t))‖ ≤
            A * (1 + ‖t‖) ^ m := by
  sorry

end

end LFunctions
end Boundary
