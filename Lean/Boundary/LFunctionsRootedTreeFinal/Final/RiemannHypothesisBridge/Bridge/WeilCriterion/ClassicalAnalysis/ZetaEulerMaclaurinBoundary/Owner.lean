import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.AbelSummation

/-!
# Euler-Maclaurin boundary estimates for zeta

This file owns the classical estimates for zeta on the boundary line
`s = 1 + it`.  The guard `1 ≤ ‖t‖` is part of the owner surface: no
Dirichlet-series or tail statement here applies at `t = 0`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Boundary-line point in the classical zeta variable. -/
noncomputable def Complex.boundaryLineOnePointRealParam
    (t : ℝ) : ℂ :=
  (1 : ℂ) + (t : ℂ) * Complex.I

/-- Guarded finite truncation used on the boundary line `1 + it`. -/
noncomputable def Complex.riemannZetaBoundaryLineTruncation
    (t : ℝ)
    (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    ((n : ℂ) ^ (-(Complex.boundaryLineOnePointRealParam t)))⁻¹

/-- First-derivative estimate for the logarithmic phase sums on the boundary
line. -/
theorem Complex.boundaryLineOnePointRealParam_logarithmicPhasePartialSum_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            ‖∑ n ∈ Finset.Icc 1 N,
              ((n : ℂ) ^ (-(t : ℂ) * Complex.I))‖ ≤
                A * (1 + Real.log (2 + N)) := by
  sorry

/-- Euler-Maclaurin post-cutoff tail for zeta on the boundary line, with the
nonzero-frequency guard exposed. -/
theorem Complex.boundaryLineOnePointRealParam_eulerMaclaurinTail_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            1 ≤ N →
              ‖∑' n : ℕ,
                if N < n then
                  ((n : ℂ) ^ (-(Complex.boundaryLineOnePointRealParam t)))⁻¹
                else
                  0‖ ≤
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
  sorry

/-- Guarded finite truncation comparison for zeta on the boundary line. -/
theorem Complex.riemannZeta_boundaryLine_truncated_dirichlet_remainder_bound :
    ∃ A : ℝ,
      0 < A ∧
      ∀ t : ℝ,
        1 ≤ ‖t‖ →
          ∀ N : ℕ,
            1 ≤ N →
              ‖riemannZeta (Complex.boundaryLineOnePointRealParam t) -
                Complex.riemannZetaBoundaryLineTruncation t N‖ ≤
                  A * Real.log (2 + ‖t‖) := by
  sorry

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
