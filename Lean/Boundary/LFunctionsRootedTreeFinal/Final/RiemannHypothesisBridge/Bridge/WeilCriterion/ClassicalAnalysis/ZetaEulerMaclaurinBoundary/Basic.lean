import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.AbelSummation

/-!
# Basic boundary-line objects for Euler-Maclaurin estimates

This file owns the elementary objects shared by the boundary-line
Euler-Maclaurin package for zeta.
-/

namespace Boundary
namespace LFunctions

noncomputable section

/-- Boundary-line point in the classical zeta variable. -/
def Complex.boundaryLineOnePointRealParam
    (t : ℝ) : ℂ :=
  (1 : ℂ) + (t : ℂ) * Complex.I

/-- Guarded finite truncation used on the boundary line `1 + it`. -/
def Complex.riemannZetaBoundaryLineTruncation
    (t : ℝ)
    (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N,
    ((n : ℂ) ^ (Complex.boundaryLineOnePointRealParam t))⁻¹

end

end LFunctions
end Boundary
