import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Complex.Exponential

/-!
# Basic Gamma Binet-Stirling definitions

This file owns the basic sector and Binet/Stirling terms used by the
Gamma Binet-Stirling package.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- The closed right half-plane sector for the Binet/Stirling package. -/
def Complex.closedRightHalfPlaneSector (w : ℂ) : Prop :=
  0 ≤ w.re

/-- Binet's second-formula remainder for `log Γ`. -/
noncomputable def Complex.binetSecondFormulaRemainder (w : ℂ) : ℂ :=
  2 * ∫ t : ℝ in Set.Ioi (0 : ℝ),
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)

/-- The main term in Binet's logarithmic Stirling formula. -/
noncomputable def Complex.binetLogGammaMainTerm (w : ℂ) : ℂ :=
  (w - (1 / 2 : ℂ)) * Complex.log w - w +
    (((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2

end

end LFunctions
end Boundary
