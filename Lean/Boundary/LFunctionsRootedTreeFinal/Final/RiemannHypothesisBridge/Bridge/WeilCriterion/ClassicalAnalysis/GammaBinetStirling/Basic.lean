import Mathlib.Analysis.Complex.PhragmenLindelof
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan
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

/-- Unfolding of the Binet logarithmic Gamma main term. -/
theorem Complex.binetLogGammaMainTerm_unfold
    (w : ℂ) :
    Complex.binetLogGammaMainTerm w =
      (w - (1 / 2 : ℂ)) * Complex.log w - w +
        (((Real.log (2 * Real.pi)) : ℝ) : ℂ) / 2 :=
  rfl

/-- The analytic Euler/Binet logarithm branch of `Gamma` on the right
half-plane.

Binet's second formula naturally constructs this logarithm branch.  It should
not be identified globally with Lean's principal `Complex.log (Complex.Gamma w)`
without a separate branch-coherence theorem, because the principal logarithm
has a branch cut while this analytic branch is transported from the positive
real axis. -/
noncomputable def Complex.binetLogGammaBranch (w : ℂ) : ℂ :=
  Complex.binetLogGammaMainTerm w +
    Complex.binetSecondFormulaRemainder w

end

end LFunctions
end Boundary
