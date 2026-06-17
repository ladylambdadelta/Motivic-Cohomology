import Boundary.LFunctionsRootedTreeCanonicalAll.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.ZetaCompletedNormalization
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# Boundary zeta transform calculus: zeta bridge

This file owns the completed-zeta and Dirichlet-series normalization lemmas
that are separate from the Mellin/Fourier transform calculus.
-/

namespace Boundary
namespace LFunctions

section Zeta

/-- Boundary name for the completed zeta decomposition. -/
theorem boundary_completedRiemannZeta_eq (s : ℂ) :
    completedRiemannZeta s = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) := by
  exact completedRiemannZeta_eq s

/-- Boundary name for the symmetry of the completed zeta function. -/
theorem boundary_completedRiemannZeta_one_sub (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s := by
  exact completedRiemannZeta_one_sub s

/-- Boundary name for zeta's functional equation identity in mathlib. -/
theorem boundary_riemannZeta_one_sub {s : ℂ} (hs : ∀ n : ℕ, s ≠ -n) (hs' : s ≠ 1) :
    riemannZeta (1 - s) =
      2 * (2 * Real.pi) ^ (-s) * Complex.Gamma s * Complex.cos (Real.pi * s / 2) *
        riemannZeta s := by
  exact riemannZeta_one_sub (s := s) hs hs'

/-- Boundary name for the Dirichlet-series expansion of zeta. -/
theorem boundary_riemannZeta_eq_tsum_one_div_nat_cpow {s : ℂ} (hs : 1 < s.re) :
    riemannZeta s = ∑' n : ℕ, 1 / (n : ℂ) ^ s := by
  exact zeta_eq_tsum_one_div_nat_cpow (s := s) hs

end Zeta

end LFunctions
end Boundary
