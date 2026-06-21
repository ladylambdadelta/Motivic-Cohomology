import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.CenteredZeros.Owner
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Boundary explicit-formula normalization bridge

This file packages the completed-zeta normalization lemmas needed by the
analytic explicit-formula route. It does not prove the contour argument; it
just exposes the completed zeta identities in the owner namespace used by the
contour-shift proof chain.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The centered completed zeta decomposition in explicit-formula notation. -/
theorem zetaCompletedExplicitFormula_completedRiemannZeta_eq
    (s : ℂ) :
    completedRiemannZeta s = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) := by
  exact completedRiemannZeta_eq s

/-- The centered completed zeta is invariant under `s ↦ 1 - s`. -/
theorem zetaCompletedExplicitFormula_completedRiemannZeta_one_sub
    (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s := by
  exact completedRiemannZeta_one_sub s

/-- The completed zeta normalization centered at the critical line. -/
theorem zetaCompletedExplicitFormula_centered_eq
    (s : ℂ) :
    centeredCompletedRiemannZeta s =
      centeredCompletedRiemannZeta₀ s -
        1 / (1 / 2 + s) - 1 / (1 - (1 / 2 + s)) := by
  exact centeredCompletedRiemannZeta_eq s

/-- The centered completed zeta is reflection invariant. -/
theorem zetaCompletedExplicitFormula_centered_neg
    (s : ℂ) :
    centeredCompletedRiemannZeta (-s) = centeredCompletedRiemannZeta s := by
  exact centeredCompletedRiemannZeta_neg s

/-- The centered entire part is reflection invariant. -/
theorem zetaCompletedExplicitFormula_centered_entire_neg
    (s : ℂ) :
    centeredCompletedRiemannZeta₀ (-s) = centeredCompletedRiemannZeta₀ s := by
  exact centeredCompletedRiemannZeta₀_neg s

/-- The pole correction term is reflection invariant in centered form. -/
theorem zetaCompletedExplicitFormula_centered_correction_neg
    (s : ℂ) :
    1 / (1 / 2 + (-s)) + 1 / (1 - (1 / 2 + (-s))) =
      1 / (1 / 2 + s) + 1 / (1 - (1 / 2 + s)) := by
  exact centeredCompletedRiemannZeta_correction_symm s

/-- The completed zeta factorization through `riemannZeta` and `Gammaℝ`. -/
theorem completedRiemannZeta_mul_gamma_eq
    {s : ℂ} (hs : s ≠ 0) (hΓ : Complex.Gammaℝ s ≠ 0) :
    completedRiemannZeta s = riemannZeta s * Complex.Gammaℝ s := by
  have h := riemannZeta_def_of_ne_zero (s := s) hs
  have hmul := congrArg (fun x => x * Complex.Gammaℝ s) h
  have hcancel : (completedRiemannZeta s / Complex.Gammaℝ s) * Complex.Gammaℝ s =
      completedRiemannZeta s := by
    exact div_mul_cancel₀ _ hΓ
  exact (hmul.trans hcancel).symm

/-- The completed zeta factorization through `riemannZeta` and `Gammaℝ`. -/
theorem zetaCompletedExplicitFormula_completed_factorization
    {s : ℂ} (hs : s ≠ 0) (hΓ : Complex.Gammaℝ s ≠ 0) :
    completedRiemannZeta s = riemannZeta s * Complex.Gammaℝ s := by
  exact completedRiemannZeta_mul_gamma_eq hs hΓ

/-- The Riemann zeta function is the completed zeta divided by the archimedean factor. -/
theorem zetaCompletedExplicitFormula_riemannZeta_eq_completed_mul_invGamma
    {s : ℂ} (hs : s ≠ 0) :
    riemannZeta s = completedRiemannZeta s * (Complex.Gammaℝ s)⁻¹ := by
  exact riemannZeta_def_of_ne_zero (s := s) hs

/-- The logarithmic-line zeta-factor relation at the critical center. -/
theorem zetaCompletedExplicitFormula_centered_factorization
    (s : ℂ) (hs : (1 / 2 : ℂ) + s ≠ 0) (hΓ : Complex.Gammaℝ (1 / 2 + s) ≠ 0) :
    completedRiemannZeta (1 / 2 + s) =
      riemannZeta (1 / 2 + s) * Complex.Gammaℝ (1 / 2 + s) := by
  exact completedRiemannZeta_mul_gamma_eq hs hΓ

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
