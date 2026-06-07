import Boundary.LFunctions.ZetaExplicitFormulaAnalyticCore
import Boundary.LFunctions.ZetaCompletedNormalization
import Boundary.LFunctions.ZetaTransformCalculus

/-!
# Boundary explicit-formula normalization bridge

This file packages the completed-zeta normalization lemmas needed by the
analytic explicit-formula route. It does not prove the contour argument; it
just exposes the completed zeta identities in the owner namespace where the
future proof will consume them.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The centered completed zeta decomposition in explicit-formula notation. -/
theorem zetaCompletedExplicitFormula_completedRiemannZeta_eq
    (s : ℂ) :
    completedRiemannZeta s = completedRiemannZeta₀ s - 1 / s - 1 / (1 - s) := by
  exact boundary_completedRiemannZeta_eq s

/-- The centered completed zeta is invariant under `s ↦ 1 - s`. -/
theorem zetaCompletedExplicitFormula_completedRiemannZeta_one_sub
    (s : ℂ) :
    completedRiemannZeta (1 - s) = completedRiemannZeta s := by
  exact boundary_completedRiemannZeta_one_sub s

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
theorem zetaCompletedExplicitFormula_completed_factorization
    {s : ℂ} (hs : s ≠ 0) (hΓ : Gammaℝ s ≠ 0) :
    completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
  exact completedRiemannZeta_eq_riemannZeta_mul_gamma hs hΓ

/-- The Riemann zeta function is the completed zeta divided by the archimedean factor. -/
theorem zetaCompletedExplicitFormula_riemannZeta_eq_completed_mul_invGamma
    {s : ℂ} (hs : s ≠ 0) (hΓ : Gammaℝ s ≠ 0) :
    riemannZeta s = completedRiemannZeta s * (Gammaℝ s)⁻¹ := by
  rw [riemannZeta_def_of_ne_zero hs]
  field_simp [hΓ]
  ring

/-- The logarithmic-line zeta-factor relation at the critical center. -/
theorem zetaCompletedExplicitFormula_centered_factorization
    (s : ℂ) (hs : (1 / 2 : ℂ) + s ≠ 0) (hΓ : Gammaℝ (1 / 2 + s) ≠ 0) :
    completedRiemannZeta (1 / 2 + s) =
      riemannZeta (1 / 2 + s) * Gammaℝ (1 / 2 + s) := by
  exact completedRiemannZeta_eq_riemannZeta_mul_gamma hs hΓ

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
