import Boundary.LFunctions.ZetaExplicitFormulaComplexAnalysis
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne

/-!
# Boundary explicit-formula log derivative API

This file exposes the prime / archimedean / correction decomposition vocabulary
for the completed zeta logarithmic derivative. The actual analytic theorem will
prove that the completed negative logarithmic derivative expands as these
pieces; this file just names the pieces in owner form.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex

namespace ZetaAdmissibleFunction

/-- The prime-side logarithmic derivative contribution. -/
def explicitFormulaPrimeLogDerivative (s : ℂ) : ℂ :=
  - deriv riemannZeta s / riemannZeta s

/-- The archimedean logarithmic derivative contribution. -/
def explicitFormulaArchimedeanLogDerivative (s : ℂ) : ℂ :=
  (1 / 2 : ℂ) * Complex.log π - (1 / 2 : ℂ) * deriv (fun z : ℂ => Complex.log (Gamma ℝ z)) (s / 2)

/-- The pole correction logarithmic derivative contribution. -/
def explicitFormulaCorrectionLogDerivative (s : ℂ) : ℂ :=
  - 1 / s - 1 / (s - 1)

/-- The combined completed explicit-formula log derivative on the critical shift. -/
def explicitFormulaCompletedLogDerivative (s : ℂ) : ℂ :=
  explicitFormulaPrimeLogDerivative s +
    explicitFormulaArchimedeanLogDerivative s +
    explicitFormulaCorrectionLogDerivative s

/-- The product-side logarithmic derivative split for the `Λ · Γℝ⁻¹` factorization of `ζ`. -/
theorem riemannZeta_factorization_logDeriv
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1) (hΛ : completedRiemannZeta s ≠ 0)
    (hΓ : Gammaℝ s ≠ 0) :
    logDeriv (fun z : ℂ => completedRiemannZeta z * (Gammaℝ z)⁻¹) s =
      logDeriv completedRiemannZeta s + logDeriv (fun z : ℂ => (Gammaℝ z)⁻¹) s := by
  rw [logDeriv_mul s hΛ (by simpa using inv_ne_zero hΓ)
      (differentiableAt_completedZeta hs0 hs1) differentiable_Gammaℝ_inv.differentiableAt]


end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
