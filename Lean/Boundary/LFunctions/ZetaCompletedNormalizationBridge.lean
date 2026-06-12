import Boundary.LFunctions.ZetaCompletedNormalization
import Boundary.LFunctions.ZetaCompletedLogDerivativeCore
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.NumberTheory.LSeries.RiemannZeta

/-!
# Boundary completed normalization bridge

This file owns the direct factorization bridge between the completed zeta and
the ordinary zeta/Gamma product. It sits below the contour file so the
punctured-plane and contour owner files can consume it without importing the
full Weil-criterion surface.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex

namespace ZetaAdmissibleFunction

/-- The finite zeta-side factor obtained from the completed zeta by removing `Γℝ`. -/
def zetaSideFactor (s : ℂ) : ℂ :=
  completedRiemannZeta s * (Gammaℝ s)⁻¹

/-- The negative logarithmic derivative of the finite zeta-side factor. -/
def zetaSideNegLogDeriv (s : ℂ) : ℂ :=
  - deriv zetaSideFactor s / zetaSideFactor s

theorem zetaSideFactor_eq (s : ℂ) :
    zetaSideFactor s = completedRiemannZeta s * (Gammaℝ s)⁻¹ := by
  rfl

theorem zetaSideFactor_ne_zero {s : ℂ}
    (hΛ : completedRiemannZeta s ≠ 0) (hΓ : Gammaℝ s ≠ 0) :
    zetaSideFactor s ≠ 0 := by
  exact mul_ne_zero hΛ (inv_ne_zero hΓ)

/-- Away from the singular point of the completed normalization, removing the Gamma factor
from the completed zeta recovers the ordinary Riemann zeta function. -/
theorem zetaSideFactor_eq_riemannZeta {s : ℂ}
    (hs : s ≠ 0) (hΓ : Gammaℝ s ≠ 0) :
    zetaSideFactor s = riemannZeta s := by
  have hcompleted :
      completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
    have h := riemannZeta_def_of_ne_zero hs
    exact (div_eq_iff hΓ).mp h.symm
  unfold zetaSideFactor
  calc
    completedRiemannZeta s * (Gammaℝ s)⁻¹ =
        (riemannZeta s * Gammaℝ s) * (Gammaℝ s)⁻¹ := by
      exact congrArg (fun x : ℂ => x * (Gammaℝ s)⁻¹) hcompleted
    _ = riemannZeta s * (Gammaℝ s * (Gammaℝ s)⁻¹) := by
      exact mul_assoc (riemannZeta s) (Gammaℝ s) (Gammaℝ s)⁻¹
    _ = riemannZeta s * 1 := by
      exact congrArg (fun x : ℂ => riemannZeta s * x) (mul_inv_cancel₀ hΓ)
    _ = riemannZeta s := by
      exact mul_one (riemannZeta s)

theorem deriv_zetaSideFactor_at {s : ℂ}
    (hs0 : s ≠ 0) (hs1 : s ≠ 1) (_hΓ : Gammaℝ s ≠ 0) :
    deriv zetaSideFactor s =
      deriv completedRiemannZeta s * (Gammaℝ s)⁻¹ +
        completedRiemannZeta s * deriv (fun z : ℂ => (Gammaℝ z)⁻¹) s := by
  unfold zetaSideFactor
  exact
    deriv_mul (differentiableAt_completedZeta hs0 hs1)
      differentiable_Gammaℝ_inv.differentiableAt

/-- Removing the Gamma factor adds the explicit archimedean correction to the negative
logarithmic derivative. This inverse-Gamma form is the owner-level statement available from
Mathlib's `Gammaℝ` API; it is equivalent to the usual `+ Γ'/Γ` correction once a direct
`Gammaℝ` differentiability theorem is imported. -/
theorem zetaSideNegLogDeriv_eq_completed_sub_invGamma_correction
    {s : ℂ} (hs0 : s ≠ 0) (hs1 : s ≠ 1)
    (hΛ : completedRiemannZeta s ≠ 0) (hΓ : Gammaℝ s ≠ 0) :
    zetaSideNegLogDeriv s =
      completedZetaNegLogDeriv s -
        deriv (fun z : ℂ => (Gammaℝ z)⁻¹) s / (Gammaℝ s)⁻¹ := by
  unfold zetaSideNegLogDeriv completedZetaNegLogDeriv
  rw [deriv_zetaSideFactor_at hs0 hs1 hΓ]
  unfold zetaSideFactor
  field_simp [hΛ, hΓ]
  ring

end ZetaAdmissibleFunction

/-- The completed Riemann zeta factors as `ζ · Γℝ` away from `0`. -/
theorem completedRiemannZeta_eq_riemannZeta_mul_gamma {s : ℂ}
    (hs : s ≠ 0) (hΓ : Gammaℝ s ≠ 0) :
    completedRiemannZeta s = riemannZeta s * Gammaℝ s := by
  have h := riemannZeta_def_of_ne_zero hs
  exact (div_eq_iff hΓ).mp h.symm

end
end LFunctions
end Boundary
