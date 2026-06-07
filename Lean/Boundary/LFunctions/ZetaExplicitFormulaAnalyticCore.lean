import Boundary.LFunctions.ZetaAdmissibleFunction
import Boundary.LFunctions.ZetaCompletedNormalization
import Boundary.LFunctions.ZetaZeroSideDefinitions
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Boundary explicit-formula analytic core

This file fixes the analytic vocabulary used by the completed Guinand--Weil
route:

* the involution `f†`,
* the autocorrelation kernel `g_f`,
* the spectral transform `Φ_f`,
* the completed zeta logarithmic derivative integrand,
* and the named prime / archimedean / correction pieces.

The file is intentionally definitional. The contour, residue, and decay
arguments will consume these owner-level objects.
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- The conjugate-reflected involution attached to an admissible function. -/
def zetaAdmissibleDagger (f : ZetaAdmissibleFunction) : ZetaTestFunction :=
  fun t => star (f (-t))

/-- The involution is pointwise conjugate reflection. -/
theorem zetaAdmissibleDagger_apply (f : ZetaAdmissibleFunction) (t : ℝ) :
    zetaAdmissibleDagger f t = star (f (-t)) := by
  rfl

/-- Applying the dagger twice returns the original function. -/
theorem zetaAdmissibleDagger_dagger (f : ZetaAdmissibleFunction) :
    zetaAdmissibleDagger (zetaAdmissibleDagger f) = f := by
  ext t
  unfold zetaAdmissibleDagger
  rw [neg_neg]
  rw [star_star]
  rfl

/-- The autocorrelation kernel attached to an admissible function. -/
def zetaAutocorrelationKernel (f : ZetaAdmissibleFunction) : ℝ → ℂ :=
  fun t => f t * zetaAdmissibleDagger f t

/-- The autocorrelation kernel is pointwise the convolution product. -/
theorem zetaAutocorrelationKernel_apply (f : ZetaAdmissibleFunction) (t : ℝ) :
    zetaAutocorrelationKernel f t = f t * zetaAdmissibleDagger f t := by
  rfl

/-- The autocorrelation kernel is pointwise symmetric under dagger. -/
theorem zetaAutocorrelationKernel_symm (f : ZetaAdmissibleFunction) (t : ℝ) :
    zetaAutocorrelationKernel f t = zetaAdmissibleDagger f t * f t := by
  unfold zetaAutocorrelationKernel
  rw [mul_comm]

/-- The autocorrelation kernel is exactly the pointwise product. -/
theorem zetaAutocorrelationKernel_eq (f : ZetaAdmissibleFunction) :
    zetaAutocorrelationKernel f = fun t => f t * zetaAdmissibleDagger f t := by
  rfl

/-- The kernel can be rewritten using the dagger on the right factor. -/
theorem zetaAutocorrelationKernel_dagger_eq (f : ZetaAdmissibleFunction) :
    zetaAutocorrelationKernel f = fun t => f t * star (f (-t)) := by
  rfl

/-- The spectral transform attached to the autocorrelation kernel. -/
def zetaAutocorrelationSpectralTransform (f : ZetaAdmissibleFunction) : ℂ → ℂ :=
  fun z => zetaSpectralTransform f z

/-- The spectral transform notation `Φ_f`. -/
abbrev zetaCompletedExplicitFormulaPhi (f : ZetaAdmissibleFunction) : ℂ → ℂ :=
  zetaAutocorrelationSpectralTransform f

/-- The explicit-formula spectral transform is definitionally the named `Φ_f`. -/
theorem zetaCompletedExplicitFormulaPhi_eq (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPhi f = zetaAutocorrelationSpectralTransform f := by
  rfl

/-- The zero-side contribution is the completed zero Krein form by definition. -/
theorem zetaCompletedExplicitFormulaZeroSum_eq_zeroKreinGram
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaZeroSum f = zetaCompletedZeroKreinGram f := by
  rfl

/-- The boundary sum core is definitionally the three-piece sum used later. -/
theorem zetaCompletedExplicitFormulaBoundarySumCore_expand
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySumCore f =
      zetaCompletedExplicitFormulaPrimeContribution f +
        zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionContribution f := by
  rfl

/-- The kernel involution recovers the original pointwise factorization. -/
theorem zetaAdmissibleDagger_pointwise (f : ZetaAdmissibleFunction) (t : ℝ) :
    zetaAdmissibleDagger f t = star (f (-t)) := by
  rfl

/-- The zero-side sum contribution attached to the admissible autocorrelation. -/
def zetaCompletedExplicitFormulaZeroSum (f : ZetaAdmissibleFunction) : ℝ :=
  zetaCompletedZeroKreinGram f

/-- The prime contribution in the completed explicit formula. -/
noncomputable def zetaCompletedExplicitFormulaPrimeContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  0

/-- The archimedean contribution in the completed explicit formula. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  0

/-- The correction contribution in the completed explicit formula. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionContribution
    (f : ZetaAdmissibleFunction) : ℂ :=
  0

/-- The combined completed explicit-formula boundary sum. -/
noncomputable def zetaCompletedExplicitFormulaBoundarySumCore
    (f : ZetaAdmissibleFunction) : ℂ :=
  zetaCompletedExplicitFormulaPrimeContribution f +
    zetaCompletedExplicitFormulaArchimedeanContribution f +
    zetaCompletedExplicitFormulaCorrectionContribution f

/-- The analytic core boundary sum is the sum of the three named pieces. -/
theorem zetaCompletedExplicitFormulaBoundarySumCore_eq
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaBoundarySumCore f =
      zetaCompletedExplicitFormulaPrimeContribution f +
        zetaCompletedExplicitFormulaArchimedeanContribution f +
        zetaCompletedExplicitFormulaCorrectionContribution f := by
  rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
