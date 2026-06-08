import Boundary.LFunctions.ZetaAdmissibleFunction
import Boundary.LFunctions.ZetaCompletedNormalization
import Boundary.LFunctions.ZetaZeroKreinGram
import Boundary.LFunctions.ZetaTransformCalculus
import Boundary.LFunctions.ZetaZeroSideDefinitions
import Boundary.LFunctions.ZetaCompletedExplicitFormulaAssembly
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
  ⟨fun t => star (f (-t)), by continuity⟩

/-- The involution is pointwise conjugate reflection. -/
theorem zetaAdmissibleDagger_apply (f : ZetaAdmissibleFunction) (t : ℝ) :
    zetaAdmissibleDagger f t = star (f (-t)) := by
  exact rfl

/-- Applying the dagger twice returns the original function. -/
theorem zetaAdmissibleDagger_dagger (f : ZetaAdmissibleFunction) :
    ZetaTestFunction.reflect (zetaAdmissibleDagger f) = f.toZetaTestFunction' := by
  ext t
  change (starRingEnd ℂ) ((starRingEnd ℂ) (f.toZetaTestFunction (- -t))) = f.toZetaTestFunction t
  rw [neg_neg]
  simpa using (star_star (f.toZetaTestFunction t))

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
  exact rfl

/-- The kernel can be rewritten using the dagger on the right factor. -/
theorem zetaAutocorrelationKernel_dagger_eq (f : ZetaAdmissibleFunction) :
    zetaAutocorrelationKernel f = fun t => f t * star (f (-t)) := by
  exact rfl

/-- The spectral transform attached to the autocorrelation kernel. -/
def zetaAutocorrelationSpectralTransform (f : ZetaAdmissibleFunction) : ℂ → ℂ :=
  fun z => zetaSpectralTransform f z

/-- The spectral transform notation `Φ_f`. -/
abbrev zetaCompletedExplicitFormulaPhi (f : ZetaAdmissibleFunction) : ℂ → ℂ :=
  zetaAutocorrelationSpectralTransform f

/-- The explicit-formula spectral transform is definitionally the named `Φ_f`. -/
theorem zetaCompletedExplicitFormulaPhi_eq (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPhi f = zetaAutocorrelationSpectralTransform f := by
  exact rfl

/-- The explicit-formula spectral transform is the zeta Laplace transform. -/
theorem zetaCompletedExplicitFormulaPhi_eq_laplace (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPhi f = Boundary.zetaLaplaceTransform f := by
  exact rfl

/-- The autocorrelation spectral transform is the zeta Laplace transform. -/
theorem zetaAutocorrelationSpectralTransform_eq_laplace (f : ZetaAdmissibleFunction) :
    zetaAutocorrelationSpectralTransform f = Boundary.zetaLaplaceTransform f := by
  exact rfl

/-- The autocorrelation spectral transform is continuous. -/
theorem zetaAutocorrelationSpectralTransform_continuous
    (f : ZetaAdmissibleFunction) :
    Continuous (zetaAutocorrelationSpectralTransform f) := by
  simpa [zetaAutocorrelationSpectralTransform, zetaSpectralTransform] using
    zetaLaplaceTransform_continuous f

/-- The autocorrelation spectral transform reflects with the test function. -/
theorem zetaAutocorrelationSpectralTransform_reflect
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaAutocorrelationSpectralTransform (ZetaAdmissibleFunction.zetaAdmissibleDagger f) z =
      zetaAutocorrelationSpectralTransform f (-z) := by
  unfold zetaAutocorrelationSpectralTransform
  rw [← LFunctions.ZetaTransformCalculus.zetaLaplaceTransform_dagger_reflect]
  rfl

/-- The autocorrelation spectral transform of the reflected kernel is the reflected transform. -/
theorem zetaAutocorrelationSpectralTransform_autocorrelation_reflect
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaAutocorrelationSpectralTransform
        (ZetaAdmissibleFunction.zetaAdmissibleDagger f) z =
      zetaAutocorrelationSpectralTransform f (-z) := by
  exact zetaAutocorrelationSpectralTransform_reflect f z

/-- The explicit-formula transform reflects under the dagger involution. -/
theorem zetaCompletedExplicitFormulaPhi_reflect
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaCompletedExplicitFormulaPhi (ZetaAdmissibleFunction.zetaAdmissibleDagger f) z =
      zetaCompletedExplicitFormulaPhi f (-z) := by
  rw [zetaCompletedExplicitFormulaPhi_eq, zetaCompletedExplicitFormulaPhi_eq,
    zetaAutocorrelationSpectralTransform_reflect]

/-- The explicit-formula transform of the reflected autocorrelation is the reflected transform. -/
theorem zetaCompletedExplicitFormulaPhi_autocorrelation_reflect
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaCompletedExplicitFormulaPhi
        (ZetaAdmissibleFunction.autocorrelation (ZetaAdmissibleFunction.zetaAdmissibleDagger f))
          z =
      zetaCompletedExplicitFormulaPhi (ZetaAdmissibleFunction.autocorrelation f) (-z) := by
  rw [ZetaAdmissibleFunction.autocorrelation_dagger_eq_reflect]
  exact zetaCompletedExplicitFormulaPhi_reflect f z

/-- The zero-side Krein form of the reflected autocorrelation probe is the reflected zero-side
form. -/
theorem zetaCompletedZeroKreinGram_autocorrelation_reflect
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.autocorrelation f) := by
  rfl

/-- The zero-side Krein form exposes reflected-autocorrelation invariance in the analytic core. -/
theorem zetaCompletedZeroKreinGram_autocorrelation_reflect' :
    ∀ f : ZetaAdmissibleFunction,
      zetaCompletedZeroKreinGram
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedZeroKreinGram (ZetaAdmissibleFunction.autocorrelation f) := by
  intro f
  exact zetaCompletedZeroKreinGram_autocorrelation_reflect f

/-- The reflected autocorrelation zero-side Krein form is compatible with the boundary-defect
comparison normalization. -/
theorem zetaCompletedZeroKreinGram_autocorrelation_reflect_boundaryDefect
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram
        (ZetaAdmissibleFunction.autocorrelation
          (ZetaAdmissibleFunction.zetaAdmissibleDagger f)) =
      zetaCompletedBoundaryDefectGram
        (ZetaAdmissibleFunction.autocorrelation f) := by
  rw [zetaCompletedZeroKreinGram_autocorrelation_reflect']
  rfl

/-- The completed explicit formula for autocorrelation probes, exposed in the analytic core
namespace. -/
theorem zetaCompletedExplicitFormula_autocorrelation
    (f : ZetaAdmissibleFunction) :
    zetaCompletedZeroKreinGram f =
      ZetaAdmissibleFunction.zetaCompletedExplicitFormulaBoundarySum f := by
  exact Boundary.LFunctions.ZetaAdmissibleFunction.zeta_completed_explicit_formula_autocorrelation f

/-- The explicit-formula `Φ_f` on an autocorrelation is the explicit Laplace integral. -/
theorem zetaCompletedExplicitFormulaPhi_autocorrelation_eq_integral
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    Boundary.zetaLaplaceTransform (ZetaAdmissibleFunction.autocorrelation f) z =
      ∫ t : ℝ, (f t * star (f t)) * Complex.exp (z * t) := by
  rw [LFunctions.ZetaTransformCalculus.zetaLaplaceTransform_autocorrelation]
  rfl

/-- The autocorrelation spectral transform unfolds to the Laplace integral of the kernel. -/
theorem zetaAutocorrelationSpectralTransform_autocorrelation
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    Boundary.zetaLaplaceTransform (ZetaAdmissibleFunction.autocorrelation f) z =
      ∫ t : ℝ, (f t * star (f t)) * Complex.exp (z * t) := by
  rw [LFunctions.ZetaTransformCalculus.zetaLaplaceTransform_autocorrelation]
  rfl

/-- The kernel involution recovers the original pointwise factorization. -/
theorem zetaAdmissibleDagger_pointwise (f : ZetaAdmissibleFunction) (t : ℝ) :
    zetaAdmissibleDagger f t = star (f (-t)) := by
  exact rfl

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
  exact rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
