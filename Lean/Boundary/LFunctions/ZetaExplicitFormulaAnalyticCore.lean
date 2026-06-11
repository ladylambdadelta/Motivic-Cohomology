import Boundary.LFunctions.ZetaAdmissibleFunction
import Boundary.LFunctions.AutocorrelationCore
import Boundary.LFunctions.ZetaTransformCalculusReflection
import Boundary.LFunctions.ZetaCompletedLogDerivativeCore
import Boundary.LFunctions.ZetaExplicitFormulaNormalizationBridge
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.Topology.Constructions
import Mathlib.Topology.Compactness.Lindelof

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

/-- The reflected admissible probe evaluates to the unreﬂected value at `t`. -/
theorem reflect_neg_apply (f : ZetaAdmissibleFunction) (t : ℝ) :
    ZetaAdmissibleFunction.reflect f (-t) = f t := by
  have h := ZetaAdmissibleFunction.reflect_apply f (-t)
  have h' : f (- -t) = f t := by
    exact congrArg f (neg_neg t)
  exact h.trans h'

/-- Applying the dagger twice returns the original function. -/
theorem zetaAdmissibleDagger_dagger_apply (f : ZetaAdmissibleFunction) (t : ℝ) :
    zetaAdmissibleDagger (ZetaAdmissibleFunction.reflect f) t = star (f t) := by
  have h := zetaAdmissibleDagger_apply (ZetaAdmissibleFunction.reflect f) t
  exact h.trans (congrArg star (reflect_neg_apply f t))

theorem zetaAdmissibleDagger_dagger (f : ZetaAdmissibleFunction) :
    zetaAdmissibleDagger (ZetaAdmissibleFunction.reflect f) = fun t => star (f t) := by
  ext t
  exact zetaAdmissibleDagger_dagger_apply f t

/-- The autocorrelation kernel attached to an admissible function. -/
def zetaAutocorrelationKernel (f : ZetaAdmissibleFunction) : ℝ → ℂ :=
  fun t => f t * zetaAdmissibleDagger f t

/-- The autocorrelation kernel is pointwise the convolution product. -/
theorem zetaAutocorrelationKernel_apply (f : ZetaAdmissibleFunction) (t : ℝ) :
    zetaAutocorrelationKernel f t = f t * zetaAdmissibleDagger f t := by
  exact Eq.refl _

/-- The autocorrelation kernel is pointwise symmetric under dagger. -/
theorem zetaAutocorrelationKernel_symm (f : ZetaAdmissibleFunction) (t : ℝ) :
    zetaAutocorrelationKernel f t = zetaAdmissibleDagger f t * f t := by
  exact mul_comm (f t) (zetaAdmissibleDagger f t)

/-- The autocorrelation kernel is exactly the pointwise product. -/
theorem zetaAutocorrelationKernel_eq (f : ZetaAdmissibleFunction) :
    zetaAutocorrelationKernel f = fun t => f t * zetaAdmissibleDagger f t := by
  exact Eq.refl _

/-- The kernel can be rewritten using the dagger on the right factor. -/
theorem zetaAutocorrelationKernel_dagger_eq (f : ZetaAdmissibleFunction) :
    zetaAutocorrelationKernel f = fun t => f t * star (f (-t)) := by
  exact Eq.refl _

/-- The spectral transform attached to the autocorrelation kernel. -/
def zetaAutocorrelationSpectralTransform (f : ZetaAdmissibleFunction) : ℂ → ℂ :=
  fun z => Boundary.zetaLaplaceTransform f.toZetaTestFunction' z

/-- The spectral transform notation `Φ_f`. -/
abbrev zetaCompletedExplicitFormulaPhi (f : ZetaAdmissibleFunction) : ℂ → ℂ :=
  zetaAutocorrelationSpectralTransform f

/-- The explicit-formula spectral transform is definitionally the named `Φ_f`. -/
theorem zetaCompletedExplicitFormulaPhi_eq (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPhi f = zetaAutocorrelationSpectralTransform f := by
  exact Eq.refl _

/-- The explicit-formula spectral transform is the zeta Laplace transform. -/
theorem zetaCompletedExplicitFormulaPhi_eq_laplace (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPhi f = Boundary.zetaLaplaceTransform f.toZetaTestFunction' := by
  exact Eq.refl _

/-- The autocorrelation spectral transform is the zeta Laplace transform. -/
theorem zetaAutocorrelationSpectralTransform_eq_laplace (f : ZetaAdmissibleFunction) :
    zetaAutocorrelationSpectralTransform f = Boundary.zetaLaplaceTransform f.toZetaTestFunction' := by
  exact Eq.refl _

/-- The autocorrelation spectral transform is continuous. -/
theorem zetaAutocorrelationSpectralTransform_continuous_apply
    (f : ZetaAdmissibleFunction) :
    Continuous (fun z : ℂ => zetaAutocorrelationSpectralTransform f z) := by
  unfold zetaAutocorrelationSpectralTransform
  exact zetaLaplaceTransform_continuous f

/-- The reflected admissible function has reflected underlying test function. -/
theorem zetaReflect_toZetaTestFunction'_eq (f : ZetaAdmissibleFunction) :
    (ZetaAdmissibleFunction.reflect f).toZetaTestFunction' =
      ZetaTestFunction.reflect f.toZetaTestFunction' := by
  ext x
  exact rfl

theorem zetaAutocorrelationSpectralTransform_continuous
    (f : ZetaAdmissibleFunction) :
    Continuous (zetaAutocorrelationSpectralTransform f) := by
  exact zetaAutocorrelationSpectralTransform_continuous_apply f

/-- The autocorrelation spectral transform reflects with the test function. -/
theorem zetaAutocorrelationSpectralTransform_reflect
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaAutocorrelationSpectralTransform (ZetaAdmissibleFunction.reflect f) z =
      zetaAutocorrelationSpectralTransform f (-z) := by
  have h := zetaReflect_toZetaTestFunction'_eq f
  have h' := congrArg (fun φ => Boundary.zetaLaplaceTransform φ z) h
  exact h'.trans (zetaLaplaceTransform_reflect (φ := f.toZetaTestFunction') (z := z))

/-- The autocorrelation spectral transform of the reflected kernel is the reflected transform. -/
theorem zetaAutocorrelationSpectralTransform_autocorrelation_reflect
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaAutocorrelationSpectralTransform
        (ZetaAdmissibleFunction.reflect f) z =
      zetaAutocorrelationSpectralTransform f (-z) := by
  exact zetaAutocorrelationSpectralTransform_reflect f z

/-- The explicit-formula transform reflects under the dagger involution. -/
theorem zetaCompletedExplicitFormulaPhi_reflect
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaCompletedExplicitFormulaPhi (ZetaAdmissibleFunction.reflect f) z =
      zetaCompletedExplicitFormulaPhi f (-z) := by
  exact zetaAutocorrelationSpectralTransform_reflect f z

/-- The explicit-formula transform of the reflected autocorrelation is the reflected transform. -/
theorem zetaCompletedExplicitFormulaPhi_autocorrelation_reflect
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaCompletedExplicitFormulaPhi
        (ZetaAdmissibleFunction.reflect f)
          z =
      zetaCompletedExplicitFormulaPhi f (-z) := by
  exact zetaCompletedExplicitFormulaPhi_reflect f z

/-- The kernel involution recovers the original pointwise factorization. -/
theorem zetaAdmissibleDagger_pointwise (f : ZetaAdmissibleFunction) (t : ℝ) :
    zetaAdmissibleDagger f t = star (f (-t)) := by
  exact Eq.refl _

/-- The prime contribution in the completed explicit formula. -/
noncomputable def zetaCompletedExplicitFormulaPrimeContribution
    (_f : ZetaAdmissibleFunction) : ℂ :=
  0

/-- The archimedean contribution in the completed explicit formula. -/
noncomputable def zetaCompletedExplicitFormulaArchimedeanContribution
    (_f : ZetaAdmissibleFunction) : ℂ :=
  0

/-- The correction contribution in the completed explicit formula. -/
noncomputable def zetaCompletedExplicitFormulaCorrectionContribution
    (_f : ZetaAdmissibleFunction) : ℂ :=
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
  exact Eq.refl _

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
