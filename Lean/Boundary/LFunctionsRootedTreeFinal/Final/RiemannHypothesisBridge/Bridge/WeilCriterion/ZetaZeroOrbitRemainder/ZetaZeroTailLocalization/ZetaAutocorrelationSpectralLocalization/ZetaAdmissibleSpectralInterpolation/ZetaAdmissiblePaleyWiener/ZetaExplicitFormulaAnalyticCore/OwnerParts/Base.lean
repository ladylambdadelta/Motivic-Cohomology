import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ProbeInterface.ZetaAdmissibleFunction.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.AutocorrelationInterface.AutocorrelationCore.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.ZetaTransformCalculusReflection.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaAdmissibleSpectralInterpolation.ZetaAdmissiblePaleyWiener.ZetaExplicitFormulaAnalyticCore.ZetaLogBoundaryDefect.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaZeroOrbitRemainder.ZetaZeroTailLocalization.ZetaAutocorrelationSpectralLocalization.ZetaCompletedHilbertSource.ZetaHermitianPacket.ZetaPrimePowerWindow.Owner
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.NormedSpace.Connected
import Mathlib.Analysis.Calculus.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import Mathlib.Analysis.SpecialFunctions.Gamma.Deriv
import Mathlib.MeasureTheory.Integral.Bochner
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

/-! This owner part contains the base definitions and transform vocabulary. -/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction


/-- The conjugate-reflected involution attached to an admissible function. -/
abbrev zetaAdmissibleDagger (f : ZetaAdmissibleFunction) : ZetaAdmissibleFunction :=
  ZetaAdmissibleFunction.dagger f

/-- The involution is pointwise conjugate reflection. -/
theorem zetaAdmissibleDagger_apply (f : ZetaAdmissibleFunction) (t : ℝ) :
    zetaAdmissibleDagger f t = star (f (-t)) := by
  exact ZetaAdmissibleFunction.dagger_apply f t

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
    ⇑(zetaAdmissibleDagger (ZetaAdmissibleFunction.reflect f)) = fun t => star (f t) := by
  ext t
  exact zetaAdmissibleDagger_dagger_apply f t

/-- The pointwise autocorrelation presentation attached to an admissible function.

This is not the convolution autocorrelation kernel used by the RH-lane
holography theorem. -/
def zetaAutocorrelationKernel (f : ZetaAdmissibleFunction) : ℝ → ℂ :=
  fun t => f t * zetaAdmissibleDagger f t

/-- The pointwise autocorrelation kernel is the product with the dagger. -/
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
  ext t
  calc
    zetaAutocorrelationKernel f t =
        f t * zetaAdmissibleDagger f t := by
      exact zetaAutocorrelationKernel_apply f t
    _ = f t * star (f (-t)) := by
      exact congrArg (fun z : ℂ => f t * z) (zetaAdmissibleDagger_apply f t)

/-- The spectral transform attached to the autocorrelation kernel. -/
def zetaAutocorrelationSpectralTransform (f : ZetaAdmissibleFunction) : ℂ → ℂ :=
  fun z => Boundary.zetaLaplaceTransform f.toZetaTestFunction' z

/-- The time/log-side boundary value of an admissible probe.  This is the raw value on the
logarithmic line; it is deliberately separate from the spectral/Laplace transform. -/
def zetaCompletedTimeBoundaryValue (f : ZetaAdmissibleFunction) (a : ℝ) : ℂ :=
  f.toZetaTestFunction' a

/-- The spectral/Laplace-side transform of an admissible probe. -/
def zetaCompletedSpectralLaplaceTransform (f : ZetaAdmissibleFunction) : ℂ → ℂ :=
  fun z => Boundary.zetaLaplaceTransform f.toZetaTestFunction' z

/- The time-side value and spectral/Laplace transform are distinct realizations.  The
completed explicit formula compares their completed prime distributions; it does not identify
`zetaCompletedTimeBoundaryValue f a` with `zetaCompletedSpectralLaplaceTransform f (a : ℂ)`.
-/

/-- The spectral transform notation `Φ_f`. -/
abbrev zetaCompletedExplicitFormulaPhi (f : ZetaAdmissibleFunction) : ℂ → ℂ :=
  zetaAutocorrelationSpectralTransform f

/-- The `Φ` notation is the spectral/Laplace transform, not a time-side boundary value. -/
theorem zetaCompletedExplicitFormulaPhi_eq_spectralLaplaceTransform
    (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPhi f =
      zetaCompletedSpectralLaplaceTransform f := by
  rfl

/-- The time-side value unfolds to the underlying test function. -/
theorem zetaCompletedTimeBoundaryValue_eq_apply
    (f : ZetaAdmissibleFunction) (a : ℝ) :
    zetaCompletedTimeBoundaryValue f a = f a := by
  calc
    zetaCompletedTimeBoundaryValue f a = f.toZetaTestFunction' a := rfl
    _ = f a := ZetaAdmissibleFunction.toZetaTestFunction'_apply f a

/-- The zero admissible probe has zero time-side boundary value. -/
theorem zetaCompletedTimeBoundaryValue_zero
    (a : ℝ) :
    zetaCompletedTimeBoundaryValue (0 : ZetaAdmissibleFunction) a = 0 := by
  exact zetaCompletedTimeBoundaryValue_eq_apply 0 a

/-- The time-side value of the convolution autocorrelation is the autocorrelation kernel. -/
theorem zetaCompletedTimeBoundaryValue_convolutionAutocorrelation_eq_kernel
    (f : ZetaAdmissibleFunction) (a : ℝ) :
    zetaCompletedTimeBoundaryValue
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) a =
      ZetaAdmissibleFunction.convolutionAutocorrelationKernel f a := by
  have htime :
      zetaCompletedTimeBoundaryValue
          (ZetaAdmissibleFunction.convolutionAutocorrelation f) a =
        (ZetaAdmissibleFunction.convolutionAutocorrelation f).toZetaTestFunction' a := rfl
  have htest :
      (ZetaAdmissibleFunction.convolutionAutocorrelation f).toZetaTestFunction' a =
        ZetaAdmissibleFunction.convolutionAutocorrelationKernel f a :=
    (ZetaAdmissibleFunction.convolutionAutocorrelation_toZetaTestFunction'_apply
      f a).trans
      (ZetaAdmissibleFunction.convolutionAutocorrelationKernel_apply f a)
  exact htime.trans htest

/-- The explicit-formula spectral transform is definitionally the named `Φ_f`. -/
theorem zetaCompletedExplicitFormulaPhi_eq (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPhi f = zetaAutocorrelationSpectralTransform f := by
  exact Eq.refl _

/-- The explicit-formula spectral transform is the zeta Laplace transform. -/
theorem zetaCompletedExplicitFormulaPhi_eq_laplace (f : ZetaAdmissibleFunction) :
    zetaCompletedExplicitFormulaPhi f = Boundary.zetaLaplaceTransform f.toZetaTestFunction' := by
  exact Eq.refl _

/-- The zero admissible probe has zero spectral/Laplace transform. -/
theorem zetaCompletedExplicitFormulaPhi_zero
    (z : ℂ) :
    zetaCompletedExplicitFormulaPhi (0 : ZetaAdmissibleFunction) z = 0 := by
  have hphi :
      zetaCompletedExplicitFormulaPhi (0 : ZetaAdmissibleFunction) z =
        Boundary.zetaLaplaceTransform
          (0 : ZetaAdmissibleFunction).toZetaTestFunction' z := rfl
  have hlaplace :
      Boundary.zetaLaplaceTransform
          (0 : ZetaAdmissibleFunction).toZetaTestFunction' z = 0 := by
    show
      (∫ t : ℝ,
          (0 : ZetaAdmissibleFunction).toZetaTestFunction' t *
            Complex.exp (z * t)) = 0
    calc
      (∫ t : ℝ,
          (0 : ZetaAdmissibleFunction).toZetaTestFunction' t *
            Complex.exp (z * t)) =
          ∫ _t : ℝ, 0 := by
        exact MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall
            (fun t : ℝ =>
              calc
                (0 : ZetaAdmissibleFunction).toZetaTestFunction' t *
                    Complex.exp (z * t) =
                    (0 : ℂ) * Complex.exp (z * t) := by
                  exact congrArg
                    (fun x : ℂ => x * Complex.exp (z * t))
                    (ZetaAdmissibleFunction.toZetaTestFunction'_apply 0 t)
                _ = 0 := zero_mul (Complex.exp (z * t))))
      _ = 0 := by
        exact MeasureTheory.integral_zero ℝ ℂ
  exact hphi.trans hlaplace

/-- The spectral transform of the convolution autocorrelation pairs opposite real spectral
parameters. -/
theorem zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation_real_pair
    (f : ZetaAdmissibleFunction) (a : ℝ) :
    zetaCompletedExplicitFormulaPhi
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) (a : ℂ) =
      zetaCompletedExplicitFormulaPhi f (a : ℂ) *
        star (zetaCompletedExplicitFormulaPhi f (-(a : ℂ))) := by
  exact Boundary.zetaLaplaceTransform_convolutionAutocorrelation_real_pair f a

/-- The spectral transform of the convolution autocorrelation factors at every complex
parameter as a seed transform times its dagger-reflected conjugate. -/
theorem zetaCompletedExplicitFormulaPhi_convolutionAutocorrelation
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaCompletedExplicitFormulaPhi
        (ZetaAdmissibleFunction.convolutionAutocorrelation f) z =
      zetaCompletedExplicitFormulaPhi f z *
        star (zetaCompletedExplicitFormulaPhi f (-star z)) := by
  exact Boundary.zetaLaplaceTransform_convolutionAutocorrelation f z

/-- The autocorrelation spectral transform is the zeta Laplace transform. -/
theorem zetaAutocorrelationSpectralTransform_eq_laplace (f : ZetaAdmissibleFunction) :
    zetaAutocorrelationSpectralTransform f = Boundary.zetaLaplaceTransform f.toZetaTestFunction' := by
  exact Eq.refl _

/-- The autocorrelation spectral transform is continuous. -/
theorem zetaAutocorrelationSpectralTransform_continuous_apply
    (f : ZetaAdmissibleFunction) :
    Continuous (fun z : ℂ => zetaAutocorrelationSpectralTransform f z) := by
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

/-- The explicit-formula transform of the dagger is the conjugate opposite spectral face. -/
theorem zetaCompletedExplicitFormulaPhi_dagger
    (f : ZetaAdmissibleFunction) (z : ℂ) :
    zetaCompletedExplicitFormulaPhi (zetaAdmissibleDagger f) z =
      star (zetaCompletedExplicitFormulaPhi f (-star z)) := by
  exact Boundary.zetaLaplaceTransform_dagger f z

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
  exact zetaAdmissibleDagger_apply f t


end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
