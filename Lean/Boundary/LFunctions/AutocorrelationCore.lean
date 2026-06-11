import Boundary.LFunctions.ZetaAdmissibleFunction
import Mathlib.Analysis.Convolution
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner

/-!
# Boundary autocorrelation core

This file owns the raw pointwise autocorrelation constructor for admissible
test functions. It stays below the transform and explicit-formula stack.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped ContDiff
open scoped CompactlySupported
open scoped Convolution
open MeasureTheory

namespace ZetaAdmissibleFunction

/-- Complex conjugation preserves admissible smoothness. -/
theorem contDiff_star (f : ZetaAdmissibleFunction) :
    ContDiff ℝ ∞ (fun x : ℝ => star (f x)) := by
  have hconj : ContDiff ℝ ∞ (fun z : ℂ => Complex.conjCLE z) :=
    Complex.conjCLE.contDiff
  have hcomp : ContDiff ℝ ∞ ((fun z : ℂ => Complex.conjCLE z) ∘ fun x : ℝ => f x) :=
    hconj.comp f.smooth
  exact hcomp

/-- The conjugate-reflected admissible probe. -/
def dagger (f : ZetaAdmissibleFunction) : ZetaAdmissibleFunction where
  toZetaTestFunction := star (ZetaAdmissibleFunction.reflect f).toZetaTestFunction
  smooth := by
    change ContDiff ℝ ∞ (fun x : ℝ => star (f (-x)))
    exact contDiff_star (ZetaAdmissibleFunction.reflect f)

/-- The dagger evaluates by conjugate reflection. -/
theorem dagger_apply (f : ZetaAdmissibleFunction) (x : ℝ) :
    dagger f x = star (f (-x)) := by
  rfl

/-- The underlying test function of the dagger is the reflected conjugate test function. -/
theorem dagger_toZetaTestFunction'_eq (f : ZetaAdmissibleFunction) :
    (dagger f).toZetaTestFunction' =
      ⟨fun x => star (f (-x)), by
        have hreflect : Continuous fun x : ℝ => f (-x) :=
          f.toZetaTestFunction.continuous.comp continuous_neg
        exact continuous_star.comp hreflect⟩ := by
  ext x
  rfl

/-- The raw pointwise autocorrelation test function attached to an admissible function. -/
def autocorrelationTestFunction (f : ZetaAdmissibleFunction) : ZetaTestFunction where
  toFun := fun x => f x * star (f x)
  continuous := by
    have hf : Continuous fun x : ℝ => f x := f.toZetaTestFunction.continuous
    exact hf.mul (continuous_star.comp hf)

/-- Products with conjugates preserve admissible smoothness. -/
theorem contDiff_autocorrelation (f : ZetaAdmissibleFunction) :
    ContDiff ℝ ∞ (fun x : ℝ => f x * star (f x)) := by
  have hleft : ContDiff ℝ ∞ (fun x : ℝ => f x) := f.smooth
  have hright : ContDiff ℝ ∞ (fun x : ℝ => star (f x)) := contDiff_star f
  exact hleft.mul hright

/-- The pointwise autocorrelation attached to an admissible function. -/
def autocorrelation (f : ZetaAdmissibleFunction) : ZetaAdmissibleFunction where
  toZetaTestFunction := f.toZetaTestFunction * star f.toZetaTestFunction
  smooth := by
    change ContDiff ℝ ∞ (fun x : ℝ => f x * star (f x))
    exact contDiff_autocorrelation f

/-- The admissible autocorrelation agrees pointwise with the conjugate square. -/
theorem autocorrelation_apply (f : ZetaAdmissibleFunction) (x : ℝ) :
    autocorrelation f x = f x * star (f x) := by
  rfl

/-- The raw autocorrelation test function agrees pointwise with the conjugate square. -/
theorem autocorrelationTestFunction_apply (f : ZetaAdmissibleFunction) (x : ℝ) :
    autocorrelationTestFunction f x = f x * star (f x) := by
  rfl

/-- The admissible autocorrelation has the raw autocorrelation as its underlying test function. -/
theorem autocorrelation_toZetaTestFunction'_eq
    (f : ZetaAdmissibleFunction) :
    (autocorrelation f).toZetaTestFunction' = autocorrelationTestFunction f := by
  ext x
  rfl

/-- The admissible autocorrelation is the pointwise conjugate square as a function. -/
theorem autocorrelation_eq (f : ZetaAdmissibleFunction) :
    autocorrelation f = (fun x => f x * star (f x)) := by
  rfl

/-- The autocorrelation of the reflected probe is the reflection of the original autocorrelation. -/
theorem autocorrelation_dagger_eq_reflect (f : ZetaAdmissibleFunction) :
    autocorrelation (ZetaAdmissibleFunction.reflect f) =
      ZetaAdmissibleFunction.reflect (autocorrelation f) := by
  ext t
  rfl

/-- The autocorrelation kernel is even under reflection of the underlying probe. -/
theorem autocorrelation_reflect_eq (f : ZetaAdmissibleFunction) :
    autocorrelation (ZetaAdmissibleFunction.reflect f) =
      fun t => autocorrelation f (-t) := by
  rw [autocorrelation_dagger_eq_reflect]
  rfl

/-- The analytic convolution autocorrelation kernel
`g_f(t) = ∫ f(u + t / 2) * conj(f(u - t / 2)) du`.

This function-level object is the autocorrelation used by the explicit-formula holography.
The existing `autocorrelation` constructor remains the pointwise-square probe surface used by
older files; the channel identities should unfold analytically to this convolution kernel and
then compare the result with the seed packet Gram. -/
noncomputable def convolutionAutocorrelationKernel
    (f : ZetaAdmissibleFunction) : ℝ → ℂ :=
  fun t : ℝ => ∫ u : ℝ, f (u + t / 2) * star (f (u - t / 2))

/-- The two-variable convolution pairing kernel
`g_{f,h}(t) = ∫ f(u+t/2) * conj(h(u-t/2)) du`.

The diagonal `h = f` is the autocorrelation kernel used by the positivity route. -/
noncomputable def convolutionPairKernel
    (f h : ZetaAdmissibleFunction) : ℝ → ℂ :=
  fun t : ℝ => ∫ u : ℝ, f (u + t / 2) * star (h (u - t / 2))

/-- The standard convolution face of the paired kernel.

The centered integral is the display form used by the explicit formula; the standard convolution
face is the regularity owner form consumed by mathlib's convolution API. -/
noncomputable def convolutionPairKernelStandard
    (f h : ZetaAdmissibleFunction) : ℝ → ℂ :=
  (f : ℝ → ℂ) ⋆[ContinuousLinearMap.mul ℝ ℂ] (dagger h : ℝ → ℂ)

/-- The standard convolution face of the autocorrelation kernel. -/
noncomputable def convolutionAutocorrelationKernelStandard
    (f : ZetaAdmissibleFunction) : ℝ → ℂ :=
  convolutionPairKernelStandard f f

/-- The convolution autocorrelation kernel unfolds to its defining integral. -/
theorem convolutionAutocorrelationKernel_apply
    (f : ZetaAdmissibleFunction) (t : ℝ) :
    convolutionAutocorrelationKernel f t =
      ∫ u : ℝ, f (u + t / 2) * star (f (u - t / 2)) := by
  change
    (fun t : ℝ => ∫ u : ℝ, f (u + t / 2) * star (f (u - t / 2))) t =
      ∫ u : ℝ, f (u + t / 2) * star (f (u - t / 2))
  rfl

/-- The two-variable convolution-pair kernel unfolds to its defining integral. -/
theorem convolutionPairKernel_apply
    (f h : ZetaAdmissibleFunction) (t : ℝ) :
    convolutionPairKernel f h t =
      ∫ u : ℝ, f (u + t / 2) * star (h (u - t / 2)) := by
  rfl

/-- The diagonal convolution-pair kernel is the autocorrelation kernel. -/
theorem convolutionPairKernel_self
    (f : ZetaAdmissibleFunction) :
    convolutionPairKernel f f = convolutionAutocorrelationKernel f := by
  rfl

/-- The centered convolution-pair integrand is the translated standard convolution integrand. -/
theorem convolutionPairKernel_centeredIntegrand_eq_standardIntegrand
    (f h : ZetaAdmissibleFunction) (t y : ℝ) :
    f ((y - t / 2) + t / 2) *
        star (h ((y - t / 2) - t / 2)) =
      f y * (dagger h) (t - y) := by
  have hleft : (y - t / 2) + t / 2 = y := by
    ring
  have hright_arg : (y - t / 2) - t / 2 = y - t := by
    ring
  have hdagger_arg : -(t - y) = y - t := by
    ring
  calc
    f ((y - t / 2) + t / 2) *
        star (h ((y - t / 2) - t / 2)) =
        f y * star (h ((y - t / 2) - t / 2)) := by
      exact congrArg
        (fun x : ℝ => f x * star (h ((y - t / 2) - t / 2)))
        hleft
    _ = f y * star (h (y - t)) := by
      exact congrArg (fun x : ℝ => f y * star (h x)) hright_arg
    _ = f y * star (h (-(t - y))) := by
      exact congrArg (fun x : ℝ => f y * star (h x)) hdagger_arg.symm
    _ = f y * (dagger h) (t - y) := by
      exact congrArg (fun x : ℂ => f y * x) (dagger_apply h (t - y)).symm

/-- The centered convolution-pair kernel is the standard convolution against the dagger face. -/
theorem convolutionPairKernel_eq_standard
    (f h : ZetaAdmissibleFunction) :
    convolutionPairKernel f h = convolutionPairKernelStandard f h := by
  ext t
  unfold convolutionPairKernel
  unfold convolutionPairKernelStandard
  have htranslate :
      (∫ u : ℝ, f (u + t / 2) * star (h (u - t / 2))) =
        ∫ y : ℝ, f ((y - t / 2) + t / 2) *
          star (h ((y - t / 2) - t / 2)) := by
    have hraw :=
      integral_add_right_eq_self
        (μ := (volume : Measure ℝ))
        (fun y : ℝ =>
          f ((y - t / 2) + t / 2) *
            star (h ((y - t / 2) - t / 2)))
        (t / 2)
    have hpoint :
        (fun x : ℝ =>
          f (((x + t / 2) - t / 2) + t / 2) *
            star (h (((x + t / 2) - t / 2) - t / 2))) =
          fun x : ℝ => f (x + t / 2) * star (h (x - t / 2)) := by
      funext x
      have hxleft : ((x + t / 2) - t / 2) + t / 2 = x + t / 2 := by
        ring
      have hxright : ((x + t / 2) - t / 2) - t / 2 = x - t / 2 := by
        ring
      calc
        f (((x + t / 2) - t / 2) + t / 2) *
            star (h (((x + t / 2) - t / 2) - t / 2)) =
            f (x + t / 2) *
              star (h (((x + t / 2) - t / 2) - t / 2)) := by
          exact congrArg
            (fun y : ℝ => f y *
              star (h (((x + t / 2) - t / 2) - t / 2)))
            hxleft
        _ = f (x + t / 2) * star (h (x - t / 2)) := by
          exact congrArg (fun y : ℝ => f (x + t / 2) * star (h y)) hxright
    exact Eq.trans
      (integral_congr_ae (Filter.Eventually.of_forall fun x =>
        congrArg (fun F : ℝ → ℂ => F x) hpoint)).symm
      hraw
  have hintegrand :
      (∫ y : ℝ,
          f ((y - t / 2) + t / 2) *
            star (h ((y - t / 2) - t / 2))) =
        ∫ y : ℝ, f y * (dagger h) (t - y) := by
    exact integral_congr_ae (Filter.Eventually.of_forall fun y =>
      convolutionPairKernel_centeredIntegrand_eq_standardIntegrand f h t y)
  calc
    (∫ u : ℝ, f (u + t / 2) * star (h (u - t / 2))) =
        ∫ y : ℝ,
          f ((y - t / 2) + t / 2) *
            star (h ((y - t / 2) - t / 2)) := htranslate
    _ = ∫ y : ℝ, f y * (dagger h) (t - y) := hintegrand

/-- The centered autocorrelation kernel is the standard convolution against the dagger face. -/
theorem convolutionAutocorrelationKernel_eq_standard
    (f : ZetaAdmissibleFunction) :
    convolutionAutocorrelationKernel f = convolutionAutocorrelationKernelStandard f := by
  exact convolutionPairKernel_eq_standard f f

/-- Admissible functions are locally integrable on the logarithmic line. -/
theorem locallyIntegrable (f : ZetaAdmissibleFunction) :
    LocallyIntegrable (fun x : ℝ => f x) (volume : Measure ℝ) := by
  exact f.toZetaTestFunction.continuous.locallyIntegrable

/-- At the origin, the convolution autocorrelation is the seed norm-density integral. -/
theorem convolutionAutocorrelationKernel_zero
    (f : ZetaAdmissibleFunction) :
    convolutionAutocorrelationKernel f 0 =
      ∫ u : ℝ, f u * star (f u) := by
  change
    (∫ u : ℝ, f (u + 0 / 2) * star (f (u - 0 / 2))) =
      ∫ u : ℝ, f u * star (f u)
  congr 1
  funext u
  have hleft : u + 0 / 2 = u := by ring
  have hright : u - 0 / 2 = u := by ring
  calc
    f (u + 0 / 2) * star (f (u - 0 / 2)) =
        f u * star (f (u - 0 / 2)) := by
      exact congrArg (fun y : ℝ => f y * star (f (u - 0 / 2))) hleft
    _ = f u * star (f u) := by
      exact congrArg (fun y : ℝ => f u * star (f y)) hright

/-- The convolution autocorrelation kernel is continuous. -/
theorem convolutionAutocorrelationKernel_continuous
    (f : ZetaAdmissibleFunction) :
    Continuous (convolutionAutocorrelationKernel f) := by
  have hstandard :
      Continuous (convolutionAutocorrelationKernelStandard f) := by
    unfold convolutionAutocorrelationKernelStandard
    unfold convolutionPairKernelStandard
    exact (dagger f).toZetaTestFunction.hasCompactSupport.continuous_convolution_right
      (ContinuousLinearMap.mul ℝ ℂ)
      (locallyIntegrable f)
      (dagger f).toZetaTestFunction.continuous
  exact Eq.subst
    (motive := fun k : ℝ → ℂ => Continuous k)
    (convolutionAutocorrelationKernel_eq_standard f).symm
    hstandard

/-- The convolution autocorrelation kernel has compact support. -/
theorem convolutionAutocorrelationKernel_hasCompactSupport
    (f : ZetaAdmissibleFunction) :
    HasCompactSupport (convolutionAutocorrelationKernel f) := by
  have hstandard :
      HasCompactSupport (convolutionAutocorrelationKernelStandard f) := by
    unfold convolutionAutocorrelationKernelStandard
    unfold convolutionPairKernelStandard
    exact HasCompactSupport.convolution
      (L := ContinuousLinearMap.mul ℝ ℂ)
      (μ := (volume : Measure ℝ))
      (f := fun x : ℝ => f x)
      (g := fun x : ℝ => (dagger f) x)
      f.toZetaTestFunction.hasCompactSupport
      (dagger f).toZetaTestFunction.hasCompactSupport
  exact Eq.subst
    (motive := fun k : ℝ → ℂ => HasCompactSupport k)
    (convolutionAutocorrelationKernel_eq_standard f).symm
    hstandard

/-- The convolution autocorrelation kernel is smooth. -/
theorem convolutionAutocorrelationKernel_contDiff
    (f : ZetaAdmissibleFunction) :
    ContDiff ℝ ∞ (convolutionAutocorrelationKernel f) := by
  have hstandard :
      ContDiff ℝ ∞ (convolutionAutocorrelationKernelStandard f) := by
    unfold convolutionAutocorrelationKernelStandard
    unfold convolutionPairKernelStandard
    exact (dagger f).toZetaTestFunction.hasCompactSupport.contDiff_convolution_right
      (ContinuousLinearMap.mul ℝ ℂ)
      (locallyIntegrable f)
      (dagger f).smooth
  exact Eq.subst
    (motive := fun k : ℝ → ℂ => ContDiff ℝ ∞ k)
    (convolutionAutocorrelationKernel_eq_standard f).symm
    hstandard

/-- The two-variable convolution-pair kernel is continuous. -/
theorem convolutionPairKernel_continuous
    (f h : ZetaAdmissibleFunction) :
    Continuous (convolutionPairKernel f h) := by
  have hstandard :
      Continuous (convolutionPairKernelStandard f h) := by
    unfold convolutionPairKernelStandard
    exact (dagger h).toZetaTestFunction.hasCompactSupport.continuous_convolution_right
      (ContinuousLinearMap.mul ℝ ℂ)
      (locallyIntegrable f)
      (dagger h).toZetaTestFunction.continuous
  exact Eq.subst
    (motive := fun k : ℝ → ℂ => Continuous k)
    (convolutionPairKernel_eq_standard f h).symm
    hstandard

/-- The two-variable convolution-pair kernel has compact support. -/
theorem convolutionPairKernel_hasCompactSupport
    (f h : ZetaAdmissibleFunction) :
    HasCompactSupport (convolutionPairKernel f h) := by
  have hstandard :
      HasCompactSupport (convolutionPairKernelStandard f h) := by
    unfold convolutionPairKernelStandard
    exact HasCompactSupport.convolution
      (L := ContinuousLinearMap.mul ℝ ℂ)
      (μ := (volume : Measure ℝ))
      (f := fun x : ℝ => f x)
      (g := fun x : ℝ => (dagger h) x)
      f.toZetaTestFunction.hasCompactSupport
      (dagger h).toZetaTestFunction.hasCompactSupport
  exact Eq.subst
    (motive := fun k : ℝ → ℂ => HasCompactSupport k)
    (convolutionPairKernel_eq_standard f h).symm
    hstandard

/-- The two-variable convolution-pair kernel is smooth. -/
theorem convolutionPairKernel_contDiff
    (f h : ZetaAdmissibleFunction) :
    ContDiff ℝ ∞ (convolutionPairKernel f h) := by
  have hstandard :
      ContDiff ℝ ∞ (convolutionPairKernelStandard f h) := by
    unfold convolutionPairKernelStandard
    exact (dagger h).toZetaTestFunction.hasCompactSupport.contDiff_convolution_right
      (ContinuousLinearMap.mul ℝ ℂ)
      (locallyIntegrable f)
      (dagger h).smooth
  exact Eq.subst
    (motive := fun k : ℝ → ℂ => ContDiff ℝ ∞ k)
    (convolutionPairKernel_eq_standard f h).symm
    hstandard

/-- The convolution autocorrelation test function attached to an admissible function. -/
def convolutionAutocorrelationTestFunction
    (f : ZetaAdmissibleFunction) : ℝ →C_c ℂ :=
  CompactlySupportedContinuousMap.mk
    (ContinuousMap.mk
      (convolutionAutocorrelationKernel f)
    (convolutionAutocorrelationKernel_continuous f))
    (convolutionAutocorrelationKernel_hasCompactSupport f)

/-- The two-variable convolution-pair test function attached to two admissible functions. -/
def convolutionPairTestFunction
    (f h : ZetaAdmissibleFunction) : ℝ →C_c ℂ :=
  CompactlySupportedContinuousMap.mk
    (ContinuousMap.mk
      (convolutionPairKernel f h)
      (convolutionPairKernel_continuous f h))
    (convolutionPairKernel_hasCompactSupport f h)

/-- The admissible convolution autocorrelation attached to a seed admissible function. -/
def convolutionAutocorrelation
    (f : ZetaAdmissibleFunction) : ZetaAdmissibleFunction where
  toZetaTestFunction := convolutionAutocorrelationTestFunction f
  smooth := convolutionAutocorrelationKernel_contDiff f

/-- The admissible two-variable convolution pairing attached to two seed admissible functions. -/
def convolutionPair
    (f h : ZetaAdmissibleFunction) : ZetaAdmissibleFunction where
  toZetaTestFunction := convolutionPairTestFunction f h
  smooth := convolutionPairKernel_contDiff f h

/-- The admissible convolution autocorrelation evaluates as the convolution kernel. -/
theorem convolutionAutocorrelation_apply
    (f : ZetaAdmissibleFunction) (t : ℝ) :
    convolutionAutocorrelation f t =
      convolutionAutocorrelationKernel f t := by
  change convolutionAutocorrelationTestFunction f t = convolutionAutocorrelationKernel f t
  rfl

/-- The admissible convolution pair evaluates as the convolution-pair kernel. -/
theorem convolutionPair_apply
    (f h : ZetaAdmissibleFunction) (t : ℝ) :
    convolutionPair f h t =
      convolutionPairKernel f h t := by
  change convolutionPairTestFunction f h t = convolutionPairKernel f h t
  rfl

/-- The diagonal convolution pair is the convolution autocorrelation. -/
theorem convolutionPair_self
    (f : ZetaAdmissibleFunction) :
    convolutionPair f f = convolutionAutocorrelation f := by
  ext t
  exact
    (convolutionPair_apply f f t).trans
      ((convolutionPairKernel_self f ▸
        (convolutionAutocorrelation_apply f t).symm))

/-- The underlying test function of the admissible convolution autocorrelation is the
convolution autocorrelation kernel. -/
theorem convolutionAutocorrelation_toZetaTestFunction'_apply
    (f : ZetaAdmissibleFunction) (t : ℝ) :
    (convolutionAutocorrelation f).toZetaTestFunction' t =
      convolutionAutocorrelationKernel f t := by
  change convolutionAutocorrelationTestFunction f t = convolutionAutocorrelationKernel f t
  rfl

/-- The underlying test function of the admissible convolution pair is the
two-variable convolution-pair kernel. -/
theorem convolutionPair_toZetaTestFunction'_apply
    (f h : ZetaAdmissibleFunction) (t : ℝ) :
    (convolutionPair f h).toZetaTestFunction' t =
      convolutionPairKernel f h t := by
  change convolutionPairTestFunction f h t = convolutionPairKernel f h t
  rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
