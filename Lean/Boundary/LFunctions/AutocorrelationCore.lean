import Boundary.LFunctions.ZetaAdmissibleFunction
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

/-- The convolution autocorrelation kernel unfolds to its defining integral. -/
theorem convolutionAutocorrelationKernel_apply
    (f : ZetaAdmissibleFunction) (t : ℝ) :
    convolutionAutocorrelationKernel f t =
      ∫ u : ℝ, f (u + t / 2) * star (f (u - t / 2)) := by
  change
    (fun t : ℝ => ∫ u : ℝ, f (u + t / 2) * star (f (u - t / 2))) t =
      ∫ u : ℝ, f (u + t / 2) * star (f (u - t / 2))
  rfl

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
  sorry

/-- The convolution autocorrelation kernel has compact support. -/
theorem convolutionAutocorrelationKernel_hasCompactSupport
    (f : ZetaAdmissibleFunction) :
    HasCompactSupport (convolutionAutocorrelationKernel f) := by
  sorry

/-- The convolution autocorrelation kernel is smooth. -/
theorem convolutionAutocorrelationKernel_contDiff
    (f : ZetaAdmissibleFunction) :
    ContDiff ℝ ∞ (convolutionAutocorrelationKernel f) := by
  sorry

/-- The convolution autocorrelation test function attached to an admissible function. -/
def convolutionAutocorrelationTestFunction
    (f : ZetaAdmissibleFunction) : ℝ →C_c ℂ :=
  CompactlySupportedContinuousMap.mk
    (ContinuousMap.mk
      (convolutionAutocorrelationKernel f)
      (convolutionAutocorrelationKernel_continuous f))
    (convolutionAutocorrelationKernel_hasCompactSupport f)

/-- The admissible convolution autocorrelation attached to a seed admissible function. -/
def convolutionAutocorrelation
    (f : ZetaAdmissibleFunction) : ZetaAdmissibleFunction where
  toZetaTestFunction := convolutionAutocorrelationTestFunction f
  smooth := convolutionAutocorrelationKernel_contDiff f

/-- The admissible convolution autocorrelation evaluates as the convolution kernel. -/
theorem convolutionAutocorrelation_apply
    (f : ZetaAdmissibleFunction) (t : ℝ) :
    convolutionAutocorrelation f t =
      convolutionAutocorrelationKernel f t := by
  rfl

/-- The underlying test function of the admissible convolution autocorrelation is the
convolution autocorrelation kernel. -/
theorem convolutionAutocorrelation_toZetaTestFunction'_apply
    (f : ZetaAdmissibleFunction) (t : ℝ) :
    (convolutionAutocorrelation f).toZetaTestFunction' t =
      convolutionAutocorrelationKernel f t := by
  rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
