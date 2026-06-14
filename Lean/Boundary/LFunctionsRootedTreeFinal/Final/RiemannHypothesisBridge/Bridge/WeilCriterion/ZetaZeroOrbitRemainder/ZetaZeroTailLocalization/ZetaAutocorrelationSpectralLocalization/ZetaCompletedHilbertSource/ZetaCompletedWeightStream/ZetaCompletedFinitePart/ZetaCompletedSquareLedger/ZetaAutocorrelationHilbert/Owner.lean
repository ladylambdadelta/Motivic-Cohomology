import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.AutocorrelationInterface.AutocorrelationCore.Owner
import Mathlib.MeasureTheory.Integral.Bochner
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Boundary autocorrelation Hilbert API

This file owns the Hilbert-space vocabulary behind the convolution
autocorrelation route.  The definitions are deliberately analytic: inner
products are integrals on the logarithmic line, translations are the existing
admissible translations, and defect squares are integral norms of translation
differences.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open MeasureTheory
open scoped CompactlySupported

namespace ZetaAdmissibleFunction

/-- Centered negative half-translation is subtraction by the positive half. -/
theorem real_add_neg_half_eq_sub_half (u a : ℝ) :
    u + (-a / 2) = u - a / 2 := by
  calc
    u + (-a / 2) = u + -(a / 2) := by
      exact congrArg (fun x : ℝ => u + x) (neg_div 2 a)
    _ = u - a / 2 := by
      exact (sub_eq_add_neg u (a / 2)).symm

/-- Two identical diagonal terms rewrite as twice the diagonal. -/
theorem real_add_self_sub_eq_two_mul_sub (A X : ℝ) :
    A + A - X = 2 * A - X := by
  exact congrArg (fun y : ℝ => y - X) (two_mul A).symm

/-- A positive half remains after adding the whole displacement to the negative half. -/
theorem real_neg_half_add_self_eq_half (a : ℝ) :
    -(a / 2) + a = a / 2 := by
  calc
    -(a / 2) + a = a + -(a / 2) := by
      exact add_comm (-(a / 2)) a
    _ = a - a / 2 := by
      exact (sub_eq_add_neg a (a / 2)).symm
    _ = a / 2 := by
      exact sub_self_div_two a

/-- The seed sesquilinear form on admissible logarithmic-line probes. -/
def zetaSeedInner (f h : ZetaAdmissibleFunction) : ℂ :=
  ∫ u : ℝ, f u * star (h u)

/-- The real seed norm square attached to the sesquilinear form. -/
def zetaSeedNormSq (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (zetaSeedInner f f)

/-- Translation on the seed Hilbert object. -/
def zetaTranslate (a : ℝ) (f : ZetaAdmissibleFunction) : ZetaAdmissibleFunction :=
  ZetaAdmissibleFunction.translate a f

/-- The pointwise translation defect value. -/
def zetaTranslationDefectValue (a : ℝ) (f : ZetaAdmissibleFunction) (u : ℝ) : ℂ :=
  f u - zetaTranslate a f u

/-- The integral norm square of a translation defect. -/
def zetaTranslationDefectNormSq (a : ℝ) (f : ZetaAdmissibleFunction) : ℝ :=
  Complex.re (∫ u : ℝ,
    zetaTranslationDefectValue a f u * star (zetaTranslationDefectValue a f u))

/-- The real part of a complex conjugate square is its norm square. -/
theorem complex_re_mul_star_self_eq_normSq (z : ℂ) :
    Complex.re (z * star z) = Complex.normSq z := by
  have hmul : z * star z = (Complex.normSq z : ℂ) := by
    exact Complex.mul_conj z
  calc
    Complex.re (z * star z) = Complex.re (Complex.normSq z : ℂ) := by
      exact congrArg Complex.re hmul
    _ = Complex.normSq z := by
      rfl

/-- Complex conjugate-square densities are pointwise nonnegative after taking real parts. -/
theorem complex_re_mul_star_self_nonnegative (z : ℂ) :
    0 ≤ Complex.re (z * star z) := by
  have hnorm : Complex.re (z * star z) = Complex.normSq z :=
    complex_re_mul_star_self_eq_normSq z
  exact hnorm.symm ▸ Complex.normSq_nonneg z

/-- The conjugate of a sesquilinear density swaps its two entries. -/
theorem complex_star_mul_star_eq_swap (z w : ℂ) :
    star (z * star w) = w * star z := by
  calc
    star (z * star w) = star (star w) * star z := by
      exact star_mul z (star w)
    _ = w * star z := by
      exact congrArg (fun y : ℂ => y * star z) (star_star w)

/-- Swapping the two entries of a conjugate product preserves its real part. -/
theorem complex_re_mul_star_swap (z w : ℂ) :
    Complex.re (z * star w) = Complex.re (w * star z) := by
  have hstar : star (z * star w) = w * star z :=
    complex_star_mul_star_eq_swap z w
  have hre : Complex.re (star (z * star w)) = Complex.re (z * star w) := by
    rfl
  calc
    Complex.re (z * star w) = Complex.re (star (z * star w)) := by
      exact hre.symm
    _ = Complex.re (w * star z) := by
      exact congrArg Complex.re hstar

/-- Pointwise expansion of a complex defect conjugate square. -/
theorem complex_re_defect_conjSquare_eq_diagonal_sub_offDiagonal
    (z w : ℂ) :
    Complex.re ((z - w) * star (z - w)) =
      Complex.re (z * star z) + Complex.re (w * star w) -
        2 * Complex.re (w * star z) := by
  have hnormDefect :
      Complex.re ((z - w) * star (z - w)) =
        Complex.normSq (z - w) :=
    complex_re_mul_star_self_eq_normSq (z - w)
  have hnormSub :
      Complex.normSq (z - w) =
        Complex.normSq z + Complex.normSq w - 2 * Complex.re (z * star w) :=
    Complex.normSq_sub z w
  have hz :
      Complex.normSq z = Complex.re (z * star z) :=
    (complex_re_mul_star_self_eq_normSq z).symm
  have hw :
      Complex.normSq w = Complex.re (w * star w) :=
    (complex_re_mul_star_self_eq_normSq w).symm
  have hoff :
      Complex.re (z * star w) = Complex.re (w * star z) := by
    exact complex_re_mul_star_swap z w
  calc
    Complex.re ((z - w) * star (z - w)) =
        Complex.normSq (z - w) := hnormDefect
    _ = Complex.normSq z + Complex.normSq w -
        2 * Complex.re (z * star w) := hnormSub
    _ = Complex.re (z * star z) + Complex.normSq w -
        2 * Complex.re (z * star w) := by
      exact congrArg
        (fun x : ℝ => x + Complex.normSq w -
          2 * Complex.re (z * star w))
        hz
    _ = Complex.re (z * star z) + Complex.re (w * star w) -
        2 * Complex.re (z * star w) := by
      exact congrArg
        (fun x : ℝ => Complex.re (z * star z) + x -
          2 * Complex.re (z * star w))
        hw
    _ = Complex.re (z * star z) + Complex.re (w * star w) -
        2 * Complex.re (w * star z) := by
      exact congrArg
        (fun x : ℝ => Complex.re (z * star z) + Complex.re (w * star w) - 2 * x)
        hoff

/-- Conjugation commutes with the seed-density integral in the expected Hermitian way. -/
theorem integral_seedDensity_conj_symm
    (f h : ZetaAdmissibleFunction) :
    (∫ u : ℝ, h u * star (f u)) =
      star (∫ u : ℝ, f u * star (h u)) := by
  have hconj :
      (∫ u : ℝ, star (f u * star (h u))) =
        star (∫ u : ℝ, f u * star (h u)) := by
    exact integral_conj
  have hdensity :
      (fun u : ℝ => star (f u * star (h u))) =
        fun u : ℝ => h u * star (f u) := by
    funext u
    exact complex_star_mul_star_eq_swap (f u) (h u)
  calc
    (∫ u : ℝ, h u * star (f u)) =
        ∫ u : ℝ, star (f u * star (h u)) := by
      exact congrArg (fun F : ℝ → ℂ => ∫ u : ℝ, F u) hdensity.symm
    _ = star (∫ u : ℝ, f u * star (h u)) := hconj

/-- The seed conjugate-square density is integrable. -/
theorem zetaSeedConjSquare_integrable (f : ZetaAdmissibleFunction) :
    Integrable (fun u : ℝ => f u * star (f u)) := by
  have hcont : Continuous fun u : ℝ => f u * star (f u) :=
    f.toZetaTestFunction.continuous.mul
      (continuous_star.comp f.toZetaTestFunction.continuous)
  have hsupport : HasCompactSupport fun u : ℝ => f u * star (f u) :=
    f.hasCompactSupport.mul_right
  exact hcont.integrable_of_hasCompactSupport hsupport

/-- The real part of the seed conjugate-square integral is the integral of the pointwise norm
square density. -/
theorem zetaSeedNormSq_eq_integral_re_conjSquare
    (f : ZetaAdmissibleFunction) :
    zetaSeedNormSq f =
      ∫ u : ℝ, Complex.re (f u * star (f u)) := by
  unfold zetaSeedNormSq
  unfold zetaSeedInner
  exact (integral_re (zetaSeedConjSquare_integrable f)).symm

/-- The translation-defect value is continuous. -/
theorem zetaTranslationDefectValue_continuous
    (a : ℝ) (f : ZetaAdmissibleFunction) :
    Continuous fun u : ℝ => zetaTranslationDefectValue a f u := by
  unfold zetaTranslationDefectValue
  exact f.toZetaTestFunction.continuous.sub
    (zetaTranslate a f).toZetaTestFunction.continuous

/-- The translation-defect value has compact support. -/
theorem zetaTranslationDefectValue_hasCompactSupport
    (a : ℝ) (f : ZetaAdmissibleFunction) :
    HasCompactSupport fun u : ℝ => zetaTranslationDefectValue a f u := by
  let F : ℝ →C_c ℂ :=
    f.toZetaTestFunction - (zetaTranslate a f).toZetaTestFunction
  have hF : HasCompactSupport fun u : ℝ => F u :=
    F.hasCompactSupport
  exact hF

/-- The translation-defect conjugate-square density is integrable. -/
theorem zetaTranslationDefectConjSquare_integrable
    (a : ℝ) (f : ZetaAdmissibleFunction) :
    Integrable fun u : ℝ =>
      zetaTranslationDefectValue a f u *
        star (zetaTranslationDefectValue a f u) := by
  have hcontDefect := zetaTranslationDefectValue_continuous a f
  have hcont : Continuous fun u : ℝ =>
      zetaTranslationDefectValue a f u *
        star (zetaTranslationDefectValue a f u) :=
    hcontDefect.mul (continuous_star.comp hcontDefect)
  have hsupportDefect := zetaTranslationDefectValue_hasCompactSupport a f
  have hsupport : HasCompactSupport fun u : ℝ =>
      zetaTranslationDefectValue a f u *
        star (zetaTranslationDefectValue a f u) :=
    hsupportDefect.mul_right
  exact hcont.integrable_of_hasCompactSupport hsupport

/-- The real part of the translation-defect integral is the integral of the pointwise norm square. -/
theorem zetaTranslationDefectNormSq_eq_integral_re_conjSquare
    (a : ℝ) (f : ZetaAdmissibleFunction) :
    zetaTranslationDefectNormSq a f =
      ∫ u : ℝ, Complex.re
        (zetaTranslationDefectValue a f u *
          star (zetaTranslationDefectValue a f u)) := by
  unfold zetaTranslationDefectNormSq
  exact (integral_re (zetaTranslationDefectConjSquare_integrable a f)).symm

/-- The off-diagonal translation density is integrable. -/
theorem zetaTranslationOffDiagonal_integrable
    (a : ℝ) (f : ZetaAdmissibleFunction) :
    Integrable fun u : ℝ => zetaTranslate a f u * star (f u) := by
  have hleft : Continuous fun u : ℝ => zetaTranslate a f u :=
    (zetaTranslate a f).toZetaTestFunction.continuous
  have hright : Continuous fun u : ℝ => star (f u) :=
    continuous_star.comp f.toZetaTestFunction.continuous
  have hcont : Continuous fun u : ℝ => zetaTranslate a f u * star (f u) :=
    hleft.mul hright
  have hsupport : HasCompactSupport fun u : ℝ => zetaTranslate a f u * star (f u) :=
    (zetaTranslate a f).hasCompactSupport.mul_right
  exact hcont.integrable_of_hasCompactSupport hsupport

/-- The real part of the off-diagonal translation density is integrable. -/
theorem zetaTranslationOffDiagonal_re_integrable
    (a : ℝ) (f : ZetaAdmissibleFunction) :
    Integrable (fun u : ℝ => Complex.re (zetaTranslate a f u * star (f u))) :=
  (zetaTranslationOffDiagonal_integrable a f).re

/-- The real seed square density is integrable. -/
theorem zetaSeedConjSquare_re_integrable (f : ZetaAdmissibleFunction) :
    Integrable (fun u : ℝ => Complex.re (f u * star (f u))) :=
  (zetaSeedConjSquare_integrable f).re

/-- The real translated seed square density is integrable. -/
theorem zetaTranslateConjSquare_re_integrable
    (a : ℝ) (f : ZetaAdmissibleFunction) :
    Integrable (fun u : ℝ =>
      Complex.re (zetaTranslate a f u * star (zetaTranslate a f u))) :=
  zetaSeedConjSquare_re_integrable (zetaTranslate a f)

/-- The pointwise real translation-defect density expands into two diagonal densities and the
off-diagonal density. -/
theorem zetaTranslationDefectDensity_re_eq_diagonal_sub_offDiagonal
    (a : ℝ) (f : ZetaAdmissibleFunction) (u : ℝ) :
    Complex.re
      (zetaTranslationDefectValue a f u *
        star (zetaTranslationDefectValue a f u)) =
      Complex.re (f u * star (f u)) +
        Complex.re (zetaTranslate a f u * star (zetaTranslate a f u)) -
        2 * Complex.re (zetaTranslate a f u * star (f u)) := by
  unfold zetaTranslationDefectValue
  exact complex_re_defect_conjSquare_eq_diagonal_sub_offDiagonal
    (f u) (zetaTranslate a f u)

/-- Integral expansion of the real translation-defect density. -/
theorem integral_zetaTranslationDefectDensity_re_eq_diagonal_sub_offDiagonal
    (a : ℝ) (f : ZetaAdmissibleFunction) :
    (∫ u : ℝ, Complex.re
      (zetaTranslationDefectValue a f u *
        star (zetaTranslationDefectValue a f u))) =
      (∫ u : ℝ, Complex.re (f u * star (f u))) +
        (∫ u : ℝ,
          Complex.re (zetaTranslate a f u * star (zetaTranslate a f u))) -
        2 * (∫ u : ℝ,
          Complex.re (zetaTranslate a f u * star (f u))) := by
  let A : ℝ → ℝ := fun u : ℝ => Complex.re (f u * star (f u))
  let B : ℝ → ℝ := fun u : ℝ =>
    Complex.re (zetaTranslate a f u * star (zetaTranslate a f u))
  let C : ℝ → ℝ := fun u : ℝ =>
    Complex.re (zetaTranslate a f u * star (f u))
  have hpoint :
      (fun u : ℝ => Complex.re
        (zetaTranslationDefectValue a f u *
          star (zetaTranslationDefectValue a f u))) =
        fun u : ℝ => A u + B u - 2 * C u := by
    funext u
    exact zetaTranslationDefectDensity_re_eq_diagonal_sub_offDiagonal a f u
  have hA : Integrable A :=
    zetaSeedConjSquare_re_integrable f
  have hB : Integrable B :=
    zetaTranslateConjSquare_re_integrable a f
  have hC : Integrable C :=
    zetaTranslationOffDiagonal_re_integrable a f
  have hAB : Integrable fun u : ℝ => A u + B u :=
    hA.add hB
  have htwoC : Integrable fun u : ℝ => 2 * C u :=
    hC.const_mul 2
  have hadd :
      (∫ u : ℝ, A u + B u) =
        (∫ u : ℝ, A u) + (∫ u : ℝ, B u) :=
    integral_add hA hB
  have hsub :
      (∫ u : ℝ, (A u + B u) - 2 * C u) =
        (∫ u : ℝ, A u + B u) - (∫ u : ℝ, 2 * C u) :=
    integral_sub hAB htwoC
  have hscale :
      (∫ u : ℝ, 2 * C u) = 2 * (∫ u : ℝ, C u) := by
    change (∫ u : ℝ, (2 : ℝ) • C u) = (2 : ℝ) • (∫ u : ℝ, C u)
    exact integral_smul (2 : ℝ) C
  calc
    (∫ u : ℝ, Complex.re
      (zetaTranslationDefectValue a f u *
        star (zetaTranslationDefectValue a f u))) =
        ∫ u : ℝ, A u + B u - 2 * C u := by
      exact congrArg (fun F : ℝ → ℝ => ∫ u : ℝ, F u) hpoint
    _ = (∫ u : ℝ, A u + B u) - (∫ u : ℝ, 2 * C u) := hsub
    _ = ((∫ u : ℝ, A u) + (∫ u : ℝ, B u)) - (∫ u : ℝ, 2 * C u) := by
      exact congrArg (fun x : ℝ => x - (∫ u : ℝ, 2 * C u)) hadd
    _ = ((∫ u : ℝ, A u) + (∫ u : ℝ, B u)) -
        2 * (∫ u : ℝ, C u) := by
      exact congrArg
        (fun x : ℝ => ((∫ u : ℝ, A u) + (∫ u : ℝ, B u)) - x)
        hscale

/-- Lebesgue integration on the logarithmic line is invariant under right translation. -/
theorem integral_comp_add_right_eq_self_complex
    (F : ℝ → ℂ) (c : ℝ) :
    (∫ u : ℝ, F (u + c)) = ∫ u : ℝ, F u := by
  exact integral_add_right_eq_self F c

/-- The centered autocorrelation density is a translated uncentered density. -/
theorem convolutionAutocorrelationCenteredDensity_eq_translateDensity
    (f : ZetaAdmissibleFunction) (a u : ℝ) :
    f (u + a / 2) * star (f (u - a / 2)) =
      (fun v : ℝ => f (v + a) * star (f v)) (u + (-a / 2)) := by
  have hleft : u + (-a / 2) + a = u + a / 2 := by
    calc
      u + (-a / 2) + a = u + (-(a / 2)) + a := by
        exact congrArg (fun x : ℝ => u + x + a) (neg_div 2 a)
      _ = u + (-(a / 2) + a) := by
        exact add_assoc u (-(a / 2)) a
      _ = u + (a / 2) := by
        exact congrArg (fun x : ℝ => u + x) (real_neg_half_add_self_eq_half a)
  have hright : u + (-a / 2) = u - a / 2 :=
    real_add_neg_half_eq_sub_half u a
  calc
    f (u + a / 2) * star (f (u - a / 2)) =
        f (u + (-a / 2) + a) * star (f (u - a / 2)) := by
      exact congrArg (fun y : ℝ => f y * star (f (u - a / 2))) hleft.symm
    _ = f (u + (-a / 2) + a) * star (f (u + (-a / 2))) := by
      exact congrArg
        (fun y : ℝ => f (u + (-a / 2) + a) * star (f y))
        hright.symm

/-- Translating the left face backwards is the same pairing as translating the right face
forwards. -/
theorem zetaSeedInner_translate_neg_left_eq_right
    (a : ℝ) (f : ZetaAdmissibleFunction) :
    zetaSeedInner (zetaTranslate (-a) f) f =
      zetaSeedInner f (zetaTranslate a f) := by
  unfold zetaSeedInner
  unfold zetaTranslate
  have hshift :
      (∫ u : ℝ, f (u + -a) * star (f u)) =
        ∫ u : ℝ, (fun v : ℝ => f v * star (f (v + a))) (u + -a) := by
    congr 1
    funext u
    have hright : u + -a + a = u := by
      calc
        u + -a + a = u + (-a + a) := by
          exact add_assoc u (-a) a
        _ = u + 0 := by
          exact congrArg (fun x : ℝ => u + x) (neg_add_cancel a)
        _ = u := by
          exact add_zero u
    exact congrArg (fun y : ℝ => f (u + -a) * star (f y)) hright.symm
  calc
    (∫ u : ℝ, f (u + -a) * star (f u)) =
        ∫ u : ℝ, (fun v : ℝ => f v * star (f (v + a))) (u + -a) := hshift
    _ = ∫ u : ℝ, f u * star (f (u + a)) := by
      exact integral_comp_add_right_eq_self_complex
        (fun v : ℝ => f v * star (f (v + a))) (-a)

/-- The convolution autocorrelation is the inner product of the two centered translated faces. -/
theorem convolutionAutocorrelationKernel_eq_centeredTranslateInner
    (f : ZetaAdmissibleFunction) (a : ℝ) :
    convolutionAutocorrelationKernel f a =
      zetaSeedInner (zetaTranslate (a / 2) f) (zetaTranslate (-a / 2) f) := by
  unfold convolutionAutocorrelationKernel
  unfold zetaSeedInner
  unfold zetaTranslate
  congr 1
  funext u
  have hminus : u + (-a / 2) = u - a / 2 :=
    real_add_neg_half_eq_sub_half u a
  exact congrArg (fun y : ℝ => f (u + a / 2) * star (f y)) hminus.symm

/-- The two-variable convolution pair is the inner product of the two centered translated
faces. -/
theorem convolutionPairKernel_eq_centeredTranslateInner
    (f h : ZetaAdmissibleFunction) (a : ℝ) :
    convolutionPairKernel f h a =
      zetaSeedInner (zetaTranslate (a / 2) f) (zetaTranslate (-a / 2) h) := by
  unfold convolutionPairKernel
  unfold zetaSeedInner
  unfold zetaTranslate
  congr 1
  funext u
  have hminus : u + (-a / 2) = u - a / 2 :=
    real_add_neg_half_eq_sub_half u a
  exact congrArg (fun y : ℝ => f (u + a / 2) * star (h y)) hminus.symm

/-- The uncentered translation-pairing form of the convolution autocorrelation. -/
theorem convolutionAutocorrelationKernel_eq_translateInner
    (f : ZetaAdmissibleFunction) (a : ℝ) :
    convolutionAutocorrelationKernel f a =
      zetaSeedInner (zetaTranslate a f) f := by
  unfold convolutionAutocorrelationKernel
  unfold zetaSeedInner
  unfold zetaTranslate
  calc
    (∫ u : ℝ, f (u + a / 2) * star (f (u - a / 2))) =
        ∫ u : ℝ, (fun v : ℝ => f (v + a) * star (f v)) (u + (-a / 2)) := by
      congr 1
      funext u
      exact convolutionAutocorrelationCenteredDensity_eq_translateDensity f a u
    _ = ∫ u : ℝ, f (u + a) * star (f u) := by
      exact integral_comp_add_right_eq_self_complex
        (fun v : ℝ => f (v + a) * star (f v)) (-a / 2)

/-- The seed inner product is conjugate-symmetric. -/
theorem zetaSeedInner_conj_symm
    (f h : ZetaAdmissibleFunction) :
    zetaSeedInner h f = star (zetaSeedInner f h) := by
  unfold zetaSeedInner
  exact integral_seedDensity_conj_symm f h

/-- Seed norm squares are nonnegative. -/
theorem zetaSeedNormSq_nonnegative (f : ZetaAdmissibleFunction) :
    0 ≤ zetaSeedNormSq f := by
  have hpoint :
      ∀ u : ℝ, 0 ≤ Complex.re (f u * star (f u)) :=
    fun u => complex_re_mul_star_self_nonnegative (f u)
  have hintegral :
      0 ≤ ∫ u : ℝ, Complex.re (f u * star (f u)) :=
    integral_nonneg hpoint
  exact (zetaSeedNormSq_eq_integral_re_conjSquare f).symm ▸ hintegral

/-- Translation-defect norm squares are nonnegative. -/
theorem zetaTranslationDefectNormSq_nonnegative
    (a : ℝ) (f : ZetaAdmissibleFunction) :
    0 ≤ zetaTranslationDefectNormSq a f := by
  have hpoint :
      ∀ u : ℝ,
        0 ≤ Complex.re
          (zetaTranslationDefectValue a f u *
            star (zetaTranslationDefectValue a f u)) :=
    fun u => complex_re_mul_star_self_nonnegative (zetaTranslationDefectValue a f u)
  have hintegral :
      0 ≤ ∫ u : ℝ, Complex.re
        (zetaTranslationDefectValue a f u *
          star (zetaTranslationDefectValue a f u)) :=
    integral_nonneg hpoint
  exact (zetaTranslationDefectNormSq_eq_integral_re_conjSquare a f).symm ▸ hintegral

/-- Translation preserves the seed norm square. -/
theorem zetaTranslate_normSq (a : ℝ) (f : ZetaAdmissibleFunction) :
    zetaSeedNormSq (zetaTranslate a f) = zetaSeedNormSq f := by
  unfold zetaSeedNormSq
  unfold zetaSeedInner
  unfold zetaTranslate
  have hshift :
      (∫ u : ℝ, f (u + a) * star (f (u + a))) =
        ∫ u : ℝ, f u * star (f u) := by
    exact integral_comp_add_right_eq_self_complex
      (fun u : ℝ => f u * star (f u)) a
  exact congrArg Complex.re hshift

/-- Opposite autocorrelation values are complex conjugates. -/
theorem convolutionAutocorrelationKernel_neg_eq_conj
    (f : ZetaAdmissibleFunction) (a : ℝ) :
    convolutionAutocorrelationKernel f (-a) =
      star (convolutionAutocorrelationKernel f a) := by
  have hneg :
      convolutionAutocorrelationKernel f (-a) =
        zetaSeedInner (zetaTranslate (-a) f) f :=
    convolutionAutocorrelationKernel_eq_translateInner f (-a)
  have hshift :
      zetaSeedInner (zetaTranslate (-a) f) f =
        zetaSeedInner f (zetaTranslate a f) :=
    zetaSeedInner_translate_neg_left_eq_right a f
  have hconj :
      zetaSeedInner f (zetaTranslate a f) =
        star (zetaSeedInner (zetaTranslate a f) f) :=
    zetaSeedInner_conj_symm (zetaTranslate a f) f
  have hpos :
      zetaSeedInner (zetaTranslate a f) f =
        convolutionAutocorrelationKernel f a :=
    (convolutionAutocorrelationKernel_eq_translateInner f a).symm
  calc
    convolutionAutocorrelationKernel f (-a) =
        zetaSeedInner (zetaTranslate (-a) f) f := hneg
    _ = zetaSeedInner f (zetaTranslate a f) := hshift
    _ = star (zetaSeedInner (zetaTranslate a f) f) := hconj
    _ = star (convolutionAutocorrelationKernel f a) := by
      exact congrArg star hpos

/-- The real symmetric autocorrelation value is the real part of the translation pairing. -/
theorem convolutionAutocorrelationKernel_add_neg_eq_two_re_translateInner
    (f : ZetaAdmissibleFunction) (a : ℝ) :
    Complex.re (convolutionAutocorrelationKernel f a +
        convolutionAutocorrelationKernel f (-a)) =
      2 * Complex.re (zetaSeedInner (zetaTranslate a f) f) := by
  let z : ℂ := zetaSeedInner (zetaTranslate a f) f
  have hpos :
      convolutionAutocorrelationKernel f a = z :=
    convolutionAutocorrelationKernel_eq_translateInner f a
  have hneg :
      convolutionAutocorrelationKernel f (-a) = star z := by
    calc
      convolutionAutocorrelationKernel f (-a) =
          star (convolutionAutocorrelationKernel f a) :=
        convolutionAutocorrelationKernel_neg_eq_conj f a
      _ = star z := by
        exact congrArg star hpos
  have hstar_re :
      Complex.re (star z) = Complex.re z := by
    rfl
  calc
    Complex.re (convolutionAutocorrelationKernel f a +
        convolutionAutocorrelationKernel f (-a)) =
        Complex.re (convolutionAutocorrelationKernel f a) +
          Complex.re (convolutionAutocorrelationKernel f (-a)) := by
      exact Complex.add_re
        (convolutionAutocorrelationKernel f a)
        (convolutionAutocorrelationKernel f (-a))
    _ = Complex.re z + Complex.re (star z) := by
      exact congrArg₂ HAdd.hAdd
        (congrArg Complex.re hpos)
        (congrArg Complex.re hneg)
    _ = Complex.re z + Complex.re z := by
      exact congrArg (fun x : ℝ => Complex.re z + x) hstar_re
    _ = 2 * Complex.re z := by
      exact (two_mul (Complex.re z)).symm

/-- The translation-defect norm square expands into the diagonal terms minus the off-diagonal
translation pairing. -/
theorem zetaTranslationDefectNormSq_eq_diagonal_sub_offDiagonal
    (a : ℝ) (f : ZetaAdmissibleFunction) :
    zetaTranslationDefectNormSq a f =
      zetaSeedNormSq f + zetaSeedNormSq (zetaTranslate a f) -
        2 * Complex.re (zetaSeedInner (zetaTranslate a f) f) := by
  have hdef :
      zetaTranslationDefectNormSq a f =
        ∫ u : ℝ, Complex.re
          (zetaTranslationDefectValue a f u *
            star (zetaTranslationDefectValue a f u)) :=
    zetaTranslationDefectNormSq_eq_integral_re_conjSquare a f
  have hexp :
      (∫ u : ℝ, Complex.re
        (zetaTranslationDefectValue a f u *
          star (zetaTranslationDefectValue a f u))) =
        (∫ u : ℝ, Complex.re (f u * star (f u))) +
          (∫ u : ℝ,
            Complex.re (zetaTranslate a f u * star (zetaTranslate a f u))) -
          2 * (∫ u : ℝ,
            Complex.re (zetaTranslate a f u * star (f u))) :=
    integral_zetaTranslationDefectDensity_re_eq_diagonal_sub_offDiagonal a f
  have hseed :
      (∫ u : ℝ, Complex.re (f u * star (f u))) =
        zetaSeedNormSq f :=
    (zetaSeedNormSq_eq_integral_re_conjSquare f).symm
  have htranslate :
      (∫ u : ℝ,
        Complex.re (zetaTranslate a f u * star (zetaTranslate a f u))) =
        zetaSeedNormSq (zetaTranslate a f) :=
    (zetaSeedNormSq_eq_integral_re_conjSquare (zetaTranslate a f)).symm
  have hoff :
      (∫ u : ℝ, Complex.re (zetaTranslate a f u * star (f u))) =
        Complex.re (zetaSeedInner (zetaTranslate a f) f) := by
    unfold zetaSeedInner
    exact integral_re (zetaTranslationOffDiagonal_integrable a f)
  calc
    zetaTranslationDefectNormSq a f =
        ∫ u : ℝ, Complex.re
          (zetaTranslationDefectValue a f u *
            star (zetaTranslationDefectValue a f u)) := hdef
    _ =
        (∫ u : ℝ, Complex.re (f u * star (f u))) +
          (∫ u : ℝ,
            Complex.re (zetaTranslate a f u * star (zetaTranslate a f u))) -
          2 * (∫ u : ℝ,
            Complex.re (zetaTranslate a f u * star (f u))) := hexp
    _ =
        zetaSeedNormSq f +
          (∫ u : ℝ,
            Complex.re (zetaTranslate a f u * star (zetaTranslate a f u))) -
          2 * (∫ u : ℝ,
            Complex.re (zetaTranslate a f u * star (f u))) := by
      exact congrArg
        (fun x : ℝ =>
          x +
            (∫ u : ℝ,
              Complex.re (zetaTranslate a f u * star (zetaTranslate a f u))) -
            2 * (∫ u : ℝ,
              Complex.re (zetaTranslate a f u * star (f u))))
        hseed
    _ =
        zetaSeedNormSq f + zetaSeedNormSq (zetaTranslate a f) -
          2 * (∫ u : ℝ,
            Complex.re (zetaTranslate a f u * star (f u))) := by
      exact congrArg
        (fun x : ℝ =>
          zetaSeedNormSq f + x -
            2 * (∫ u : ℝ,
              Complex.re (zetaTranslate a f u * star (f u))))
        htranslate
    _ =
        zetaSeedNormSq f + zetaSeedNormSq (zetaTranslate a f) -
          2 * Complex.re (zetaSeedInner (zetaTranslate a f) f) := by
      exact congrArg
        (fun x : ℝ =>
          zetaSeedNormSq f + zetaSeedNormSq (zetaTranslate a f) - 2 * x)
        hoff

/-- With translation isometry, the defect square has the standard two-diagonal form. -/
theorem zetaTranslationDefectNormSq_eq_two_norm_sub_offDiagonal
    (a : ℝ) (f : ZetaAdmissibleFunction) :
    zetaTranslationDefectNormSq a f =
      2 * zetaSeedNormSq f -
        2 * Complex.re (zetaSeedInner (zetaTranslate a f) f) := by
  have hdef := zetaTranslationDefectNormSq_eq_diagonal_sub_offDiagonal a f
  have hiso := zetaTranslate_normSq a f
  calc
    zetaTranslationDefectNormSq a f =
        zetaSeedNormSq f + zetaSeedNormSq (zetaTranslate a f) -
          2 * Complex.re (zetaSeedInner (zetaTranslate a f) f) := hdef
    _ =
        zetaSeedNormSq f + zetaSeedNormSq f -
          2 * Complex.re (zetaSeedInner (zetaTranslate a f) f) := by
      exact congrArg
        (fun x : ℝ =>
          zetaSeedNormSq f + x -
            2 * Complex.re (zetaSeedInner (zetaTranslate a f) f))
        hiso
    _ =
        2 * zetaSeedNormSq f -
          2 * Complex.re (zetaSeedInner (zetaTranslate a f) f) := by
      exact real_add_self_sub_eq_two_mul_sub
        (zetaSeedNormSq f)
        (2 * Complex.re (zetaSeedInner (zetaTranslate a f) f))

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
