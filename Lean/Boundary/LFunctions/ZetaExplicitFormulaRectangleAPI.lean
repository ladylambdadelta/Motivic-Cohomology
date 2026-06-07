import Boundary.LFunctions.ZetaExplicitFormulaComplexAnalysis
import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Boundary explicit-formula rectangle API

This file re-exports the exact mathlib rectangle boundary theorem surface under
Boundary-facing names. The explicit-formula contour proof will consume these
aliases directly.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex

namespace ZetaAdmissibleFunction

/-- Boundary alias for the rectangle boundary integral theorem. -/
theorem boundary_integral_rect_of_has_fderiv_at_real_off_countable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : ℂ → E) (f' : ℂ → (ℂ →L[ℝ] E)) (z w : ℂ) (s : Set ℂ) (hs : s.Countable)
    (Hc : ContinuousOn f (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im))
    (Hd : ∀ x, x ∈ Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
        Set.Ioo (min z.im w.im) (max z.im w.im) \ s → HasFDerivAt f (f' x) x)
    (Hi : IntegrableOn (fun z => Complex.I • ⇑(f' z) 1 - ⇑(f' z) Complex.I)
      (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im) volume) :
    (((∫ x in z.re..w.re, f (x + z.im * Complex.I)) -
        ∫ x in z.re..w.re, f (x + w.im * Complex.I)) +
      Complex.I • ∫ y in z.im..w.im, f (w.re + y * Complex.I)) -
      Complex.I • ∫ y in z.im..w.im, f (z.re + y * Complex.I)
      =
      ∫ x in z.re..w.re, ∫ y in z.im..w.im,
        Complex.I • ⇑(f' (x + y * Complex.I)) 1 - ⇑(f' (x + y * Complex.I)) Complex.I := by
  exact Complex.integral_boundary_rect_of_has_fderiv_at_real_off_countable
    (f := f) (f' := f') (z := z) (w := w) (s := s) (hs := hs)
    (Hc := Hc) (Hd := Hd) (Hi := Hi)

/-- Boundary alias for the zero integral over a rectangle boundary. -/
theorem boundary_integral_rect_eq_zero_of_differentiable_on_off_countable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (f : ℂ → E) (z w : ℂ) (s : Set ℂ) (hs : s.Countable)
    (Hc : ContinuousOn f (Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im))
    (Hd : ∀ x, x ∈ Set.Ioo (min z.re w.re) (max z.re w.re) ×ℂ
        Set.Ioo (min z.im w.im) (max z.im w.im) \ s → DifferentiableAt ℂ f x) :
    ∫ x in z.re..w.re, f (x + z.im * Complex.I) -
        ∫ x in z.re..w.re, f (x + w.im * Complex.I) +
        Complex.I • ∫ y in z.im..w.im, f (w.re + y * Complex.I) -
        Complex.I • ∫ y in z.im..w.im, f (z.re + y * Complex.I) = 0 := by
  exact Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    (f := f) (z := z) (w := w) (s := s) (hs := hs) (Hc := Hc) (Hd := Hd)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
