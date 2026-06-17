import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleStaircaseCauchyCell

/-!
# Cauchy-Goursat cancellation on one semicircle staircase cell

This file owns the finite rectangular Cauchy cancellation for one cell of the
semicircle staircase.  The surrounding geometry file consumes this theorem as a
single named boundary-cancellation input.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology Interval
open Filter MeasureTheory

/-- Cauchy-Goursat on one rectangular strip of the staircase exhaustion. -/
theorem Complex.rightSemicircleStaircaseCellBoundary_eq_zero
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1))
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Complex.rightSemicircleStaircaseCellBoundaryIntegral f c ρ m k = 0 := by
  let z₀ : ℂ :=
    (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
      Complex.I * (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))
  let z₁ : ℂ :=
    (((c.re + ρ : ℝ) : ℂ) +
      Complex.I * (((c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) : ℝ) : ℂ)))
  have hclosed :
      ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) ⊆
        Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
    exact
      Complex.rightSemicircleStaircaseCellCauchyRectangle_subset_core
        c hρ m k hk
  have hopen :
      (Set.Ioo (min z₀.re z₁.re) (max z₀.re z₁.re) ×ℂ
          Set.Ioo (min z₀.im z₁.im) (max z₀.im z₁.im)) ⊆
        Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
    exact
      Complex.rightSemicircleStaircaseCellCauchyOpenRectangle_subset_core
        c hρ m k hk
  have hcontinuous_closed :
      ContinuousOn f ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) :=
    hcont.mono hclosed
  have hdifferentiable_open :
      DifferentiableOn ℂ f
        (Set.Ioo (min z₀.re z₁.re) (max z₀.re z₁.re) ×ℂ
          Set.Ioo (min z₀.im z₁.im) (max z₀.im z₁.im)) :=
    hdiff.mono hopen
  have hcauchy :
      (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₀.im : ℂ) * Complex.I)) -
          (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₁.im : ℂ) * Complex.I)) +
            Complex.I •
              (∫ y : ℝ in z₀.im..z₁.im, f ((z₁.re : ℂ) + (y : ℂ) * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in z₀.im..z₁.im, f ((z₀.re : ℂ) + (y : ℂ) * Complex.I)) =
        0 :=
    Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
      f z₀ z₁ hcontinuous_closed hdifferentiable_open
  show
    (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₀.im : ℂ) * Complex.I)) -
        (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₁.im : ℂ) * Complex.I)) +
          Complex.I •
            (∫ y : ℝ in z₀.im..z₁.im, f ((z₁.re : ℂ) + (y : ℂ) * Complex.I)) -
            Complex.I •
              (∫ y : ℝ in z₀.im..z₁.im, f ((z₀.re : ℂ) + (y : ℂ) * Complex.I)) =
      0
  exact hcauchy

end

end LFunctions
end Boundary
