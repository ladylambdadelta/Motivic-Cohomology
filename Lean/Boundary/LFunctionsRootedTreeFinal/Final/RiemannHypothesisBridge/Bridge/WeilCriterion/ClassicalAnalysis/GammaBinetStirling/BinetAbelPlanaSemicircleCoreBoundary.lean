import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicirclePathConvergence
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleCoreTail

/-!
# Semicircular core boundary wrappers

This file owns the final boundary-convergence and tangent-width
semicircular-core Cauchy-Goursat theorem.  Wider collar assembly is owned by
`BinetAbelPlanaSemicircleCoreCauchy`.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter MeasureTheory
open scoped Topology Interval

/-- The polygonal full half-collar boundary converges to the true curvilinear
semicircular-core boundary. -/
theorem Complex.tendsto_rightHalfRectangleDeletedDiskPolygonalCoreBoundary
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Tendsto
      (fun m : ℕ =>
        Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundaryIntegral f c ρ m)
      atTop
      (𝓝 (Complex.rightHalfRectangleDeletedDiskSemicircularCoreBoundaryIntegral f c ρ)) := by
  have harc :
      Tendsto
        (fun m : ℕ => Complex.rightSemicirclePolygonalArcIntegral f c ρ m)
        atTop
        (𝓝
          (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
            f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))) :=
    Complex.rightSemicirclePolygonalArcIntegral_tendsto f c hρ hcont
  let C : ℂ :=
    (∫ x : ℝ in c.re..(c.re + ρ),
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) -
      (∫ x : ℝ in c.re..(c.re + ρ),
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) +
        Complex.I *
          (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
            f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
  have hconst :
      Tendsto (fun _ : ℕ => C) atTop (𝓝 C) :=
    tendsto_const_nhds
  show
    Tendsto
      (fun m : ℕ => C - Complex.rightSemicirclePolygonalArcIntegral f c ρ m)
      atTop
      (𝓝
        (C -
          (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
            f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))))
  exact hconst.sub harc

/-- Cauchy-Goursat for the tangent-width semicircular half-collar.

The tangent-width half-rectangle with the center disk removed has boundary
equal to the lower tangent chord, the outer vertical tangent chord, the upper
tangent chord with opposite orientation, and the inner right semicircle with
deleted-boundary orientation. -/
theorem Complex.rightHalfRectangleDeletedDiskSemicircularCoreBoundary_eq_zero
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Complex.rightHalfRectangleDeletedDiskSemicircularCoreBoundaryIntegral f c ρ = 0 := by
  exact
    Complex.eq_zero_of_tendsto_identically_zero
      (Filter.Eventually.of_forall
        (fun m : ℕ =>
          Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundary_eq_zero
            f c hρ m hcont hdiff))
      (Complex.tendsto_rightHalfRectangleDeletedDiskPolygonalCoreBoundary
        f c hρ hcont)

end

end LFunctions
end Boundary
