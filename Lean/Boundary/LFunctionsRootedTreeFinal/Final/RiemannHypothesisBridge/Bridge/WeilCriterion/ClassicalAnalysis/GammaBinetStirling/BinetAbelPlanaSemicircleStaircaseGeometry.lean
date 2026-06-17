import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleStaircaseBoundaryAssembly

/-!
# Semicircle staircase geometry for finite-height Abel-Plana collars

This file owns the polygonal staircase approximation to the right semicircle and
its finite Cauchy-Goursat boundary cancellation.  Later contour files consume
this geometry to prove convergence to the curvilinear semicircle boundary.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology Interval
open Filter MeasureTheory

/-- Finite Cauchy-Goursat for the exterior staircase half-collar, after the
cell boundaries and the finite boundary assembly have been identified. -/
theorem Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundary_eq_zero_from_staircaseGeometry
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m : ℕ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundaryIntegral f c ρ m = 0 := by
  have hcell_zero :
      ∀ k ∈ Finset.range (m + 1),
        Complex.rightSemicircleStaircaseCellBoundaryIntegral f c ρ m k = 0 := by
    intro k hk
    exact
      Complex.rightSemicircleStaircaseCellBoundary_eq_zero
        f c hρ m k hk hcont hdiff
  have hsum_zero :
      (∑ k in Finset.range (m + 1),
          Complex.rightSemicircleStaircaseCellBoundaryIntegral f c ρ m k) = 0 := by
    exact Finset.sum_eq_zero hcell_zero
  have hassemble :
      (∑ k in Finset.range (m + 1),
          Complex.rightSemicircleStaircaseCellBoundaryIntegral f c ρ m k) =
        Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundaryIntegral f c ρ m :=
    Complex.sum_rightSemicircleStaircaseCellBoundary_eq_polygonalCoreBoundary
      f c hρ m hcont
  exact Eq.trans hassemble.symm hsum_zero

/-- Generic finite polygonal Cauchy-Goursat theorem for the right half-collar.

This is the finite path-integration owner theorem used by the local collar
argument.  The polygonal boundary is obtained by replacing the inner right
semicircle by its exterior staircase.  Cauchy-Goursat applies on the finite
polygonal subdivision of the half-collar, and internal chord contributions
cancel in pairs. -/
theorem Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundary_eq_zero_owner
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m : ℕ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundaryIntegral f c ρ m = 0 := by
  exact
    Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundary_eq_zero_from_staircaseGeometry
      f c hρ m hcont hdiff

/-- Finite polygonal Cauchy-Goursat for the full right half-collar.

For each polygonal approximation to the deleted right semicircle, the polygonal
half-collar is decomposed into finitely many ordinary polygonal cells.  Cauchy-
Goursat kills each cell boundary, and all internal edges cancel, leaving the
displayed polygonal core boundary. -/
theorem Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundary_eq_zero
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m : ℕ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundaryIntegral f c ρ m = 0 := by
  exact
    Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundary_eq_zero_owner
      f c hρ m hcont hdiff

end

end LFunctions
end Boundary
