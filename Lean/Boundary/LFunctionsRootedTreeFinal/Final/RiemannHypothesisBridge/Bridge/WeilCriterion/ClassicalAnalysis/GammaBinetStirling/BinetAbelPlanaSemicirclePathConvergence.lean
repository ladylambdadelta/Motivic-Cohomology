import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleApproximation

/-!
# Right-semicircle path convergence wrappers

This file owns the final path-convergence wrappers downstream of the
right-semicircle approximation estimates.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Filter MeasureTheory
open scoped Topology

theorem Complex.rightSemicircleStaircaseHorizontal_recompose_point
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) :
    Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m +
      (((∑ k in Finset.range (m + 1),
        Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) +
        Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m) -
        Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m) =
      (∑ k in Finset.range (m + 1),
        Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) +
        Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m :=
  add_sub_right_cancel'
    (Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m)
    ((∑ k in Finset.range (m + 1),
        Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) +
      Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m)

/-- The graph finite-difference horizontal samples converge to the nonzero
horizontal graph contribution.  The samples are taken from the uniform height
partition and use the safe-coordinate finite differences; this is the
owner-level path-projection consequence for the horizontal part of the right
semicircle. -/
theorem Complex.rightSemicircleStaircaseHorizontalSampleSum_tendsto_graphHorizontal
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Tendsto
      (fun m : ℕ =>
        Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m)
      atTop
      (𝓝 (Complex.rightSemicircleGraphHorizontalIntegral f c ρ)) := by
  exact
    Complex.rightSemicircleStaircaseHorizontalSampleSum_tendsto_graphHorizontal_ownerQuadrature
      f c hρ hcont

/-- The graph finite-difference horizontal samples converge to the nonzero
`dx` component of the circular line integral. -/
theorem Complex.rightSemicircleStaircaseHorizontalSampleSum_tendsto_angle_dx
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Tendsto
      (fun m : ℕ =>
        Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m)
      atTop
      (𝓝
        (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (((-ρ * Real.sin θ : ℝ) : ℂ)))) := by
  have hgraph :
      Tendsto
        (fun m : ℕ =>
          Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m)
        atTop
        (𝓝 (Complex.rightSemicircleGraphHorizontalIntegral f c ρ)) :=
    Complex.rightSemicircleStaircaseHorizontalSampleSum_tendsto_graphHorizontal
      f c hρ hcont
  have htarget :
      Complex.rightSemicircleGraphHorizontalIntegral f c ρ =
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (((-ρ * Real.sin θ : ℝ) : ℂ)) :=
    Complex.rightSemicircleGraphHorizontalIntegral_eq_angle_dx
      f c hρ hcont
  exact htarget ▸ hgraph

/-- Horizontal staircase connectors, including the final top connector,
converge to the nonvertical `dx` part of the circular graph integral. -/
theorem Complex.rightSemicircleStaircaseHorizontalIntegral_tendsto_graphHorizontal
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Tendsto
      (fun m : ℕ =>
        (∑ k in Finset.range (m + 1),
          Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) +
          Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m)
      atTop
      (𝓝 (Complex.rightSemicircleGraphHorizontalIntegral f c ρ)) := by
  have hsamples :
      Tendsto
        (fun m : ℕ =>
          Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m)
        atTop
        (𝓝 (Complex.rightSemicircleGraphHorizontalIntegral f c ρ)) :=
    Complex.rightSemicircleStaircaseHorizontalSampleSum_tendsto_graphHorizontal
      f c hρ hcont
  have herr :
      Tendsto
        (fun m : ℕ =>
          ((∑ k in Finset.range (m + 1),
            Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) +
            Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m) -
            Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m)
        atTop
        (𝓝 0) :=
    Complex.rightSemicircleStaircaseHorizontalIntegral_sub_sampleSum_tendsto_zero
      f c hρ hcont
  have hsum :
      Tendsto
        (fun m : ℕ =>
          Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m +
            (((∑ k in Finset.range (m + 1),
              Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) +
              Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m) -
              Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m))
        atTop
        (𝓝
          (Complex.rightSemicircleGraphHorizontalIntegral f c ρ + 0)) :=
    hsamples.add herr
  have hsum_target :
      Tendsto
        (fun m : ℕ =>
          Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m +
            (((∑ k in Finset.range (m + 1),
              Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) +
              Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m) -
              Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m))
        atTop
        (𝓝 (Complex.rightSemicircleGraphHorizontalIntegral f c ρ)) := by
    have htarget :
        Complex.rightSemicircleGraphHorizontalIntegral f c ρ + 0 =
          Complex.rightSemicircleGraphHorizontalIntegral f c ρ :=
      add_zero (Complex.rightSemicircleGraphHorizontalIntegral f c ρ)
    exact
      Eq.subst
        (motive := fun z : ℂ =>
          Tendsto
            (fun m : ℕ =>
              Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m +
                (((∑ k in Finset.range (m + 1),
                  Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) +
                  Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m) -
                  Complex.rightSemicircleStaircaseHorizontalSampleSum f c ρ m))
            atTop
            (𝓝 z))
        htarget
        hsum
  exact
    Tendsto.congr'
      (Filter.Eventually.of_forall
        (fun m : ℕ =>
          Complex.rightSemicircleStaircaseHorizontal_recompose_point
            f c ρ m))
      hsum_target

/-- Exterior staircase line-integral convergence for the right semicircle. -/
theorem Complex.rightSemicircleStaircaseArcIntegral_tendsto_owner
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Tendsto
      (fun m : ℕ => Complex.rightSemicirclePolygonalArcIntegral f c ρ m)
      atTop
      (𝓝
        (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))) := by
  exact
    Complex.rightSemicircleStaircaseArcIntegral_tendsto_by_pathApproximation
      f c hρ hcont

/-- Exterior staircase approximations to the full inner right semicircle
converge to the circular line integral. -/
theorem Complex.rightSemicirclePolygonalArcIntegral_tendsto
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Tendsto
      (fun m : ℕ => Complex.rightSemicirclePolygonalArcIntegral f c ρ m)
      atTop
      (𝓝
        (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))) := by
  exact
    Complex.rightSemicircleStaircaseArcIntegral_tendsto_owner
      f c hρ hcont

end

end LFunctions
end Boundary
