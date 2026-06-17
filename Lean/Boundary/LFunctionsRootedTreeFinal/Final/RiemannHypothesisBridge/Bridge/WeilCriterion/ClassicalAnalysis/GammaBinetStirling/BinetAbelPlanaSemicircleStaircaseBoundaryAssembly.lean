import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleStaircaseBoundaryNormalization

/-!
# Boundary assembly for semicircle staircase cells

This file owns the passage from normalized cell-boundary pieces to the named
polygonal half-collar boundary.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology Interval
open Filter MeasureTheory

/-- If the horizontal tails, outer vertical sides, and inner vertical sides
have already been identified, the finite sum of cell boundaries is the named
polygonal half-collar boundary. -/
theorem Complex.sum_rightSemicircleStaircaseCellBoundary_eq_polygonalCoreBoundary_of_parts_algebra
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ)
    (hhorizontal :
      (∑ k in Finset.range (m + 1),
          ((∫ x : ℝ in
              (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k)..(c.re + ρ),
              f ((x : ℂ) +
                Complex.I *
                  (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))) -
            (∫ x : ℝ in
              (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k)..(c.re + ρ),
              f ((x : ℂ) +
                Complex.I *
                  (((c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) : ℝ) : ℂ)))))) =
        (∫ x : ℝ in c.re..(c.re + ρ),
            f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) -
          (∫ x : ℝ in c.re..(c.re + ρ),
            f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) -
          (∑ k in Finset.range (m + 1),
            Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) -
          Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m)
    (houter :
      (∑ k in Finset.range (m + 1),
          ∫ y : ℝ in
            (c.im + Complex.rightSemicircleStaircaseY ρ m k)..
              (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)),
            f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) =
        ∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
          f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
    (hinner :
      (∑ k in Finset.range (m + 1),
          Complex.I *
            (∫ y : ℝ in
              (c.im + Complex.rightSemicircleStaircaseY ρ m k)..
                (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)),
              f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
                Complex.I * (y : ℂ)))) =
        ∑ k in Finset.range (m + 1),
          Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k) :
    (∑ k in Finset.range (m + 1),
        Complex.rightSemicircleStaircaseCellBoundaryIntegral f c ρ m k) =
      Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundaryIntegral f c ρ m := by
  let H : ℕ → ℂ := fun k =>
    ∫ x : ℝ in
      (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k)..(c.re + ρ),
      f ((x : ℂ) +
        Complex.I *
          (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))
  let T : ℕ → ℂ := fun k =>
    ∫ x : ℝ in
      (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k)..(c.re + ρ),
      f ((x : ℂ) +
        Complex.I *
          (((c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) : ℝ) : ℂ)))
  let O : ℕ → ℂ := fun k =>
    ∫ y : ℝ in
      (c.im + Complex.rightSemicircleStaircaseY ρ m k)..
        (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)),
      f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))
  let J : ℕ → ℂ := fun k =>
    ∫ y : ℝ in
      (c.im + Complex.rightSemicircleStaircaseY ρ m k)..
        (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)),
      f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
        Complex.I * (y : ℂ))
  have hcell_parts :
      (∑ k in Finset.range (m + 1),
          Complex.rightSemicircleStaircaseCellBoundaryIntegral f c ρ m k) =
        Finset.sum (Finset.range (m + 1))
          (fun k => (H k - T k) + Complex.I * O k - Complex.I * J k) :=
    Finset.sum_congr
      rfl
      (fun k _hk =>
        Complex.rightSemicircleStaircaseCellBoundaryIntegral_eq_parts f c ρ m k)
  have hcollected :
      Finset.sum (Finset.range (m + 1))
          (fun k => (H k - T k) + Complex.I * O k - Complex.I * J k) =
        (∫ x : ℝ in c.re..(c.re + ρ),
            f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) -
          (∫ x : ℝ in c.re..(c.re + ρ),
            f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) +
          Complex.I *
            (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
              f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
          (((∑ k in Finset.range (m + 1),
              Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) +
            (∑ k in Finset.range (m + 1),
              Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k)) +
            Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m) :=
    Complex.sum_staircaseCellBoundary_parts_collect
      (Finset.range (m + 1))
      H T O J
      (∫ x : ℝ in c.re..(c.re + ρ),
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ)))
      (∫ x : ℝ in c.re..(c.re + ρ),
        f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)))
      (∑ k in Finset.range (m + 1),
        Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k)
      (Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m)
      (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
        f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
      (∑ k in Finset.range (m + 1),
        Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k)
      Complex.I
      hhorizontal
      houter
      hinner
  have hpolygonal :
      Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundaryIntegral f c ρ m =
        (∫ x : ℝ in c.re..(c.re + ρ),
            f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) -
          (∫ x : ℝ in c.re..(c.re + ρ),
            f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) +
          Complex.I *
            (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
              f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
          (((∑ k in Finset.range (m + 1),
              Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) +
            (∑ k in Finset.range (m + 1),
              Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k)) +
            Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m) :=
    Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundaryIntegral_eq_parts f c ρ m
  exact Eq.trans hcell_parts (Eq.trans hcollected hpolygonal.symm)

/-- If the horizontal tails, outer vertical sides, and inner vertical sides
have already been identified, the finite sum of cell boundaries is the named
polygonal half-collar boundary. -/
theorem Complex.sum_rightSemicircleStaircaseCellBoundary_eq_polygonalCoreBoundary_of_parts
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ)
    (hhorizontal :
      (∑ k in Finset.range (m + 1),
          ((∫ x : ℝ in
              (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k)..(c.re + ρ),
              f ((x : ℂ) +
                Complex.I *
                  (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))) -
            (∫ x : ℝ in
              (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k)..(c.re + ρ),
              f ((x : ℂ) +
                Complex.I *
                  (((c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) : ℝ) : ℂ)))))) =
        (∫ x : ℝ in c.re..(c.re + ρ),
            f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) -
          (∫ x : ℝ in c.re..(c.re + ρ),
            f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) -
          (∑ k in Finset.range (m + 1),
            Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) -
          Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m)
    (houter :
      (∑ k in Finset.range (m + 1),
          ∫ y : ℝ in
            (c.im + Complex.rightSemicircleStaircaseY ρ m k)..
              (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)),
            f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) =
        ∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
          f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
    (hinner :
      (∑ k in Finset.range (m + 1),
          Complex.I *
            (∫ y : ℝ in
              (c.im + Complex.rightSemicircleStaircaseY ρ m k)..
                (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)),
              f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
                Complex.I * (y : ℂ)))) =
        ∑ k in Finset.range (m + 1),
          Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k) :
    (∑ k in Finset.range (m + 1),
        Complex.rightSemicircleStaircaseCellBoundaryIntegral f c ρ m k) =
      Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundaryIntegral f c ρ m := by
  exact
    Complex.sum_rightSemicircleStaircaseCellBoundary_eq_polygonalCoreBoundary_of_parts_algebra
      f c ρ m hhorizontal houter hinner

/-- The finite sum of staircase strip boundaries assembles to the polygonal
half-collar boundary. -/
theorem Complex.sum_rightSemicircleStaircaseCellBoundary_eq_polygonalCoreBoundary
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m : ℕ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    (∑ k in Finset.range (m + 1),
        Complex.rightSemicircleStaircaseCellBoundaryIntegral f c ρ m k) =
      Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundaryIntegral f c ρ m := by
  have hhorizontal :=
    Complex.sum_rightSemicircleStaircaseCellHorizontal_eq_outerHorizontal_sub_arcHorizontal
      f c hρ m hcont
  have houter :=
    Complex.sum_rightSemicircleStaircaseCellOuterVertical_eq_outerVertical
      f c hρ m hcont
  have hinner :=
    Complex.sum_rightSemicircleStaircaseCellInnerVertical_eq_verticalArc
      f c ρ m
  exact
    Complex.sum_rightSemicircleStaircaseCellBoundary_eq_polygonalCoreBoundary_of_parts
      f c ρ m hhorizontal houter hinner

end

end LFunctions
end Boundary
