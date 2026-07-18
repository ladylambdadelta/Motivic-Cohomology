import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.SquareSideGeometry

/-!
# Horizontal excision-side integrability
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- A raw-strip horizontal level avoiding every raw singular height gives sorted-side
integrability for every horizontal endpoint subdivision. -/
theorem explicitFormulaRectangleSortedXHorizontalSideIntegrable_of_regularLevel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f) (T radius y : ℝ)
    (hy : |y| < T)
    (hlevel :
      ∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates T → y ≠ b.im) :
    explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T radius y := by
  exact
    explicitFormulaRectangleSortedXHorizontalSideIntegrable_of_avoidsSingularSet
      f F hPhi T radius y
      (fun k hk x hx =>
        explicitFormulaRectangle_horizontalLine_avoidsSingularSet
          T y hy hlevel x)

/-- The lower horizontal side of every selected inscribed square is sorted-side
integrable at a square-side regular radius. -/
theorem explicitFormulaRectangleSortedXHorizontalSideIntegrable_lowerHole_of_regularRadius
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f) {T epsilon : ℝ}
    (hepsilon : 0 < epsilon)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a epsilon ⊆ explicitFormulaContourFamilyInterior F T)
    (hregular :
      epsilon ∉ finiteRectangleSquareSideForbiddenRadii
        (explicitFormulaRectangleRawSingularCoordinates T))
    (a : ℂ) (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    explicitFormulaRectangleSortedXHorizontalSideIntegrable
      f F T (epsilon / 2)
        (explicitFormulaRectangleRawInscribedSquareLowerCorner (epsilon / 2) a).im := by
  have hhalf : 0 < epsilon / 2 :=
    finiteRectangle_halfRadius_pos hepsilon
  have hclosedHalf :
      ∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall b (epsilon / 2) ⊆
            explicitFormulaContourFamilyInterior F T :=
    explicitFormulaRectangleRawSingularCoordinates_halfRadius_closedBall_subset_interior
      F hepsilon hclosed
  have him :
      (explicitFormulaRectangleRawInscribedSquareLowerCorner (epsilon / 2) a).im ∈
        Set.Ioo (-T) T :=
    explicitFormulaRectangleInscribedSquareLowerCorner_im_mem_vertical_Ioo_of_closedRadiusControls
      F T (epsilon / 2) (le_of_lt hhalf) hclosedHalf ha
  have habs :
      |(explicitFormulaRectangleRawInscribedSquareLowerCorner (epsilon / 2) a).im| < T :=
    abs_lt.mpr him
  have hlevel :
      ∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates T →
          (explicitFormulaRectangleRawInscribedSquareLowerCorner (epsilon / 2) a).im ≠
            b.im :=
    fun b hb =>
      explicitFormulaRectangleRawInscribedSquareLowerCorner_im_ne_rawSingular
        (explicitFormulaRectangleRawSingularCoordinates T)
        epsilon hregular ha hb
  exact
    explicitFormulaRectangleSortedXHorizontalSideIntegrable_of_regularLevel
      f F hPhi T (epsilon / 2)
      (explicitFormulaRectangleRawInscribedSquareLowerCorner (epsilon / 2) a).im
      habs hlevel

/-- The upper horizontal side of every selected inscribed square is sorted-side
integrable at a square-side regular radius. -/
theorem explicitFormulaRectangleSortedXHorizontalSideIntegrable_upperHole_of_regularRadius
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (hPhi : ZetaPhiAnalyticControl f) {T epsilon : ℝ}
    (hepsilon : 0 < epsilon)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a epsilon ⊆ explicitFormulaContourFamilyInterior F T)
    (hregular :
      epsilon ∉ finiteRectangleSquareSideForbiddenRadii
        (explicitFormulaRectangleRawSingularCoordinates T))
    (a : ℂ) (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    explicitFormulaRectangleSortedXHorizontalSideIntegrable
      f F T (epsilon / 2)
        (explicitFormulaRectangleRawInscribedSquareUpperCorner (epsilon / 2) a).im := by
  have hhalf : 0 < epsilon / 2 :=
    finiteRectangle_halfRadius_pos hepsilon
  have hclosedHalf :
      ∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall b (epsilon / 2) ⊆
            explicitFormulaContourFamilyInterior F T :=
    explicitFormulaRectangleRawSingularCoordinates_halfRadius_closedBall_subset_interior
      F hepsilon hclosed
  have him :
      (explicitFormulaRectangleRawInscribedSquareUpperCorner (epsilon / 2) a).im ∈
        Set.Ioo (-T) T :=
    explicitFormulaRectangleInscribedSquareUpperCorner_im_mem_vertical_Ioo_of_closedRadiusControls
      F T (epsilon / 2) (le_of_lt hhalf) hclosedHalf ha
  have habs :
      |(explicitFormulaRectangleRawInscribedSquareUpperCorner (epsilon / 2) a).im| < T :=
    abs_lt.mpr him
  have hlevel :
      ∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates T →
          (explicitFormulaRectangleRawInscribedSquareUpperCorner (epsilon / 2) a).im ≠
            b.im :=
    fun b hb =>
      explicitFormulaRectangleRawInscribedSquareUpperCorner_im_ne_rawSingular
        (explicitFormulaRectangleRawSingularCoordinates T)
        epsilon hregular ha hb
  exact
    explicitFormulaRectangleSortedXHorizontalSideIntegrable_of_regularLevel
      f F hPhi T (epsilon / 2)
      (explicitFormulaRectangleRawInscribedSquareUpperCorner (epsilon / 2) a).im
      habs hlevel

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
