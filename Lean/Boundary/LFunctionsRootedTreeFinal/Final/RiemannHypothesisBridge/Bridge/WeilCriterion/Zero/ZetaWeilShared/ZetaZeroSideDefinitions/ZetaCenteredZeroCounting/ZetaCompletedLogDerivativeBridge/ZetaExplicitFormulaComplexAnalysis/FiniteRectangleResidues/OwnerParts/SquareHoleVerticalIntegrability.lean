import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.SortedVerticalSpan

/-!
# Vertical excision-side integrability
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- A regular vertical level gives sorted-side integrability throughout the scheduled
closed height span. -/
theorem explicitFormulaRectangleSortedYVerticalSideIntegrable_of_regularLevel
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u radius x : ℝ)
    (hT : 0 < h.height_schedule.height u) (hradius : 0 ≤ radius)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          Metric.closedBall a radius ⊆
            explicitFormulaContourFamilyInterior F (h.height_schedule.height u))
    (hx : x ∈ Set.uIcc F.c (1 - F.c))
    (hlevel :
      ∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          x ≠ b.re) :
    explicitFormulaRectangleSortedYVerticalSideIntegrable
      f (h.height_schedule.height u) radius x := by
  exact
    explicitFormulaRectangleSortedYVerticalSideIntegrable_of_avoidsSingularSet
      f h.phi_control (h.height_schedule.height u) radius x
      (fun k hk y hy =>
        explicitFormulaRectangle_verticalLine_avoidsSingularSet_on_closedHeightSpan
          f F h u x y hx
          (explicitFormulaRectangleSortedYAdjacent_uIcc_subset_vertical_Icc
            F (h.height_schedule.height u) radius (le_of_lt hT) hradius hclosed k hk hy)
          hlevel)

/-- The right vertical side of every selected inscribed square is sorted-side integrable
at a square-side regular radius. -/
theorem explicitFormulaRectangleSortedYVerticalSideIntegrable_upperHole_of_regularRadius
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {u epsilon : ℝ}
    (hT : 0 < h.height_schedule.height u) (hepsilon : 0 < epsilon)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          Metric.closedBall a epsilon ⊆
            explicitFormulaContourFamilyInterior F (h.height_schedule.height u))
    (hregular :
      epsilon ∉ finiteRectangleSquareSideForbiddenRadii
        (explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u)))
    (a : ℂ)
    (ha : a ∈
      explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u)) :
    explicitFormulaRectangleSortedYVerticalSideIntegrable
      f (h.height_schedule.height u) (epsilon / 2)
        (explicitFormulaRectangleRawInscribedSquareUpperCorner (epsilon / 2) a).re := by
  have hhalf : 0 < epsilon / 2 := finiteRectangle_halfRadius_pos hepsilon
  have hclosedHalf :
      ∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          Metric.closedBall b (epsilon / 2) ⊆
            explicitFormulaContourFamilyInterior F (h.height_schedule.height u) :=
    explicitFormulaRectangleRawSingularCoordinates_halfRadius_closedBall_subset_interior
      F hepsilon hclosed
  have hx :
      (explicitFormulaRectangleRawInscribedSquareUpperCorner (epsilon / 2) a).re ∈
        Set.uIcc F.c (1 - F.c) :=
    Set.uIoo_subset_uIcc F.c (1 - F.c)
      (explicitFormulaRectangleInscribedSquareUpperCorner_re_mem_horizontal_uIoo_of_closedRadiusControls
        F (h.height_schedule.height u) (epsilon / 2) (le_of_lt hhalf) hclosedHalf ha)
  have hlevel :
      ∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          (explicitFormulaRectangleRawInscribedSquareUpperCorner (epsilon / 2) a).re ≠
            b.re :=
    fun b hb =>
      explicitFormulaRectangleRawInscribedSquareUpperCorner_re_ne_rawSingular
        (explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u))
        epsilon hregular ha hb
  exact
    explicitFormulaRectangleSortedYVerticalSideIntegrable_of_regularLevel
      f F h u (epsilon / 2)
      (explicitFormulaRectangleRawInscribedSquareUpperCorner (epsilon / 2) a).re
      hT (le_of_lt hhalf) hclosedHalf hx hlevel

/-- The left vertical side of every selected inscribed square is sorted-side integrable
at a square-side regular radius. -/
theorem explicitFormulaRectangleSortedYVerticalSideIntegrable_lowerHole_of_regularRadius
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {u epsilon : ℝ}
    (hT : 0 < h.height_schedule.height u) (hepsilon : 0 < epsilon)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          Metric.closedBall a epsilon ⊆
            explicitFormulaContourFamilyInterior F (h.height_schedule.height u))
    (hregular :
      epsilon ∉ finiteRectangleSquareSideForbiddenRadii
        (explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u)))
    (a : ℂ)
    (ha : a ∈
      explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u)) :
    explicitFormulaRectangleSortedYVerticalSideIntegrable
      f (h.height_schedule.height u) (epsilon / 2)
        (explicitFormulaRectangleRawInscribedSquareLowerCorner (epsilon / 2) a).re := by
  have hhalf : 0 < epsilon / 2 := finiteRectangle_halfRadius_pos hepsilon
  have hclosedHalf :
      ∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          Metric.closedBall b (epsilon / 2) ⊆
            explicitFormulaContourFamilyInterior F (h.height_schedule.height u) :=
    explicitFormulaRectangleRawSingularCoordinates_halfRadius_closedBall_subset_interior
      F hepsilon hclosed
  have hx :
      (explicitFormulaRectangleRawInscribedSquareLowerCorner (epsilon / 2) a).re ∈
        Set.uIcc F.c (1 - F.c) :=
    Set.uIoo_subset_uIcc F.c (1 - F.c)
      (explicitFormulaRectangleInscribedSquareLowerCorner_re_mem_horizontal_uIoo_of_closedRadiusControls
        F (h.height_schedule.height u) (epsilon / 2) (le_of_lt hhalf) hclosedHalf ha)
  have hlevel :
      ∀ b : ℂ,
        b ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          (explicitFormulaRectangleRawInscribedSquareLowerCorner (epsilon / 2) a).re ≠
            b.re :=
    fun b hb =>
      explicitFormulaRectangleRawInscribedSquareLowerCorner_re_ne_rawSingular
        (explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u))
        epsilon hregular ha hb
  exact
    explicitFormulaRectangleSortedYVerticalSideIntegrable_of_regularLevel
      f F h u (epsilon / 2)
      (explicitFormulaRectangleRawInscribedSquareLowerCorner (epsilon / 2) a).re
      hT (le_of_lt hhalf) hclosedHalf hx hlevel

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
