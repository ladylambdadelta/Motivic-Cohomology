import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.ComplementSubdivisionNarrow
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.SquareHoleHorizontalIntegrability
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.SquareHoleVerticalIntegrability
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.OuterSideIntegrability

/-!
# Selected-radius finite-hole Cauchy assembly
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

/-- All eight sorted side-integrability fields at one selected square-side regular radius. -/
theorem explicitFormulaRectangle_selectedRegularRadius_sideIntegrability_of_boundaryData
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (phiControl : ZetaPhiAnalyticControl f)
    (T : ℝ) {epsilon : ℝ} (hT : 0 < T) (hepsilon : 0 < epsilon)
    (hboundaryRegular :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hboundaryAvoidance :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          z ∉ completedZetaContourIntegrandSingularSet)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a epsilon ⊆
            explicitFormulaContourFamilyInterior F T)
    (hregular :
      epsilon ∉ finiteRectangleSquareSideForbiddenRadii
        (explicitFormulaRectangleRawSingularCoordinates T)) :
    explicitFormulaRectangleSortedXHorizontalSideIntegrable f F
        T (epsilon / 2) (-T) ∧
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F
        T (epsilon / 2) T ∧
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F
            T (epsilon / 2)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner (epsilon / 2) a).im) ∧
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F
            T (epsilon / 2)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner (epsilon / 2) a).im) ∧
      explicitFormulaRectangleSortedYVerticalSideIntegrable f
        T (epsilon / 2) F.c ∧
      explicitFormulaRectangleSortedYVerticalSideIntegrable f
        T (epsilon / 2) (1 - F.c) ∧
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f
            T (epsilon / 2)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner (epsilon / 2) a).re) ∧
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f
            T (epsilon / 2)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner (epsilon / 2) a).re) := by
  have hhalf : 0 < epsilon / 2 := finiteRectangle_halfRadius_pos hepsilon
  have hclosedHalf :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a (epsilon / 2) ⊆
            explicitFormulaContourFamilyInterior F T :=
    explicitFormulaRectangleRawSingularCoordinates_halfRadius_closedBall_subset_interior
      F hepsilon hclosed
  exact And.intro
    (explicitFormulaRectangleSortedXHorizontalSideIntegrable_bottom_of_boundaryRegular
      f F T (epsilon / 2) (le_of_lt hhalf) hboundaryRegular hclosedHalf)
    (And.intro
      (explicitFormulaRectangleSortedXHorizontalSideIntegrable_top_of_boundaryRegular
        f F T (epsilon / 2) (le_of_lt hhalf) hboundaryRegular hclosedHalf)
      (And.intro
        (fun a ha =>
          explicitFormulaRectangleSortedXHorizontalSideIntegrable_lowerHole_of_regularRadius
            f F phiControl hepsilon hclosed hregular a ha)
        (And.intro
          (fun a ha =>
            explicitFormulaRectangleSortedXHorizontalSideIntegrable_upperHole_of_regularRadius
              f F phiControl hepsilon hclosed hregular a ha)
          (And.intro
            (explicitFormulaRectangleSortedYVerticalSideIntegrable_right_of_boundaryRegular
              f F T (epsilon / 2) hT (le_of_lt hhalf) hboundaryRegular hclosedHalf)
            (And.intro
              (explicitFormulaRectangleSortedYVerticalSideIntegrable_left_of_boundaryRegular
                f F T (epsilon / 2) hT (le_of_lt hhalf) hboundaryRegular hclosedHalf)
              (And.intro
                (fun a ha =>
                  explicitFormulaRectangleSortedYVerticalSideIntegrable_upperHole_of_regularRadius_boundaryAvoidance
                    f F phiControl T hT hepsilon hboundaryAvoidance hclosed hregular a ha)
                (fun a ha =>
                  explicitFormulaRectangleSortedYVerticalSideIntegrable_lowerHole_of_regularRadius_boundaryAvoidance
                    f F phiControl T hT hepsilon hboundaryAvoidance hclosed hregular a ha)))))))

/-- All eight sorted side-integrability fields at one selected square-side regular radius. -/
theorem explicitFormulaRectangle_selectedRegularRadius_sideIntegrability
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
        (explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u))) :
    explicitFormulaRectangleSortedXHorizontalSideIntegrable f F
        (h.height_schedule.height u) (epsilon / 2) (-(h.height_schedule.height u)) ∧
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F
        (h.height_schedule.height u) (epsilon / 2) (h.height_schedule.height u) ∧
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F
            (h.height_schedule.height u) (epsilon / 2)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner (epsilon / 2) a).im) ∧
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F
            (h.height_schedule.height u) (epsilon / 2)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner (epsilon / 2) a).im) ∧
      explicitFormulaRectangleSortedYVerticalSideIntegrable f
        (h.height_schedule.height u) (epsilon / 2) F.c ∧
      explicitFormulaRectangleSortedYVerticalSideIntegrable f
        (h.height_schedule.height u) (epsilon / 2) (1 - F.c) ∧
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f
            (h.height_schedule.height u) (epsilon / 2)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner (epsilon / 2) a).re) ∧
      (∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f
            (h.height_schedule.height u) (epsilon / 2)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner (epsilon / 2) a).re) := by
  exact
    explicitFormulaRectangle_selectedRegularRadius_sideIntegrability_of_boundaryData
      f F h.phi_control (h.height_schedule.height u) hT hepsilon
      (explicitFormulaRectangleContourIntegrand_boundaryRegular_of_avoidsBoundary
        f F h (h.height_schedule.height u)
        (explicitFormulaScheduledRectangle_avoidsSingularBoundary f F h u))
      (fun z hz =>
        completedZetaContourIntegrand_not_mem_singularSet_of_scheduledBoundary
          f F h u hz)
      hclosed hregular

/-- Finite-hole Cauchy at one selected square-side regular radius from explicit
boundary data, a supplied complement-grid subdivision, and the supplied circle-square
deleted-boundary agreement. -/
theorem explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_selectedRegularRadius_boundaryData
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {T epsilon : ℝ}
    (hT : 0 < T) (hepsilon : 0 < epsilon)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow T ↔
          completedZeroResidueCoordinate rho ∈
              explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet)
    (hboundaryRegular :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hboundaryAvoidance :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          z ∉ completedZetaContourIntegrandSingularSet)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a epsilon ⊆ explicitFormulaContourFamilyInterior F T)
    (hseparated :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → epsilon + epsilon < dist a b)
    (hregular :
      epsilon ∉ finiteRectangleSquareSideForbiddenRadii
        (explicitFormulaRectangleRawSingularCoordinates T))
    (hgrid :
      ∀ radius : ℝ,
        0 < radius →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a radius ⊆ explicitFormulaContourFamilyInterior F T) →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (radius / 2) (-T) →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (radius / 2) T →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (radius / 2)
                (explicitFormulaRectangleRawInscribedSquareLowerCorner (radius / 2) a).im) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (radius / 2)
                (explicitFormulaRectangleRawInscribedSquareUpperCorner (radius / 2) a).im) →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T (radius / 2) F.c →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T (radius / 2) (1 - F.c) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              explicitFormulaRectangleSortedYVerticalSideIntegrable f T (radius / 2)
                (explicitFormulaRectangleRawInscribedSquareUpperCorner (radius / 2) a).re) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              explicitFormulaRectangleSortedYVerticalSideIntegrable f T (radius / 2)
                (explicitFormulaRectangleRawInscribedSquareLowerCorner (radius / 2) a).re) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → radius + radius < dist a b) →
            ∃ grid :
                List (ExplicitFormulaRectangleRegularGridCellEndpointData F T (radius / 2)),
              zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
                  ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
                    finiteRectangleSubdivisionCellBoundaryIntegral
                      (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                      (explicitFormulaRectangleRawInscribedSquareLowerCorner (radius / 2) a)
                      (explicitFormulaRectangleRawInscribedSquareUpperCorner (radius / 2) a) =
                explicitFormulaRectangleRegularGridEndpointDataBoundarySum f grid)
    (hdeleted :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleRawDeletedCircleBoundary f (epsilon / 2) a =
            explicitFormulaRectangleRawInscribedSquareBoundary f (epsilon / 2) a) :
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
      f F T epsilon = 0 := by
  match explicitFormulaRectangle_selectedRegularRadius_sideIntegrability_of_boundaryData
      f F h.phi_control T hT hepsilon hboundaryRegular hboundaryAvoidance hclosed hregular with
  | ⟨hbottom, htop, hbottomHole, htopHole, hright, hleft, hrightHole, hleftHole⟩ =>
      match hgrid epsilon hepsilon hclosed
          hbottom htop hbottomHole htopHole hright hleft hrightHole hleftHole hseparated with
      | ⟨grid, hsubdivision⟩ =>
          have hsquare :
              explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
                f F T (epsilon / 2) = 0 :=
            explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_endpointData_tangentContour_sub_rawInscribedSquareCellBoundarySum_halfRadius_closedRadiusControls
              grid f h hT hepsilon hinterior hboundaryRegular hclosed hsubdivision
          have hhalfZero :
              explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
                f F T (epsilon / 2) = 0 :=
            explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_deletedBoundary_eq_on
              f F T (epsilon / 2)
              (explicitFormulaRectangleRawInscribedSquareBoundary f (epsilon / 2))
              hsquare hdeleted
          exact
            explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_halfRadius_closedRadiusControls
              f F h hT hepsilon hinterior hclosed hseparated hhalfZero

/-- Finite-hole Cauchy at one selected square-side regular radius. -/
theorem explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_selectedRegularRadius
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) {u epsilon : ℝ}
    (hT : 0 < h.height_schedule.height u) (hepsilon : 0 < epsilon)
    (hinterior :
      ∀ rho : {rho : ℂ // ZetaCompletedZero rho},
        rho ∈ explicitFormulaCompletedZeroContourHeightWindow (h.height_schedule.height u) ↔
          completedZeroResidueCoordinate rho ∈
              explicitFormulaContourFamilyInterior F (h.height_schedule.height u) ∧
            completedZeroResidueCoordinate rho ∈ completedZetaContourIntegrandSingularSet)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          Metric.closedBall a epsilon ⊆
            explicitFormulaContourFamilyInterior F (h.height_schedule.height u))
    (hseparated :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
              a ≠ b → epsilon + epsilon < dist a b)
    (hregular :
      epsilon ∉ finiteRectangleSquareSideForbiddenRadii
        (explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u))) :
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
      f F (h.height_schedule.height u) epsilon = 0 := by
  have hboundaryRegular :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
          ContinuousAt
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z :=
    explicitFormulaRectangleContourIntegrand_boundaryRegular_of_avoidsBoundary
      f F h (h.height_schedule.height u)
      (explicitFormulaScheduledRectangle_avoidsSingularBoundary f F h u)
  have hboundaryAvoidance :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F (h.height_schedule.height u) →
          z ∉ completedZetaContourIntegrandSingularSet :=
    fun z hz =>
      completedZetaContourIntegrand_not_mem_singularSet_of_scheduledBoundary
        f F h u hz
  exact
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_selectedRegularRadius_boundaryData
      f F h hT hepsilon hinterior hboundaryRegular hboundaryAvoidance hclosed hseparated
      hregular
      (explicitFormulaRectangleComplement_hgrid_noPackage f F hT)
      (explicitFormulaRectangleComplement_circleEqSquare_of_puncturedResidueRegularity
        f (h.height_schedule.height u) epsilon hepsilon
        (fun a ha =>
          explicitFormulaRectangleRawSingular_puncturedResidueRegularity_of_coefficientRegularity
            f h.phi_control a ha
            (explicitFormulaRectangleRawSingular_coefficientRegularity_of_phiControl
              f F h.phi_control hT hinterior epsilon hepsilon hclosed hseparated a ha)))

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
