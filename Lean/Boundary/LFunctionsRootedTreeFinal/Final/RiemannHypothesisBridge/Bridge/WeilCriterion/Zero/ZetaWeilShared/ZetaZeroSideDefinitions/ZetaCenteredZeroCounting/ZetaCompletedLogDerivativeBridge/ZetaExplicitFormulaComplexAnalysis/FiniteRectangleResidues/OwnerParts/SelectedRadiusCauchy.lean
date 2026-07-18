import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.OuterSideIntegrability

/-!
# Selected-radius finite-hole Cauchy assembly
-/

namespace Boundary
namespace LFunctions

noncomputable section

namespace ZetaAdmissibleFunction

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
  have hhalf : 0 < epsilon / 2 := finiteRectangle_halfRadius_pos hepsilon
  have hclosedHalf :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates (h.height_schedule.height u) →
          Metric.closedBall a (epsilon / 2) ⊆
            explicitFormulaContourFamilyInterior F (h.height_schedule.height u) :=
    explicitFormulaRectangleRawSingularCoordinates_halfRadius_closedBall_subset_interior
      F hepsilon hclosed
  exact And.intro
    (explicitFormulaRectangleSortedXHorizontalSideIntegrable_bottom_of_scheduledPackage
      f F h u (epsilon / 2) (le_of_lt hhalf) hclosedHalf)
    (And.intro
      (explicitFormulaRectangleSortedXHorizontalSideIntegrable_top_of_scheduledPackage
        f F h u (epsilon / 2) (le_of_lt hhalf) hclosedHalf)
      (And.intro
        (fun a ha =>
          explicitFormulaRectangleSortedXHorizontalSideIntegrable_lowerHole_of_regularRadius
            f F h.phi_control hepsilon hclosed hregular a ha)
        (And.intro
          (fun a ha =>
            explicitFormulaRectangleSortedXHorizontalSideIntegrable_upperHole_of_regularRadius
              f F h.phi_control hepsilon hclosed hregular a ha)
          (And.intro
            (explicitFormulaRectangleSortedYVerticalSideIntegrable_right_of_scheduledPackage
              f F h u (epsilon / 2) hT (le_of_lt hhalf) hclosedHalf)
            (And.intro
              (explicitFormulaRectangleSortedYVerticalSideIntegrable_left_of_scheduledPackage
                f F h u (epsilon / 2) hT (le_of_lt hhalf) hclosedHalf)
              (And.intro
                (fun a ha =>
                  explicitFormulaRectangleSortedYVerticalSideIntegrable_upperHole_of_regularRadius
                    f F h hT hepsilon hclosed hregular a ha)
                (fun a ha =>
                  explicitFormulaRectangleSortedYVerticalSideIntegrable_lowerHole_of_regularRadius
                    f F h hT hepsilon hclosed hregular a ha)))))))

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
  have hboundary :=
    explicitFormulaRectangleContourIntegrand_boundaryRegular_of_avoidsBoundary
      f F h (h.height_schedule.height u)
      (explicitFormulaScheduledRectangle_avoidsSingularBoundary f F h u)
  match explicitFormulaRectangle_selectedRegularRadius_sideIntegrability
      f F h hT hepsilon hclosed hregular with
  | ⟨hbottom, htop, hbottomHole, htopHole, hright, hleft, hrightHole, hleftHole⟩ =>
      match explicitFormulaRectangleComplement_hgrid
          f F h hT hinterior hboundary epsilon hepsilon hclosed
          hbottom htop hbottomHole htopHole hright hleft hrightHole hleftHole hseparated with
      | ⟨data, hsubdivision⟩ =>
          have hsquare :
              explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
                f F (h.height_schedule.height u) (epsilon / 2) = 0 :=
            explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_endpointData_tangentContour_sub_rawInscribedSquareCellBoundarySum_halfRadius_closedRadiusControls
              data f h hT hepsilon hinterior hboundary hclosed hsubdivision
          have hdeleted :=
            explicitFormulaRectangleComplement_circleEqSquare
              f F h hT hinterior epsilon hepsilon hclosed hseparated
          have hhalfZero :
              explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
                f F (h.height_schedule.height u) (epsilon / 2) = 0 :=
            explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_deletedBoundary_eq_on
              f F (h.height_schedule.height u) (epsilon / 2)
              (explicitFormulaRectangleRawInscribedSquareBoundary f (epsilon / 2))
              hsquare hdeleted
          exact
            explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_halfRadius_closedRadiusControls
              f F h hT hepsilon hinterior hclosed hseparated hhalfZero

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
