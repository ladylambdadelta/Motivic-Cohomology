import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part27

/-!
# Explicit-formula finite rectangle residues

This owner layer contains finite-rectangle residue equalities, scheduled avoidance, and residue-window error transport.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Finite-hole Cauchy from a half-radius proof-carrying endpoint-data subdivision.  This
is the list-level consumer for the constructive regular-grid path: the geometric layer
proves the endpoint-data boundary decomposition and each listed cell boundary vanishes;
the deleted-boundary transport then returns from inscribed-square holes to public circular
holes. -/
theorem explicitFormulaRectangle_finiteHoleCauchy_of_regularGridEndpointDataHalfRadius_closedRadiusControls
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hgrid :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∃ data : List
                (ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2)),
              zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
                  ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
                    finiteRectangleSubdivisionCellBoundaryIntegral
                      (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                      (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a)
                      (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a) =
                explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data ∧
              (∀ d : ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2),
                d ∈ data →
                  explicitFormulaRectangleRegularGridCellEndpointDataBoundary f d = 0))
    (hdeleted :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∀ a : ℂ,
              a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a =
                  explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
            f F T ε = 0 := by
  have hsquare :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
              f F T (ε / 2) = 0 := by
    intro ε hε hclosed hsep
    match hgrid ε hε hclosed hsep with
    | ⟨data, hsubdivision, hcell⟩ =>
        exact
          explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_regularGridEndpointDataBoundarySum
            f data hsubdivision hcell
  exact
    explicitFormulaRectangle_finiteHoleCauchy_of_inscribedSquareHalfRadiusZero_closedRadiusControls
      f F h hT hinterior hsquare hdeleted

/-- Finite-hole Cauchy from a half-radius proof-carrying endpoint-data subdivision, with
cell Cauchy-Goursat discharged from closed-radius controls.  The geometric layer only has
to prove the endpoint-data boundary decomposition and the circle-to-inscribed-square
deleted-boundary transport. -/
theorem explicitFormulaRectangle_finiteHoleCauchy_of_regularGridEndpointDataSubdivision_closedRadiusControls
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hgrid :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∃ data : List
                (ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2)),
              zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
                  ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
                    finiteRectangleSubdivisionCellBoundaryIntegral
                      (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                      (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a)
                      (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a) =
                explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data)
    (hdeleted :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∀ a : ℂ,
              a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a =
                  explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
            f F T ε = 0 := by
  have hsquare :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
              f F T (ε / 2) = 0 := by
    intro ε hε hclosed hsep
    match hgrid ε hε hclosed hsep with
    | ⟨data, hsubdivision⟩ =>
        exact
          explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_endpointData_tangentContour_sub_rawInscribedSquareCellBoundarySum_halfRadius_closedRadiusControls
            data f h hT hε hinterior hboundary hclosed hsubdivision
  exact
    explicitFormulaRectangle_finiteHoleCauchy_of_inscribedSquareHalfRadiusZero_closedRadiusControls
      f F h hT hinterior hsquare hdeleted

/-- Finite-hole Cauchy from endpoint-data subdivision when the local square evaluation is
proved in the natural orientation from the inscribed-square boundary to the circle
boundary.  This is the transport direction produced by a square residue calculation; the
finite-hole consumer expects the reverse circle-to-square deleted-boundary replacement. -/
theorem explicitFormulaRectangle_finiteHoleCauchy_of_regularGridEndpointDataSubdivision_closedRadiusControls_of_inscribedSquare_values
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hgrid :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∃ data : List
                (ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2)),
              zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
                  ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
                    finiteRectangleSubdivisionCellBoundaryIntegral
                      (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                      (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a)
                      (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a) =
                explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data)
    (hsquare_circle :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∀ a : ℂ,
              a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a =
                  explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
            f F T ε = 0 := by
  have hdeleted :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∀ a : ℂ,
              a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a =
                  explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a := by
    intro ε hε hclosed hsep a ha
    exact (hsquare_circle ε hε hclosed hsep a ha).symm
  exact
    explicitFormulaRectangle_finiteHoleCauchy_of_regularGridEndpointDataSubdivision_closedRadiusControls
      f F h hT hinterior hboundary hgrid hdeleted

/-- Half-radius deleted-boundary transport for the endpoint-data subdivision, expressed in
the lower-level pointwise deformation form.  The geometric input is only the deformation
of each half-radius circle to the deleted square of half that half-radius. -/
theorem explicitFormulaRectangle_finiteHoleCauchy_of_regularGridEndpointDataSubdivision_closedRadiusControls_of_rawDeletedSquare_quarter
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hgrid :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∃ data : List
                (ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2)),
              zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
                  ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
                    finiteRectangleSubdivisionCellBoundaryIntegral
                      (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                      (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a)
                      (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a) =
                explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data)
    (hcircle_square :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∀ a : ℂ,
              a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a =
                  explicitFormulaRectangleRawDeletedSquareBoundary f ((ε / 2) / 2) a) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
            f F T ε = 0 := by
  have hdeleted :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∀ a : ℂ,
              a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a =
                  explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a :=
    fun ε hε hclosed hsep =>
      explicitFormulaRectangleRawDeletedCircleBoundary_half_eq_rawInscribedSquareBoundary_half_on_of_rawDeletedSquare_quarter_on
        f T ε (hcircle_square ε hε hclosed hsep)
  exact
    explicitFormulaRectangle_finiteHoleCauchy_of_regularGridEndpointDataSubdivision_closedRadiusControls
      f F h hT hinterior hboundary hgrid hdeleted

/-- Finite-hole Cauchy from endpoint-data subdivision and common residue values for the
half-radius circle and quarter-width deleted-square boundaries.  This is the form consumed
by a future square-boundary residue evaluation theorem. -/
theorem explicitFormulaRectangle_finiteHoleCauchy_of_regularGridEndpointDataSubdivision_closedRadiusControls_of_common_values
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hgrid :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∃ data : List
                (ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2)),
              zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
                  ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
                    finiteRectangleSubdivisionCellBoundaryIntegral
                      (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                      (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a)
                      (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a) =
                explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data)
    (value : ℝ → ℂ → ℂ)
    (hcircle :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∀ a : ℂ,
              a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a = value ε a)
    (hsquare :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∀ a : ℂ,
              a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                explicitFormulaRectangleRawDeletedSquareBoundary f ((ε / 2) / 2) a = value ε a) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
            f F T ε = 0 := by
  have hcircle_square :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∀ a : ℂ,
              a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a =
                  explicitFormulaRectangleRawDeletedSquareBoundary f ((ε / 2) / 2) a := by
    intro ε hε hclosed hsep a ha
    exact
      explicitFormulaRectangleRawDeletedCircleBoundary_half_eq_rawDeletedSquareBoundary_quarter_of_common_value
        f ε a (value ε a)
        (hcircle ε hε hclosed hsep a ha)
        (hsquare ε hε hclosed hsep a ha)
  exact
    explicitFormulaRectangle_finiteHoleCauchy_of_regularGridEndpointDataSubdivision_closedRadiusControls_of_rawDeletedSquare_quarter
      f F h hT hinterior hboundary hgrid hcircle_square

/-- Finite-hole Cauchy from canonical deleted-circle residue evaluations and a separate
half-radius inscribed-square common-value theorem.  The square side is normalized through
the already proved inscribed-square-to-quarter-square bridge before applying the
common-value finite-hole consumer. -/
theorem explicitFormulaRectangle_finiteHoleCauchy_of_regularGridEndpointDataSubdivision_closedRadiusControls_of_inscribedSquareCommonValues_circleResidues
    (f : ZetaAdmissibleFunction) (hPhi : ZetaPhiAnalyticControl f)
    (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T : ℝ} (hT : 0 < T)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hgrid :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∃ data : List
                (ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2)),
              zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
                  ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
                    finiteRectangleSubdivisionCellBoundaryIntegral
                      (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                      (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a)
                      (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a) =
                explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data)
    (value : ℝ → ℂ → ℂ)
    (hvalue_zero :
      ∀ ε : ℝ,
        value ε 0 =
          (2 * ↑Real.pi * Complex.I : ℂ) •
            explicitFormulaRectangle_zeroPoleResidue f)
    (hvalue_one :
      ∀ ε : ℝ,
        value ε 1 =
          (2 * ↑Real.pi * Complex.I : ℂ) •
            explicitFormulaRectangle_onePoleResidue f)
    (hvalue_completed :
      ∀ ε : ℝ,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ∀ hρ : ρ ∈ explicitFormulaCompletedZeroHeightWindow T,
            value ε (completedZeroResidueCoordinate ρ) =
              (2 * ↑Real.pi * Complex.I : ℂ) •
                explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ))
    (s0 s1 : ℝ → Set ℂ)
    (hs0 : ∀ ε : ℝ, (s0 ε).Countable)
    (hs1 : ∀ ε : ℝ, (s1 ε).Countable)
    (szero : ℝ → {ρ : ℂ // ZetaCompletedZero ρ} → Set ℂ)
    (hszero :
      ∀ ε : ℝ,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ρ ∈ explicitFormulaCompletedZeroHeightWindow T →
            (szero ε ρ).Countable)
    (hzero_continuous :
      ∀ ε : ℝ,
        ContinuousOn
          (fun z : ℂ => z * zetaCompletedExplicitFormulaContourIntegrand f z)
          (Metric.closedBall (0 : ℂ) (ε / 2) \ {(0 : ℂ)}))
    (hzero_differentiable :
      ∀ ε : ℝ,
        ∀ z : ℂ,
          z ∈ (Metric.ball (0 : ℂ) (ε / 2) \ {(0 : ℂ)}) \ s0 ε →
            DifferentiableAt ℂ
              (fun w : ℂ => w * zetaCompletedExplicitFormulaContourIntegrand f w)
              z)
    (hone_continuous :
      ∀ ε : ℝ,
        ContinuousOn
          (fun z : ℂ => (z - 1) * zetaCompletedExplicitFormulaContourIntegrand f z)
          (Metric.closedBall (1 : ℂ) (ε / 2) \ {(1 : ℂ)}))
    (hone_differentiable :
      ∀ ε : ℝ,
        ∀ z : ℂ,
          z ∈ (Metric.ball (1 : ℂ) (ε / 2) \ {(1 : ℂ)}) \ s1 ε →
            DifferentiableAt ℂ
              (fun w : ℂ => (w - 1) * zetaCompletedExplicitFormulaContourIntegrand f w)
              z)
    (hcompleted_continuous :
      ∀ ε : ℝ,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ρ ∈ explicitFormulaCompletedZeroHeightWindow T →
            ContinuousOn
              (fun z : ℂ =>
                (z - completedZeroResidueCoordinate ρ) *
                  zetaCompletedExplicitFormulaContourIntegrand f z)
              (Metric.closedBall (completedZeroResidueCoordinate ρ) (ε / 2) \
                {completedZeroResidueCoordinate ρ}))
    (hcompleted_differentiable :
      ∀ ε : ℝ,
        ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
          ∀ hρ : ρ ∈ explicitFormulaCompletedZeroHeightWindow T,
            ∀ z : ℂ,
              z ∈ (Metric.ball (completedZeroResidueCoordinate ρ) (ε / 2) \
                  {completedZeroResidueCoordinate ρ}) \ szero ε ρ →
                DifferentiableAt ℂ
                  (fun w : ℂ =>
                    (w - completedZeroResidueCoordinate ρ) *
                      zetaCompletedExplicitFormulaContourIntegrand f w)
                  z)
    (hsquare :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∀ a : ℂ,
              a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a = value ε a)
    (hlocal :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T →
          Tendsto
            (fun z : ℂ =>
              (z - completedZeroResidueCoordinate ρ) * zetaCompletedExplicitFormulaContourIntegrand f z)
            (𝓝[≠] (completedZeroResidueCoordinate ρ))
            (𝓝 (explicitFormulaZeroResidue f (explicitFormulaZeroDataOfCompletedZero ρ)))) :
    ∀ ε : ℝ,
      0 < ε →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
        (∀ a : ℂ,
          a ∈ explicitFormulaRectangleRawSingularCoordinates T →
            ∀ b : ℂ,
              b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a ≠ b → ε + ε < dist a b) →
          explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
            f F T ε = 0 := by
  have hcircle :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∀ a : ℂ,
              a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a = value ε a :=
    explicitFormulaRectangleRawDeletedCircleBoundary_half_eq_commonValue_on_rawSingularCoordinates
      f hPhi F T value
      hvalue_zero hvalue_one hvalue_completed
      s0 s1 hs0 hs1 szero hszero
      hzero_continuous hzero_differentiable
      hone_continuous hone_differentiable
      hcompleted_continuous hcompleted_differentiable
      hlocal
  have hsquare_quarter :
      ∀ ε : ℝ,
        0 < ε →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) →
          (∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              ∀ b : ℂ,
                b ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a ≠ b → ε + ε < dist a b) →
            ∀ a : ℂ,
              a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                explicitFormulaRectangleRawDeletedSquareBoundary f ((ε / 2) / 2) a =
                  value ε a :=
    explicitFormulaRectangleRawDeletedSquareBoundary_quarter_eq_value_of_rawInscribedSquareBoundary_half_eq_value_controls
      f F T value hsquare
  exact
    explicitFormulaRectangle_finiteHoleCauchy_of_regularGridEndpointDataSubdivision_closedRadiusControls_of_common_values
      f F h hT hinterior hboundary hgrid value hcircle hsquare_quarter

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
