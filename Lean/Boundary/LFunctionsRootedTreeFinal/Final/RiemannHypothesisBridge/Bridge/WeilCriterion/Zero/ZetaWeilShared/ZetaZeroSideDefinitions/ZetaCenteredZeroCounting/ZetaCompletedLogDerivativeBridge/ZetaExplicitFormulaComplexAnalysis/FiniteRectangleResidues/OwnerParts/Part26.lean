import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part25

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

/-- Algebraic form of the inscribed-square subdivision target: once the tangent outer
rectangle contour minus the finite inscribed-square hole boundaries has been identified
with a finite sum of regular subdivision-cell boundaries, the public inscribed-square
punctured-boundary expression is exactly that regular cell-boundary sum. -/
theorem explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_regularCellBoundarySum_of_tangentContour_sub_rawInscribedSquareCellBoundarySum
    {ι : Type*} (cells : Finset ι)
    (lower upper : ι → ℂ)
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hregular :
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
        ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) =
        ∑ c in cells,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (lower c) (upper c)) :
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
        f F T ε =
      ∑ c in cells,
        finiteRectangleSubdivisionCellBoundaryIntegral
          (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
          (lower c) (upper c) := by
  calc
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
        f F T ε =
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
        ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) := by
      exact
        explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_tangentContour_sub_rawInscribedSquareCellBoundarySum
          f F T ε
    _ =
      ∑ c in cells,
        finiteRectangleSubdivisionCellBoundaryIntegral
          (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (lower c) (upper c) := by
      exact hregular

/-- Algebraic boundary-normalization for a concrete list-level regular-grid subdivision:
once the outer tangent rectangle boundary minus the finite inscribed-square hole
boundaries has been proved equal to the endpoint-data boundary sum, the public
inscribed-square punctured-boundary expression is exactly that list sum. -/
theorem explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_regularGridEndpointDataBoundarySum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε))
    (hsubdivision :
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            finiteRectangleSubdivisionCellBoundaryIntegral
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) =
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data) :
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
        f F T ε =
      explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data := by
  calc
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
        f F T ε =
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
        ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) := by
      exact
        explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_tangentContour_sub_rawInscribedSquareCellBoundarySum
          f F T ε
    _ = explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data := by
      exact hsubdivision

/-- Endpoint-data normalization from a subdivision equality first proved as a boundary
list over the associated proof-carrying regular cells. -/
theorem explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_regularGridEndpointDataBoundarySum_of_cellBoundaryListSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε))
    (hsubdivision :
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            finiteRectangleSubdivisionCellBoundaryIntegral
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) =
        explicitFormulaRectangleRegularGridCellBoundaryListSum f
          (explicitFormulaRectangleRegularGridCellListOfEndpointData data)) :
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
        f F T ε =
      explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data := by
  have hendpoint :
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            finiteRectangleSubdivisionCellBoundaryIntegral
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) =
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data :=
    explicitFormulaRectangleRegularGridEndpointDataBoundarySum_eq_of_cellBoundaryListSum
      f data hsubdivision
  exact
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_regularGridEndpointDataBoundarySum
      f data hendpoint

/-- Cauchy-Goursat zero from a concrete endpoint-data list subdivision once every listed
regular-cell boundary has been proved zero.  This is the list-level consumer for the
proof-carrying complement subdivision and avoids converting the list into a filtered
`Finset`. -/
theorem explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_regularGridEndpointDataBoundarySum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε))
    (hsubdivision :
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            finiteRectangleSubdivisionCellBoundaryIntegral
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) =
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data)
    (hcell :
      ∀ d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε,
        d ∈ data →
          explicitFormulaRectangleRegularGridCellEndpointDataBoundary f d = 0) :
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
        f F T ε = 0 := by
  have hboundary :
      explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
          f F T ε =
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data :=
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_regularGridEndpointDataBoundarySum
      f data hsubdivision
  have hsum_zero :
      explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data = 0 :=
    explicitFormulaRectangleRegularGridEndpointDataBoundarySum_eq_zero_of_forall_mem
      f data hcell
  exact Eq.trans hboundary hsum_zero

/-- Cauchy-Goursat zero from a concrete endpoint-data list subdivision written in the
outer-minus-inscribed-square-hole boundary form. -/
theorem explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_endpointData_tangentContour_sub_rawInscribedSquareCellBoundarySum_halfRadius_closedRadiusControls
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2)))
    (f : ZetaAdmissibleFunction)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hT : 0 < T) (hε : 0 < ε)
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
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hsubdivision :
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            finiteRectangleSubdivisionCellBoundaryIntegral
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a) =
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data) :
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
      f F T (ε / 2) = 0 := by
  have hboundarySum :
      explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
          f F T (ε / 2) =
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data :=
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_regularGridEndpointDataBoundarySum
      f data hsubdivision
  exact
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_endpointDataBoundarySum_halfRadius_closedRadiusControls
      data f h hT hε hinterior hboundary hclosed hboundarySum

/-- Algebraic boundary-normalization for a concrete regular-grid subdivision: once the
outer tangent rectangle boundary minus the finite inscribed-square hole boundaries has
been proved equal to the selected regular-grid-cell boundary sum, the public
inscribed-square punctured-boundary expression is exactly that regular-cell sum. -/
theorem explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_regularGridCellBoundarySum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (cells : Finset (ExplicitFormulaRectangleRegularGridCell F T ε))
    (hsubdivision :
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            finiteRectangleSubdivisionCellBoundaryIntegral
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) =
        explicitFormulaRectangleRegularGridCellBoundarySum f cells) :
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
        f F T ε =
      explicitFormulaRectangleRegularGridCellBoundarySum f cells := by
  calc
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
        f F T ε =
        ∑ c in cells,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            c.lower c.upper := by
      exact
        explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_regularCellBoundarySum_of_tangentContour_sub_rawInscribedSquareCellBoundarySum
          cells
          (fun c : ExplicitFormulaRectangleRegularGridCell F T ε => c.lower)
          (fun c : ExplicitFormulaRectangleRegularGridCell F T ε => c.upper)
          f F T ε
          (explicitFormulaRectangleRegularGridCellBoundarySum_unfold_right
            f cells hsubdivision)
    _ = explicitFormulaRectangleRegularGridCellBoundarySum f cells := by
      exact explicitFormulaRectangleRegularGridCellBoundarySum_sum_eq f cells

/-- Cauchy-Goursat zero from the named regular-grid boundary-sum normalization at
half radius.  This is the regular-grid form suited to the edge-cancellation layer: prove
the named boundary-sum equality, and the analytic cell regularity follows from
closed-radius controls. -/
theorem explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_regularGridHalfRadius_boundarySum_closedRadiusControls
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (cells : Finset (ExplicitFormulaRectangleRegularGridCell F T (ε / 2)))
    (f : ZetaAdmissibleFunction)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hT : 0 < T) (hε : 0 < ε)
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
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hboundarySum :
      explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
          f F T (ε / 2) =
        explicitFormulaRectangleRegularGridCellBoundarySum f cells) :
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
      f F T (ε / 2) = 0 := by
  have hsubdivision :
      explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
          f F T (ε / 2) =
        ∑ c in cells,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            c.lower c.upper :=
    explicitFormulaRectangleRegularGridCellBoundarySum_unfold_right
      f cells hboundarySum
  exact
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_regularGridHalfRadius_subdivision_closedRadiusControls
      cells f h hT hε hinterior hboundary hclosed hsubdivision

/-- Cauchy-Goursat zero from an explicitly supplied regular-grid cell-boundary function
at half radius.  The supplied finite sum is first folded to the named regular-grid
boundary-sum owner normalization, then consumed by the regular-grid boundary-sum theorem. -/
theorem explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_regularGridHalfRadius_suppliedBoundarySum_closedRadiusControls
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (cells : Finset (ExplicitFormulaRectangleRegularGridCell F T (ε / 2)))
    (B : ExplicitFormulaRectangleRegularGridCell F T (ε / 2) → ℂ)
    (f : ZetaAdmissibleFunction)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hT : 0 < T) (hε : 0 < ε)
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
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hsubdivision :
      explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
          f F T (ε / 2) =
        ∑ c in cells, B c)
    (hB :
      ∀ c : ExplicitFormulaRectangleRegularGridCell F T (ε / 2), c ∈ cells →
        B c =
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            c.lower c.upper) :
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
      f F T (ε / 2) = 0 := by
  have hboundarySum :
      explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
          f F T (ε / 2) =
        explicitFormulaRectangleRegularGridCellBoundarySum f cells :=
    explicitFormulaRectangleRegularGridCellBoundarySum_fold_supplied_right
      f cells B hsubdivision hB
  exact
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_regularGridHalfRadius_boundarySum_closedRadiusControls
      cells f h hT hε hinterior hboundary hclosed hboundarySum

/-- Cauchy-Goursat zero for the finite-radius inscribed-square-punctured rectangle from
the concrete regular-cell subdivision identity in `outer minus inscribed-square holes`
form.  This is the intended consumer of the rectangular complement-cell subdivision:
the geometric work must prove `hregular` and `hcell_closed` for the actual complement
cells. -/
theorem explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_tangentContour_sub_rawInscribedSquareCellBoundarySum
    {ι : Type*} (cells : Finset ι)
    (lower upper : ι → ℂ)
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hregular :
      zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T) -
        ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) =
        ∑ c in cells,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (lower c) (upper c))
    (hcell_closed :
      ∀ c : ι, c ∈ cells →
        ([[ (lower c).re, (upper c).re ]] ×ℂ
          [[ (lower c).im, (upper c).im ]]) ⊆
          finiteRectanglePuncturedDomain
            (explicitFormulaContourFamilyInterior F T)
            (explicitFormulaRectangleRawSingularCoordinates T)
            ε) :
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
      f F T ε = 0 :=
  explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_rawPuncturedClosedSubdivision
    cells lower upper f F h hT hε hinterior
    (explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_regularCellBoundarySum_of_tangentContour_sub_rawInscribedSquareCellBoundarySum
      cells lower upper f F T ε hregular)
    hcell_closed

/-- The tangent finite-radius circular-hole punctured boundary vanishes once a replacement
deleted-boundary choice has the same finite deleted-boundary sum and has zero punctured
boundary.  This is the algebraic bridge from a square-hole rectangular subdivision back to
the public circular deleted-boundary normalization. -/
theorem explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_deletedBoundarySum_eq
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (deletedBoundary : ℂ → ℂ)
    (hzero :
      explicitFormulaRectangleTangentPuncturedBoundaryIntegral f F T
        (explicitFormulaRectangleRawSingularCoordinates T) deletedBoundary = 0)
    (hsum :
      finiteRectangleDeletedCircleBoundarySum
          (explicitFormulaRectangleRawSingularCoordinates T)
          (explicitFormulaRectangleRawDeletedCircleBoundary f ε) =
        finiteRectangleDeletedCircleBoundarySum
          (explicitFormulaRectangleRawSingularCoordinates T)
          deletedBoundary) :
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral f F T ε = 0 :=
  finiteRectanglePuncturedBoundaryIntegral_eq_zero_of_deletedBoundarySum_eq
    (explicitFormulaRectangleRawSingularCoordinates T)
    (zetaCompletedExplicitFormulaTangentContourIntegral f (F.rectangle T))
    (explicitFormulaRectangleRawDeletedCircleBoundary f ε)
    deletedBoundary
    hzero
    hsum

/-- The public circular-hole finite-radius tangent punctured boundary zero transports from
a smaller radius `r` to a larger radius `R` when each raw deleted circle crosses only a
regular annulus. -/
theorem explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_annulus_regular_radius_transport
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hzero :
      explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral f F T r = 0)
    (s : ℂ → Set ℂ)
    (hs : ∀ a : ℂ,
      a ∈ explicitFormulaRectangleRawSingularCoordinates T → (s a).Countable)
    (hcontinuous :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ContinuousOn
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (Metric.closedBall a R \ Metric.ball a r))
    (hdifferentiable :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ z : ℂ,
            z ∈ (Metric.ball a R \ Metric.closedBall a r) \ s a →
              DifferentiableAt ℂ
                (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z) :
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral f F T R = 0 :=
  explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_deletedBoundarySum_eq
    f F T R
    (explicitFormulaRectangleRawDeletedCircleBoundary f r)
    hzero
    (explicitFormulaRectangleRawDeletedCircleBoundarySum_eq_of_annulus_regular
      f T hr hrR s hs hcontinuous hdifferentiable)

/-- Under closed-radius controls, finite-radius circular-hole Cauchy zero at half radius
transports to finite-radius circular-hole Cauchy zero at the selected radius. -/
theorem explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_halfRadius_closedRadiusControls
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    {T ε : ℝ} (hT : 0 < T) (hε : 0 < ε)
    (hinterior :
      ∀ ρ : {ρ : ℂ // ZetaCompletedZero ρ},
        ρ ∈ explicitFormulaCompletedZeroHeightWindow T ↔
          completedZeroResidueCoordinate ρ ∈ explicitFormulaContourFamilyInterior F T ∧
            completedZeroResidueCoordinate ρ ∈ completedZetaContourIntegrandSingularSet)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ε + ε < dist a b)
    (hhalfZero :
      explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
        f F T (ε / 2) = 0) :
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral f F T ε = 0 := by
  have hhalf_pos : 0 < ε / 2 :=
    finiteRectangle_halfRadius_pos hε
  have hhalf_le : ε / 2 ≤ ε :=
    finiteRectangle_halfRadius_le_self hε
  exact
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_annulus_regular_radius_transport
      f F T hhalf_pos hhalf_le hhalfZero
      (fun _ : ℂ => completedZetaContourIntegrandSingularSet)
      (fun _ _ => completedZetaContourIntegrandSingularSet_countable)
      (fun a ha =>
        explicitFormulaRectangleRawSingularHalfAnnulus_continuousOn_of_closedRadiusControls
          f F h hT hε hinterior hclosed hsep a ha)
      (fun a ha z hz =>
        explicitFormulaRectangleRawSingularHalfAnnulus_differentiableAt_of_closedRadiusControls
          f F h hT hε hinterior hclosed hsep a ha z hz.1)

/-- Pointwise replacement form of the square-hole/circular-hole bridge for the tangent
finite-radius punctured boundary. -/
theorem explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_deletedBoundary_eq_on
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (deletedBoundary : ℂ → ℂ)
    (hzero :
      explicitFormulaRectangleTangentPuncturedBoundaryIntegral f F T
        (explicitFormulaRectangleRawSingularCoordinates T) deletedBoundary = 0)
    (hpoint :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleRawDeletedCircleBoundary f ε a =
            deletedBoundary a) :
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral f F T ε = 0 :=
  explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_deletedBoundarySum_eq
    f F T ε deletedBoundary hzero
    (finiteRectangleDeletedCircleBoundarySum_eq_of_forall_mem
      (explicitFormulaRectangleRawSingularCoordinates T)
      (explicitFormulaRectangleRawDeletedCircleBoundary f ε)
      deletedBoundary
      hpoint)

/-- Half-radius circular-hole Cauchy zero from a concrete regular grid-cell subdivision of
the corresponding inscribed-square-punctured rectangle.  The square-hole Cauchy zero is
proved from the grid cells; the circular-hole statement follows by transporting the
deleted boundary from circles to the inscribed-square deleted-boundary choice. -/
theorem explicitFormulaRectangleTangentHalfRadiusPuncturedBoundaryIntegral_eq_zero_of_regularGridCellSubtype
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (cells : Finset (ExplicitFormulaRectangleRegularGridCell F T (ε / 2)))
    (f : ZetaAdmissibleFunction)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hT : 0 < T)
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
    (hsubdivision :
      explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
          f F T (ε / 2) =
        ∑ c in cells,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            c.lower c.upper)
    (hcell_location :
      ∀ c : ExplicitFormulaRectangleRegularGridCell F T (ε / 2), c ∈ cells →
        ∀ z : ℂ,
          z ∈ ([[ c.lower.re, c.upper.re ]] ×ℂ [[ c.lower.im, c.upper.im ]]) →
            z ∈ explicitFormulaContourFamilyInterior F T ∨
              z ∈ explicitFormulaContourFamilyBoundary F T)
    (hcell_open_interior :
      ∀ c : ExplicitFormulaRectangleRegularGridCell F T (ε / 2), c ∈ cells →
        ∀ z : ℂ,
          z ∈ Set.Ioo (min c.lower.re c.upper.re)
                (max c.lower.re c.upper.re) ×ℂ
              Set.Ioo (min c.lower.im c.upper.im)
                (max c.lower.im c.upper.im) →
            z ∈ explicitFormulaContourFamilyInterior F T)
    (hdeleted :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a =
            explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a) :
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
      f F T (ε / 2) = 0 := by
  have hsquareZero :
      explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
        f F T (ε / 2) = 0 :=
    explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral_eq_zero_of_regularGridCellSubtype
      cells f h hT hinterior hboundary hsubdivision hcell_location hcell_open_interior
  exact
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_deletedBoundary_eq_on
      f F T (ε / 2)
      (explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2))
      hsquareZero
      hdeleted

/-- Finite-radius circular-hole Cauchy zero at the selected closed radius from a concrete
regular grid-cell subdivision at half radius.  This is the exact finite-hole Cauchy input
shape consumed by the finite rectangle residue theorem. -/
theorem explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_regularGridCellHalfRadius_closedRadiusControls
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (cells : Finset (ExplicitFormulaRectangleRegularGridCell F T (ε / 2)))
    (f : ZetaAdmissibleFunction)
    (h : ExplicitFormulaFamilyAnalyticPackage f F)
    (hT : 0 < T) (hε : 0 < ε)
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
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ε + ε < dist a b)
    (hsubdivision :
      explicitFormulaRectangleTangentFiniteRadiusInscribedSquarePuncturedBoundaryIntegral
          f F T (ε / 2) =
        ∑ c in cells,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            c.lower c.upper)
    (hcell_location :
      ∀ c : ExplicitFormulaRectangleRegularGridCell F T (ε / 2), c ∈ cells →
        ∀ z : ℂ,
          z ∈ ([[ c.lower.re, c.upper.re ]] ×ℂ [[ c.lower.im, c.upper.im ]]) →
            z ∈ explicitFormulaContourFamilyInterior F T ∨
              z ∈ explicitFormulaContourFamilyBoundary F T)
    (hcell_open_interior :
      ∀ c : ExplicitFormulaRectangleRegularGridCell F T (ε / 2), c ∈ cells →
        ∀ z : ℂ,
          z ∈ Set.Ioo (min c.lower.re c.upper.re)
                (max c.lower.re c.upper.re) ×ℂ
              Set.Ioo (min c.lower.im c.upper.im)
                (max c.lower.im c.upper.im) →
            z ∈ explicitFormulaContourFamilyInterior F T)
    (hdeleted :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleRawDeletedCircleBoundary f (ε / 2) a =
            explicitFormulaRectangleRawInscribedSquareBoundary f (ε / 2) a) :
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral f F T ε = 0 := by
  have hhalfZero :
      explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral
        f F T (ε / 2) = 0 :=
    explicitFormulaRectangleTangentHalfRadiusPuncturedBoundaryIntegral_eq_zero_of_regularGridCellSubtype
      cells f h hT hinterior hboundary hsubdivision hcell_location hcell_open_interior hdeleted
  exact
    explicitFormulaRectangleTangentFiniteRadiusPuncturedBoundaryIntegral_eq_zero_of_halfRadius_closedRadiusControls
      f F h hT hε hinterior hclosed hsep hhalfZero

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
