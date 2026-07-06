import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part20Parts.Part20_20

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

/-!
## Part20 21: EdgeSumsAndTangentBoundary
-/

/-
The old selected-box wrappers below used coordinate-selected boxes.  Raw exposed
boundary accounting now belongs to raw-hole-selected endpoint data exported by
Part20_20.

theorem explicitFormulaRectangleSelectedBoxEdgeCoordinates_verticalContribution_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ε : ℝ} (hT_nonneg : 0 ≤ T) (hε : 0 < ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hright :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2) F.c)
    (hleft :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2) (1 - F.c))
    (hrightHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a).re)
    (hleftHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a).re)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ε + ε < dist a b) :
    let boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
      explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T (ε / 2))
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T (ε / 2))
    explicitFormulaRectangleBoxRightEdgeIntegralSum f boxes -
        explicitFormulaRectangleBoxLeftEdgeIntegralSum f boxes =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T (ε / 2)) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T (ε / 2)) := by
  let boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
    explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
      (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T (ε / 2))
      (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T (ε / 2))
  calc
    explicitFormulaRectangleBoxRightEdgeIntegralSum f boxes -
        explicitFormulaRectangleBoxLeftEdgeIntegralSum f boxes =
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
            (explicitFormulaRectangleSelectedEndpointData F T (ε / 2)) -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
            (explicitFormulaRectangleSelectedEndpointData F T (ε / 2)) := by
      exact
        explicitFormulaRectangleSelectedBoxEdgeCoordinates_verticalContribution_eq_selectedEndpointData
          f F T (ε / 2)
    _ =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T (ε / 2)) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T (ε / 2)) := by
      exact
        explicitFormulaRectangleSelectedEndpointData_verticalContribution_core
          f F hT_nonneg hε hclosed hright hleft hrightHole hleftHole hsep
-/

/-- Grouped side-contribution constructor for the raw-edge-sum exposed-boundary
collapse.  This is the correct algebraic shape for a selected complement grid: internal
edges cancel in horizontal and vertical pairs, not in individual one-sided sums. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinates_edgeSums_tangentBoundary_rawEdgeSums_of_groupedSideSums
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge)
    (outerBottom outerTop outerRight outerLeft : ℂ)
    (hhorizontal :
      explicitFormulaRectangleBoxBottomEdgeIntegralSum f boxes -
          explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes =
        (outerBottom -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
            f T ε) -
          (outerTop -
            explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
              f T ε))
    (hvertical :
      explicitFormulaRectangleBoxRightEdgeIntegralSum f boxes -
          explicitFormulaRectangleBoxLeftEdgeIntegralSum f boxes =
        (outerRight -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
            f T ε) -
          (outerLeft -
            explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
              f T ε)) :
    explicitFormulaRectangleBoxBottomEdgeIntegralSum f boxes -
        explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes +
          (explicitFormulaRectangleBoxRightEdgeIntegralSum f boxes -
            explicitFormulaRectangleBoxLeftEdgeIntegralSum f boxes) =
      (outerBottom - outerTop + (outerRight - outerLeft)) -
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
            f T ε -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T ε +
            (explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
                f T ε -
              explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
                f T ε)) := by
  let B : ℂ := explicitFormulaRectangleBoxBottomEdgeIntegralSum f boxes
  let U : ℂ := explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes
  let R : ℂ := explicitFormulaRectangleBoxRightEdgeIntegralSum f boxes
  let L : ℂ := explicitFormulaRectangleBoxLeftEdgeIntegralSum f boxes
  let b : ℂ :=
    explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum f T ε
  let u : ℂ :=
    explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum f T ε
  let r : ℂ :=
    explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum f T ε
  let l : ℂ :=
    explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum f T ε
  calc
    B - U + (R - L) =
        ((outerBottom - b) - (outerTop - u)) + (R - L) := by
      exact congrArg (fun z : ℂ => z + (R - L)) hhorizontal
    _ =
        ((outerBottom - b) - (outerTop - u)) +
          ((outerRight - r) - (outerLeft - l)) := by
      exact congrArg
        (fun z : ℂ => ((outerBottom - b) - (outerTop - u)) + z)
        hvertical
    _ =
        (outerBottom - outerTop + (outerRight - outerLeft)) +
          ((-b) - (-u) + ((-r) - (-l))) := by
      exact
        (finiteRectangleSubdivisionEndpointBoundary_consEdgeAlgebra
          outerBottom outerTop outerRight outerLeft (-b) (-u) (-r) (-l)).symm
    _ =
        (outerBottom - outerTop + (outerRight - outerLeft)) +
          -(b - u + (r - l)) := by
      exact congrArg
        (fun z : ℂ => (outerBottom - outerTop + (outerRight - outerLeft)) + z)
        (explicitFormulaRectangleEndpointDataBoxEdgeSums_neg_group b u r l)
    _ =
        (outerBottom - outerTop + (outerRight - outerLeft)) -
          (b - u + (r - l)) := by
      exact
        (sub_eq_add_neg
          (outerBottom - outerTop + (outerRight - outerLeft))
          (b - u + (r - l))).symm

/- /-- Edge-sum form of the exposed-boundary theorem with the raw deleted boxes already
expanded into their four side sums. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinates_edgeSums_forwardBoundary_rawEdgeSums_closedRadiusControls
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ε : ℝ} (hT_nonneg : 0 ≤ T) (hε : 0 < ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hbottom :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2) (-T))
    (htop :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2) T)
    (hbottomHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a).im)
    (htopHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a).im)
    (hright :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2) F.c)
    (hleft :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2) (1 - F.c))
    (hrightHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a).re)
    (hleftHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a).re)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ε + ε < dist a b) :
    let boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
      explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T (ε / 2))
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T (ε / 2))
    explicitFormulaRectangleBoxBottomEdgeIntegralSum f boxes -
        explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes +
          (explicitFormulaRectangleBoxRightEdgeIntegralSum f boxes -
            explicitFormulaRectangleBoxLeftEdgeIntegralSum f boxes) =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
          zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) +
          (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
            zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I)) -
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
            f T (ε / 2) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T (ε / 2) +
            (explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
                f T (ε / 2) -
              explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
                f T (ε / 2))) := by
  let boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
    explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
      (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T (ε / 2))
      (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T (ε / 2))
  exact
    explicitFormulaRectangleSelectedBoxEdgeCoordinates_edgeSums_tangentBoundary_rawEdgeSums_of_groupedSideSums
      f F T (ε / 2) boxes
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T))
      (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T))
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I)
      (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I)
      (explicitFormulaRectangleSelectedBoxEdgeCoordinates_horizontalContribution_core
        f F hT_nonneg hε hclosed hbottom htop hbottomHole htopHole hsep)
      (explicitFormulaRectangleSelectedBoxEdgeCoordinates_verticalContribution_core
        f F hT_nonneg hε hclosed hright hleft hrightHole hleftHole hsep)

/-- Edge-sum form of the selected-grid exposed-boundary theorem.

This is the remaining discrete cancellation statement: after the selected half-radius
grid boxes are expanded into bottom, top, right, and left side sums, every internal side
cancels, the exposed outer sides give the tangent rectangle contour, and the exposed hole
sides give the raw inscribed-square box-boundary sum. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinates_edgeSums_tangentBoundary_closedRadiusControls
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ε : ℝ} (hT_nonneg : 0 ≤ T) (hε : 0 < ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hbottom :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2) (-T))
    (htop :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2) T)
    (hbottomHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a).im)
    (htopHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a).im)
    (hright :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2) F.c)
    (hleft :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2) (1 - F.c))
    (hrightHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a).re)
    (hleftHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a).re)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ε + ε < dist a b) :
    let boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
      explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T (ε / 2))
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T (ε / 2))
    explicitFormulaRectangleBoxBottomEdgeIntegralSum f boxes -
        explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes +
          (explicitFormulaRectangleBoxRightEdgeIntegralSum f boxes -
            explicitFormulaRectangleBoxLeftEdgeIntegralSum f boxes) =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
          zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) +
          (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
            zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I)) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBoundaryFinsetSum
          f T (ε / 2) := by
  let boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
    explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
      (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T (ε / 2))
      (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T (ε / 2))
  have hraw :
      explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBoundaryFinsetSum
          f T (ε / 2) =
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
            f T (ε / 2) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T (ε / 2) +
            (explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
                f T (ε / 2) -
              explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
                f T (ε / 2)) :=
    explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBoundaryFinsetSum_eq_edgeSums
      f T (ε / 2)
  have hedges :
      explicitFormulaRectangleBoxBottomEdgeIntegralSum f boxes -
          explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes +
            (explicitFormulaRectangleBoxRightEdgeIntegralSum f boxes -
              explicitFormulaRectangleBoxLeftEdgeIntegralSum f boxes) =
        (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
            zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) +
            (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
              zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I)) -
          (explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
              f T (ε / 2) -
            explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
              f T (ε / 2) +
              (explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
                  f T (ε / 2) -
                explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
                  f T (ε / 2))) :=
    explicitFormulaRectangleSelectedBoxEdgeCoordinates_edgeSums_forwardBoundary_rawEdgeSums_closedRadiusControls
      f F hT_nonneg hε hclosed hbottom htop hbottomHole htopHole hright hleft hrightHole hleftHole hsep
  calc
    explicitFormulaRectangleBoxBottomEdgeIntegralSum f boxes -
        explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes +
          (explicitFormulaRectangleBoxRightEdgeIntegralSum f boxes -
            explicitFormulaRectangleBoxLeftEdgeIntegralSum f boxes) =
        (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
            zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) +
            (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
              zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I)) -
          (explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
              f T (ε / 2) -
            explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
              f T (ε / 2) +
              (explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
                  f T (ε / 2) -
                explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
                  f T (ε / 2))) := by
      exact hedges
    _ =
        (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
            zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) +
            (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
              zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I)) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBoundaryFinsetSum
            f T (ε / 2) := by
      exact congrArg
        (fun z : ℂ =>
          (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
              zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) +
              (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
                zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I)) - z)
        hraw.symm
-/

/- /-- Pure sorted-box exposed-boundary theorem for the selected finite complement grid.

This is the combinatorial core after endpoint data has been erased: the selected boxes
from the sorted horizontal and vertical adjacent endpoint-pair lists have exposed
boundary equal to the tangent-oriented outer rectangle boundary minus the raw
inscribed-square box boundaries. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinates_tangentBoundary_closedRadiusControls
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ε : ℝ} (hT_nonneg : 0 ≤ T) (hε : 0 < ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hbottom :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2) (-T))
    (htop :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2) T)
    (hbottomHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a).im)
    (htopHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a).im)
    (hright :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2) F.c)
    (hleft :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2) (1 - F.c))
    (hrightHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a).re)
    (hleftHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a).re)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ε + ε < dist a b) :
    explicitFormulaRectangleEndpointDataBoxBoundarySum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T (ε / 2))
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T (ε / 2))) =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
          zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) +
          (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
            zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I)) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBoundaryFinsetSum
          f T (ε / 2) := by
  let boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
    explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
      (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T (ε / 2))
      (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T (ε / 2))
  have hboundary :
      explicitFormulaRectangleEndpointDataBoxBoundarySum f boxes =
        explicitFormulaRectangleBoxBottomEdgeIntegralSum f boxes -
          explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes +
            (explicitFormulaRectangleBoxRightEdgeIntegralSum f boxes -
              explicitFormulaRectangleBoxLeftEdgeIntegralSum f boxes) :=
    explicitFormulaRectangleSelectedBoxEdgeCoordinatesBoundarySum_halfRadius_sortedPairLists_eq_edgeSums
      f F T ε
  have hedges :
      explicitFormulaRectangleBoxBottomEdgeIntegralSum f boxes -
          explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes +
            (explicitFormulaRectangleBoxRightEdgeIntegralSum f boxes -
              explicitFormulaRectangleBoxLeftEdgeIntegralSum f boxes) =
        (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
            zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) +
            (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
              zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I)) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBoundaryFinsetSum
            f T (ε / 2) :=
    explicitFormulaRectangleSelectedBoxEdgeCoordinates_edgeSums_tangentBoundary_closedRadiusControls
      f F hT_nonneg hε hclosed hbottom htop hbottomHole htopHole hright hleft hrightHole hleftHole hsep
  exact Eq.trans hboundary hedges

/-- Geometric exposed-boundary theorem for the selected finite complement grid.

The selected adjacent endpoint-pair cells are exactly the rectangular cells in the
outer box after deleting the raw inscribed-square boxes at half radius.  Summing their
box-boundaries cancels every internal selected-grid edge, leaving the tangent-oriented
outer rectangle boundary minus the raw inscribed-square box-boundary sum. -/
theorem explicitFormulaRectangleSelectedEndpointData_tangentBoxBoundary_closedRadiusControls
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ε : ℝ} (hT_nonneg : 0 ≤ T) (hε : 0 < ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hbottom :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2) (-T))
    (htop :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2) T)
    (hbottomHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a).im)
    (htopHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a).im)
    (hright :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2) F.c)
    (hleft :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2) (1 - F.c))
    (hrightHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a).re)
    (hleftHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a).re)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ε + ε < dist a b) :
    explicitFormulaRectangleEndpointDataBoxBoundarySum f
        ((explicitFormulaRectangleSelectedEndpointData F T (ε / 2)).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2) =>
            d.boxEdgeCoordinates)) =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
          zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) +
          (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
            zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I)) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBoundaryFinsetSum
          f T (ε / 2) := by
  calc
    explicitFormulaRectangleEndpointDataBoxBoundarySum f
        ((explicitFormulaRectangleSelectedEndpointData F T (ε / 2)).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2) =>
            d.boxEdgeCoordinates)) =
        explicitFormulaRectangleEndpointDataBoxBoundarySum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
            (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T (ε / 2))
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T (ε / 2))) := by
      exact
        explicitFormulaRectangleSelectedEndpointData_boxBoundarySum_eq_sortedPairLists
          f F T (ε / 2)
    _ =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
          zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) +
          (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
            zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I)) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBoundaryFinsetSum
          f T (ε / 2) := by
      exact
        explicitFormulaRectangleSelectedBoxEdgeCoordinates_tangentBoundary_closedRadiusControls
          f F hT_nonneg hε hclosed hbottom htop hbottomHole htopHole hright hleft hrightHole hleftHole hsep
-/

/-- Box-boundary sum over selected crossed adjacent-pair lists splits into the selected
row for the head horizontal pair plus the selected remaining rows. -/
theorem explicitFormulaRectangleEndpointDataBoxBoundarySum_selectedPairLists_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (rest : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    let firstRowBoxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
      (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair ypairs)).map
        (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
          d.boxEdgeCoordinates)
    let remainingBoxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
      (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          rest ypairs)).map
        (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
          d.boxEdgeCoordinates)
    explicitFormulaRectangleEndpointDataBoxBoundarySum f
        ((explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
            (xpair :: rest) ypairs)).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.boxEdgeCoordinates)) =
      explicitFormulaRectangleEndpointDataBoxBoundarySum f firstRowBoxes +
        explicitFormulaRectangleEndpointDataBoxBoundarySum f remainingBoxes := by
  let whole : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        (xpair :: rest) ypairs)
  let firstRow : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
        xpair ypairs)
  let remaining : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        rest ypairs)
  let firstRowBoxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
    firstRow.map
      (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
        d.boxEdgeCoordinates)
  let remainingBoxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
    remaining.map
      (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
        d.boxEdgeCoordinates)
  have hcells :
      explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          (xpair :: rest) ypairs =
        explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair ypairs ++
          explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
            rest ypairs := by
    exact Eq.refl _
  have hdata :
      whole = firstRow ++ remaining := by
    have hmap :
        explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
              xpair ypairs ++
              explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
                rest ypairs) =
          firstRow ++ remaining := by
      exact
        List.map_append
          (fun c : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε =>
            c.toEndpointData)
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
            xpair ypairs)
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
            rest ypairs)
    exact
      Eq.trans
        (congrArg
          (fun cells : List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε) =>
            explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells cells)
          hcells)
        hmap
  have hboxes :
      whole.map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.boxEdgeCoordinates) =
        firstRowBoxes ++ remainingBoxes := by
    calc
      whole.map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.boxEdgeCoordinates) =
          (firstRow ++ remaining).map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
              d.boxEdgeCoordinates) := by
        exact
          congrArg
            (fun data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) =>
              data.map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.boxEdgeCoordinates))
            hdata
      _ = firstRowBoxes ++ remainingBoxes := by
        exact
          List.map_append
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
              d.boxEdgeCoordinates)
            firstRow
            remaining
  exact
    Eq.trans
      (congrArg
        (fun boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge =>
          explicitFormulaRectangleEndpointDataBoxBoundarySum f boxes)
        hboxes)
      (explicitFormulaRectangleEndpointDataBoxBoundarySum_append
        f firstRowBoxes remainingBoxes)

/-- Bottom-edge accounting for canonical selected endpoint data may be reduced to the
selected crossed sorted adjacent-pair list. -/
theorem explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum_selectedEndpointData_eq_sortedPairLists
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
        (explicitFormulaRectangleSelectedEndpointData F T ε) =
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
            (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε))) := by
  exact Eq.refl _
/-- Top-edge accounting for canonical selected endpoint data may be reduced to the
selected crossed sorted adjacent-pair list. -/
theorem explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_selectedEndpointData_eq_sortedPairLists
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
        (explicitFormulaRectangleSelectedEndpointData F T ε) =
      explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
            (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε))) := by
  exact Eq.refl _
/-- The canonical selected endpoint-data bottom-edge sum is the sum of the selected
bottom horizontal coordinate-edge integrals. -/
theorem explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum_selectedEndpointData_eq_bottomHorizontalEdgeIntegralSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
        (explicitFormulaRectangleSelectedEndpointData F T ε) =
      explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
        ((explicitFormulaRectangleSelectedEndpointData F T ε).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.bottomEdgeCoordinates)) :=
  explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum_eq_bottomHorizontalEdgeIntegralSum
    f (explicitFormulaRectangleSelectedEndpointData F T ε)

/-- The canonical selected endpoint-data top-edge sum is the sum of the selected
top horizontal coordinate-edge integrals. -/
theorem explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_selectedEndpointData_eq_topHorizontalEdgeIntegralSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
        (explicitFormulaRectangleSelectedEndpointData F T ε) =
      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
        ((explicitFormulaRectangleSelectedEndpointData F T ε).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.topEdgeCoordinates)) := by
  induction explicitFormulaRectangleSelectedEndpointData F T ε with
  | nil =>
      exact Eq.refl _
  | cons d rest ih =>
      have hcell :
          explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f d =
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f d.topEdgeCoordinates :=
        explicitFormulaRectangleRegularGridCellEndpointDataTopEdge_eq_coordinateIntegral f d
      calc
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f (d :: rest) =
            explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f d +
              explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f rest := by
          exact Eq.refl _
        _ =
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f d.topEdgeCoordinates +
              explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f rest := by
          exact congrArg
            (fun z : ℂ => z + explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f rest)
            hcell
        _ =
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f d.topEdgeCoordinates +
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
                (rest.map
                  (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                    d.topEdgeCoordinates)) := by
          exact congrArg
            (fun z : ℂ =>
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
                d.topEdgeCoordinates + z)
            ih
        _ =
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
              ((d :: rest).map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.topEdgeCoordinates)) := by
          exact Eq.refl _
/-- The canonical selected endpoint-data top-edge sum is the top coordinate-label sum
over the selected sorted adjacent endpoint-pair grid. -/
theorem explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_selectedEndpointData_eq_selectedTopCoordinates
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
        (explicitFormulaRectangleSelectedEndpointData F T ε) =
      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
        (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfPairLists
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)) := by
  calc
    explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
        (explicitFormulaRectangleSelectedEndpointData F T ε) =
      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
        ((explicitFormulaRectangleSelectedEndpointData F T ε).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.topEdgeCoordinates)) := by
      exact
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_selectedEndpointData_eq_topHorizontalEdgeIntegralSum
          f F T ε
    _ =
      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
        (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfPairLists
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)) := by
      exact congrArg
        (fun edges : List ExplicitFormulaRectangleHorizontalEndpointDataEdge =>
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f edges)
        (explicitFormulaRectangleSelectedEndpointData_topEdgeCoordinates_eq_sortedPairLists
          F T ε)

/-- The canonical selected endpoint-data bottom-edge sum is the sum of the selected
bottom endpoint-data box integrals. -/
theorem explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum_selectedEndpointData_eq_boxBottomEdgeIntegralSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
        (explicitFormulaRectangleSelectedEndpointData F T ε) =
      explicitFormulaRectangleBoxBottomEdgeIntegralSum f
        ((explicitFormulaRectangleSelectedEndpointData F T ε).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.boxEdgeCoordinates)) :=
  explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum_eq_boxBottomEdgeIntegralSum
    f (explicitFormulaRectangleSelectedEndpointData F T ε)

/-- The canonical selected endpoint-data top-edge sum is the sum of the selected
top endpoint-data box integrals. -/
theorem explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_selectedEndpointData_eq_boxTopEdgeIntegralSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
        (explicitFormulaRectangleSelectedEndpointData F T ε) =
      explicitFormulaRectangleBoxTopEdgeIntegralSum f
        ((explicitFormulaRectangleSelectedEndpointData F T ε).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.boxEdgeCoordinates)) :=
  explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_eq_boxTopEdgeIntegralSum
    f (explicitFormulaRectangleSelectedEndpointData F T ε)

/-- The canonical selected endpoint-data right-edge sum is the sum of the selected
right endpoint-data box integrals. -/
theorem explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum_selectedEndpointData_eq_boxRightEdgeIntegralSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
        (explicitFormulaRectangleSelectedEndpointData F T ε) =
      explicitFormulaRectangleBoxRightEdgeIntegralSum f
        ((explicitFormulaRectangleSelectedEndpointData F T ε).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.boxEdgeCoordinates)) :=
  explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum_eq_boxRightEdgeIntegralSum
    f (explicitFormulaRectangleSelectedEndpointData F T ε)

/-- The canonical selected endpoint-data left-edge sum is the sum of the selected
left endpoint-data box integrals. -/
theorem explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum_selectedEndpointData_eq_boxLeftEdgeIntegralSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
        (explicitFormulaRectangleSelectedEndpointData F T ε) =
      explicitFormulaRectangleBoxLeftEdgeIntegralSum f
        ((explicitFormulaRectangleSelectedEndpointData F T ε).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.boxEdgeCoordinates)) :=
  explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum_eq_boxLeftEdgeIntegralSum
    f (explicitFormulaRectangleSelectedEndpointData F T ε)

/-- The selected box-coordinate bottom-side sum is the selected endpoint-data
bottom-side sum over the same crossed adjacent-pair lists. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinates_bottomEdgeIntegralSum_eq_sortedEndpointData
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleBoxBottomEdgeIntegralSum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists xpairs ypairs) =
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
            xpairs ypairs)) := by
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        xpairs ypairs)
  have hboxes :
      data.map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.boxEdgeCoordinates) =
        explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists xpairs ypairs :=
    explicitFormulaRectangleSelectedEndpointDataPairLists_boxEdgeCoordinates xpairs ypairs
  calc
    explicitFormulaRectangleBoxBottomEdgeIntegralSum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists xpairs ypairs) =
        explicitFormulaRectangleBoxBottomEdgeIntegralSum f
          (data.map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
              d.boxEdgeCoordinates)) := by
      exact congrArg
        (fun boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge =>
          explicitFormulaRectangleBoxBottomEdgeIntegralSum f boxes)
        hboxes.symm
    _ =
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data := by
      exact
        (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum_eq_boxBottomEdgeIntegralSum
          f data).symm

/-- The selected box-coordinate top-side sum is the selected endpoint-data top-side
sum over the same crossed adjacent-pair lists. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinates_topEdgeIntegralSum_eq_sortedEndpointData
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleBoxTopEdgeIntegralSum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists xpairs ypairs) =
      explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
            xpairs ypairs)) := by
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        xpairs ypairs)
  have hboxes :
      data.map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.boxEdgeCoordinates) =
        explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists xpairs ypairs :=
    explicitFormulaRectangleSelectedEndpointDataPairLists_boxEdgeCoordinates xpairs ypairs
  calc
    explicitFormulaRectangleBoxTopEdgeIntegralSum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists xpairs ypairs) =
        explicitFormulaRectangleBoxTopEdgeIntegralSum f
          (data.map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
              d.boxEdgeCoordinates)) := by
      exact congrArg
        (fun boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge =>
          explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes)
        hboxes.symm
    _ =
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data := by
      exact
        (explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_eq_boxTopEdgeIntegralSum
          f data).symm

/-- The selected box-coordinate horizontal grouped contribution is the selected
endpoint-data horizontal grouped contribution over the same crossed adjacent-pair lists. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinates_horizontalContribution_eq_sortedEndpointData
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleBoxBottomEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists xpairs ypairs) -
        explicitFormulaRectangleBoxTopEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists xpairs ypairs) =
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              xpairs ypairs)) -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              xpairs ypairs)) := by
  let boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
    explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists xpairs ypairs
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        xpairs ypairs)
  have hbottom :
      explicitFormulaRectangleBoxBottomEdgeIntegralSum f boxes =
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data :=
    explicitFormulaRectangleSelectedBoxEdgeCoordinates_bottomEdgeIntegralSum_eq_sortedEndpointData
      f xpairs ypairs
  have htop :
      explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes =
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data :=
    explicitFormulaRectangleSelectedBoxEdgeCoordinates_topEdgeIntegralSum_eq_sortedEndpointData
      f xpairs ypairs
  calc
    explicitFormulaRectangleBoxBottomEdgeIntegralSum f boxes -
        explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes =
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
          explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes := by
      exact congrArg
        (fun z : ℂ => z - explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes)
        hbottom
    _ =
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data := by
      exact congrArg
        (fun z : ℂ =>
          explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data - z)
        htop

/-- The selected box-coordinate right-side sum is the selected endpoint-data
right-side sum over the same crossed adjacent-pair lists. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinates_rightEdgeIntegralSum_eq_sortedEndpointData
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleBoxRightEdgeIntegralSum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists xpairs ypairs) =
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
            xpairs ypairs)) := by
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        xpairs ypairs)
  have hboxes :
      data.map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.boxEdgeCoordinates) =
        explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists xpairs ypairs :=
    explicitFormulaRectangleSelectedEndpointDataPairLists_boxEdgeCoordinates xpairs ypairs
  calc
    explicitFormulaRectangleBoxRightEdgeIntegralSum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists xpairs ypairs) =
        explicitFormulaRectangleBoxRightEdgeIntegralSum f
          (data.map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
              d.boxEdgeCoordinates)) := by
      exact congrArg
        (fun boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge =>
          explicitFormulaRectangleBoxRightEdgeIntegralSum f boxes)
        hboxes.symm
    _ =
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data := by
      exact
        (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum_eq_boxRightEdgeIntegralSum
          f data).symm

/-- The selected box-coordinate left-side sum is the selected endpoint-data left-side
sum over the same crossed adjacent-pair lists. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinates_leftEdgeIntegralSum_eq_sortedEndpointData
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleBoxLeftEdgeIntegralSum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists xpairs ypairs) =
      explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
            xpairs ypairs)) := by
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        xpairs ypairs)
  have hboxes :
      data.map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.boxEdgeCoordinates) =
        explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists xpairs ypairs :=
    explicitFormulaRectangleSelectedEndpointDataPairLists_boxEdgeCoordinates xpairs ypairs
  calc
    explicitFormulaRectangleBoxLeftEdgeIntegralSum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists xpairs ypairs) =
        explicitFormulaRectangleBoxLeftEdgeIntegralSum f
          (data.map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
              d.boxEdgeCoordinates)) := by
      exact congrArg
        (fun boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge =>
          explicitFormulaRectangleBoxLeftEdgeIntegralSum f boxes)
        hboxes.symm
    _ =
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data := by
      exact
        (explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum_eq_boxLeftEdgeIntegralSum
          f data).symm

/-- The selected box-coordinate vertical contribution is the selected endpoint-data
vertical contribution over the same crossed adjacent-pair lists. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinates_verticalContribution_eq_sortedEndpointData
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleBoxRightEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists xpairs ypairs) -
        explicitFormulaRectangleBoxLeftEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists xpairs ypairs) =
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              xpairs ypairs)) -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              xpairs ypairs)) := by
  let boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
    explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists xpairs ypairs
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        xpairs ypairs)
  have hright :
      explicitFormulaRectangleBoxRightEdgeIntegralSum f boxes =
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data :=
    explicitFormulaRectangleSelectedBoxEdgeCoordinates_rightEdgeIntegralSum_eq_sortedEndpointData
      f xpairs ypairs
  have hleft :
      explicitFormulaRectangleBoxLeftEdgeIntegralSum f boxes =
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data :=
    explicitFormulaRectangleSelectedBoxEdgeCoordinates_leftEdgeIntegralSum_eq_sortedEndpointData
      f xpairs ypairs
  calc
    explicitFormulaRectangleBoxRightEdgeIntegralSum f boxes -
        explicitFormulaRectangleBoxLeftEdgeIntegralSum f boxes =
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
          explicitFormulaRectangleBoxLeftEdgeIntegralSum f boxes := by
      exact congrArg
        (fun z : ℂ => z - explicitFormulaRectangleBoxLeftEdgeIntegralSum f boxes)
        hright
    _ =
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data := by
      exact congrArg
        (fun z : ℂ =>
          explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data - z)
        hleft

/-- Right-edge accounting for canonical selected endpoint data may be reduced to the
selected crossed sorted adjacent-pair list. -/
theorem explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum_selectedEndpointData_eq_sortedPairLists
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
        (explicitFormulaRectangleSelectedEndpointData F T ε) =
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
            (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε))) := by
  exact Eq.refl _
/-- Left-edge accounting for canonical selected endpoint data may be reduced to the
selected crossed sorted adjacent-pair list. -/
theorem explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum_selectedEndpointData_eq_sortedPairLists
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
        (explicitFormulaRectangleSelectedEndpointData F T ε) =
      explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
            (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε))) := by
  exact Eq.refl _
/-- Mapping endpoint-data cells to their right vertical edge coordinates is the same as
mapping the underlying selected adjacent-pair cells to their vertical span at the
right horizontal endpoint. -/
theorem explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells_rightEdgeCoordinates
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (cells : List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε)) :
    (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells cells).map
        (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
          d.rightEdgeCoordinates) =
      cells.map
        (fun c : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε =>
          ((c.ypair.y₀, c.ypair.y₁), c.xpair.x₁)) := by
  induction cells with
  | nil =>
      exact Eq.refl _
  | cons c rest ih =>
      exact
        congrArg
          (fun tail : List ExplicitFormulaRectangleVerticalEndpointDataEdge =>
            ((c.ypair.y₀, c.ypair.y₁), c.xpair.x₁) :: tail)
          ih

/-- Mapping endpoint-data cells to their left vertical edge coordinates is the same as
mapping the underlying selected adjacent-pair cells to their vertical span at the
left horizontal endpoint. -/
theorem explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells_leftEdgeCoordinates
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (cells : List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε)) :
    (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells cells).map
        (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
          d.leftEdgeCoordinates) =
      cells.map
        (fun c : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε =>
          ((c.ypair.y₀, c.ypair.y₁), c.xpair.x₀)) := by
  induction cells with
  | nil =>
      exact Eq.refl _
  | cons c rest ih =>
      exact
        congrArg
          (fun tail : List ExplicitFormulaRectangleVerticalEndpointDataEdge =>
            ((c.ypair.y₀, c.ypair.y₁), c.xpair.x₀) :: tail)
          ih

/-- The canonical selected endpoint-data right-edge coordinate list is the selected
adjacent-pair cell list mapped to the vertical span at each right horizontal endpoint. -/
theorem explicitFormulaRectangleSelectedEndpointData_rightEdgeCoordinates
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    (explicitFormulaRectangleSelectedEndpointData F T ε).map
        (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
          d.rightEdgeCoordinates) =
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCells F T ε).map
        (fun c : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε =>
          ((c.ypair.y₀, c.ypair.y₁), c.xpair.x₁)) := by
  exact
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells_rightEdgeCoordinates
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCells F T ε)

/-- The canonical selected endpoint-data left-edge coordinate list is the selected
adjacent-pair cell list mapped to the vertical span at each left horizontal endpoint. -/
theorem explicitFormulaRectangleSelectedEndpointData_leftEdgeCoordinates
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    (explicitFormulaRectangleSelectedEndpointData F T ε).map
        (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
          d.leftEdgeCoordinates) =
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCells F T ε).map
        (fun c : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε =>
          ((c.ypair.y₀, c.ypair.y₁), c.xpair.x₀)) := by
  exact
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells_leftEdgeCoordinates
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCells F T ε)

/-- A right vertical edge coordinate of selected endpoint data comes from a concrete
selected adjacent-pair cell, hence from sorted adjacent endpoint-pair lists. -/
theorem explicitFormulaRectangleSelectedEndpointData_rightEdgeCoordinates_mem_sortedPairs
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    {d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε}
    (hd : d ∈ explicitFormulaRectangleSelectedEndpointData F T ε) :
    ∃ c : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε,
      c.toEndpointData = d ∧
        c.xpair ∈ explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε ∧
          c.ypair ∈ explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε ∧
            d.rightEdgeCoordinates = ((c.ypair.y₀, c.ypair.y₁), c.xpair.x₁) := by
  match explicitFormulaRectangleSelectedEndpointData_mem_cell hd with
  | ⟨c, hc, hcd⟩ =>
      have hx :
          c.xpair ∈ explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε :=
        explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists_mem_xpair
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)
          c hc
      have hy :
          c.ypair ∈ explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε :=
        explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists_mem_ypair
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)
          c hc
      have hcoord :
          d.rightEdgeCoordinates = ((c.ypair.y₀, c.ypair.y₁), c.xpair.x₁) :=
        Eq.subst
          (motive := fun d' : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d'.rightEdgeCoordinates = ((c.ypair.y₀, c.ypair.y₁), c.xpair.x₁))
          hcd
          (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell.toEndpointData_rightEdgeCoordinates
            c)
      exact ⟨c, hcd, hx, hy, hcoord⟩

/-- A left vertical edge coordinate of selected endpoint data comes from a concrete
selected adjacent-pair cell, hence from sorted adjacent endpoint-pair lists. -/
theorem explicitFormulaRectangleSelectedEndpointData_leftEdgeCoordinates_mem_sortedPairs
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    {d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε}
    (hd : d ∈ explicitFormulaRectangleSelectedEndpointData F T ε) :
    ∃ c : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε,
      c.toEndpointData = d ∧
        c.xpair ∈ explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε ∧
          c.ypair ∈ explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε ∧
            d.leftEdgeCoordinates = ((c.ypair.y₀, c.ypair.y₁), c.xpair.x₀) := by
  match explicitFormulaRectangleSelectedEndpointData_mem_cell hd with
  | ⟨c, hc, hcd⟩ =>
      have hx :
          c.xpair ∈ explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε :=
        explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists_mem_xpair
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)
          c hc
      have hy :
          c.ypair ∈ explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε :=
        explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists_mem_ypair
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)
          c hc
      have hcoord :
          d.leftEdgeCoordinates = ((c.ypair.y₀, c.ypair.y₁), c.xpair.x₀) :=
        Eq.subst
          (motive := fun d' : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d'.leftEdgeCoordinates = ((c.ypair.y₀, c.ypair.y₁), c.xpair.x₀))
          hcd
          (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell.toEndpointData_leftEdgeCoordinates
            c)
      exact ⟨c, hcd, hx, hy, hcoord⟩

/-- Vertical selected-grid accounting for canonical selected endpoint data, after the
right and left sorted-pair edge identifications have been proved.  This is the Part20
bridge that keeps the remaining geometric work at the concrete right/left edge-sum
level: the selected endpoint-data list is the sorted selected grid from `Part17`, and
its vertical contribution is `right target - left target`. -/
theorem explicitFormulaRectangleSelectedEndpointData_verticalEdgeContribution_eq_of_sortedPairEdgeSums
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (rightTarget leftTarget : ℂ)
    (hright :
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
              (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε))) =
        rightTarget)
    (hleft :
      explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
              (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε))) =
        leftTarget) :
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
        (explicitFormulaRectangleSelectedEndpointData F T ε) -
      explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
        (explicitFormulaRectangleSelectedEndpointData F T ε) =
        rightTarget - leftTarget := by
  have hrightSelected :
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
          (explicitFormulaRectangleSelectedEndpointData F T ε) =
        rightTarget := by
    exact
      Eq.trans
        (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum_selectedEndpointData_eq_sortedPairLists
          f F T ε)
        hright
  have hleftSelected :
      explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
          (explicitFormulaRectangleSelectedEndpointData F T ε) =
        leftTarget := by
    exact
      Eq.trans
        (explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum_selectedEndpointData_eq_sortedPairLists
          f F T ε)
        hleft
  calc
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
        (explicitFormulaRectangleSelectedEndpointData F T ε) -
      explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
        (explicitFormulaRectangleSelectedEndpointData F T ε) =
        rightTarget -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
            (explicitFormulaRectangleSelectedEndpointData F T ε) := by
      exact
        congrArg
          (fun z : ℂ =>
            z -
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
                (explicitFormulaRectangleSelectedEndpointData F T ε))
          hrightSelected
    _ = rightTarget - leftTarget := by
      exact congrArg (fun z : ℂ => rightTarget - z) hleftSelected

/-- Specialized vertical selected-grid accounting when the sorted right-edge sum has
already been identified with the outer right side minus the right sides of the square
holes, and the sorted left-edge sum with the outer left side minus the left sides of the
square holes. -/
theorem explicitFormulaRectangleSelectedEndpointData_verticalEdgeContribution_eq_outer_sub_holes
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (outerRight outerLeft holeRight holeLeft : ℂ)
    (hright :
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
              (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε))) =
        outerRight - holeRight)
    (hleft :
      explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
              (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε))) =
        outerLeft - holeLeft) :
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
        (explicitFormulaRectangleSelectedEndpointData F T ε) -
      explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
        (explicitFormulaRectangleSelectedEndpointData F T ε) =
        (outerRight - holeRight) - (outerLeft - holeLeft) :=
  explicitFormulaRectangleSelectedEndpointData_verticalEdgeContribution_eq_of_sortedPairEdgeSums
    f F T ε (outerRight - holeRight) (outerLeft - holeLeft) hright hleft

/-- The endpoint-data boundary sum decomposes into the four list-level edge sums. -/
theorem explicitFormulaRectangleRegularGridEndpointDataBoundarySum_eq_edgeSums
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)) :
    explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data =
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data +
          (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data) := by
  induction data with
  | nil =>
      calc
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum f [] = 0 := by
          exact Eq.refl _
        _ =
          explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f [] -
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f [] +
              (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f [] -
                explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f []) := by
          have hsub : (0 : ℂ) - 0 = 0 :=
            sub_self 0
          calc
            (0 : ℂ) = 0 + 0 := by
              exact (zero_add 0).symm
            _ = (0 - 0) + (0 - 0) := by
              exact congrArg₂ HAdd.hAdd hsub.symm hsub.symm
            _ =
                explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f [] -
                  explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f [] +
                    (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f [] -
                      explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f []) := by
              exact Eq.refl _
  | cons d rest ih =>
      let b : ℂ := explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f d
      let t : ℂ := explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f d
      let r : ℂ := explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f d
      let l : ℂ := explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f d
      let B : ℂ := explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f rest
      let U : ℂ := explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f rest
      let R : ℂ := explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f rest
      let L : ℂ := explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f rest
      have hd :
          explicitFormulaRectangleRegularGridCellEndpointDataBoundary f d =
            b - t + (r - l) := by
        exact explicitFormulaRectangleRegularGridCellEndpointDataBoundary_eq_edges f d
      have hrest :
          explicitFormulaRectangleRegularGridEndpointDataBoundarySum f rest =
            B - U + (R - L) := by
        exact ih
      calc
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum f (d :: rest) =
            explicitFormulaRectangleRegularGridCellEndpointDataBoundary f d +
              explicitFormulaRectangleRegularGridEndpointDataBoundarySum f rest := by
          exact explicitFormulaRectangleRegularGridEndpointDataBoundarySum_cons f d rest
        _ = (b - t + (r - l)) +
              explicitFormulaRectangleRegularGridEndpointDataBoundarySum f rest := by
          exact congrArg
            (fun z : ℂ =>
              z + explicitFormulaRectangleRegularGridEndpointDataBoundarySum f rest)
            hd
        _ = (b - t + (r - l)) + (B - U + (R - L)) := by
          exact congrArg
            (fun z : ℂ => (b - t + (r - l)) + z)
            hrest
        _ = (b + B) - (t + U) + ((r + R) - (l + L)) := by
          exact
            finiteRectangleSubdivisionEndpointBoundary_consEdgeAlgebra
              b t r l B U R L
        _ =
          explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f (d :: rest) -
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f (d :: rest) +
              (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f (d :: rest) -
                explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f (d :: rest)) := by
          exact Eq.refl _
/-- Algebraic bridge from the selected box-boundary collapse in the tangent normalization
directly to selected endpoint-data edge-accounting.  This avoids committing the outer
side comparison to a misleading single outer-corner box orientation: the remaining
geometric sink is precisely that the selected complement box-boundary sum is the tangent
outer boundary minus the raw inscribed-square box boundaries. -/
theorem explicitFormulaRectangleSelectedEndpointData_edgeAccounting_of_tangentBoxBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hboxes :
      explicitFormulaRectangleEndpointDataBoxBoundarySum f
          ((explicitFormulaRectangleSelectedEndpointData F T ε).map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
              d.boxEdgeCoordinates)) =
        (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
            zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) +
            (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
              zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I)) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBoundaryFinsetSum
            f T ε) :
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
        (explicitFormulaRectangleSelectedEndpointData F T ε) -
      explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
        (explicitFormulaRectangleSelectedEndpointData F T ε) +
        (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
            (explicitFormulaRectangleSelectedEndpointData F T ε) -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
            (explicitFormulaRectangleSelectedEndpointData F T ε)) =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
          zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) +
          (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
            zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I)) -
        ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) := by
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleSelectedEndpointData F T ε
  let boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
    data.map
      (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
        d.boxEdgeCoordinates)
  have hdataBoundary :
      explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data =
        explicitFormulaRectangleEndpointDataBoxBoundarySum f boxes :=
    explicitFormulaRectangleRegularGridEndpointDataBoundarySum_eq_boxBoundarySum
      f data
  have hdataEdges :
      explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data =
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data +
            (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data) :=
    explicitFormulaRectangleRegularGridEndpointDataBoundarySum_eq_edgeSums f data
  have hholes :
      explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBoundaryFinsetSum
          f T ε =
        ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) :=
    explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBoundaryFinsetSum_eq
      f T ε
  calc
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
        (explicitFormulaRectangleSelectedEndpointData F T ε) -
      explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
        (explicitFormulaRectangleSelectedEndpointData F T ε) +
        (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
            (explicitFormulaRectangleSelectedEndpointData F T ε) -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
            (explicitFormulaRectangleSelectedEndpointData F T ε)) =
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data := by
      exact hdataEdges.symm
    _ = explicitFormulaRectangleEndpointDataBoxBoundarySum f boxes := by
      exact hdataBoundary
    _ =
        (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
            zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) +
            (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
              zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I)) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBoundaryFinsetSum
            f T ε := by
      exact hboxes
    _ =
        (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
            zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) +
            (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
              zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I)) -
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            finiteRectangleSubdivisionCellBoundaryIntegral
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) := by
      exact congrArg
        (fun z : ℂ =>
          (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
              zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) +
              (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
                zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I)) - z)
        hholes

/-- Grouped side-contribution constructor for raw-hole-selected endpoint data. -/
theorem explicitFormulaRectangleRawHoleSelectedEndpointData_edgeSums_tangentBoundary_rawEdgeSums_of_groupedSideSums
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε))
    (outerBottom outerTop outerRight outerLeft : ℂ)
    (hhorizontal :
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data =
        (outerBottom -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
            f T ε) -
          (outerTop -
            explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
              f T ε))
    (hvertical :
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data =
        (outerRight -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
            f T ε) -
          (outerLeft -
            explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
              f T ε)) :
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data +
          (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data) =
      (outerBottom - outerTop + (outerRight - outerLeft)) -
        (explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
            f T ε -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T ε +
            (explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
                f T ε -
              explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
                f T ε)) := by
  let B : ℂ := explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data
  let U : ℂ := explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data
  let R : ℂ := explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data
  let L : ℂ := explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data
  let b : ℂ :=
    explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum f T ε
  let u : ℂ :=
    explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum f T ε
  let r : ℂ :=
    explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum f T ε
  let l : ℂ :=
    explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum f T ε
  calc
    B - U + (R - L) =
        ((outerBottom - b) - (outerTop - u)) + (R - L) := by
      exact congrArg (fun z : ℂ => z + (R - L)) hhorizontal
    _ =
        ((outerBottom - b) - (outerTop - u)) +
          ((outerRight - r) - (outerLeft - l)) := by
      exact congrArg
        (fun z : ℂ => ((outerBottom - b) - (outerTop - u)) + z)
        hvertical
    _ =
        (outerBottom - outerTop + (outerRight - outerLeft)) +
          ((-b) - (-u) + ((-r) - (-l))) := by
      exact
        (finiteRectangleSubdivisionEndpointBoundary_consEdgeAlgebra
          outerBottom outerTop outerRight outerLeft (-b) (-u) (-r) (-l)).symm
    _ =
        (outerBottom - outerTop + (outerRight - outerLeft)) +
          -(b - u + (r - l)) := by
      exact congrArg
        (fun z : ℂ => (outerBottom - outerTop + (outerRight - outerLeft)) + z)
        (explicitFormulaRectangleEndpointDataBoxEdgeSums_neg_group b u r l)
    _ =
        (outerBottom - outerTop + (outerRight - outerLeft)) -
          (b - u + (r - l)) := by
      exact
        (sub_eq_add_neg
          (outerBottom - outerTop + (outerRight - outerLeft))
          (b - u + (r - l))).symm

theorem explicitFormulaRectangleRawHoleSelectedEndpointData_tangentBoxBoundary_closedRadiusControls
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ε : ℝ} (hT_nonneg : 0 ≤ T) (hε : 0 < ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    (hbottom :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2) (-T))
    (htop :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2) T)
    (hbottomHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a).im)
    (htopHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T (ε / 2)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a).im)
    (hright :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2) F.c)
    (hleft :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2) (1 - F.c))
    (hrightHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner (ε / 2) a).re)
    (hleftHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T (ε / 2)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner (ε / 2) a).re)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ε + ε < dist a b) :
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointData F T (ε / 2)
            (finiteRectangle_halfRadius_pos hε)) -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
          (explicitFormulaRectangleRawHoleSelectedEndpointData F T (ε / 2)
            (finiteRectangle_halfRadius_pos hε)) +
          (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
              (explicitFormulaRectangleRawHoleSelectedEndpointData F T (ε / 2)
                (finiteRectangle_halfRadius_pos hε)) -
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
              (explicitFormulaRectangleRawHoleSelectedEndpointData F T (ε / 2)
                (finiteRectangle_halfRadius_pos hε))) =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
          zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) +
          (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
            zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I)) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBoundaryFinsetSum
          f T (ε / 2) := by
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T (ε / 2)) :=
    explicitFormulaRectangleRawHoleSelectedEndpointData F T (ε / 2)
      (finiteRectangle_halfRadius_pos hε)
  have hraw :
      explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBoundaryFinsetSum
          f T (ε / 2) =
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
            f T (ε / 2) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T (ε / 2) +
            (explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
                f T (ε / 2) -
              explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
                f T (ε / 2)) :=
    explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBoundaryFinsetSum_eq_edgeSums
      f T (ε / 2)
  have hedges :
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data +
            (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data) =
        (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
            zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) +
            (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
              zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I)) -
          (explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
              f T (ε / 2) -
            explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
              f T (ε / 2) +
              (explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
                  f T (ε / 2) -
                explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
                  f T (ε / 2))) :=
    explicitFormulaRectangleRawHoleSelectedEndpointData_edgeSums_tangentBoundary_rawEdgeSums_of_groupedSideSums
      f F T (ε / 2) data
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T))
      (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T))
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I)
      (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I)
      (explicitFormulaRectangleRawHoleSelectedEndpointData_horizontalContribution_core
        f F hT_nonneg hε hclosed hbottom htop hbottomHole htopHole hsep)
      (explicitFormulaRectangleRawHoleSelectedEndpointData_verticalContribution_core
        f F hT_nonneg hε hclosed hright hleft hrightHole hleftHole hsep)
  calc
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data +
          (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data) =
        (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
            zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) +
            (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
              zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I)) -
          (explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
              f T (ε / 2) -
            explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
              f T (ε / 2) +
              (explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
                  f T (ε / 2) -
                explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
                  f T (ε / 2))) := by
      exact hedges
    _ =
        (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
            zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) +
            (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
              zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I)) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBoundaryFinsetSum
            f T (ε / 2) := by
      exact congrArg
        (fun z : ℂ =>
          (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
              zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) +
              (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
                zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I)) - z)
        hraw.symm

theorem explicitFormulaRectangleRawHoleSelectedEndpointData_edgeAccounting_of_tangentBoxBoundary
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (hε : 0 < ε)
    (hboundary :
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
            (explicitFormulaRectangleRawHoleSelectedEndpointData F T ε hε) -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
            (explicitFormulaRectangleRawHoleSelectedEndpointData F T ε hε) +
            (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
                (explicitFormulaRectangleRawHoleSelectedEndpointData F T ε hε) -
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
                (explicitFormulaRectangleRawHoleSelectedEndpointData F T ε hε)) =
        (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
            zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) +
            (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
              zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I)) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBoundaryFinsetSum
            f T ε) :
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
        (explicitFormulaRectangleRawHoleSelectedEndpointData F T ε hε) -
      explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
        (explicitFormulaRectangleRawHoleSelectedEndpointData F T ε hε) +
        (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
            (explicitFormulaRectangleRawHoleSelectedEndpointData F T ε hε) -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
            (explicitFormulaRectangleRawHoleSelectedEndpointData F T ε hε)) =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
          zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) +
          (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
            zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I)) -
        ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) := by
  have hholes :
      explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBoundaryFinsetSum
          f T ε =
        ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) :=
    explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBoundaryFinsetSum_eq
      f T ε
  calc
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
        (explicitFormulaRectangleRawHoleSelectedEndpointData F T ε hε) -
      explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
        (explicitFormulaRectangleRawHoleSelectedEndpointData F T ε hε) +
        (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
            (explicitFormulaRectangleRawHoleSelectedEndpointData F T ε hε) -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
            (explicitFormulaRectangleRawHoleSelectedEndpointData F T ε hε)) =
        (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
            zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) +
            (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
              zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I)) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBoundaryFinsetSum
            f T ε := by
      exact hboundary
    _ =
        (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
            zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) +
            (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
              zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I)) -
          ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
            finiteRectangleSubdivisionCellBoundaryIntegral
              (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
              (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a)
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a) := by
      exact congrArg
        (fun z : ℂ =>
          (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
              zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) +
              (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
                zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I)) - z)
        hholes
end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
