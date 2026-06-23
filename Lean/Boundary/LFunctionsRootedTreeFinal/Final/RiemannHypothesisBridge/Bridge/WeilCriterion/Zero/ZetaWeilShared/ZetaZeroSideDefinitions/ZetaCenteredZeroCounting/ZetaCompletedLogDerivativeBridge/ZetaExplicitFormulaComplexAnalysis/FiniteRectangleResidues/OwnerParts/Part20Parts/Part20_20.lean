import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part20Parts.Part20_19

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
## Part20 20: SelectedEndpointGlobalCores
-/

theorem explicitFormulaRectangleSelectedEndpointDataHorizontalSortedPairListsContribution_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hbottom :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ (-T))
    (htop :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ T)
    (hbottomHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
    (htopHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b) :
    let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
      explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
    let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
      explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
    let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          xpairs ypairs)
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T ρ) := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        xpairs ypairs)
  let boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
    explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists xpairs ypairs
  calc
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data =
        explicitFormulaRectangleBoxBottomEdgeIntegralSum f boxes -
          explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes := by
      exact
        explicitFormulaRectangleSelectedEndpointDataHorizontalSortedPairListsContribution_eq_boxCoordinates
          f xpairs ypairs
    _ =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T ρ) := by
      exact
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalSortedPairListsContribution_core
          f F hT_nonneg hρ hclosed hbottom htop hbottomHole htopHole hsep

/-- Endpoint-data vertical side-collapse for the sorted selected grid after the
recursive column contribution has been erased. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalSortedPairListsContribution_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hright :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ F.c)
    (hleft :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ (1 - F.c))
    (hrightHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
    (hleftHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b) :
    let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
      explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
    let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
      explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
    let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          xpairs ypairs)
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T ρ) := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        xpairs ypairs)
  let boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
    explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists xpairs ypairs
  calc
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data =
        explicitFormulaRectangleBoxRightEdgeIntegralSum f boxes -
          explicitFormulaRectangleBoxLeftEdgeIntegralSum f boxes := by
      exact
        explicitFormulaRectangleSelectedEndpointDataVerticalSortedPairListsContribution_eq_boxCoordinates
          f xpairs ypairs
    _ =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T ρ) := by
      exact
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalSortedPairListsContribution_core
          f F hT_nonneg hρ hclosed hright hleft hrightHole hleftHole hsep

/-- Vertical exposed-boundary accounting for the column-contribution sum over the sorted
horizontal and vertical adjacent-pair lists.  This is the correctly oriented column
telescoping statement: internal vertical sides cancel across adjacent horizontal
intervals, leaving only the outer right/left sides and raw square-hole right/left sides. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum_sortedPairLists_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hright :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ F.c)
    (hleft :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ (1 - F.c))
    (hrightHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
    (hleftHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b) :
    explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum
        f
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T ρ) := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        xpairs ypairs)
  calc
    explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum
        f xpairs ypairs =
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data := by
      exact
        explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum_eq_sortedPairListsContribution
          f F T ρ
    _ =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T ρ) := by
      exact
        explicitFormulaRectangleSelectedEndpointDataVerticalSortedPairListsContribution_core
          f F hT_nonneg hρ hclosed hright hleft hrightHole hleftHole hsep

/-- Row-contribution-sum horizontal exposed-boundary accounting over the sorted
horizontal and vertical adjacent-pair lists.  This is the remaining purely finite
row-telescoping statement after the selected endpoint-data list has been reduced to a
recursive sum of fixed-row contributions. -/
theorem explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum_sortedPairLists_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hbottom :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ (-T))
    (htop :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ T)
    (hbottomHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
    (htopHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b) :
    explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum
        f
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T ρ) := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        xpairs ypairs)
  calc
    explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum
        f xpairs ypairs =
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data := by
      exact
        explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum_eq_sortedPairListsContribution
          f F T ρ
    _ =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T ρ) := by
      exact
        explicitFormulaRectangleSelectedEndpointDataHorizontalSortedPairListsContribution_core
          f F hT_nonneg hρ hclosed hbottom htop hbottomHole htopHole hsep

/-- Row-contribution-sum vertical exposed-boundary accounting over the sorted horizontal
and vertical adjacent-pair lists.  This is the remaining purely finite row/column
telescoping statement after the selected endpoint-data list has been reduced to a
recursive sum of fixed-row contributions. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum_sortedPairLists_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hright :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ F.c)
    (hleft :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ (1 - F.c))
    (hrightHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
    (hleftHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b) :
    explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum
        f
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T ρ) := by
  calc
    explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum
        f
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
        explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum
          f
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) := by
      exact
        explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum_eq_columnContributionSum
          f
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ)
    _ =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T ρ) := by
      exact
        explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum_sortedPairLists_core
          f F hT_nonneg hρ hclosed hright hleft hrightHole hleftHole hsep

/-- Global horizontal exposed-edge accounting over the sorted horizontal adjacent-pair
list, reduced to row-contribution accounting. -/
theorem explicitFormulaRectangleSelectedEndpointData_horizontalContribution_sortedPairLists_of_rowSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hbottom :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ (-T))
    (htop :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ T)
    (hbottomHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
    (htopHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b) :
    let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ))
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T ρ) := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        xpairs ypairs)
  calc
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data =
        explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum
          f xpairs ypairs := by
      exact
        explicitFormulaRectangleSelectedEndpointDataHorizontalContribution_pairLists_eq_rowSum
          f xpairs ypairs
    _ =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T ρ) := by
      exact
        explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum_sortedPairLists_core
          f F hT_nonneg hρ hclosed hbottom htop hbottomHole htopHole hsep

/-- Global vertical exposed-edge accounting over the sorted horizontal adjacent-pair list,
reduced to row-contribution accounting. -/
theorem explicitFormulaRectangleSelectedEndpointData_verticalContribution_sortedPairLists_of_rowSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hright :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ F.c)
    (hleft :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ (1 - F.c))
    (hrightHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
    (hleftHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b) :
    let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ))
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T ρ) := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        xpairs ypairs)
  calc
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data =
        explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum
          f xpairs ypairs := by
      exact
        explicitFormulaRectangleSelectedEndpointDataVerticalContribution_pairLists_eq_rowSum
          f xpairs ypairs
    _ =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T ρ) := by
      exact
        explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum_sortedPairLists_core
          f F hT_nonneg hρ hclosed hright hleft hrightHole hleftHole hsep

/-- Horizontal contribution collapse for the explicit sorted crossed adjacent-pair list.
This is the concrete row-telescoping theorem: after expanding the selected cells in
sorted `x` rows and sorted `y` intervals, internal horizontal sides cancel and the
remaining horizontal sides are the outer bottom/top sides minus the square-hole
bottom/top sides. -/
theorem explicitFormulaRectangleSelectedEndpointData_horizontalContribution_sortedPairLists_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hbottom :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ (-T))
    (htop :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ T)
    (hbottomHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
    (htopHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b) :
    let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ))
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T ρ) := by
  exact
    explicitFormulaRectangleSelectedEndpointData_horizontalContribution_sortedPairLists_of_rowSum
      f F hT_nonneg hρ hclosed hbottom htop hbottomHole htopHole hsep

/-- Vertical contribution collapse for the explicit sorted crossed adjacent-pair list.
This is the concrete column-telescoping theorem: after expanding the selected cells in
sorted `x` rows and sorted `y` intervals, internal vertical sides cancel and the
remaining vertical sides are the outer right/left sides minus the square-hole right/left
sides. -/
theorem explicitFormulaRectangleSelectedEndpointData_verticalContribution_sortedPairLists_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hright :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ F.c)
    (hleft :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ (1 - F.c))
    (hrightHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
    (hleftHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b) :
    let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ))
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T ρ) := by
  exact
    explicitFormulaRectangleSelectedEndpointData_verticalContribution_sortedPairLists_of_rowSum
      f F hT_nonneg hρ hclosed hright hleft hrightHole hleftHole hsep

/-- Horizontal contribution collapse for the canonical selected endpoint data at a fixed
subdivision radius.  This is the row-telescoping finite classification: the selected
regular complement cells expose exactly the bottom/top sides of the outer rectangle and
the bottom/top sides of the raw square holes. -/
theorem explicitFormulaRectangleSelectedEndpointData_horizontalContribution_sortedRadius_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hbottom :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ (-T))
    (htop :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ T)
    (hbottomHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
    (htopHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b) :
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
          (explicitFormulaRectangleSelectedEndpointData F T ρ) -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
          (explicitFormulaRectangleSelectedEndpointData F T ρ) =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T ρ) := by
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
    explicitFormulaRectangleSelectedEndpointData F T ρ
  let sortedData : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ))
  have hdata : data = sortedData :=
    explicitFormulaRectangleSelectedEndpointData_eq_sortedPairLists F T ρ
  calc
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data =
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f sortedData -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data := by
      exact congrArg
        (fun z : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) =>
          explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f z -
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data)
        hdata
    _ =
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f sortedData -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f sortedData := by
      exact congrArg
        (fun z : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) =>
          explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f sortedData -
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f z)
        hdata
    _ =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T ρ) := by
      exact
        explicitFormulaRectangleSelectedEndpointData_horizontalContribution_sortedPairLists_core
          f F hT_nonneg hρ hclosed hbottom htop hbottomHole htopHole hsep

/-- Vertical contribution collapse for the canonical selected endpoint data at a fixed
subdivision radius.  This is the column-telescoping finite classification: the selected
regular complement cells expose exactly the right/left sides of the outer rectangle and
the right/left sides of the raw square holes. -/
theorem explicitFormulaRectangleSelectedEndpointData_verticalContribution_sortedRadius_core
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hright :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ F.c)
    (hleft :
      explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ (1 - F.c))
    (hrightHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re)
    (hleftHole :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b) :
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
          (explicitFormulaRectangleSelectedEndpointData F T ρ) -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
          (explicitFormulaRectangleSelectedEndpointData F T ρ) =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T ρ) := by
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
    explicitFormulaRectangleSelectedEndpointData F T ρ
  let sortedData : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ))
  have hdata : data = sortedData :=
    explicitFormulaRectangleSelectedEndpointData_eq_sortedPairLists F T ρ
  calc
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data =
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f sortedData -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data := by
      exact congrArg
        (fun z : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) =>
          explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f z -
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data)
        hdata
    _ =
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f sortedData -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f sortedData := by
      exact congrArg
        (fun z : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) =>
          explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f sortedData -
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f z)
        hdata
    _ =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T ρ) := by
      exact
        explicitFormulaRectangleSelectedEndpointData_verticalContribution_sortedPairLists_core
          f F hT_nonneg hρ hclosed hright hleft hrightHole hleftHole hsep

/-- Endpoint-data horizontal contribution collapse for the sorted selected grid. -/
theorem explicitFormulaRectangleSelectedEndpointData_horizontalContribution_core
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
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ε + ε < dist a b) :
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
          (explicitFormulaRectangleSelectedEndpointData F T (ε / 2)) -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
          (explicitFormulaRectangleSelectedEndpointData F T (ε / 2)) =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T (ε / 2)) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T (ε / 2)) := by
  exact
    explicitFormulaRectangleSelectedEndpointData_horizontalContribution_sortedRadius_core
      f F
      hT_nonneg
      (finiteRectangle_halfRadius_pos hε)
      (explicitFormulaRectangle_closedRadiusControls_halfRadius F T ε hε hclosed)
      hbottom
      htop
      (fun a ha b hb hab =>
        calc
          ε / 2 + ε / 2 = ε := by
            exact add_halves ε
          _ < ε + ε := by
            exact lt_add_of_pos_right ε hε
          _ < dist a b := by
            exact hsep a ha b hb hab)

/-- Endpoint-data vertical contribution collapse for the sorted selected grid. -/
theorem explicitFormulaRectangleSelectedEndpointData_verticalContribution_core
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
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
          (explicitFormulaRectangleSelectedEndpointData F T (ε / 2)) -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
          (explicitFormulaRectangleSelectedEndpointData F T (ε / 2)) =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T (ε / 2)) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T (ε / 2)) := by
  exact
    explicitFormulaRectangleSelectedEndpointData_verticalContribution_sortedRadius_core
      f F
      hT_nonneg
      (finiteRectangle_halfRadius_pos hε)
      (explicitFormulaRectangle_closedRadiusControls_halfRadius F T ε hε hclosed)
      hright
      hleft
      hrightHole
      hleftHole
      (fun a ha b hb hab =>
        calc
          ε / 2 + ε / 2 = ε := by
            exact add_halves ε
          _ < ε + ε := by
            exact lt_add_of_pos_right ε hε
          _ < dist a b := by
            exact hsep a ha b hb hab)

/-- Horizontal contribution collapse for selected sorted box labels.  This is the
finite exposed-edge classification statement in the horizontal direction: internal
horizontal edges cancel only in the grouped `bottom - top` contribution. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinates_horizontalContribution_core
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
        explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T (ε / 2)) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T (ε / 2)) := by
  let boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
    explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
      (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T (ε / 2))
      (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T (ε / 2))
  calc
    explicitFormulaRectangleBoxBottomEdgeIntegralSum f boxes -
        explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes =
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
            (explicitFormulaRectangleSelectedEndpointData F T (ε / 2)) -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
            (explicitFormulaRectangleSelectedEndpointData F T (ε / 2)) := by
      exact
        explicitFormulaRectangleSelectedBoxEdgeCoordinates_horizontalContribution_eq_selectedEndpointData
          f F T (ε / 2)
    _ =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T (ε / 2)) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T (ε / 2)) := by
      exact
        explicitFormulaRectangleSelectedEndpointData_horizontalContribution_core
          f F hT_nonneg hε hclosed hbottom htop hbottomHole htopHole hsep

/-- Vertical contribution collapse for selected sorted box labels.  This is the
finite exposed-edge classification statement in the vertical direction: internal
vertical edges cancel only in the grouped `right - left` contribution. -/

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
