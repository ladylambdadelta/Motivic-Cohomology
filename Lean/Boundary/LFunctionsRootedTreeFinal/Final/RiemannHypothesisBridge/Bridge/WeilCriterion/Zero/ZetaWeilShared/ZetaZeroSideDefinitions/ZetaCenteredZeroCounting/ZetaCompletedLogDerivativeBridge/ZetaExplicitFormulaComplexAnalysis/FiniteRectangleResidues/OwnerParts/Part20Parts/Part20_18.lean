import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part20Parts.Part20_17

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
## Part20 18: GlobalOuterMinusHoleAccounting
-/

theorem explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum_eq_outer_sub_holes
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
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalHoleSideSum f T ρ := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  have hrows :
      explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum
          f xpairs ypairs =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
              f xpair ypairs)
          xpairs :=
    explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum_eq_listSum
      f ypairs xpairs
  have hpoint :
      ∀ xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ,
        explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
            f xpair ypairs =
          explicitFormulaRectangleHorizontalOuterSliceContribution f F T xpair -
            explicitFormulaRectangleHorizontalHoleSliceContribution f T ρ xpair :=
    fun xpair =>
      explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution_eq_outerSlice_sub_holeSlice
        f F hT_nonneg hρ hclosed hsep xpair
  have hslices :
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
              f xpair ypairs)
          xpairs =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            explicitFormulaRectangleHorizontalOuterSliceContribution f F T xpair -
              explicitFormulaRectangleHorizontalHoleSliceContribution f T ρ xpair)
          xpairs := by
    exact
      congrArg
        (fun g : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ =>
          explicitFormulaRectangleListSum g xpairs)
        (funext hpoint)
  calc
    explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum
        f xpairs ypairs =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
              f xpair ypairs)
          xpairs := by
      exact hrows
    _ =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            explicitFormulaRectangleHorizontalOuterSliceContribution f F T xpair -
              explicitFormulaRectangleHorizontalHoleSliceContribution f T ρ xpair)
          xpairs := by
      exact hslices
    _ =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            explicitFormulaRectangleHorizontalOuterSliceContribution f F T xpair) xpairs -
          explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              explicitFormulaRectangleHorizontalHoleSliceContribution f T ρ xpair) xpairs := by
      exact
        explicitFormulaRectangleListSum_sub
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            explicitFormulaRectangleHorizontalOuterSliceContribution f F T xpair)
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            explicitFormulaRectangleHorizontalHoleSliceContribution f T ρ xpair)
          xpairs
    _ =
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalHoleSideSum f T ρ := by
      have houter :
          explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                explicitFormulaRectangleHorizontalOuterSliceContribution f F T xpair) xpairs =
            explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T :=
        explicitFormulaRectangleHorizontalOuterSliceContributionSum_eq_outerSideSum
          f F T ρ hT_nonneg hρ hclosed hbottom htop
      have hhole :
          explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                explicitFormulaRectangleHorizontalHoleSliceContribution f T ρ xpair) xpairs =
            explicitFormulaRectangleSelectedBoxCoordinatesHorizontalHoleSideSum f T ρ :=
        explicitFormulaRectangleHorizontalHoleSliceContributionSum_eq_holeSideSum
          f F hT_nonneg hρ hclosed hbottomHole htopHole hsep
      calc
        explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              explicitFormulaRectangleHorizontalOuterSliceContribution f F T xpair) xpairs -
          explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              explicitFormulaRectangleHorizontalHoleSliceContribution f T ρ xpair) xpairs =
            explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
              explicitFormulaRectangleListSum
                (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                  explicitFormulaRectangleHorizontalHoleSliceContribution f T ρ xpair)
                xpairs := by
          exact congrArg
            (fun z : ℂ =>
              z -
                explicitFormulaRectangleListSum
                  (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                    explicitFormulaRectangleHorizontalHoleSliceContribution f T ρ xpair)
                  xpairs)
            houter
        _ =
            explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
              explicitFormulaRectangleSelectedBoxCoordinatesHorizontalHoleSideSum f T ρ := by
          exact congrArg
            (fun z : ℂ =>
              explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T - z)
            hhole

/-- Vertical column-contribution exposed-boundary accounting over the sorted selected
adjacent-pair grid.  This is the column-telescoping finite classification sink. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum_eq_outer_sub_holes
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
      explicitFormulaRectangleSelectedBoxCoordinatesVerticalOuterSideSum f F T -
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalHoleSideSum f T ρ := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  have hcolumns :
      explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum
          f xpairs ypairs =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
              f xpairs ypair)
          ypairs :=
    explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum_eq_listSum
      f xpairs ypairs
  have hpoint :
      ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ,
        explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
            f xpairs ypair =
          explicitFormulaRectangleVerticalOuterSliceContribution f F T ypair -
            explicitFormulaRectangleVerticalHoleSliceContribution f T ρ ypair :=
    fun ypair =>
      explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution_eq_outerSlice_sub_holeSlice
        f F hT_nonneg hρ hclosed hsep ypair
  have hslices :
      explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
              f xpairs ypair)
          ypairs =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            explicitFormulaRectangleVerticalOuterSliceContribution f F T ypair -
              explicitFormulaRectangleVerticalHoleSliceContribution f T ρ ypair)
          ypairs := by
    exact
      congrArg
        (fun g : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ =>
          explicitFormulaRectangleListSum g ypairs)
        (funext hpoint)
  calc
    explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum
        f xpairs ypairs =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
              f xpairs ypair)
          ypairs := by
      exact hcolumns
    _ =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            explicitFormulaRectangleVerticalOuterSliceContribution f F T ypair -
              explicitFormulaRectangleVerticalHoleSliceContribution f T ρ ypair)
          ypairs := by
      exact hslices
    _ =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            explicitFormulaRectangleVerticalOuterSliceContribution f F T ypair) ypairs -
          explicitFormulaRectangleListSum
            (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              explicitFormulaRectangleVerticalHoleSliceContribution f T ρ ypair) ypairs := by
      exact
        explicitFormulaRectangleListSum_sub
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            explicitFormulaRectangleVerticalOuterSliceContribution f F T ypair)
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            explicitFormulaRectangleVerticalHoleSliceContribution f T ρ ypair)
          ypairs
    _ =
      explicitFormulaRectangleSelectedBoxCoordinatesVerticalOuterSideSum f F T -
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalHoleSideSum f T ρ := by
      have houter :
        explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                explicitFormulaRectangleVerticalOuterSliceContribution f F T ypair) ypairs =
            explicitFormulaRectangleSelectedBoxCoordinatesVerticalOuterSideSum f F T :=
        explicitFormulaRectangleVerticalOuterSliceContributionSum_eq_outerSideSum
          f F T ρ hT_nonneg hρ hclosed hright hleft
      have hhole :
          explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                explicitFormulaRectangleVerticalHoleSliceContribution f T ρ ypair) ypairs =
            explicitFormulaRectangleSelectedBoxCoordinatesVerticalHoleSideSum f T ρ :=
        explicitFormulaRectangleVerticalHoleSliceContributionSum_eq_holeSideSum
          f F hT_nonneg hρ hclosed hrightHole hleftHole hsep
      calc
        explicitFormulaRectangleListSum
            (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              explicitFormulaRectangleVerticalOuterSliceContribution f F T ypair) ypairs -
          explicitFormulaRectangleListSum
            (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
              explicitFormulaRectangleVerticalHoleSliceContribution f T ρ ypair) ypairs =
            explicitFormulaRectangleSelectedBoxCoordinatesVerticalOuterSideSum f F T -
              explicitFormulaRectangleListSum
                (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                  explicitFormulaRectangleVerticalHoleSliceContribution f T ρ ypair)
                ypairs := by
          exact congrArg
            (fun z : ℂ =>
              z -
                explicitFormulaRectangleListSum
                  (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                    explicitFormulaRectangleVerticalHoleSliceContribution f T ρ ypair)
                  ypairs)
            houter
        _ =
            explicitFormulaRectangleSelectedBoxCoordinatesVerticalOuterSideSum f F T -
              explicitFormulaRectangleSelectedBoxCoordinatesVerticalHoleSideSum f T ρ := by
          exact congrArg
            (fun z : ℂ =>
              explicitFormulaRectangleSelectedBoxCoordinatesVerticalOuterSideSum f F T - z)
            hhole

/-- Vertical row/column-contribution exposed-boundary accounting over the sorted
selected adjacent-pair grid.  This is the column-telescoping finite classification sink
for vertical sides. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum_eq_outer_sub_holes
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
      explicitFormulaRectangleSelectedBoxCoordinatesVerticalOuterSideSum f F T -
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalHoleSideSum f T ρ := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  calc
    explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum
        f xpairs ypairs =
        explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum
          f xpairs ypairs := by
      exact
        explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum_eq_columnContributionSum
          f xpairs ypairs
    _ =
      explicitFormulaRectangleSelectedBoxCoordinatesVerticalOuterSideSum f F T -
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalHoleSideSum f T ρ := by
      exact
        explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum_eq_outer_sub_holes
          f F hT_nonneg hρ hclosed hright hleft hrightHole hleftHole hsep

/-- Endpoint-data horizontal side-collapse for the sorted selected grid, in the grouped
outer-minus-hole normalization.  This is the geometric finite-grid cancellation sink:
recursive row accounting has already been erased. -/
theorem explicitFormulaRectangleSelectedEndpointDataHorizontalSortedPairListsContribution_eq_outer_sub_holes
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
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalHoleSideSum f T ρ := by
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
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalHoleSideSum f T ρ := by
      exact
        explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum_eq_outer_sub_holes
          f F hT_nonneg hρ hclosed hbottom htop hbottomHole htopHole hsep

/-- Endpoint-data vertical side-collapse for the sorted selected grid, in the grouped
outer-minus-hole normalization.  This is the geometric finite-grid cancellation sink:
recursive column accounting has already been erased. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalSortedPairListsContribution_eq_outer_sub_holes
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
      explicitFormulaRectangleSelectedBoxCoordinatesVerticalOuterSideSum f F T -
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalHoleSideSum f T ρ := by
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
      explicitFormulaRectangleSelectedBoxCoordinatesVerticalOuterSideSum f F T -
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalHoleSideSum f T ρ := by
      exact
        explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum_eq_outer_sub_holes
          f F hT_nonneg hρ hclosed hright hleft hrightHole hleftHole hsep

/-- Box-coordinate horizontal side-collapse for the sorted selected grid, after
transport to endpoint data. -/
theorem explicitFormulaRectangleSelectedBoxCoordinatesHorizontalContribution_eq_outer_sub_holes
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
    let boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
      explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ)
    explicitFormulaRectangleBoxBottomEdgeIntegralSum f boxes -
        explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes =
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalHoleSideSum f T ρ := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  let boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
    explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists xpairs ypairs
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        xpairs ypairs)
  have hdata :
      explicitFormulaRectangleSelectedEndpointData F T ρ = data :=
    explicitFormulaRectangleSelectedEndpointData_eq_sortedPairLists F T ρ
  calc
    explicitFormulaRectangleBoxBottomEdgeIntegralSum f boxes -
        explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes =
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
            (explicitFormulaRectangleSelectedEndpointData F T ρ) -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
            (explicitFormulaRectangleSelectedEndpointData F T ρ) := by
      exact
        explicitFormulaRectangleSelectedBoxEdgeCoordinates_horizontalContribution_eq_selectedEndpointData
          f F T ρ
    _ =
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data := by
      exact
        congrArg
          (fun z : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) =>
            explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f z -
              explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f z)
          hdata
    _ =
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalHoleSideSum f T ρ := by
      exact
        explicitFormulaRectangleSelectedEndpointDataHorizontalSortedPairListsContribution_eq_outer_sub_holes
          f F hT_nonneg hρ hclosed hbottom htop hbottomHole htopHole hsep

/-- Box-coordinate vertical side-collapse for the sorted selected grid, after transport
to endpoint data. -/
theorem explicitFormulaRectangleSelectedBoxCoordinatesVerticalContribution_eq_outer_sub_holes
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hsep :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          ∀ b : ℂ,
            b ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a ≠ b → ρ + ρ < dist a b) :
    let boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
      explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ)
    explicitFormulaRectangleBoxRightEdgeIntegralSum f boxes -
        explicitFormulaRectangleBoxLeftEdgeIntegralSum f boxes =
      explicitFormulaRectangleSelectedBoxCoordinatesVerticalOuterSideSum f F T -
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalHoleSideSum f T ρ := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  let boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
    explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists xpairs ypairs
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        xpairs ypairs)
  have hdata :
      explicitFormulaRectangleSelectedEndpointData F T ρ = data :=
    explicitFormulaRectangleSelectedEndpointData_eq_sortedPairLists F T ρ
  calc
    explicitFormulaRectangleBoxRightEdgeIntegralSum f boxes -
        explicitFormulaRectangleBoxLeftEdgeIntegralSum f boxes =
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
            (explicitFormulaRectangleSelectedEndpointData F T ρ) -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
            (explicitFormulaRectangleSelectedEndpointData F T ρ) := by
      exact
        explicitFormulaRectangleSelectedBoxEdgeCoordinates_verticalContribution_eq_selectedEndpointData
          f F T ρ
    _ =
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data := by
      exact
        congrArg
          (fun z : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) =>
            explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f z -
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f z)
          hdata
    _ =
      explicitFormulaRectangleSelectedBoxCoordinatesVerticalOuterSideSum f F T -
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalHoleSideSum f T ρ := by
      exact
        explicitFormulaRectangleSelectedEndpointDataVerticalSortedPairListsContribution_eq_outer_sub_holes
          f F hT_nonneg hρ hclosed hright hleft hrightHole hleftHole hsep

/-- Row-major horizontal selected-cell box-coordinate sum equals outer horizontal sides
minus raw square-hole horizontal sides. -/
theorem explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowMajorDoubleSum_eq_outer_sub_holes
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
    explicitFormulaRectangleRowMajorDoubleSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            explicitFormulaRectangleSelectedBoxCoordinatesHorizontalCellContribution
              f xpair ypair)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalHoleSideSum f T ρ := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  let boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
    explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists xpairs ypairs
  calc
    explicitFormulaRectangleRowMajorDoubleSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            explicitFormulaRectangleSelectedBoxCoordinatesHorizontalCellContribution
              f xpair ypair)
        xpairs ypairs =
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContributionSum
          f xpairs ypairs := by
      exact
        (explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContributionSum_eq_rowMajorDoubleSum
          f xpairs ypairs).symm
    _ =
        explicitFormulaRectangleBoxBottomEdgeIntegralSum f boxes -
          explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes := by
      exact
        (explicitFormulaRectangleSelectedBoxCoordinatesHorizontalContribution_eq_rowSum
          f xpairs ypairs).symm
    _ =
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalHoleSideSum f T ρ := by
      exact
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalContribution_eq_outer_sub_holes
          f F hT_nonneg hρ hclosed hbottom htop hbottomHole htopHole hsep

/-- Row-major vertical selected-cell box-coordinate sum equals outer vertical sides minus
raw square-hole vertical sides. -/

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
