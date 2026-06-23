import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part20Parts.Part20_16

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
## Part20 17: HorizontalRowContributionCollapse
-/

theorem explicitFormulaRectangleSelectedEndpointDataHorizontalRowScanSub_eq_outerSlice_sub_holeSlice
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
              a ≠ b → ρ + ρ < dist a b)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
              ({ x₀ := xpair.x₀
                x₁ := xpair.x₁
                y₀ := ypair.y₀
                y₁ := ypair.y₁
                hx₀ := xpair.hx₀
                hx₁ := xpair.hx₁
                hy₀ := ypair.hy₀
                hy₁ := ypair.hy₁
                hx_order := xpair.hx_order
                hy_order := ypair.hy_order
                hx_adj := xpair.hx_adj
                hy_adj := ypair.hy_adj
                homit := homit } :
                  ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ)
          else
            0)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) -
      explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
              ({ x₀ := xpair.x₀
                x₁ := xpair.x₁
                y₀ := ypair.y₀
                y₁ := ypair.y₁
                hx₀ := xpair.hx₀
                hx₁ := xpair.hx₁
                hy₀ := ypair.hy₀
                hy₁ := ypair.hy₁
                hx_order := xpair.hx_order
                hy_order := ypair.hy_order
                hx_adj := xpair.hx_adj
                hy_adj := ypair.hy_adj
                homit := homit } :
                  ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ)
          else
            0)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleHorizontalOuterSliceContribution f F T xpair -
        explicitFormulaRectangleHorizontalHoleSliceContribution f T ρ xpair := by
  calc
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
              ({ x₀ := xpair.x₀
                x₁ := xpair.x₁
                y₀ := ypair.y₀
                y₁ := ypair.y₁
                hx₀ := xpair.hx₀
                hx₁ := xpair.hx₁
                hy₀ := ypair.hy₀
                hy₁ := ypair.hy₁
                hx_order := xpair.hx_order
                hy_order := ypair.hy_order
                hx_adj := xpair.hx_adj
                hy_adj := ypair.hy_adj
                homit := homit } :
                  ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ)
          else
            0)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) -
      explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
              ({ x₀ := xpair.x₀
                x₁ := xpair.x₁
                y₀ := ypair.y₀
                y₁ := ypair.y₁
                hx₀ := xpair.hx₀
                hx₁ := xpair.hx₁
                hy₀ := ypair.hy₀
                hy₁ := ypair.hy₁
                hx_order := xpair.hx_order
                hy_order := ypair.hy_order
                hx_adj := xpair.hx_adj
                hy_adj := ypair.hy_adj
                homit := homit } :
                  ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ)
          else
            0)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX
            xpair
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ)) -
        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
          (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX
            xpair
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ)) := by
      exact
        congrArg₂ HSub.hSub
          (explicitFormulaRectangleSelectedFixedX_bottomScan_eq_coordinateIntegralSum
            f xpair
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ))
          (explicitFormulaRectangleSelectedFixedX_topScan_eq_coordinateIntegralSum
            f xpair
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ))
    _ =
        explicitFormulaRectangleHorizontalOuterSliceContribution f F T xpair -
          explicitFormulaRectangleHorizontalHoleSliceContribution f T ρ xpair := by
      exact
        explicitFormulaRectangleSelectedHorizontalEdgeCoordinatesOfFixedX_integralSum_eq_outerSlice_sub_holeSlice
          f F hT_nonneg hρ hclosed hsep xpair

/-- A fixed-row selected horizontal contribution is its selected bottom-edge scan minus
its selected top-edge scan. -/
theorem explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution_eq_bottomScan_sub_topScan
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :
    explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
        f xpair
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
              ({ x₀ := xpair.x₀
                x₁ := xpair.x₁
                y₀ := ypair.y₀
                y₁ := ypair.y₁
                hx₀ := xpair.hx₀
                hx₁ := xpair.hx₁
                hy₀ := ypair.hy₀
                hy₁ := ypair.hy₁
                hx_order := xpair.hx_order
                hy_order := ypair.hy_order
                hx_adj := xpair.hx_adj
                hy_adj := ypair.hy_adj
                homit := homit } :
                  ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ)
          else
            0)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) -
      explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
              ({ x₀ := xpair.x₀
                x₁ := xpair.x₁
                y₀ := ypair.y₀
                y₁ := ypair.y₁
                hx₀ := xpair.hx₀
                hx₁ := xpair.hx₁
                hy₀ := ypair.hy₀
                hy₁ := ypair.hy₁
                hx_order := xpair.hx_order
                hy_order := ypair.hy_order
                hx_adj := xpair.hx_adj
                hy_adj := ypair.hy_adj
                homit := homit } :
                  ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ)
          else
            0)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) := by
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  let bottomScan : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ :=
    fun ypair =>
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
          ({ x₀ := xpair.x₀
            x₁ := xpair.x₁
            y₀ := ypair.y₀
            y₁ := ypair.y₁
            hx₀ := xpair.hx₀
            hx₁ := xpair.hx₁
            hy₀ := ypair.hy₀
            hy₁ := ypair.hy₁
            hx_order := xpair.hx_order
            hy_order := ypair.hy_order
            hx_adj := xpair.hx_adj
            hy_adj := ypair.hy_adj
            homit := homit } :
              ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ)
      else
        0
  let topScan : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ :=
    fun ypair =>
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
          ({ x₀ := xpair.x₀
            x₁ := xpair.x₁
            y₀ := ypair.y₀
            y₁ := ypair.y₁
            hx₀ := xpair.hx₀
            hx₁ := xpair.hx₁
            hy₀ := ypair.hy₀
            hy₁ := ypair.hy₁
            hx_order := xpair.hx_order
            hy_order := ypair.hy_order
            hx_adj := xpair.hx_adj
            hy_adj := ypair.hy_adj
            homit := homit } :
              ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ)
      else
        0
  have hrow :
      explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
          f xpair ypairs =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
              f xpair ypair)
          ypairs :=
    explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution_eq_listSum
      f xpair ypairs
  have hpoint :
      ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ,
        explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
            f xpair ypair =
          bottomScan ypair - topScan ypair := by
    intro ypair
    by_cases homit :
        explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair
    · rfl
    · exact (sub_zero (0 : ℂ)).symm
  have hreplace :
      explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
              f xpair ypair)
          ypairs =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            bottomScan ypair - topScan ypair)
          ypairs := by
    exact congrArg
      (fun g : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ =>
        explicitFormulaRectangleListSum g ypairs)
      (funext hpoint)
  calc
    explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution f xpair ypairs =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
              f xpair ypair)
          ypairs := by
      exact hrow
    _ =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            bottomScan ypair - topScan ypair)
          ypairs := by
      exact hreplace
    _ =
        explicitFormulaRectangleListSum bottomScan ypairs -
          explicitFormulaRectangleListSum topScan ypairs := by
      exact explicitFormulaRectangleListSum_sub bottomScan topScan ypairs

/-- The paired selected horizontal coordinate-label sums are exactly the selected
fixed-row endpoint-data contribution.  This keeps the remaining exposure problem at the
geometric telescope layer. -/
theorem explicitFormulaRectangleSelectedHorizontalEdgeCoordinatesOfFixedX_integralSum_eq_rowContribution
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :
    explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
        (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX
          xpair
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ)) -
      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
        (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX
          xpair
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ)) =
      explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
        f xpair
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) := by
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  let bottomScan : ℂ :=
    explicitFormulaRectangleListSum
      (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
        if homit :
            explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
          explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
            ({ x₀ := xpair.x₀
              x₁ := xpair.x₁
              y₀ := ypair.y₀
              y₁ := ypair.y₁
              hx₀ := xpair.hx₀
              hx₁ := xpair.hx₁
              hy₀ := ypair.hy₀
              hy₁ := ypair.hy₁
              hx_order := xpair.hx_order
              hy_order := ypair.hy_order
              hx_adj := xpair.hx_adj
              hy_adj := ypair.hy_adj
              homit := homit } :
                ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ)
        else
          0)
      ypairs
  let topScan : ℂ :=
    explicitFormulaRectangleListSum
      (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
        if homit :
            explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
          explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
            ({ x₀ := xpair.x₀
              x₁ := xpair.x₁
              y₀ := ypair.y₀
              y₁ := ypair.y₁
              hx₀ := xpair.hx₀
              hx₁ := xpair.hx₁
              hy₀ := ypair.hy₀
              hy₁ := ypair.hy₁
              hx_order := xpair.hx_order
              hy_order := ypair.hy_order
              hx_adj := xpair.hx_adj
              hy_adj := ypair.hy_adj
              homit := homit } :
                ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ)
        else
          0)
      ypairs
  have hbottom :
      bottomScan =
        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair ypairs) :=
    explicitFormulaRectangleSelectedFixedX_bottomScan_eq_coordinateIntegralSum
      f xpair ypairs
  have htop :
      topScan =
        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
          (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair ypairs) :=
    explicitFormulaRectangleSelectedFixedX_topScan_eq_coordinateIntegralSum
      f xpair ypairs
  have hrow :
      explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
          f xpair ypairs =
        bottomScan - topScan :=
    explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution_eq_bottomScan_sub_topScan
      f F xpair
  calc
    explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
        (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair ypairs) -
      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
        (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair ypairs) =
        bottomScan -
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
            (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair ypairs) := by
      exact congrArg
        (fun z : ℂ =>
          z -
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
              (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair ypairs))
        hbottom.symm
    _ = bottomScan - topScan := by
      exact congrArg (fun z : ℂ => bottomScan - z) htop.symm
    _ =
        explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
          f xpair ypairs := by
      exact hrow.symm

/-- Fixed-row horizontal selected contribution collapses to the local outer horizontal
slice minus the local square-hole horizontal slices. -/
theorem explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution_eq_outerSlice_sub_holeSlice
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
              a ≠ b → ρ + ρ < dist a b)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :
    explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
        f xpair
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleHorizontalOuterSliceContribution f F T xpair -
        explicitFormulaRectangleHorizontalHoleSliceContribution f T ρ xpair := by
  exact
    explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution_eq_outerSlice_sub_holeSlice_core
      f F hT_nonneg hρ hclosed hsep xpair

/-- The local outer horizontal slices over the sorted horizontal subdivision assemble to
the oriented outer horizontal side sum. -/
theorem explicitFormulaRectangleHorizontalOuterSliceContributionSum_eq_outerSideSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ρ : ℝ)
    (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
    (hbottom :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ (-T))
    (htop :
      explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ T) :
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          explicitFormulaRectangleHorizontalOuterSliceContribution f F T xpair)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  have hsplit :
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            explicitFormulaRectangleHorizontalOuterSliceContribution f F T xpair)
          xpairs =
        explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁), -T))
            xpairs -
          explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁), T))
            xpairs :=
    explicitFormulaRectangleListSum_sub
      (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
          f ((xpair.x₀, xpair.x₁), -T))
      (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
          f ((xpair.x₀, xpair.x₁), T))
      xpairs
  have hbottom :
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
              f ((xpair.x₀, xpair.x₁), -T))
          xpairs =
        zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) :=
    explicitFormulaRectangleHorizontalOuterBottomSliceContributionSum_eq_outerBottomSide
      f F hT_nonneg hρ hclosed hbottom htop
  have htop :
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
              f ((xpair.x₀, xpair.x₁), T))
          xpairs =
        zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) :=
    explicitFormulaRectangleHorizontalOuterTopSliceContributionSum_eq_outerTopSide
      f F hT_nonneg hρ hclosed hbottom htop
  calc
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          explicitFormulaRectangleHorizontalOuterSliceContribution f F T xpair)
        xpairs =
        explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁), -T))
            xpairs -
          explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁), T))
            xpairs := by
      exact hsplit
    _ =
        zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleListSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁), T))
            xpairs := by
      exact congrArg
        (fun z : ℂ =>
          z -
            explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                  f ((xpair.x₀, xpair.x₁), T))
              xpairs)
        hbottom
    _ =
        zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
          zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) := by
      exact congrArg
        (fun z : ℂ =>
          zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) - z)
        htop
    _ =
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T := by
      rfl

/-- The local raw square-hole horizontal slices over the sorted horizontal subdivision
assemble to the grouped raw square-hole horizontal side sum. -/
theorem explicitFormulaRectangleHorizontalHoleSliceContributionSum_eq_holeSideSum
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
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          explicitFormulaRectangleHorizontalHoleSliceContribution f T ρ xpair)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalHoleSideSum f T ρ := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let bottomSlice : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ :=
    fun xpair =>
      ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
        if _hspan :
            explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
              ρ xpair a then
          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
            ((xpair.x₀, xpair.x₁),
              (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im)
        else
          0
  let topSlice : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ :=
    fun xpair =>
      ∑ a in explicitFormulaRectangleRawSingularCoordinates T,
        if _hspan :
            explicitFormulaRectangleXAdjacentEndpointPairSubspanOfRawHole
              ρ xpair a then
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
            ((xpair.x₀, xpair.x₁),
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im)
        else
          0
  have hpoint :
      ∀ xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ,
        explicitFormulaRectangleHorizontalHoleSliceContribution f T ρ xpair =
          bottomSlice xpair - topSlice xpair :=
    fun xpair =>
      explicitFormulaRectangleHorizontalHoleSliceContribution_eq_bottom_sub_top
        f F T ρ xpair
  have hreplace :
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            explicitFormulaRectangleHorizontalHoleSliceContribution f T ρ xpair)
          xpairs =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            bottomSlice xpair - topSlice xpair)
          xpairs := by
    exact congrArg
      (fun g : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ =>
        explicitFormulaRectangleListSum g xpairs)
      (funext hpoint)
  have hsplit :
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            bottomSlice xpair - topSlice xpair)
          xpairs =
        explicitFormulaRectangleListSum bottomSlice xpairs -
          explicitFormulaRectangleListSum topSlice xpairs :=
    explicitFormulaRectangleListSum_sub bottomSlice topSlice xpairs
  have hbottom :
      explicitFormulaRectangleListSum bottomSlice xpairs =
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum f T ρ :=
    explicitFormulaRectangleHorizontalHoleBottomSliceContributionSum_eq_holeBottomSide
      f F hT_nonneg hρ hclosed hbottomHole hsep
  have htop :
      explicitFormulaRectangleListSum topSlice xpairs =
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum f T ρ :=
    explicitFormulaRectangleHorizontalHoleTopSliceContributionSum_eq_holeTopSide
      f F hT_nonneg hρ hclosed htopHole hsep
  calc
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          explicitFormulaRectangleHorizontalHoleSliceContribution f T ρ xpair)
        xpairs =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            bottomSlice xpair - topSlice xpair)
          xpairs := by
      exact hreplace
    _ =
        explicitFormulaRectangleListSum bottomSlice xpairs -
          explicitFormulaRectangleListSum topSlice xpairs := by
      exact hsplit
    _ =
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum f T ρ -
          explicitFormulaRectangleListSum topSlice xpairs := by
      exact congrArg
        (fun z : ℂ => z - explicitFormulaRectangleListSum topSlice xpairs)
        hbottom
    _ =
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum f T ρ -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum f T ρ := by
      exact congrArg
        (fun z : ℂ =>
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum f T ρ - z)
        htop
    _ =
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalHoleSideSum f T ρ := by
      rfl

/-- The recursive horizontal row-contribution sum is the recursive list sum over its
fixed-row contributions. -/
theorem explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum_eq_listSum
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ}
    (f : ZetaAdmissibleFunction)
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ)) :
    ∀ xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ),
      explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum
          f xpairs ypairs =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
              f xpair ypairs)
          xpairs
  | [] => by
      rfl
  | xpair :: rest => by
      have htail :
          explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum
              f rest ypairs =
            explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
                  f xpair ypairs)
              rest :=
        explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum_eq_listSum
          f ypairs rest
      calc
        explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum
            f (xpair :: rest) ypairs =
            explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
                f xpair ypairs +
              explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum
                f rest ypairs := by
          rfl
        _ =
            explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
                f xpair ypairs +
              explicitFormulaRectangleListSum
                (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                  explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
                    f xpair ypairs)
                rest := by
          exact congrArg
            (fun z : ℂ =>
              explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
                f xpair ypairs + z)
            htail
        _ =
            explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
                  f xpair ypairs)
              (xpair :: rest) := by
          rfl

/-- Horizontal row-contribution exposed-boundary accounting over the sorted selected
adjacent-pair grid.  This is the row-telescoping finite classification sink. -/

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
