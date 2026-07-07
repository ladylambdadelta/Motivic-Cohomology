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

theorem explicitFormulaRectangleSelectedEndpointDataHorizontalRowScanSub_eq_rowContribution
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
              (explicitFormulaRectangleSelectedAdjacentEndpointData
                xpair ypair homit)
          else
            0)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) -
      explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
              (explicitFormulaRectangleSelectedAdjacentEndpointData
                xpair ypair homit)
          else
            0)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
        f xpair
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) := by
  calc
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
              (explicitFormulaRectangleSelectedAdjacentEndpointData
                xpair ypair homit)
          else
            0)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) -
      explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
              (explicitFormulaRectangleSelectedAdjacentEndpointData
                xpair ypair homit)
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
        explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
          f xpair
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) := by
      exact
        explicitFormulaRectangleSelectedHorizontalEdgeCoordinatesOfFixedX_integralSum_eq_rowContribution_core
          f F xpair

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
              (explicitFormulaRectangleSelectedAdjacentEndpointData
                xpair ypair homit)
          else
            0)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) -
      explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          if homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
              (explicitFormulaRectangleSelectedAdjacentEndpointData
                xpair ypair homit)
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
          (explicitFormulaRectangleSelectedAdjacentEndpointData
                xpair ypair homit)
      else
        0
  let topScan : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ :=
    fun ypair =>
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
          (explicitFormulaRectangleSelectedAdjacentEndpointData
                xpair ypair homit)
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
    exact
      explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution_eq_bottom_sub_top
        f xpair ypair
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
            (explicitFormulaRectangleSelectedAdjacentEndpointData
                xpair ypair homit)
        else
          0)
      ypairs
  let topScan : ℂ :=
    explicitFormulaRectangleListSum
      (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
        if homit :
            explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
          explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
            (explicitFormulaRectangleSelectedAdjacentEndpointData
                xpair ypair homit)
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
theorem explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution_eq_coordinateScan
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
      explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if homit :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
                (explicitFormulaRectangleSelectedAdjacentEndpointData
                  xpair ypair homit)
            else
              0)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) -
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if homit :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
                (explicitFormulaRectangleSelectedAdjacentEndpointData
                  xpair ypair homit)
            else
              0)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) := by
  have hrow :
      explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
          f xpair
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if homit :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
                (explicitFormulaRectangleSelectedAdjacentEndpointData
                  xpair ypair homit)
            else
              0)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) -
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if homit :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
                (explicitFormulaRectangleSelectedAdjacentEndpointData
                  xpair ypair homit)
            else
              0)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) :=
    explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution_eq_bottomScan_sub_topScan
      f F xpair
  exact hrow

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
  have hbottomSum :
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
              f ((xpair.x₀, xpair.x₁), -T))
          xpairs =
        zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) :=
    explicitFormulaRectangleHorizontalOuterBottomSliceContributionSum_eq_outerBottomSide
      f F hT_nonneg hρ hclosed hbottom htop
  have htopSum :
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
        hbottomSum
    _ =
        zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
          zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) := by
      exact congrArg
        (fun z : ℂ =>
          zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) - z)
        htopSum
    _ =
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T := by
      exact Eq.refl _

/-- The local raw square-hole horizontal slices over the sorted horizontal subdivision
assemble to the grouped raw square-hole horizontal side sum. -/
theorem explicitFormulaRectangleHorizontalHoleSliceContributionSum_eq_holeSideSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
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
    ∑ z in (explicitFormulaRectangleRawSingularCoordinates T).attach,
        explicitFormulaRectangleRawHoleXBlockContribution f F hρ z.1 z.2 =
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalHoleSideSum f T ρ := by
  let S : Finset ℂ := explicitFormulaRectangleRawSingularCoordinates T
  let bottomBlock : {a : ℂ // a ∈ S} → ℂ :=
    fun z => explicitFormulaRectangleRawHoleXBlockBottomContribution f F hρ z.1 z.2
  let topBlock : {a : ℂ // a ∈ S} → ℂ :=
    fun z => explicitFormulaRectangleRawHoleXBlockTopContribution f F hρ z.1 z.2
  have hreplace :
      (∑ z in S.attach,
          explicitFormulaRectangleRawHoleXBlockContribution f F hρ z.1 z.2) =
        ∑ z in S.attach, (bottomBlock z - topBlock z) := by
    exact Finset.sum_congr (Eq.refl S.attach)
      (fun z _hz =>
        explicitFormulaRectangleRawHoleXBlockContribution_eq_bottom_sub_top
          f F hρ z.1 z.2)
  have hsplit :
      (∑ z in S.attach, (bottomBlock z - topBlock z)) =
        (∑ z in S.attach, bottomBlock z) - ∑ z in S.attach, topBlock z :=
    Finset.sum_sub_distrib
  have hbottom :
      (∑ z in S.attach, bottomBlock z) =
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum f T ρ :=
    explicitFormulaRectangleHorizontalHoleBottomSliceContributionSum_eq_holeBottomSide
      f F hT_nonneg hρ hclosed hbottomHole hsep
  have htop :
      (∑ z in S.attach, topBlock z) =
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum f T ρ :=
    explicitFormulaRectangleHorizontalHoleTopSliceContributionSum_eq_holeTopSide
      f F hT_nonneg hρ hclosed htopHole hsep
  calc
    (∑ z in S.attach,
        explicitFormulaRectangleRawHoleXBlockContribution f F hρ z.1 z.2) =
        ∑ z in S.attach, (bottomBlock z - topBlock z) := by
      exact hreplace
    _ =
        (∑ z in S.attach, bottomBlock z) - ∑ z in S.attach, topBlock z := by
      exact hsplit
    _ =
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum f T ρ -
          ∑ z in S.attach, topBlock z := by
      exact congrArg
        (fun z : ℂ => z - (∑ w in S.attach, topBlock w))
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
      exact Eq.refl _

/-- The older fixed-row filtered square-hole horizontal slices assemble to the grouped
raw square-hole horizontal side sum. -/
theorem explicitFormulaRectangleHorizontalHoleSliceContributionFilteredSum_eq_holeSideSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
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
    explicitFormulaRectangleHorizontalHoleBottomFilteredSliceContributionSum_eq_holeBottomSide
      f F hT_nonneg hρ hclosed hbottomHole hsep
  have htop :
      explicitFormulaRectangleListSum topSlice xpairs =
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum f T ρ :=
    explicitFormulaRectangleHorizontalHoleTopFilteredSliceContributionSum_eq_holeTopSide
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
      exact Eq.refl _

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
      exact Eq.refl _
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
          exact Eq.refl _
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
          exact Eq.refl _

/-- Horizontal row-contribution exposed-boundary accounting over the sorted selected
adjacent-pair grid, with generated raw square-hole block accounting. -/
theorem explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum_eq_outerSliceSum_sub_rawHoleXBlockContributionSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T ρ : ℝ} (hT_nonneg : 0 ≤ T) (hρ : 0 < ρ)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ρ ⊆ explicitFormulaContourFamilyInterior F T)
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
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                if _homit :
                    explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                  explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                    f ((xpair.x₀, xpair.x₁), ypair.y₀)
                else
                  0)
              (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) -
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                if _homit :
                    explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                  explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                    f ((xpair.x₀, xpair.x₁), ypair.y₁)
                else
                  0)
              (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ))
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) =
      explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
          explicitFormulaRectangleHorizontalOuterSliceContribution f F T xpair)
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) -
      ∑ z in (explicitFormulaRectangleRawSingularCoordinates T).attach,
        explicitFormulaRectangleRawHoleXBlockContribution f F hρ z.1 z.2 := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  let rowContribution : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ :=
    fun xpair =>
      explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if _homit :
                explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁), ypair.y₀)
            else
              0)
          ypairs -
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            if _homit :
                explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁), ypair.y₁)
            else
              0)
          ypairs
  let outerSlice : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ :=
    fun xpair => explicitFormulaRectangleHorizontalOuterSliceContribution f F T xpair
  let holeSlice : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ :=
    fun xpair => explicitFormulaRectangleHorizontalHoleSliceContribution f T ρ xpair
  have hpoint :
    ∀ xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ,
        rowContribution xpair = outerSlice xpair - holeSlice xpair :=
    fun xpair =>
      explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution_eq_outerSlice_sub_holeSlice_core
        f F hT_nonneg hρ hclosed hsep xpair
  have hreplace :
      explicitFormulaRectangleListSum rowContribution xpairs =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            outerSlice xpair - holeSlice xpair)
          xpairs := by
    exact congrArg
      (fun g : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ =>
        explicitFormulaRectangleListSum g xpairs)
      (funext hpoint)
  have hsplit :
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            outerSlice xpair - holeSlice xpair)
          xpairs =
        explicitFormulaRectangleListSum outerSlice xpairs -
          explicitFormulaRectangleListSum holeSlice xpairs :=
    explicitFormulaRectangleListSum_sub outerSlice holeSlice xpairs
  have hfilteredHole :
      explicitFormulaRectangleListSum holeSlice xpairs =
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalHoleSideSum f T ρ :=
    explicitFormulaRectangleHorizontalHoleSliceContributionFilteredSum_eq_holeSideSum
      f F hT_nonneg hρ hclosed hbottomHole htopHole hsep
  have hrawHole :
      (∑ z in (explicitFormulaRectangleRawSingularCoordinates T).attach,
          explicitFormulaRectangleRawHoleXBlockContribution f F hρ z.1 z.2) =
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalHoleSideSum f T ρ :=
    explicitFormulaRectangleHorizontalHoleSliceContributionSum_eq_holeSideSum
      f F hT_nonneg hρ hclosed hbottomHole htopHole hsep
  have hhole :
      explicitFormulaRectangleListSum holeSlice xpairs =
        ∑ z in (explicitFormulaRectangleRawSingularCoordinates T).attach,
          explicitFormulaRectangleRawHoleXBlockContribution f F hρ z.1 z.2 :=
    Eq.trans hfilteredHole hrawHole.symm
  calc
    explicitFormulaRectangleListSum rowContribution xpairs =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            outerSlice xpair - holeSlice xpair)
          xpairs := by
      exact hreplace
    _ =
        explicitFormulaRectangleListSum outerSlice xpairs -
          explicitFormulaRectangleListSum holeSlice xpairs := by
      exact hsplit
    _ =
        explicitFormulaRectangleListSum outerSlice xpairs -
          ∑ z in (explicitFormulaRectangleRawSingularCoordinates T).attach,
            explicitFormulaRectangleRawHoleXBlockContribution f F hρ z.1 z.2 := by
      exact congrArg
        (fun z : ℂ => explicitFormulaRectangleListSum outerSlice xpairs - z)
        hhole

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
