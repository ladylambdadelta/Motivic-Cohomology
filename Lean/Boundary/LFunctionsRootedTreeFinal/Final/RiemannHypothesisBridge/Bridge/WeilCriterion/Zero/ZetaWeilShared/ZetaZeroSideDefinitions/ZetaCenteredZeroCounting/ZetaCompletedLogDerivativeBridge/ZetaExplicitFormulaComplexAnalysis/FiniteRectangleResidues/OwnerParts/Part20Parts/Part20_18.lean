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

/-- Horizontal row-contribution exposed-boundary accounting over the sorted selected
adjacent-pair grid, with generated raw square-hole block accounting. -/
theorem explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum_eq_outer_sub_rawHoleXBlocks
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
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
        ∑ z in (explicitFormulaRectangleRawSingularCoordinates T).attach,
          explicitFormulaRectangleRawHoleXBlockContribution f F hρ z.1 z.2 := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  let rawRow : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ → ℂ :=
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
  have hrowsRaw :
      explicitFormulaRectangleListSum rawRow xpairs =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            explicitFormulaRectangleHorizontalOuterSliceContribution f F T xpair)
          xpairs -
        ∑ z in (explicitFormulaRectangleRawSingularCoordinates T).attach,
          explicitFormulaRectangleRawHoleXBlockContribution f F hρ z.1 z.2 :=
    explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum_eq_outerSliceSum_sub_rawHoleXBlockContributionSum
      f F hT_nonneg hρ hclosed hbottomHole htopHole hsep
  have houter :
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            explicitFormulaRectangleHorizontalOuterSliceContribution f F T xpair) xpairs =
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T :=
    explicitFormulaRectangleHorizontalOuterSliceContributionSum_eq_outerSideSum
      f F T ρ hT_nonneg hρ hclosed hbottom htop
  calc
    explicitFormulaRectangleListSum rawRow xpairs =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            explicitFormulaRectangleHorizontalOuterSliceContribution f F T xpair)
          xpairs -
        ∑ z in (explicitFormulaRectangleRawSingularCoordinates T).attach,
          explicitFormulaRectangleRawHoleXBlockContribution f F hρ z.1 z.2 := by
      exact hrowsRaw
    _ =
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
        ∑ z in (explicitFormulaRectangleRawSingularCoordinates T).attach,
          explicitFormulaRectangleRawHoleXBlockContribution f F hρ z.1 z.2 := by
      exact congrArg
        (fun z : ℂ =>
          z -
            ∑ z in (explicitFormulaRectangleRawSingularCoordinates T).attach,
              explicitFormulaRectangleRawHoleXBlockContribution f F hρ z.1 z.2)
        houter

/-- Horizontal row-contribution exposed-boundary accounting over the sorted selected
adjacent-pair grid, in the grouped outer-minus-hole normalization. -/
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
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalHoleSideSum f T ρ := by
  have hraw :
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
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
          ∑ z in (explicitFormulaRectangleRawSingularCoordinates T).attach,
            explicitFormulaRectangleRawHoleXBlockContribution f F hρ z.1 z.2 :=
    explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum_eq_outer_sub_rawHoleXBlocks
      f F hT_nonneg hρ hclosed hbottom htop hbottomHole htopHole hsep
  have hhole :
      (∑ z in (explicitFormulaRectangleRawSingularCoordinates T).attach,
          explicitFormulaRectangleRawHoleXBlockContribution f F hρ z.1 z.2) =
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalHoleSideSum f T ρ :=
    explicitFormulaRectangleHorizontalHoleSliceContributionSum_eq_holeSideSum
      f F hT_nonneg hρ hclosed hbottomHole htopHole hsep
  calc
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
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
          ∑ z in (explicitFormulaRectangleRawSingularCoordinates T).attach,
            explicitFormulaRectangleRawHoleXBlockContribution f F hρ z.1 z.2 := by
      exact hraw
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
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                if _homit :
                    explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                  explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
                    f ((ypair.y₀, ypair.y₁), xpair.x₁)
                else
                  0)
              (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) -
            explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                if _homit :
                    explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                  explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
                    f ((ypair.y₀, ypair.y₁), xpair.x₀)
                else
                  0)
              (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ))
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleSelectedBoxCoordinatesVerticalOuterSideSum f F T -
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalHoleSideSum f T ρ := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  let rawColumn : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ → ℂ :=
    fun ypair =>
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _homit :
                explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
              explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁), xpair.x₁)
            else
              0)
          xpairs -
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
            if _homit :
                explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁), xpair.x₀)
            else
              0)
          xpairs
  have hpoint :
      ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ,
        rawColumn ypair =
          explicitFormulaRectangleVerticalOuterSliceContribution f F T ypair -
            explicitFormulaRectangleVerticalHoleSliceContribution f T ρ ypair :=
    fun ypair =>
      explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution_eq_outerSlice_sub_holeSlice
        f F hT_nonneg hρ hclosed hsep ypair
  have hslices :
      explicitFormulaRectangleListSum rawColumn ypairs =
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
    explicitFormulaRectangleListSum rawColumn ypairs =
        explicitFormulaRectangleListSum rawColumn ypairs := by
      exact Eq.refl _
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
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                if _homit :
                    explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                  explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
                    f ((ypair.y₀, ypair.y₁), xpair.x₁)
                else
                  0)
              (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ) -
            explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                if _homit :
                    explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                  explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
                    f ((ypair.y₀, ypair.y₁), xpair.x₀)
                else
                  0)
              (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ))
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ) =
      explicitFormulaRectangleSelectedBoxCoordinatesVerticalOuterSideSum f F T -
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalHoleSideSum f T ρ := by
  exact
    explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum_eq_outer_sub_holes
      f F hT_nonneg hρ hclosed hright hleft hrightHole hleftHole hsep

/-- Endpoint-data horizontal side-collapse for the sorted selected grid, with generated
raw square-hole block accounting.  This is the geometric finite-grid cancellation sink:
recursive row accounting has already been erased. -/
theorem explicitFormulaRectangleSelectedEndpointDataHorizontalSortedPairListsContribution_eq_outer_sub_rawHoleXBlocks
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
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
        ∑ z in (explicitFormulaRectangleRawSingularCoordinates T).attach,
          explicitFormulaRectangleRawHoleXBlockContribution f F hρ z.1 z.2 := by
  exact
    explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum_eq_outer_sub_rawHoleXBlocks
      f F hT_nonneg hρ hclosed hbottom htop hbottomHole htopHole hsep

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
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalHoleSideSum f T ρ := by
  have hraw :
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
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
          ∑ z in (explicitFormulaRectangleRawSingularCoordinates T).attach,
            explicitFormulaRectangleRawHoleXBlockContribution f F hρ z.1 z.2 :=
    explicitFormulaRectangleSelectedEndpointDataHorizontalSortedPairListsContribution_eq_outer_sub_rawHoleXBlocks
      f F hT_nonneg hρ hclosed hbottom htop hbottomHole htopHole hsep
  have hhole :
      (∑ z in (explicitFormulaRectangleRawSingularCoordinates T).attach,
          explicitFormulaRectangleRawHoleXBlockContribution f F hρ z.1 z.2) =
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalHoleSideSum f T ρ :=
    explicitFormulaRectangleHorizontalHoleSliceContributionSum_eq_holeSideSum
      f F hT_nonneg hρ hclosed hbottomHole htopHole hsep
  calc
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
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
          ∑ z in (explicitFormulaRectangleRawSingularCoordinates T).attach,
            explicitFormulaRectangleRawHoleXBlockContribution f F hρ z.1 z.2 := by
      exact hraw
    _ =
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalHoleSideSum f T ρ := by
      exact congrArg
        (fun z : ℂ =>
          explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T - z)
        hhole

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
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                if _homit :
                    explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                  explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
                    f ((ypair.y₀, ypair.y₁), xpair.x₁)
                else
                  0)
              xpairs -
            explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                if _homit :
                    explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                  explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
                    f ((ypair.y₀, ypair.y₁), xpair.x₀)
                else
                  0)
              xpairs)
        ypairs =
      explicitFormulaRectangleSelectedBoxCoordinatesVerticalOuterSideSum f F T -
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalHoleSideSum f T ρ := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  exact
    explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum_eq_outer_sub_holes
      f F hT_nonneg hρ hclosed hright hleft hrightHole hleftHole hsep

/-- Box-coordinate horizontal side-collapse for the sorted selected grid, after
transport to endpoint data, with generated raw square-hole block accounting. -/
theorem explicitFormulaRectangleSelectedBoxCoordinatesHorizontalContribution_eq_outer_sub_rawHoleXBlocks
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
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
        ∑ z in (explicitFormulaRectangleRawSingularCoordinates T).attach,
          explicitFormulaRectangleRawHoleXBlockContribution f F hρ z.1 z.2 := by
  exact
    explicitFormulaRectangleSelectedEndpointDataHorizontalSortedPairListsContribution_eq_outer_sub_rawHoleXBlocks
      f F hT_nonneg hρ hclosed hbottom htop hbottomHole htopHole hsep

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
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalHoleSideSum f T ρ := by
  have hraw :
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
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
          ∑ z in (explicitFormulaRectangleRawSingularCoordinates T).attach,
            explicitFormulaRectangleRawHoleXBlockContribution f F hρ z.1 z.2 :=
    explicitFormulaRectangleSelectedBoxCoordinatesHorizontalContribution_eq_outer_sub_rawHoleXBlocks
      f F hT_nonneg hρ hclosed hbottom htop hbottomHole htopHole hsep
  have hhole :
      (∑ z in (explicitFormulaRectangleRawSingularCoordinates T).attach,
          explicitFormulaRectangleRawHoleXBlockContribution f F hρ z.1 z.2) =
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalHoleSideSum f T ρ :=
    explicitFormulaRectangleHorizontalHoleSliceContributionSum_eq_holeSideSum
      f F hT_nonneg hρ hclosed hbottomHole htopHole hsep
  calc
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
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
          ∑ z in (explicitFormulaRectangleRawSingularCoordinates T).attach,
            explicitFormulaRectangleRawHoleXBlockContribution f F hρ z.1 z.2 := by
      exact hraw
    _ =
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalHoleSideSum f T ρ := by
      exact congrArg
        (fun z : ℂ =>
          explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T - z)
        hhole

/-- Box-coordinate vertical side-collapse for the sorted selected grid, after transport
to endpoint data. -/
theorem explicitFormulaRectangleSelectedBoxCoordinatesVerticalContribution_eq_outer_sub_holes
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
    explicitFormulaRectangleListSum
        (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
          explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                if _homit :
                    explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                  explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
                    f ((ypair.y₀, ypair.y₁), xpair.x₁)
                else
                  0)
              xpairs -
            explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                if _homit :
                    explicitFormulaRectangleAdjacentEndpointPairRawHoleOmission xpair ypair then
                  explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
                    f ((ypair.y₀, ypair.y₁), xpair.x₀)
                else
                  0)
              xpairs)
        ypairs =
      explicitFormulaRectangleSelectedBoxCoordinatesVerticalOuterSideSum f F T -
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalHoleSideSum f T ρ := by
  exact
    explicitFormulaRectangleSelectedEndpointDataVerticalSortedPairListsContribution_eq_outer_sub_holes
      f F hT_nonneg hρ hclosed hright hleft hrightHole hleftHole hsep

/-- Row-major horizontal selected-cell box-coordinate sum equals outer horizontal sides
minus generated raw square-hole horizontal blocks. -/
theorem explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowMajorDoubleSum_eq_outer_sub_rawHoleXBlocks
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
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
        ∑ z in (explicitFormulaRectangleRawSingularCoordinates T).attach,
          explicitFormulaRectangleRawHoleXBlockContribution f F hρ z.1 z.2 := by
  exact
    explicitFormulaRectangleSelectedBoxCoordinatesHorizontalContribution_eq_outer_sub_rawHoleXBlocks
      f F hT_nonneg hρ hclosed hbottom htop hbottomHole htopHole hsep

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
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalHoleSideSum f T ρ := by
  have hraw :
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
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
          ∑ z in (explicitFormulaRectangleRawSingularCoordinates T).attach,
            explicitFormulaRectangleRawHoleXBlockContribution f F hρ z.1 z.2 :=
    explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowMajorDoubleSum_eq_outer_sub_rawHoleXBlocks
      f F hT_nonneg hρ hclosed hbottom htop hbottomHole htopHole hsep
  have hhole :
      (∑ z in (explicitFormulaRectangleRawSingularCoordinates T).attach,
          explicitFormulaRectangleRawHoleXBlockContribution f F hρ z.1 z.2) =
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalHoleSideSum f T ρ :=
    explicitFormulaRectangleHorizontalHoleSliceContributionSum_eq_holeSideSum
      f F hT_nonneg hρ hclosed hbottomHole htopHole hsep
  calc
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
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
          ∑ z in (explicitFormulaRectangleRawSingularCoordinates T).attach,
            explicitFormulaRectangleRawHoleXBlockContribution f F hρ z.1 z.2 := by
      exact hraw
    _ =
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalHoleSideSum f T ρ := by
      exact congrArg
        (fun z : ℂ =>
          explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T - z)
        hhole
end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
