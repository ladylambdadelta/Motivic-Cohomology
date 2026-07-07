import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part20Parts.Part20_18

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
## Part20 19: ExposedSideTargets
-/

def explicitFormulaRectangleRawHoleHorizontalEndpointDataSideSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (T ρ : ℝ) : ℂ :=
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
    (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ)

def explicitFormulaRectangleRawHoleVerticalEndpointDataSideSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (T ρ : ℝ) : ℂ :=
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
    (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ)

theorem explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowMajorDoubleSum_eq_outer_sub_holes
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
    explicitFormulaRectangleRawHoleVerticalEndpointDataSideSum f F T ρ =
      explicitFormulaRectangleSelectedBoxCoordinatesVerticalOuterSideSum f F T -
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalHoleSideSum f T ρ := by
  exact
    explicitFormulaRectangleSelectedBoxCoordinatesVerticalContribution_eq_outer_sub_holes
      f F hT_nonneg hρ hclosed hright hleft hrightHole hleftHole hsep

/-- Row-major horizontal selected-cell box-coordinate sum collapses to the exposed
horizontal side sum. -/
theorem explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowMajorDoubleSum_eq_exposedSideSum
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
    explicitFormulaRectangleRawHoleHorizontalEndpointDataSideSum f F T ρ =
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalExposedSideSum f F T ρ := by
  exact
    explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowMajorDoubleSum_eq_outer_sub_holes
      f F hT_nonneg hρ hclosed hbottom htop hbottomHole htopHole hsep

/-- Row-major vertical selected-cell box-coordinate sum collapses to the exposed vertical
side sum. -/
theorem explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowMajorDoubleSum_eq_exposedSideSum
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
    explicitFormulaRectangleRawHoleVerticalEndpointDataSideSum f F T ρ =
      explicitFormulaRectangleSelectedBoxCoordinatesVerticalExposedSideSum f F T ρ := by
  exact
    explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowMajorDoubleSum_eq_outer_sub_holes
      f F hT_nonneg hρ hclosed hright hleft hrightHole hleftHole hsep

/-- The exposed horizontal side sum is the target outer-minus-hole horizontal expression. -/
theorem explicitFormulaRectangleSelectedBoxCoordinatesHorizontalExposedSideSum_eq_target
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (T ρ : ℝ) :
    explicitFormulaRectangleSelectedBoxCoordinatesHorizontalExposedSideSum f F T ρ =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T ρ) := by
  exact
    explicitFormulaRectangleOuterSubHoleSideAlgebra
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T))
      (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T))
      (explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
        f T ρ)
      (explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
        f T ρ)

/-- The exposed vertical side sum is the target outer-minus-hole vertical expression. -/
theorem explicitFormulaRectangleSelectedBoxCoordinatesVerticalExposedSideSum_eq_target
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (T ρ : ℝ) :
    explicitFormulaRectangleSelectedBoxCoordinatesVerticalExposedSideSum f F T ρ =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T ρ) := by
  exact
    explicitFormulaRectangleOuterSubHoleSideAlgebra
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I)
      (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I)
      (explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
        f T ρ)
      (explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
        f T ρ)

/-- Row-major horizontal selected-cell box-coordinate side collapse. -/
theorem explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowMajorDoubleSum_core
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
    explicitFormulaRectangleRawHoleHorizontalEndpointDataSideSum f F T ρ =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T ρ) := by
  calc
    explicitFormulaRectangleRawHoleHorizontalEndpointDataSideSum f F T ρ =
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalExposedSideSum f F T ρ := by
      exact
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowMajorDoubleSum_eq_exposedSideSum
          f F hT_nonneg hρ hclosed hbottom htop hbottomHole htopHole hsep
    _ =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T ρ) := by
      exact
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalExposedSideSum_eq_target
          f F T ρ

/-- Row-major vertical selected-cell box-coordinate side collapse. -/
theorem explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowMajorDoubleSum_core
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
    explicitFormulaRectangleRawHoleVerticalEndpointDataSideSum f F T ρ =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T ρ) := by
  calc
    explicitFormulaRectangleRawHoleVerticalEndpointDataSideSum f F T ρ =
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalExposedSideSum f F T ρ := by
      exact
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowMajorDoubleSum_eq_exposedSideSum
          f F hT_nonneg hρ hclosed hright hleft hrightHole hleftHole hsep
    _ =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T ρ) := by
      exact
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalExposedSideSum_eq_target
          f F T ρ

/-- Recursive horizontal selected box-coordinate row-sum side collapse. -/
theorem explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContributionSum_core
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
    explicitFormulaRectangleRawHoleHorizontalEndpointDataSideSum f F T ρ =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T ρ) := by
  exact
    explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowMajorDoubleSum_core
      f F hT_nonneg hρ hclosed hbottom htop hbottomHole htopHole hsep

/-- Recursive vertical selected box-coordinate row-sum side collapse. -/
theorem explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContributionSum_core
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
    explicitFormulaRectangleRawHoleVerticalEndpointDataSideSum f F T ρ =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T ρ) := by
  exact
    explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowMajorDoubleSum_core
      f F hT_nonneg hρ hclosed hright hleft hrightHole hleftHole hsep

/-- Pure box-coordinate horizontal side-collapse for the sorted selected grid. -/
theorem explicitFormulaRectangleSelectedBoxCoordinatesHorizontalSortedPairListsContribution_core
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
    explicitFormulaRectangleRawHoleHorizontalEndpointDataSideSum f F T ρ =
      (zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T) -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum
            f T ρ) := by
  exact
    explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContributionSum_core
      f F hT_nonneg hρ hclosed hbottom htop hbottomHole htopHole hsep

/-- Pure box-coordinate vertical side-collapse for the sorted selected grid. -/
theorem explicitFormulaRectangleSelectedBoxCoordinatesVerticalSortedPairListsContribution_core
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
    explicitFormulaRectangleRawHoleVerticalEndpointDataSideSum f F T ρ =
      (zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
        explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum
          f T ρ) -
        (zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I -
          explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum
            f T ρ) := by
  exact
    explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContributionSum_core
      f F hT_nonneg hρ hclosed hright hleft hrightHole hleftHole hsep
end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
