import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part20Parts.Part20_06

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
## Part20 07: RowColumnContributionDefinitions
-/

noncomputable def explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) : ℂ :=
  let row : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
        xpair ypairs)
  explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f row -
    explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f row

/-- Vertical contribution of one fixed horizontal adjacent-pair row against a chosen
vertical adjacent-pair source list. -/
noncomputable def explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) : ℂ :=
  let row : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
        xpair ypairs)
  explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f row -
    explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f row

/-- Recursive horizontal row-contribution sum over a horizontal adjacent-pair source
list. -/
noncomputable def explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) : ℂ :=
  match xpairs with
  | [] => 0
  | xpair :: rest =>
      explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
        f xpair ypairs +
        explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum
          f rest ypairs

/-- Recursive vertical row-contribution sum over a horizontal adjacent-pair source list. -/
noncomputable def explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) : ℂ :=
  match xpairs with
  | [] => 0
  | xpair :: rest =>
      explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution
        f xpair ypairs +
        explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum
          f rest ypairs

/-- Horizontal selected endpoint-data contribution is the recursive sum of its fixed-row
horizontal contributions. -/
theorem explicitFormulaRectangleSelectedEndpointDataHorizontalContribution_pairLists_eq_rowSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          xpairs ypairs)
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data =
      explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum
        f xpairs ypairs := by
  induction xpairs with
  | nil =>
      exact
        explicitFormulaRectangleSelectedEndpointDataHorizontalContribution_pairLists_nil
          f ypairs
  | cons xpair rest ih =>
      let firstRow : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
        explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
            xpair ypairs)
      let remaining : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
        explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
            rest ypairs)
      let whole : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
        explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
            (xpair :: rest) ypairs)
      have hsplit :
          explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f whole -
              explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f whole =
            (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow -
                explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f firstRow) +
              (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining -
                explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f remaining) :=
        explicitFormulaRectangleSelectedEndpointDataHorizontalContribution_pairLists_cons
          f xpair rest ypairs
      calc
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f whole -
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f whole =
            (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow -
                explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f firstRow) +
              (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining -
                explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f remaining) := by
          exact hsplit
        _ =
            explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
                f xpair ypairs +
              (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining -
                explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f remaining) := by
          rfl
        _ =
            explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
                f xpair ypairs +
              explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum
                f rest ypairs := by
          exact congrArg
            (fun z : ℂ =>
              explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
                f xpair ypairs + z)
            ih
        _ =
            explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum
              f (xpair :: rest) ypairs := by
          rfl

/-- Vertical selected endpoint-data contribution is the recursive sum of its fixed-row
vertical contributions. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalContribution_pairLists_eq_rowSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          xpairs ypairs)
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data =
      explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum
        f xpairs ypairs := by
  induction xpairs with
  | nil =>
      exact
        explicitFormulaRectangleSelectedEndpointDataVerticalContribution_pairLists_nil
          f ypairs
  | cons xpair rest ih =>
      let firstRow : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
        explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
            xpair ypairs)
      let remaining : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
        explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
            rest ypairs)
      let whole : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
        explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
            (xpair :: rest) ypairs)
      have hsplit :
          explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f whole -
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f whole =
            (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f firstRow -
                explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f firstRow) +
              (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f remaining -
                explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f remaining) :=
        explicitFormulaRectangleSelectedEndpointDataVerticalContribution_pairLists_cons
          f xpair rest ypairs
      calc
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f whole -
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f whole =
            (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f firstRow -
                explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f firstRow) +
              (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f remaining -
                explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f remaining) := by
          exact hsplit
        _ =
            explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution
                f xpair ypairs +
              (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f remaining -
                explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f remaining) := by
          rfl
        _ =
            explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution
                f xpair ypairs +
              explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum
                f rest ypairs := by
          exact congrArg
            (fun z : ℂ =>
              explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution
                f xpair ypairs + z)
            ih
        _ =
            explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum
              f (xpair :: rest) ypairs := by
          rfl

/-- Selected adjacent-pair cells over a fixed vertical adjacent-pair, scanning a horizontal
adjacent-pair source list.  This is the column-oriented view needed for vertical
edge cancellation. -/
noncomputable def explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedY
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε) :
    List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε) :=
  match xpairs with
  | [] => []
  | xpair :: rest =>
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        ({ xpair := xpair, ypair := ypair, homit := homit } :
          ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε) ::
          explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedY rest ypair
      else
        explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedY rest ypair

/-- Right vertical coordinate labels selected from one fixed vertical adjacent-pair
column, with the same coordinate-omission filter as the selected cell list. -/
def explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedY
    {F : ExplicitFormulaContourFamily} {T ε : ℝ} :
    List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) →
      ExplicitFormulaRectangleYAdjacentEndpointPair T ε →
        List ExplicitFormulaRectangleVerticalEndpointDataEdge
  | [], _ypair => []
  | xpair :: rest, ypair =>
      if _homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        ((ypair.y₀, ypair.y₁), xpair.x₁) ::
          explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedY rest ypair
      else
        explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedY rest ypair

/-- Left vertical coordinate labels selected from one fixed vertical adjacent-pair
column, with the same coordinate-omission filter as the selected cell list. -/
def explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedY
    {F : ExplicitFormulaContourFamily} {T ε : ℝ} :
    List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) →
      ExplicitFormulaRectangleYAdjacentEndpointPair T ε →
        List ExplicitFormulaRectangleVerticalEndpointDataEdge
  | [], _ypair => []
  | xpair :: rest, ypair =>
      if _homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        ((ypair.y₀, ypair.y₁), xpair.x₀) ::
          explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedY rest ypair
      else
        explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedY rest ypair

/-- Selected right coordinate labels over a fixed vertical span are an ordinary filtered
recursive sum. -/
theorem explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedY_integralSum_eq_listSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε) :
    ∀ xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε),
      explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum f
          (explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedY xpairs ypair) =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
            if _homit :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁), xpair.x₁)
            else
              0)
          xpairs
  | [] => by
      rfl
  | xpair :: rest => by
      by_cases homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair
      · exact congrArg
          (fun z : ℂ =>
            explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
              f ((ypair.y₀, ypair.y₁), xpair.x₁) + z)
          (explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedY_integralSum_eq_listSum
            f ypair rest)
      · calc
          explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum f
              (explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedY
                (xpair :: rest) ypair) =
              explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum f
                (explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedY rest ypair) := by
            rfl
          _ =
              explicitFormulaRectangleListSum
                (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
                  if _homit :
                      explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission
                        xpair ypair then
                    explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
                      f ((ypair.y₀, ypair.y₁), xpair.x₁)
                  else
                    0)
                rest := by
            exact
              explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedY_integralSum_eq_listSum
                f ypair rest
          _ =
              0 +
                explicitFormulaRectangleListSum
                  (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
                    if _homit :
                        explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission
                          xpair ypair then
                      explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral
                        f ((ypair.y₀, ypair.y₁), xpair.x₁)
                    else
                      0)
                  rest := by
            exact (zero_add _).symm

/-- Selected left coordinate labels over a fixed vertical span are an ordinary filtered
recursive sum. -/
theorem explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedY_integralSum_eq_listSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε) :
    ∀ xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε),
      explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f
          (explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedY xpairs ypair) =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
            if _homit :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
                f ((ypair.y₀, ypair.y₁), xpair.x₀)
            else
              0)
          xpairs
  | [] => by
      rfl
  | xpair :: rest => by
      by_cases homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair
      · exact congrArg
          (fun z : ℂ =>
            explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
              f ((ypair.y₀, ypair.y₁), xpair.x₀) + z)
          (explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedY_integralSum_eq_listSum
            f ypair rest)
      · calc
          explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f
              (explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedY
                (xpair :: rest) ypair) =
              explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f
                (explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedY rest ypair) := by
            rfl
          _ =
              explicitFormulaRectangleListSum
                (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
                  if _homit :
                      explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission
                        xpair ypair then
                    explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
                      f ((ypair.y₀, ypair.y₁), xpair.x₀)
                  else
                    0)
                rest := by
            exact
              explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedY_integralSum_eq_listSum
                f ypair rest
          _ =
              0 +
                explicitFormulaRectangleListSum
                  (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
                    if _homit :
                        explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission
                          xpair ypair then
                      explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral
                        f ((ypair.y₀, ypair.y₁), xpair.x₀)
                    else
                      0)
                  rest := by
            exact (zero_add _).symm

/-- The selected endpoint-data list for one fixed vertical column has exactly the
selected right vertical coordinate labels. -/
theorem explicitFormulaRectangleSelectedEndpointDataFixedY_rightEdgeCoordinates
    {F : ExplicitFormulaContourFamily} {T ε : ℝ} :
    ∀ (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
      (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε),
      (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedY
          xpairs ypair)).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.rightEdgeCoordinates) =
        explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedY xpairs ypair
  | [], ypair => rfl
  | xpair :: rest, ypair =>
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        congrArg
          (fun edges : List ExplicitFormulaRectangleVerticalEndpointDataEdge =>
            ((ypair.y₀, ypair.y₁), xpair.x₁) :: edges)
          (explicitFormulaRectangleSelectedEndpointDataFixedY_rightEdgeCoordinates
            rest ypair)
      else
        explicitFormulaRectangleSelectedEndpointDataFixedY_rightEdgeCoordinates
          rest ypair

/-- The selected endpoint-data list for one fixed vertical column has exactly the
selected left vertical coordinate labels. -/
theorem explicitFormulaRectangleSelectedEndpointDataFixedY_leftEdgeCoordinates
    {F : ExplicitFormulaContourFamily} {T ε : ℝ} :
    ∀ (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
      (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε),
      (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedY
          xpairs ypair)).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.leftEdgeCoordinates) =
        explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedY xpairs ypair
  | [], ypair => rfl
  | xpair :: rest, ypair =>
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        congrArg
          (fun edges : List ExplicitFormulaRectangleVerticalEndpointDataEdge =>
            ((ypair.y₀, ypair.y₁), xpair.x₀) :: edges)
          (explicitFormulaRectangleSelectedEndpointDataFixedY_leftEdgeCoordinates
            rest ypair)
      else
        explicitFormulaRectangleSelectedEndpointDataFixedY_leftEdgeCoordinates
          rest ypair

/-- The explicit fixed-column right-edge scan is the right-edge sum of the selected
fixed-column endpoint-data list. -/
theorem explicitFormulaRectangleSelectedFixedY_rightScan_eq_endpointDataRightEdgeSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction) :
    ∀ (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
      (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε),
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
            if homit :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
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
                    ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)
            else
              0)
          xpairs =
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedY
              xpairs ypair))
  | [], ypair => rfl
  | xpair :: rest, ypair =>
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        calc
          explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
                if homit :
                    explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                  explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
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
                        ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)
                else
                  0)
              (xpair :: rest) =
            explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
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
                  ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) +
              explicitFormulaRectangleListSum
                (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
                  if homit :
                      explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                    explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
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
                          ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)
                  else
                    0)
                rest := by
            rfl
          _ =
            explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
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
                  ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) +
              explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
                (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                  (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedY
                    rest ypair)) := by
            exact congrArg
              (fun z : ℂ =>
                explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
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
                      ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) + z)
              (explicitFormulaRectangleSelectedFixedY_rightScan_eq_endpointDataRightEdgeSum
                f rest ypair)
          _ =
            explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
              (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedY
                  (xpair :: rest) ypair)) := by
            rfl
      else
        calc
          explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
                if homit :
                    explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                  explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
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
                        ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)
                else
                  0)
              (xpair :: rest) =
            0 +
              explicitFormulaRectangleListSum
                (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
                  if homit :
                      explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                    explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
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
                          ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)
                  else
                    0)
                rest := by
            rfl
          _ =
            explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
                if homit :
                    explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                  explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
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
                        ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)
                else
                  0)
              rest := by
            exact zero_add _
          _ =
            explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
              (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedY
                  rest ypair)) := by
            exact
              explicitFormulaRectangleSelectedFixedY_rightScan_eq_endpointDataRightEdgeSum
                f rest ypair
          _ =
            explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
              (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedY
                  (xpair :: rest) ypair)) := by
            rfl

/-- The explicit fixed-column left-edge scan is the left-edge sum of the selected
fixed-column endpoint-data list. -/
theorem explicitFormulaRectangleSelectedFixedY_leftScan_eq_endpointDataLeftEdgeSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction) :
    ∀ (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
      (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε),
      (let leftScan : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε → ℂ :=
        fun xpair =>
          if homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
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
                  ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)
          else
            0;
       explicitFormulaRectangleListSum leftScan xpairs) =
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedY
              xpairs ypair))
  | [], ypair => rfl
  | xpair :: rest, ypair =>
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        let head : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε :=
          { x₀ := xpair.x₀
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
            homit := homit }
        change
          explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f head +
              (let leftScan : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε → ℂ :=
                fun xpair =>
                  if homit :
                      explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                    explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
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
                          ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)
                  else
                    0;
               explicitFormulaRectangleListSum leftScan rest) =
            explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f head +
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
                (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                  (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedY
                    rest ypair))
        exact congrArg
          (fun z : ℂ =>
            explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f head + z)
          (explicitFormulaRectangleSelectedFixedY_leftScan_eq_endpointDataLeftEdgeSum
            f rest ypair)
      else
        change
          0 +
              (let leftScan : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε → ℂ :=
                fun xpair =>
                  if homit :
                      explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                    explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
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
                          ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)
                  else
                    0;
               explicitFormulaRectangleListSum leftScan rest) =
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
              (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedY
                  rest ypair))
        exact Eq.trans
          (zero_add
            ((let leftScan : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε → ℂ :=
              fun xpair =>
                if homit :
                    explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
                  explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
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
                        ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)
                else
                  0;
             explicitFormulaRectangleListSum leftScan rest)))
          (explicitFormulaRectangleSelectedFixedY_leftScan_eq_endpointDataLeftEdgeSum
            f rest ypair)

/-- The explicit fixed-column right-edge scan is the selected right coordinate-label
integral sum. -/
theorem explicitFormulaRectangleSelectedFixedY_rightScan_eq_coordinateIntegralSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε) :
    explicitFormulaRectangleListSum
        (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
          if homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
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
                  ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)
          else
            0)
        xpairs =
      explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum f
        (explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedY xpairs ypair) := by
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedY
        xpairs ypair)
  have hscan :
      explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
            if homit :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
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
                    ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)
            else
              0)
          xpairs =
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data :=
    explicitFormulaRectangleSelectedFixedY_rightScan_eq_endpointDataRightEdgeSum
      f xpairs ypair
  have hsum :
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data =
        explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum f
          (data.map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
              d.rightEdgeCoordinates)) :=
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum_eq_rightVerticalEdgeIntegralSum
      f data
  have hcoords :
      data.map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.rightEdgeCoordinates) =
        explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedY xpairs ypair :=
    explicitFormulaRectangleSelectedEndpointDataFixedY_rightEdgeCoordinates xpairs ypair
  exact Eq.trans hscan
    (Eq.trans hsum
      (congrArg
        (fun edges : List ExplicitFormulaRectangleVerticalEndpointDataEdge =>
          explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegralSum f edges)
        hcoords))

/-- The explicit fixed-column left-edge scan is the selected left coordinate-label
integral sum. -/
theorem explicitFormulaRectangleSelectedFixedY_leftScan_eq_coordinateIntegralSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε) :
    (let leftScan : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε → ℂ :=
      fun xpair =>
        if homit :
            explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
          explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
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
                ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)
        else
          0;
     explicitFormulaRectangleListSum leftScan xpairs) =
      explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f
        (explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedY xpairs ypair) := by
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedY
        xpairs ypair)
  have hscan :
      (let leftScan : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε → ℂ :=
        fun xpair =>
          if homit :
              explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
            explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
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
                  ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)
          else
            0;
       explicitFormulaRectangleListSum leftScan xpairs) =
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data :=
    explicitFormulaRectangleSelectedFixedY_leftScan_eq_endpointDataLeftEdgeSum
      f xpairs ypair
  have hsum :
      explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data =
        explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f
          (data.map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
              d.leftEdgeCoordinates)) :=
    explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum_eq_leftVerticalEdgeIntegralSum
      f data
  have hcoords :
      data.map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.leftEdgeCoordinates) =
        explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedY xpairs ypair :=
    explicitFormulaRectangleSelectedEndpointDataFixedY_leftEdgeCoordinates xpairs ypair
  exact Eq.trans hscan
    (Eq.trans hsum
      (congrArg
        (fun edges : List ExplicitFormulaRectangleVerticalEndpointDataEdge =>
          explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegralSum f edges)
        hcoords))

/-- Endpoint-data vertical grouped contribution for one selected fixed column follows the
coordinate-omission filter at the head horizontal adjacent pair. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalContribution_fixedY_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (rest : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε) :
    let column : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedY
          (xpair :: rest) ypair)
    let tail : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedY
          rest ypair)
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f column -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f column =
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        (explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
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
              ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) -
          explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
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
                ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)) +
          (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail -
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail)
      else
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail := by
  if homit :
      explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
    let column : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedY
          (xpair :: rest) ypair)
    let tail : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedY
          rest ypair)
    let head : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε :=
      { x₀ := xpair.x₀
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
        homit := homit }
    change
      (explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f head +
          explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail) -
        (explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f head +
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail) =
        (explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f head -
          explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f head) +
          (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail -
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail)
    exact
      explicitFormulaRectangleBoxVerticalContribution_consAlgebra
        (explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f head)
        (explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f head)
        (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f tail)
        (explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f tail)
  else
    rfl

/-- Endpoint-data vertical grouped contribution for one selected fixed column is zero
over an empty horizontal-pair source list. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalContribution_fixedY_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε) :
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedY
              ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) ypair)) -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedY
              ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) ypair)) =
      0 := by
  rfl

/-- Vertical contribution of one fixed vertical adjacent-pair column against a chosen
horizontal adjacent-pair source list. -/
noncomputable def explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε) : ℂ :=
  let column : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedY
        xpairs ypair)
  explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f column -
    explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f column

/-- Recursive vertical column-contribution sum over a vertical adjacent-pair source
list. -/
noncomputable def explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) : ℂ :=
  match ypairs with
  | [] => 0
  | ypair :: rest =>
      explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
        f xpairs ypair +
        explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum
          f xpairs rest

/-- Fixed-column vertical contribution over a cons horizontal adjacent-pair source list
splits according to the selected head cell and the remaining column. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (rest : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε) :
    explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
        f (xpair :: rest) ypair =
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        (explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
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
              ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) -
          explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
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
                ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)) +
          explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
            f rest ypair
      else
        explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
          f rest ypair := by
  exact
    explicitFormulaRectangleSelectedEndpointDataVerticalContribution_fixedY_cons
      f xpair rest ypair

/-- Fixed-column vertical contribution over an empty horizontal adjacent-pair source list
is zero. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε) :
    explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
        (F := F) f
        ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
        ypair =
      0 :=
  explicitFormulaRectangleSelectedEndpointDataVerticalContribution_fixedY_nil f ypair

/-- Recursive fixed-column contribution sum over a cons vertical adjacent-pair source
list unfolds to the head column plus the remaining columns. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum
        f xpairs (ypair :: rest) =
      explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
        f xpairs ypair +
        explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum
          f xpairs rest := by
  rfl

/-- Recursive fixed-column contribution sum over an empty vertical adjacent-pair source
list is zero. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) :
    explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum
        (F := F) (T := T) (ε := ε)
        f xpairs ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) =
      0 := by
  rfl

/-- The selected vertical contribution of a single crossed adjacent-pair cell.  If the
cell is omitted by the raw singular coordinate filter, the contribution is zero; if it is
selected, it is the right-minus-left contribution of that endpoint datum. -/
noncomputable def explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε) : ℂ :=
  if homit :
      explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
    explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
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
          ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) -
      explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
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
            ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)
  else
    0

/-- Recursive sum of a function over a list.  This local owner-level spelling avoids
changing the surrounding finite-grid code to a different list-sum API. -/
noncomputable def explicitFormulaRectangleListSum {α : Type} (g : α → ℂ) :
    List α → ℂ
  | [] => 0
  | x :: xs => g x + explicitFormulaRectangleListSum g xs

/-- Recursive row-major double sum over two finite lists. -/
noncomputable def explicitFormulaRectangleRowMajorDoubleSum
    {α β : Type} (g : α → β → ℂ) :
    List α → List β → ℂ
  | [], _ => 0
  | x :: xs, ys =>
      explicitFormulaRectangleListSum (fun y : β => g x y) ys +
        explicitFormulaRectangleRowMajorDoubleSum g xs ys

/-- Recursive column-major double sum over two finite lists. -/
noncomputable def explicitFormulaRectangleColumnMajorDoubleSum
    {α β : Type} (g : α → β → ℂ)
    (xs : List α) : List β → ℂ
  | [] => 0
  | y :: ys =>
      explicitFormulaRectangleListSum (fun x : α => g x y) xs +
        explicitFormulaRectangleColumnMajorDoubleSum g xs ys

/-- Appending a recursive list sum splits into the two recursive sums. -/
theorem explicitFormulaRectangleListSum_append
    {α : Type} (g : α → ℂ) :
    ∀ xs ys : List α,
      explicitFormulaRectangleListSum g (xs ++ ys) =
        explicitFormulaRectangleListSum g xs +
          explicitFormulaRectangleListSum g ys
  | [], ys => by
      calc
        explicitFormulaRectangleListSum g ([] ++ ys) =
            explicitFormulaRectangleListSum g ys := by
          rfl
        _ =
            0 + explicitFormulaRectangleListSum g ys := by
          exact (zero_add (explicitFormulaRectangleListSum g ys)).symm
        _ =
            explicitFormulaRectangleListSum g [] +
              explicitFormulaRectangleListSum g ys := by
          rfl
  | x :: xs, ys => by
      have ih :
          explicitFormulaRectangleListSum g (xs ++ ys) =
            explicitFormulaRectangleListSum g xs +
              explicitFormulaRectangleListSum g ys :=
        explicitFormulaRectangleListSum_append g xs ys
      calc
        explicitFormulaRectangleListSum g ((x :: xs) ++ ys) =
            g x + explicitFormulaRectangleListSum g (xs ++ ys) := by
          rfl
        _ =
            g x +
              (explicitFormulaRectangleListSum g xs +
                explicitFormulaRectangleListSum g ys) := by
          exact congrArg (fun z : ℂ => g x + z) ih
        _ =
            (g x + explicitFormulaRectangleListSum g xs) +
              explicitFormulaRectangleListSum g ys := by
          exact (add_assoc
            (g x)
            (explicitFormulaRectangleListSum g xs)
            (explicitFormulaRectangleListSum g ys)).symm
        _ =
            explicitFormulaRectangleListSum g (x :: xs) +
              explicitFormulaRectangleListSum g ys := by
          rfl

/-- The local recursive list sum is the ordinary additive list sum after mapping the
summand. -/
theorem explicitFormulaRectangleListSum_eq_map_sum
    {α : Type} (g : α → ℂ) :
    ∀ xs : List α,
      explicitFormulaRectangleListSum g xs = (xs.map g).sum
  | [] => by
      rfl
  | x :: xs => by
      have ih :
          explicitFormulaRectangleListSum g xs = (xs.map g).sum :=
        explicitFormulaRectangleListSum_eq_map_sum g xs
      calc
        explicitFormulaRectangleListSum g (x :: xs) =
            g x + explicitFormulaRectangleListSum g xs := by
          rfl
        _ = g x + (xs.map g).sum := by
          exact congrArg (fun z : ℂ => g x + z) ih
        _ = ((x :: xs).map g).sum := by
          rfl

/-- The local recursive list sum over a `List.ofFn` is the corresponding finite sum over
the finite index type. -/
theorem explicitFormulaRectangleListSum_ofFn
    {α : Type} {n : ℕ} (x : Fin n → α) (g : α → ℂ) :
    explicitFormulaRectangleListSum g (List.ofFn x) =
      ∑ i : Fin n, g (x i) := by
  calc
    explicitFormulaRectangleListSum g (List.ofFn x) =
        ((List.ofFn x).map g).sum := by
      exact explicitFormulaRectangleListSum_eq_map_sum g (List.ofFn x)
    _ = (List.ofFn (fun i : Fin n => g (x i))).sum := by
      exact congrArg List.sum (List.map_ofFn x g)
    _ = ∑ i : Fin n, g (x i) := by
      exact Fin.sum_ofFn (fun i : Fin n => g (x i))

/-- Finite telescoping of forward consecutive endpoint differences. -/
theorem explicitFormulaRectangle_consecutiveForwardDifferences_sum_range
    (edge : ℕ → ℂ)
    (n : ℕ) :
    (∑ k in Finset.range n, (edge (k + 1) - edge k)) =
      edge n - edge 0 := by
  induction n with
  | zero =>
      calc
        (∑ k in Finset.range 0, (edge (k + 1) - edge k)) = 0 := by
          rfl
        _ = edge 0 - edge 0 := by
          exact (sub_self (edge 0)).symm
  | succ n ih =>
      have hrange :
          (∑ k in Finset.range (n + 1), (edge (k + 1) - edge k)) =
            (∑ k in Finset.range n, (edge (k + 1) - edge k)) +
              (edge (n + 1) - edge n) :=
        Finset.sum_range_succ
          (fun k : ℕ => edge (k + 1) - edge k)
          n
      calc
        (∑ k in Finset.range (n + 1), (edge (k + 1) - edge k)) =
            (∑ k in Finset.range n, (edge (k + 1) - edge k)) +
              (edge (n + 1) - edge n) := by
          exact hrange
        _ = (edge n - edge 0) + (edge (n + 1) - edge n) := by
          exact congrArg
            (fun z : ℂ => z + (edge (n + 1) - edge n))
            ih
        _ = (edge (n + 1) - edge n) + (edge n - edge 0) := by
          exact add_comm (edge n - edge 0) (edge (n + 1) - edge n)
        _ = edge (n + 1) - edge 0 := by
          exact finiteRectangleSubdivisionSharedHorizontalEdges_cancel
            (edge (n + 1)) (edge n) (edge 0)

/-- Finite telescoping of backward consecutive endpoint differences. -/
theorem explicitFormulaRectangle_consecutiveBackwardDifferences_sum_range
    (edge : ℕ → ℂ)
    (n : ℕ) :
    (∑ k in Finset.range n, (edge k - edge (k + 1))) =
      edge 0 - edge n :=
  finiteRectangleSubdivisionHorizontalEdgeDifferences_sum_range edge n

/-- Recursive `List.ofFn` sums telescope forward consecutive endpoint differences. -/
theorem explicitFormulaRectangleListSum_ofFn_consecutiveForwardDifferences
    {n : ℕ} (edge : ℕ → ℂ) :
    explicitFormulaRectangleListSum
        (fun i : Fin n => edge (i.1 + 1) - edge i.1)
        (List.ofFn (fun i : Fin n => i)) =
      edge n - edge 0 := by
  calc
    explicitFormulaRectangleListSum
        (fun i : Fin n => edge (i.1 + 1) - edge i.1)
        (List.ofFn (fun i : Fin n => i)) =
        ∑ i : Fin n, edge (i.1 + 1) - edge i.1 := by
      exact explicitFormulaRectangleListSum_ofFn
        (fun i : Fin n => i)
        (fun i : Fin n => edge (i.1 + 1) - edge i.1)
    _ =
        ∑ k in Finset.range n, edge (k + 1) - edge k := by
      exact Fin.sum_univ_eq_sum_range
        (fun k : ℕ => edge (k + 1) - edge k)
    _ = edge n - edge 0 := by
      exact explicitFormulaRectangle_consecutiveForwardDifferences_sum_range edge n

/-- Recursive `List.ofFn` sums telescope backward consecutive endpoint differences. -/
theorem explicitFormulaRectangleListSum_ofFn_consecutiveBackwardDifferences
    {n : ℕ} (edge : ℕ → ℂ) :
    explicitFormulaRectangleListSum
        (fun i : Fin n => edge i.1 - edge (i.1 + 1))
        (List.ofFn (fun i : Fin n => i)) =
      edge 0 - edge n := by
  calc
    explicitFormulaRectangleListSum
        (fun i : Fin n => edge i.1 - edge (i.1 + 1))
        (List.ofFn (fun i : Fin n => i)) =
        ∑ i : Fin n, edge i.1 - edge (i.1 + 1) := by
      exact explicitFormulaRectangleListSum_ofFn
        (fun i : Fin n => i)
        (fun i : Fin n => edge i.1 - edge (i.1 + 1))
    _ =
        ∑ k in Finset.range n, edge k - edge (k + 1) := by
      exact Fin.sum_univ_eq_sum_range
        (fun k : ℕ => edge k - edge (k + 1))
    _ = edge 0 - edge n := by
      exact explicitFormulaRectangle_consecutiveBackwardDifferences_sum_range edge n

/-- Recursive `List.ofFn` sums telescope forward consecutive endpoint differences after
a fixed index shift. -/
theorem explicitFormulaRectangleListSum_ofFn_consecutiveForwardDifferences_shift
    {n : ℕ} (edge : ℕ → ℂ) (lo : ℕ) :
    explicitFormulaRectangleListSum
        (fun i : Fin n => edge (lo + (i.1 + 1)) - edge (lo + i.1))
        (List.ofFn (fun i : Fin n => i)) =
      edge (lo + n) - edge lo := by
  let shifted : ℕ → ℂ := fun k => edge (lo + k)
  have hbase :
      explicitFormulaRectangleListSum
          (fun i : Fin n => shifted (i.1 + 1) - shifted i.1)
          (List.ofFn (fun i : Fin n => i)) =
        shifted n - shifted 0 :=
    explicitFormulaRectangleListSum_ofFn_consecutiveForwardDifferences shifted
  have hpoint :
      (fun i : Fin n => edge (lo + (i.1 + 1)) - edge (lo + i.1)) =
        (fun i : Fin n => shifted (i.1 + 1) - shifted i.1) := by
    exact funext
      (fun i =>
        congrArg₂ HSub.hSub
          (congrArg edge (Nat.add_assoc lo i.1 1).symm)
          rfl)
  calc
    explicitFormulaRectangleListSum
        (fun i : Fin n => edge (lo + (i.1 + 1)) - edge (lo + i.1))
        (List.ofFn (fun i : Fin n => i)) =
        explicitFormulaRectangleListSum
          (fun i : Fin n => shifted (i.1 + 1) - shifted i.1)
          (List.ofFn (fun i : Fin n => i)) := by
      exact congrArg
        (fun g : Fin n → ℂ =>
          explicitFormulaRectangleListSum g (List.ofFn (fun i : Fin n => i)))
        hpoint
    _ = shifted n - shifted 0 := by
      exact hbase
    _ = edge (lo + n) - edge lo := by
      rfl

/-- Recursive `List.ofFn` sums telescope backward consecutive endpoint differences after
a fixed index shift. -/
theorem explicitFormulaRectangleListSum_ofFn_consecutiveBackwardDifferences_shift
    {n : ℕ} (edge : ℕ → ℂ) (lo : ℕ) :
    explicitFormulaRectangleListSum
        (fun i : Fin n => edge (lo + i.1) - edge (lo + (i.1 + 1)))
        (List.ofFn (fun i : Fin n => i)) =
      edge lo - edge (lo + n) := by
  let shifted : ℕ → ℂ := fun k => edge (lo + k)
  have hbase :
      explicitFormulaRectangleListSum
          (fun i : Fin n => shifted i.1 - shifted (i.1 + 1))
          (List.ofFn (fun i : Fin n => i)) =
        shifted 0 - shifted n :=
    explicitFormulaRectangleListSum_ofFn_consecutiveBackwardDifferences shifted
  have hpoint :
      (fun i : Fin n => edge (lo + i.1) - edge (lo + (i.1 + 1))) =
        (fun i : Fin n => shifted i.1 - shifted (i.1 + 1)) := by
    exact funext
      (fun i =>
        congrArg₂ HSub.hSub
          rfl
          (congrArg edge (Nat.add_assoc lo i.1 1).symm))
  calc
    explicitFormulaRectangleListSum
        (fun i : Fin n => edge (lo + i.1) - edge (lo + (i.1 + 1)))
        (List.ofFn (fun i : Fin n => i)) =
        explicitFormulaRectangleListSum
          (fun i : Fin n => shifted i.1 - shifted (i.1 + 1))
          (List.ofFn (fun i : Fin n => i)) := by
      exact congrArg
        (fun g : Fin n → ℂ =>
          explicitFormulaRectangleListSum g (List.ofFn (fun i : Fin n => i)))
        hpoint
    _ = shifted 0 - shifted n := by
      exact hbase
    _ = edge lo - edge (lo + n) := by
      rfl

/-- Finite reindexing for a contiguous block of indices inside a finite index type.
This is the remaining purely finite-combinatorial sink behind the raw-hole subspan
classification: all indices outside the block contribute zero, and indices inside the
block are reindexed by their offset from `lo`. -/
theorem explicitFormulaRectangleFinSum_contiguousBlock_ite_eq_shifted
    {n span : ℕ} (lo : ℕ)
    (P : Fin n → Prop) [DecidablePred P]
    (g : Fin n → ℂ) (gShift : Fin span → ℂ)
    (hvalid : ∀ i : Fin span, lo + i.1 < n)
    (hforward : ∀ i : Fin span, P ⟨lo + i.1, hvalid i⟩)
    (hoffset :
      ∀ j : Fin n,
        P j →
          j.1 - lo < span ∧ lo + (j.1 - lo) = j.1)
    (hshift :
      ∀ i : Fin span,
        g ⟨lo + i.1, hvalid i⟩ = gShift i) :
    (∑ j : Fin n, if _h : P j then g j else 0) =
      ∑ i : Fin span, gShift i := by
  have hfilter :
      (∑ j : Fin n, if P j then g j else 0) =
        ∑ j in (Finset.univ.filter P), g j := by
    calc
      (∑ j : Fin n, if P j then g j else 0) =
          ∑ j in (Finset.univ : Finset (Fin n)), if P j then g j else 0 := by
        rfl
      _ =
          (∑ j in (Finset.univ : Finset (Fin n)).filter P, g j) +
            ∑ j in (Finset.univ : Finset (Fin n)).filter (fun j => ¬ P j), 0 := by
        exact Finset.sum_ite g (fun _ : Fin n => (0 : ℂ))
      _ =
          (∑ j in (Finset.univ : Finset (Fin n)).filter P, g j) + 0 := by
        exact
          congrArg
            (fun z : ℂ =>
              (∑ j in (Finset.univ : Finset (Fin n)).filter P, g j) + z)
            (Finset.sum_const_zero :
              (∑ j in (Finset.univ : Finset (Fin n)).filter
                  (fun j => ¬ P j), (0 : ℂ)) = 0)
      _ = ∑ j in (Finset.univ.filter P), g j := by
        exact add_zero _
  have hindexed :
      (∑ i : Fin span, gShift i) =
        ∑ j in (Finset.univ.filter P), g j := by
    calc
      (∑ i : Fin span, gShift i) =
          ∑ i in (Finset.univ : Finset (Fin span)), gShift i := by
        rfl
      _ =
          ∑ j in (Finset.univ.filter P), g j := by
        exact
          Finset.sum_bij
            (fun i _hi => (⟨lo + i.1, hvalid i⟩ : Fin n))
            (fun i _hi => by
              exact Finset.mem_filter.mpr
                (And.intro (Finset.mem_univ _) (hforward i)))
            (fun i _hi k _hk heq => by
              exact Fin.ext
                (Nat.add_left_cancel
                  (show lo + i.1 = lo + k.1 from Fin.ext_iff.mp heq)))
            (fun j hj => by
              have hP : P j := (Finset.mem_filter.mp hj).2
              have hoff : j.1 - lo < span ∧ lo + (j.1 - lo) = j.1 :=
                hoffset j hP
              refine ⟨⟨j.1 - lo, hoff.1⟩, Finset.mem_univ _, ?_⟩
              exact Fin.ext hoff.2)
            (fun i _hi => by
              exact (hshift i).symm)
  exact Eq.trans hfilter hindexed.symm

/-- Recursive list sums of adjacent interval integrals over an indexed subdivision
assemble to the integral over the whole endpoint span. -/
theorem explicitFormulaRectangleListSum_ofFn_intervalIntegral_adjacent
    {n : ℕ} (a : ℕ → ℝ) (φ : ℝ → ℂ)
    (hint : ∀ k : ℕ, k < n → IntervalIntegrable φ volume (a k) (a (k + 1))) :
    explicitFormulaRectangleListSum
        (fun i : Fin n => ∫ x : ℝ in a i.1..a (i.1 + 1), φ x)
        (List.ofFn (fun i : Fin n => i)) =
      ∫ x : ℝ in a 0..a n, φ x := by
  calc
    explicitFormulaRectangleListSum
        (fun i : Fin n => ∫ x : ℝ in a i.1..a (i.1 + 1), φ x)
        (List.ofFn (fun i : Fin n => i)) =
        ∑ i : Fin n, ∫ x : ℝ in a i.1..a (i.1 + 1), φ x := by
      exact
        explicitFormulaRectangleListSum_ofFn
          (fun i : Fin n => i)
          (fun i : Fin n => ∫ x : ℝ in a i.1..a (i.1 + 1), φ x)
    _ =
        ∑ k in Finset.range n, ∫ x : ℝ in a k..a (k + 1), φ x := by
      exact Fin.sum_univ_eq_sum_range
        (fun k : ℕ => ∫ x : ℝ in a k..a (k + 1), φ x)
    _ = ∫ x : ℝ in a 0..a n, φ x := by
      exact intervalIntegral.sum_integral_adjacent_intervals hint

/-- Recursive list sums of adjacent interval integrals over a shifted indexed
subdivision assemble to the integral over the shifted endpoint span. -/
theorem explicitFormulaRectangleListSum_ofFn_intervalIntegral_adjacent_shift
    {n : ℕ} (a : ℕ → ℝ) (φ : ℝ → ℂ) (lo : ℕ)
    (hint :
      ∀ k : ℕ, k < n →
        IntervalIntegrable φ volume
          (a (lo + k)) (a (lo + (k + 1)))) :
    explicitFormulaRectangleListSum
        (fun i : Fin n =>
          ∫ x : ℝ in a (lo + i.1)..a (lo + (i.1 + 1)), φ x)
        (List.ofFn (fun i : Fin n => i)) =
      ∫ x : ℝ in a (lo + 0)..a (lo + n), φ x := by
  let shifted : ℕ → ℝ := fun k : ℕ => a (lo + k)
  have hshift :
      ∀ k : ℕ, k < n →
        IntervalIntegrable φ volume
          (shifted k) (shifted (k + 1)) :=
    fun k hk => hint k hk
  exact
    explicitFormulaRectangleListSum_ofFn_intervalIntegral_adjacent
      shifted φ hshift

/-- Interval-integrability data needed to telescope a fixed vertical line over a finite
adjacent endpoint subdivision.  This is the analytic input for the vertical side
assembly lemmas; the finite geometry supplies the endpoint list and first/last endpoints. -/
def explicitFormulaRectangleVerticalAdjacentEndpointIntegrable
    (f : ZetaAdmissibleFunction) (x : ℝ) (a : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ k : ℕ, k < n →
    IntervalIntegrable
      (fun y : ℝ =>
        zetaCompletedExplicitFormulaContourIntegrand f ((x : ℂ) + y * Complex.I))
      volume (a k) (a (k + 1))

/-- Interval-integrability data needed to telescope a fixed horizontal line over a finite
adjacent endpoint subdivision. -/
def explicitFormulaRectangleHorizontalAdjacentEndpointIntegrable
    (f : ZetaAdmissibleFunction) (y : ℝ) (a : ℕ → ℝ) (n : ℕ) : Prop :=
  ∀ k : ℕ, k < n →
    IntervalIntegrable
      (fun x : ℝ =>
        zetaCompletedExplicitFormulaContourIntegrand f (x + (y : ℂ) * Complex.I))
      volume (a k) (a (k + 1))

/-- Natural-number indexing of the sorted vertical endpoint list, clamped at the outer
upper endpoint once the index exceeds the list.  The telescope lemmas use it only below
`length`, where it agrees with `List.get`. -/
noncomputable def explicitFormulaRectangleSortedYEndpointAt
    (T ρ : ℝ) (k : ℕ) : ℝ :=
  if hk : k < (explicitFormulaRectangleSortedYEndpoints T ρ).length then
    (explicitFormulaRectangleSortedYEndpoints T ρ).get ⟨k, hk⟩
  else
    T

/-- Natural-number indexing of the sorted horizontal endpoint list, clamped at the outer
right endpoint once the index exceeds the list. -/
noncomputable def explicitFormulaRectangleSortedXEndpointAt
    (F : ExplicitFormulaContourFamily) (T ρ : ℝ) (k : ℕ) : ℝ :=
  if hk : k < (explicitFormulaRectangleSortedXEndpoints F T ρ).length then
    (explicitFormulaRectangleSortedXEndpoints F T ρ).get ⟨k, hk⟩
  else
    F.c

/-- Below the sorted vertical endpoint-list length, the clamped indexer is ordinary
`List.get`. -/
theorem explicitFormulaRectangleSortedYEndpointAt_of_lt
    (T ρ : ℝ) {k : ℕ}
    (hk : k < (explicitFormulaRectangleSortedYEndpoints T ρ).length) :
    explicitFormulaRectangleSortedYEndpointAt T ρ k =
      (explicitFormulaRectangleSortedYEndpoints T ρ).get ⟨k, hk⟩ := by
  exact dif_pos hk

/-- Below the sorted horizontal endpoint-list length, the clamped indexer is ordinary
`List.get`. -/
theorem explicitFormulaRectangleSortedXEndpointAt_of_lt
    (F : ExplicitFormulaContourFamily) (T ρ : ℝ) {k : ℕ}
    (hk : k < (explicitFormulaRectangleSortedXEndpoints F T ρ).length) :
    explicitFormulaRectangleSortedXEndpointAt F T ρ k =
      (explicitFormulaRectangleSortedXEndpoints F T ρ).get ⟨k, hk⟩ := by
  exact dif_pos hk

/-- Index of the lower vertical endpoint of a raw square in the sorted vertical
subdivision. -/
noncomputable def explicitFormulaRectangleRawHoleYLowerIndex
    (T ρ : ℝ) (a : ℂ) : ℕ :=
  (explicitFormulaRectangleSortedYEndpoints T ρ).indexOf
    (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im

/-- Index of the upper vertical endpoint of a raw square in the sorted vertical
subdivision. -/
noncomputable def explicitFormulaRectangleRawHoleYUpperIndex
    (T ρ : ℝ) (a : ℂ) : ℕ :=
  (explicitFormulaRectangleSortedYEndpoints T ρ).indexOf
    (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im

/-- Index of the left horizontal endpoint of a raw square in the sorted horizontal
subdivision. -/
noncomputable def explicitFormulaRectangleRawHoleXLowerIndex
    (F : ExplicitFormulaContourFamily) (T ρ : ℝ) (a : ℂ) : ℕ :=
  (explicitFormulaRectangleSortedXEndpoints F T ρ).indexOf
    (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re

/-- Index of the right horizontal endpoint of a raw square in the sorted horizontal
subdivision. -/
noncomputable def explicitFormulaRectangleRawHoleXUpperIndex
    (F : ExplicitFormulaContourFamily) (T ρ : ℝ) (a : ℂ) : ℕ :=
  (explicitFormulaRectangleSortedXEndpoints F T ρ).indexOf
    (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re

/-- The clamped vertical endpoint function recovers the lower raw-hole endpoint at its
sorted index. -/
theorem explicitFormulaRectangleSortedYEndpointAt_rawHoleLowerIndex
    (T ρ : ℝ) {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    explicitFormulaRectangleSortedYEndpointAt T ρ
        (explicitFormulaRectangleRawHoleYLowerIndex T ρ a) =
      (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im := by
  let y : ℝ := (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im
  let ys : List ℝ := explicitFormulaRectangleSortedYEndpoints T ρ
  have hy_mem : y ∈ ys :=
    explicitFormulaRectangleSortedYEndpoints_mem_rawHoleBottom T ρ ha
  have hidx_lt : ys.indexOf y < ys.length :=
    List.indexOf_lt_length.mpr hy_mem
  calc
    explicitFormulaRectangleSortedYEndpointAt T ρ
        (explicitFormulaRectangleRawHoleYLowerIndex T ρ a) =
        ys.get ⟨ys.indexOf y, hidx_lt⟩ := by
      exact explicitFormulaRectangleSortedYEndpointAt_of_lt T ρ hidx_lt
    _ = y := by
      exact List.indexOf_get hidx_lt

/-- The clamped vertical endpoint function recovers the upper raw-hole endpoint at its
sorted index. -/
theorem explicitFormulaRectangleSortedYEndpointAt_rawHoleUpperIndex
    (T ρ : ℝ) {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    explicitFormulaRectangleSortedYEndpointAt T ρ
        (explicitFormulaRectangleRawHoleYUpperIndex T ρ a) =
      (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im := by
  let y : ℝ := (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im
  let ys : List ℝ := explicitFormulaRectangleSortedYEndpoints T ρ
  have hy_mem : y ∈ ys :=
    explicitFormulaRectangleSortedYEndpoints_mem_rawHoleTop T ρ ha
  have hidx_lt : ys.indexOf y < ys.length :=
    List.indexOf_lt_length.mpr hy_mem
  calc
    explicitFormulaRectangleSortedYEndpointAt T ρ
        (explicitFormulaRectangleRawHoleYUpperIndex T ρ a) =
        ys.get ⟨ys.indexOf y, hidx_lt⟩ := by
      exact explicitFormulaRectangleSortedYEndpointAt_of_lt T ρ hidx_lt
    _ = y := by
      exact List.indexOf_get hidx_lt

/-- The clamped horizontal endpoint function recovers the left raw-hole endpoint at its
sorted index. -/
theorem explicitFormulaRectangleSortedXEndpointAt_rawHoleLowerIndex
    (F : ExplicitFormulaContourFamily) (T ρ : ℝ) {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    explicitFormulaRectangleSortedXEndpointAt F T ρ
        (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a) =
      (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re := by
  let x : ℝ := (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re
  let xs : List ℝ := explicitFormulaRectangleSortedXEndpoints F T ρ
  have hx_mem : x ∈ xs :=
    explicitFormulaRectangleSortedXEndpoints_mem_rawHoleLeft F T ρ ha
  have hidx_lt : xs.indexOf x < xs.length :=
    List.indexOf_lt_length.mpr hx_mem
  calc
    explicitFormulaRectangleSortedXEndpointAt F T ρ
        (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a) =
        xs.get ⟨xs.indexOf x, hidx_lt⟩ := by
      exact explicitFormulaRectangleSortedXEndpointAt_of_lt F T ρ hidx_lt
    _ = x := by
      exact List.indexOf_get hidx_lt

/-- The clamped horizontal endpoint function recovers the right raw-hole endpoint at its
sorted index. -/
theorem explicitFormulaRectangleSortedXEndpointAt_rawHoleUpperIndex
    (F : ExplicitFormulaContourFamily) (T ρ : ℝ) {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    explicitFormulaRectangleSortedXEndpointAt F T ρ
        (explicitFormulaRectangleRawHoleXUpperIndex F T ρ a) =
      (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re := by
  let x : ℝ := (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re
  let xs : List ℝ := explicitFormulaRectangleSortedXEndpoints F T ρ
  have hx_mem : x ∈ xs :=
    explicitFormulaRectangleSortedXEndpoints_mem_rawHoleRight F T ρ ha
  have hidx_lt : xs.indexOf x < xs.length :=
    List.indexOf_lt_length.mpr hx_mem
  calc
    explicitFormulaRectangleSortedXEndpointAt F T ρ
        (explicitFormulaRectangleRawHoleXUpperIndex F T ρ a) =
        xs.get ⟨xs.indexOf x, hidx_lt⟩ := by
      exact explicitFormulaRectangleSortedXEndpointAt_of_lt F T ρ hidx_lt
    _ = x := by
      exact List.indexOf_get hidx_lt

/-- The lower raw-hole vertical endpoint occurs strictly before the upper raw-hole
vertical endpoint in the sorted vertical subdivision. -/
theorem explicitFormulaRectangleRawHoleYLowerIndex_lt_upperIndex
    (T : ℝ) {ρ : ℝ} (hρ : 0 < ρ) {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    explicitFormulaRectangleRawHoleYLowerIndex T ρ a <
      explicitFormulaRectangleRawHoleYUpperIndex T ρ a := by
  let ylo : ℝ := (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im
  let yhi : ℝ := (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im
  let ys : List ℝ := explicitFormulaRectangleSortedYEndpoints T ρ
  have hylo_mem : ylo ∈ ys :=
    explicitFormulaRectangleSortedYEndpoints_mem_rawHoleBottom T ρ ha
  have hyhi_mem : yhi ∈ ys :=
    explicitFormulaRectangleSortedYEndpoints_mem_rawHoleTop T ρ ha
  have hlo_lt_len : ys.indexOf ylo < ys.length :=
    List.indexOf_lt_length.mpr hylo_mem
  have hhi_lt_len : ys.indexOf yhi < ys.length :=
    List.indexOf_lt_length.mpr hyhi_mem
  have hcorner : ylo < yhi :=
    explicitFormulaRectangleRawInscribedSquareLowerCorner_im_lt_upperCorner_im hρ a
  exact
    lt_of_not_ge
      (fun hhi_le_lo :
        explicitFormulaRectangleRawHoleYUpperIndex T ρ a ≤
          explicitFormulaRectangleRawHoleYLowerIndex T ρ a =>
        let hget_le :
            ys.get ⟨ys.indexOf yhi, hhi_lt_len⟩ ≤
              ys.get ⟨ys.indexOf ylo, hlo_lt_len⟩ :=
          (explicitFormulaRectangleSortedYEndpoints_sorted_le T ρ).rel_get_of_le hhi_le_lo
        let hyhi_le_ylo : yhi ≤ ylo := by
          calc
            yhi = ys.get ⟨ys.indexOf yhi, hhi_lt_len⟩ := by
              exact (List.indexOf_get hhi_lt_len).symm
            _ ≤ ys.get ⟨ys.indexOf ylo, hlo_lt_len⟩ := by
              exact hget_le
            _ = ylo := by
              exact List.indexOf_get hlo_lt_len
        (not_lt_of_ge hyhi_le_ylo) hcorner)

/-- The left raw-hole horizontal endpoint occurs strictly before the right raw-hole
horizontal endpoint in the sorted horizontal subdivision. -/
theorem explicitFormulaRectangleRawHoleXLowerIndex_lt_upperIndex
    (F : ExplicitFormulaContourFamily) (T : ℝ) {ρ : ℝ} (hρ : 0 < ρ) {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    explicitFormulaRectangleRawHoleXLowerIndex F T ρ a <
      explicitFormulaRectangleRawHoleXUpperIndex F T ρ a := by
  let xlo : ℝ := (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re
  let xhi : ℝ := (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re
  let xs : List ℝ := explicitFormulaRectangleSortedXEndpoints F T ρ
  have hxlo_mem : xlo ∈ xs :=
    explicitFormulaRectangleSortedXEndpoints_mem_rawHoleLeft F T ρ ha
  have hxhi_mem : xhi ∈ xs :=
    explicitFormulaRectangleSortedXEndpoints_mem_rawHoleRight F T ρ ha
  have hlo_lt_len : xs.indexOf xlo < xs.length :=
    List.indexOf_lt_length.mpr hxlo_mem
  have hhi_lt_len : xs.indexOf xhi < xs.length :=
    List.indexOf_lt_length.mpr hxhi_mem
  have hcorner : xlo < xhi :=
    explicitFormulaRectangleRawInscribedSquareLowerCorner_re_lt_upperCorner_re hρ a
  exact
    lt_of_not_ge
      (fun hhi_le_lo :
        explicitFormulaRectangleRawHoleXUpperIndex F T ρ a ≤
          explicitFormulaRectangleRawHoleXLowerIndex F T ρ a =>
        let hget_le :
            xs.get ⟨xs.indexOf xhi, hhi_lt_len⟩ ≤
              xs.get ⟨xs.indexOf xlo, hlo_lt_len⟩ :=
          (explicitFormulaRectangleSortedXEndpoints_sorted_le F T ρ).rel_get_of_le hhi_le_lo
        let hxhi_le_xlo : xhi ≤ xlo := by
          calc
            xhi = xs.get ⟨xs.indexOf xhi, hhi_lt_len⟩ := by
              exact (List.indexOf_get hhi_lt_len).symm
            _ ≤ xs.get ⟨xs.indexOf xlo, hlo_lt_len⟩ := by
              exact hget_le
            _ = xlo := by
              exact List.indexOf_get hlo_lt_len
        (not_lt_of_ge hxhi_le_xlo) hcorner)

/-- Number of sorted vertical adjacent intervals spanning one raw square's vertical
side. -/
noncomputable def explicitFormulaRectangleRawHoleYSpanLength
    (T ρ : ℝ) (a : ℂ) : ℕ :=
  explicitFormulaRectangleRawHoleYUpperIndex T ρ a -
    explicitFormulaRectangleRawHoleYLowerIndex T ρ a

/-- Number of sorted horizontal adjacent intervals spanning one raw square's horizontal
side. -/
noncomputable def explicitFormulaRectangleRawHoleXSpanLength
    (F : ExplicitFormulaContourFamily) (T ρ : ℝ) (a : ℂ) : ℕ :=
  explicitFormulaRectangleRawHoleXUpperIndex F T ρ a -
    explicitFormulaRectangleRawHoleXLowerIndex F T ρ a

/-- Adding the vertical raw-hole span length to the lower index reaches the upper
index. -/
theorem explicitFormulaRectangleRawHoleYLowerIndex_add_spanLength
    (T : ℝ) {ρ : ℝ} (hρ : 0 < ρ) {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    explicitFormulaRectangleRawHoleYLowerIndex T ρ a +
        explicitFormulaRectangleRawHoleYSpanLength T ρ a =
      explicitFormulaRectangleRawHoleYUpperIndex T ρ a := by
  exact
    Nat.add_sub_of_le
      (Nat.le_of_lt
        (explicitFormulaRectangleRawHoleYLowerIndex_lt_upperIndex
          T hρ ha))

/-- Adding the horizontal raw-hole span length to the left index reaches the right
index. -/
theorem explicitFormulaRectangleRawHoleXLowerIndex_add_spanLength
    (F : ExplicitFormulaContourFamily) (T : ℝ) {ρ : ℝ} (hρ : 0 < ρ) {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    explicitFormulaRectangleRawHoleXLowerIndex F T ρ a +
        explicitFormulaRectangleRawHoleXSpanLength F T ρ a =
      explicitFormulaRectangleRawHoleXUpperIndex F T ρ a := by
  exact
    Nat.add_sub_of_le
      (Nat.le_of_lt
        (explicitFormulaRectangleRawHoleXLowerIndex_lt_upperIndex
          F T hρ ha))

/-- The clamped vertical endpoint function at the end of the raw-hole span is the upper
raw-hole endpoint. -/
theorem explicitFormulaRectangleSortedYEndpointAt_rawHoleLowerIndex_add_spanLength
    (T : ℝ) {ρ : ℝ} (hρ : 0 < ρ) {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    explicitFormulaRectangleSortedYEndpointAt T ρ
        (explicitFormulaRectangleRawHoleYLowerIndex T ρ a +
          explicitFormulaRectangleRawHoleYSpanLength T ρ a) =
      (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im := by
  calc
    explicitFormulaRectangleSortedYEndpointAt T ρ
        (explicitFormulaRectangleRawHoleYLowerIndex T ρ a +
          explicitFormulaRectangleRawHoleYSpanLength T ρ a) =
        explicitFormulaRectangleSortedYEndpointAt T ρ
          (explicitFormulaRectangleRawHoleYUpperIndex T ρ a) := by
      exact congrArg
        (fun k : ℕ => explicitFormulaRectangleSortedYEndpointAt T ρ k)
        (explicitFormulaRectangleRawHoleYLowerIndex_add_spanLength T hρ ha)
    _ = (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im := by
      exact explicitFormulaRectangleSortedYEndpointAt_rawHoleUpperIndex T ρ ha

/-- The clamped horizontal endpoint function at the end of the raw-hole span is the right
raw-hole endpoint. -/
theorem explicitFormulaRectangleSortedXEndpointAt_rawHoleLowerIndex_add_spanLength
    (F : ExplicitFormulaContourFamily) (T : ℝ) {ρ : ℝ} (hρ : 0 < ρ) {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    explicitFormulaRectangleSortedXEndpointAt F T ρ
        (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a +
          explicitFormulaRectangleRawHoleXSpanLength F T ρ a) =
      (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re := by
  calc
    explicitFormulaRectangleSortedXEndpointAt F T ρ
        (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a +
          explicitFormulaRectangleRawHoleXSpanLength F T ρ a) =
        explicitFormulaRectangleSortedXEndpointAt F T ρ
          (explicitFormulaRectangleRawHoleXUpperIndex F T ρ a) := by
      exact congrArg
        (fun k : ℕ => explicitFormulaRectangleSortedXEndpointAt F T ρ k)
        (explicitFormulaRectangleRawHoleXLowerIndex_add_spanLength F T hρ ha)
    _ = (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re := by
      exact explicitFormulaRectangleSortedXEndpointAt_rawHoleUpperIndex F T ρ ha

/-- Every shifted vertical raw-hole subspan index is a valid adjacent-pair index in the
sorted vertical endpoint list. -/
theorem explicitFormulaRectangleRawHoleYLowerIndex_add_lt_sortedLength_sub_one
    (T : ℝ) {ρ : ℝ} (hρ : 0 < ρ) {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (i : Fin (explicitFormulaRectangleRawHoleYSpanLength T ρ a)) :
    explicitFormulaRectangleRawHoleYLowerIndex T ρ a + i.1 <
      (explicitFormulaRectangleSortedYEndpoints T ρ).length - 1 := by
  let lo : ℕ := explicitFormulaRectangleRawHoleYLowerIndex T ρ a
  let hi : ℕ := explicitFormulaRectangleRawHoleYUpperIndex T ρ a
  let span : ℕ := explicitFormulaRectangleRawHoleYSpanLength T ρ a
  let yhi : ℝ := (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im
  let ys : List ℝ := explicitFormulaRectangleSortedYEndpoints T ρ
  have hyhi_mem : yhi ∈ ys :=
    explicitFormulaRectangleSortedYEndpoints_mem_rawHoleTop T ρ ha
  have hhi_lt_len : hi < ys.length :=
    List.indexOf_lt_length.mpr hyhi_mem
  have hsucc_le_span : i.1 + 1 ≤ span :=
    Nat.succ_le_of_lt i.2
  have hlo_add_succ_le_hi : lo + (i.1 + 1) ≤ hi := by
    calc
      lo + (i.1 + 1) ≤ lo + span := by
        exact Nat.add_le_add_left hsucc_le_span lo
      _ = hi := by
        exact explicitFormulaRectangleRawHoleYLowerIndex_add_spanLength T hρ ha
  have hlo_add_succ_lt_len : lo + (i.1 + 1) < ys.length :=
    lt_of_le_of_lt hlo_add_succ_le_hi hhi_lt_len
  exact
    (Nat.lt_sub_iff_add_lt
      (a := lo + i.1) (b := 1) (c := ys.length)).mpr
      (by
        calc
          lo + i.1 + 1 = lo + (i.1 + 1) := by
            exact Nat.add_assoc lo i.1 1
          _ < ys.length := by
            exact hlo_add_succ_lt_len)

/-- Every shifted horizontal raw-hole subspan index is a valid adjacent-pair index in
the sorted horizontal endpoint list. -/
theorem explicitFormulaRectangleRawHoleXLowerIndex_add_lt_sortedLength_sub_one
    (F : ExplicitFormulaContourFamily) (T : ℝ) {ρ : ℝ} (hρ : 0 < ρ) {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a)) :
    explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + i.1 <
      (explicitFormulaRectangleSortedXEndpoints F T ρ).length - 1 := by
  let lo : ℕ := explicitFormulaRectangleRawHoleXLowerIndex F T ρ a
  let hi : ℕ := explicitFormulaRectangleRawHoleXUpperIndex F T ρ a
  let span : ℕ := explicitFormulaRectangleRawHoleXSpanLength F T ρ a
  let xhi : ℝ := (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re
  let xs : List ℝ := explicitFormulaRectangleSortedXEndpoints F T ρ
  have hxhi_mem : xhi ∈ xs :=
    explicitFormulaRectangleSortedXEndpoints_mem_rawHoleRight F T ρ ha
  have hhi_lt_len : hi < xs.length :=
    List.indexOf_lt_length.mpr hxhi_mem
  have hsucc_le_span : i.1 + 1 ≤ span :=
    Nat.succ_le_of_lt i.2
  have hlo_add_succ_le_hi : lo + (i.1 + 1) ≤ hi := by
    calc
      lo + (i.1 + 1) ≤ lo + span := by
        exact Nat.add_le_add_left hsucc_le_span lo
      _ = hi := by
        exact explicitFormulaRectangleRawHoleXLowerIndex_add_spanLength F T hρ ha
  have hlo_add_succ_lt_len : lo + (i.1 + 1) < xs.length :=
    lt_of_le_of_lt hlo_add_succ_le_hi hhi_lt_len
  exact
    (Nat.lt_sub_iff_add_lt
      (a := lo + i.1) (b := 1) (c := xs.length)).mpr
      (by
        calc
          lo + i.1 + 1 = lo + (i.1 + 1) := by
            exact Nat.add_assoc lo i.1 1
          _ < xs.length := by
            exact hlo_add_succ_lt_len)

/-- Integrability required for telescoping a fixed vertical side across the sorted
vertical endpoint subdivision. -/
def explicitFormulaRectangleSortedYVerticalSideIntegrable
    (f : ZetaAdmissibleFunction) (T ρ x : ℝ) : Prop :=
  explicitFormulaRectangleVerticalAdjacentEndpointIntegrable
    f x (explicitFormulaRectangleSortedYEndpointAt T ρ)
      ((explicitFormulaRectangleSortedYEndpoints T ρ).length - 1)

/-- Integrability required for telescoping a fixed horizontal side across the sorted
horizontal endpoint subdivision. -/
def explicitFormulaRectangleSortedXHorizontalSideIntegrable
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ρ y : ℝ) :
    Prop :=
  explicitFormulaRectangleHorizontalAdjacentEndpointIntegrable
    f y (explicitFormulaRectangleSortedXEndpointAt F T ρ)
      ((explicitFormulaRectangleSortedXEndpoints F T ρ).length - 1)

/-- Full sorted vertical-side integrability restricts to the shifted raw-hole vertical
subrange. -/
theorem explicitFormulaRectangleRawHoleYShiftedIntegrable_of_sorted
    (f : ZetaAdmissibleFunction) (T : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    {a : ℂ} (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (x : ℝ)
    (hint : explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ x) :
    ∀ k : ℕ,
      k < explicitFormulaRectangleRawHoleYSpanLength T ρ a →
        IntervalIntegrable
          (fun y : ℝ =>
            zetaCompletedExplicitFormulaContourIntegrand f
              ((x : ℂ) + y * Complex.I))
          volume
          (explicitFormulaRectangleSortedYEndpointAt T ρ
            (explicitFormulaRectangleRawHoleYLowerIndex T ρ a + k))
          (explicitFormulaRectangleSortedYEndpointAt T ρ
            (explicitFormulaRectangleRawHoleYLowerIndex T ρ a + (k + 1))) := by
  intro k hk
  let lo : ℕ := explicitFormulaRectangleRawHoleYLowerIndex T ρ a
  let hi : ℕ := explicitFormulaRectangleRawHoleYUpperIndex T ρ a
  let span : ℕ := explicitFormulaRectangleRawHoleYSpanLength T ρ a
  let yhi : ℝ := (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im
  let ys : List ℝ := explicitFormulaRectangleSortedYEndpoints T ρ
  have hyhi_mem : yhi ∈ ys :=
    explicitFormulaRectangleSortedYEndpoints_mem_rawHoleTop T ρ ha
  have hhi_lt_len : hi < ys.length :=
    List.indexOf_lt_length.mpr hyhi_mem
  have hsucc_le_span : k + 1 ≤ span :=
    Nat.succ_le_of_lt hk
  have hlo_add_succ_le_hi : lo + (k + 1) ≤ hi := by
    calc
      lo + (k + 1) ≤ lo + span := by
        exact Nat.add_le_add_left hsucc_le_span lo
      _ = hi := by
        exact explicitFormulaRectangleRawHoleYLowerIndex_add_spanLength T hρ ha
  have hlo_add_succ_lt_len : lo + (k + 1) < ys.length :=
    lt_of_le_of_lt hlo_add_succ_le_hi hhi_lt_len
  have hindex :
      lo + k < (explicitFormulaRectangleSortedYEndpoints T ρ).length - 1 := by
    exact
      (Nat.lt_sub_iff_add_lt
        (a := lo + k) (b := 1)
        (c := (explicitFormulaRectangleSortedYEndpoints T ρ).length)).mpr
        (by
          calc
            lo + k + 1 = lo + (k + 1) := by
              exact Nat.add_assoc lo k 1
            _ < ys.length := by
              exact hlo_add_succ_lt_len)
  exact hint (lo + k) hindex

/-- Full sorted horizontal-side integrability restricts to the shifted raw-hole horizontal
subrange. -/
theorem explicitFormulaRectangleRawHoleXShiftedIntegrable_of_sorted
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (y : ℝ)
    (hint : explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ y) :
    ∀ k : ℕ,
      k < explicitFormulaRectangleRawHoleXSpanLength F T ρ a →
        IntervalIntegrable
          (fun x : ℝ =>
            zetaCompletedExplicitFormulaContourIntegrand f
              (x + (y : ℂ) * Complex.I))
          volume
          (explicitFormulaRectangleSortedXEndpointAt F T ρ
            (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + k))
          (explicitFormulaRectangleSortedXEndpointAt F T ρ
            (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + (k + 1))) := by
  intro k hk
  let lo : ℕ := explicitFormulaRectangleRawHoleXLowerIndex F T ρ a
  let hi : ℕ := explicitFormulaRectangleRawHoleXUpperIndex F T ρ a
  let span : ℕ := explicitFormulaRectangleRawHoleXSpanLength F T ρ a
  let xhi : ℝ := (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re
  let xs : List ℝ := explicitFormulaRectangleSortedXEndpoints F T ρ
  have hxhi_mem : xhi ∈ xs :=
    explicitFormulaRectangleSortedXEndpoints_mem_rawHoleRight F T ρ ha
  have hhi_lt_len : hi < xs.length :=
    List.indexOf_lt_length.mpr hxhi_mem
  have hsucc_le_span : k + 1 ≤ span :=
    Nat.succ_le_of_lt hk
  have hlo_add_succ_le_hi : lo + (k + 1) ≤ hi := by
    calc
      lo + (k + 1) ≤ lo + span := by
        exact Nat.add_le_add_left hsucc_le_span lo
      _ = hi := by
        exact explicitFormulaRectangleRawHoleXLowerIndex_add_spanLength F T hρ ha
  have hlo_add_succ_lt_len : lo + (k + 1) < xs.length :=
    lt_of_le_of_lt hlo_add_succ_le_hi hhi_lt_len
  have hindex :
      lo + k < (explicitFormulaRectangleSortedXEndpoints F T ρ).length - 1 := by
    exact
      (Nat.lt_sub_iff_add_lt
        (a := lo + k) (b := 1)
        (c := (explicitFormulaRectangleSortedXEndpoints F T ρ).length)).mpr
        (by
          calc
            lo + k + 1 = lo + (k + 1) := by
              exact Nat.add_assoc lo k 1
            _ < xs.length := by
              exact hlo_add_succ_lt_len)
  exact hint (lo + k) hindex

/-- The shifted vertical subrange over a raw-hole side telescopes to that raw-hole
vertical coordinate integral. -/
theorem explicitFormulaRectangleRawHoleYSubrangeVerticalIntegralSum_eq_coordinate
    (f : ZetaAdmissibleFunction) (T : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    {a : ℂ} (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (x : ℝ)
    (hint : explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ x) :
    explicitFormulaRectangleListSum
        (fun i : Fin (explicitFormulaRectangleRawHoleYSpanLength T ρ a) =>
          Complex.I •
            ∫ y : ℝ in
              explicitFormulaRectangleSortedYEndpointAt T ρ
                (explicitFormulaRectangleRawHoleYLowerIndex T ρ a + i.1)..
              explicitFormulaRectangleSortedYEndpointAt T ρ
                (explicitFormulaRectangleRawHoleYLowerIndex T ρ a + (i.1 + 1)),
              zetaCompletedExplicitFormulaContourIntegrand f
                ((x : ℂ) + y * Complex.I))
        (List.ofFn
          (fun i : Fin (explicitFormulaRectangleRawHoleYSpanLength T ρ a) => i)) =
      explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
        (((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im,
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im), x) := by
  let lo : ℕ := explicitFormulaRectangleRawHoleYLowerIndex T ρ a
  let span : ℕ := explicitFormulaRectangleRawHoleYSpanLength T ρ a
  have htelescope :
      explicitFormulaRectangleListSum
          (fun i : Fin span =>
            Complex.I •
              ∫ y : ℝ in
                explicitFormulaRectangleSortedYEndpointAt T ρ (lo + i.1)..
                explicitFormulaRectangleSortedYEndpointAt T ρ (lo + (i.1 + 1)),
                zetaCompletedExplicitFormulaContourIntegrand f
                  ((x : ℂ) + y * Complex.I))
          (List.ofFn (fun i : Fin span => i)) =
        Complex.I •
          ∫ y : ℝ in
            explicitFormulaRectangleSortedYEndpointAt T ρ (lo + 0)..
            explicitFormulaRectangleSortedYEndpointAt T ρ (lo + span),
            zetaCompletedExplicitFormulaContourIntegrand f
              ((x : ℂ) + y * Complex.I) :=
    explicitFormulaRectangleListSum_ofFn_verticalIntegral_adjacent_shift
      f x
      (explicitFormulaRectangleSortedYEndpointAt T ρ)
      lo
      (explicitFormulaRectangleRawHoleYShiftedIntegrable_of_sorted
        f T hρ ha x hint)
  have hlo :
      explicitFormulaRectangleSortedYEndpointAt T ρ (lo + 0) =
        (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im := by
    calc
      explicitFormulaRectangleSortedYEndpointAt T ρ (lo + 0) =
          explicitFormulaRectangleSortedYEndpointAt T ρ lo := by
        exact congrArg
          (fun k : ℕ => explicitFormulaRectangleSortedYEndpointAt T ρ k)
          (Nat.add_zero lo)
      _ = (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im := by
        exact explicitFormulaRectangleSortedYEndpointAt_rawHoleLowerIndex T ρ ha
  have hhi :
      explicitFormulaRectangleSortedYEndpointAt T ρ (lo + span) =
        (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im :=
    explicitFormulaRectangleSortedYEndpointAt_rawHoleLowerIndex_add_spanLength T hρ ha
  calc
    explicitFormulaRectangleListSum
        (fun i : Fin (explicitFormulaRectangleRawHoleYSpanLength T ρ a) =>
          Complex.I •
            ∫ y : ℝ in
              explicitFormulaRectangleSortedYEndpointAt T ρ
                (explicitFormulaRectangleRawHoleYLowerIndex T ρ a + i.1)..
              explicitFormulaRectangleSortedYEndpointAt T ρ
                (explicitFormulaRectangleRawHoleYLowerIndex T ρ a + (i.1 + 1)),
              zetaCompletedExplicitFormulaContourIntegrand f
                ((x : ℂ) + y * Complex.I))
        (List.ofFn
          (fun i : Fin (explicitFormulaRectangleRawHoleYSpanLength T ρ a) => i)) =
        Complex.I •
          ∫ y : ℝ in
            explicitFormulaRectangleSortedYEndpointAt T ρ (lo + 0)..
            explicitFormulaRectangleSortedYEndpointAt T ρ (lo + span),
            zetaCompletedExplicitFormulaContourIntegrand f
              ((x : ℂ) + y * Complex.I) := by
      exact htelescope
    _ =
        Complex.I •
          ∫ y : ℝ in
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im..
            explicitFormulaRectangleSortedYEndpointAt T ρ (lo + span),
            zetaCompletedExplicitFormulaContourIntegrand f
              ((x : ℂ) + y * Complex.I) := by
      exact congrArg
        (fun y0 : ℝ =>
          Complex.I •
            ∫ y : ℝ in y0..
              explicitFormulaRectangleSortedYEndpointAt T ρ (lo + span),
              zetaCompletedExplicitFormulaContourIntegrand f
                ((x : ℂ) + y * Complex.I))
        hlo
    _ =
        Complex.I •
          ∫ y : ℝ in
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im..
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im,
            zetaCompletedExplicitFormulaContourIntegrand f
              ((x : ℂ) + y * Complex.I) := by
      exact congrArg
        (fun y1 : ℝ =>
          Complex.I •
            ∫ y : ℝ in
              (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im..y1,
              zetaCompletedExplicitFormulaContourIntegrand f
                ((x : ℂ) + y * Complex.I))
        hhi
    _ =
        explicitFormulaRectangleRightVerticalEndpointDataEdgeIntegral f
          (((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im,
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im), x) := by
      rfl

/-- The shifted vertical subrange over a raw-hole side telescopes to that raw-hole
left-oriented vertical coordinate integral. -/
theorem explicitFormulaRectangleRawHoleYSubrangeLeftVerticalIntegralSum_eq_coordinate
    (f : ZetaAdmissibleFunction) (T : ℝ) {ρ : ℝ} (hρ : 0 < ρ)
    {a : ℂ} (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (x : ℝ)
    (hint : explicitFormulaRectangleSortedYVerticalSideIntegrable f T ρ x) :
    explicitFormulaRectangleListSum
        (fun i : Fin (explicitFormulaRectangleRawHoleYSpanLength T ρ a) =>
          explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
            ((explicitFormulaRectangleSortedYEndpointAt T ρ
                (explicitFormulaRectangleRawHoleYLowerIndex T ρ a + i.1),
              explicitFormulaRectangleSortedYEndpointAt T ρ
                (explicitFormulaRectangleRawHoleYLowerIndex T ρ a + (i.1 + 1))), x))
        (List.ofFn
          (fun i : Fin (explicitFormulaRectangleRawHoleYSpanLength T ρ a) => i)) =
      explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
        (((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im,
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im), x) := by
  let lo : ℕ := explicitFormulaRectangleRawHoleYLowerIndex T ρ a
  let span : ℕ := explicitFormulaRectangleRawHoleYSpanLength T ρ a
  have htelescope :
      explicitFormulaRectangleListSum
          (fun i : Fin span =>
            Complex.I •
              ∫ y : ℝ in
                explicitFormulaRectangleSortedYEndpointAt T ρ (lo + i.1)..
                explicitFormulaRectangleSortedYEndpointAt T ρ (lo + (i.1 + 1)),
                zetaCompletedExplicitFormulaContourIntegrand f
                  ((x : ℂ) + y * Complex.I))
          (List.ofFn (fun i : Fin span => i)) =
        Complex.I •
          ∫ y : ℝ in
            explicitFormulaRectangleSortedYEndpointAt T ρ (lo + 0)..
            explicitFormulaRectangleSortedYEndpointAt T ρ (lo + span),
            zetaCompletedExplicitFormulaContourIntegrand f
              ((x : ℂ) + y * Complex.I) :=
    explicitFormulaRectangleListSum_ofFn_verticalIntegral_adjacent_shift
      f x
      (explicitFormulaRectangleSortedYEndpointAt T ρ)
      lo
      (explicitFormulaRectangleRawHoleYShiftedIntegrable_of_sorted
        f T hρ ha x hint)
  have hlo :
      explicitFormulaRectangleSortedYEndpointAt T ρ (lo + 0) =
        (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im := by
    calc
      explicitFormulaRectangleSortedYEndpointAt T ρ (lo + 0) =
          explicitFormulaRectangleSortedYEndpointAt T ρ lo := by
        exact congrArg
          (fun k : ℕ => explicitFormulaRectangleSortedYEndpointAt T ρ k)
          (Nat.add_zero lo)
      _ = (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im := by
        exact explicitFormulaRectangleSortedYEndpointAt_rawHoleLowerIndex T ρ ha
  have hhi :
      explicitFormulaRectangleSortedYEndpointAt T ρ (lo + span) =
        (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im :=
    explicitFormulaRectangleSortedYEndpointAt_rawHoleLowerIndex_add_spanLength T hρ ha
  calc
    explicitFormulaRectangleListSum
        (fun i : Fin (explicitFormulaRectangleRawHoleYSpanLength T ρ a) =>
          explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
            ((explicitFormulaRectangleSortedYEndpointAt T ρ
                (explicitFormulaRectangleRawHoleYLowerIndex T ρ a + i.1),
              explicitFormulaRectangleSortedYEndpointAt T ρ
                (explicitFormulaRectangleRawHoleYLowerIndex T ρ a + (i.1 + 1))), x))
        (List.ofFn
          (fun i : Fin (explicitFormulaRectangleRawHoleYSpanLength T ρ a) => i)) =
        Complex.I •
          ∫ y : ℝ in
            explicitFormulaRectangleSortedYEndpointAt T ρ (lo + 0)..
            explicitFormulaRectangleSortedYEndpointAt T ρ (lo + span),
            zetaCompletedExplicitFormulaContourIntegrand f
              ((x : ℂ) + y * Complex.I) := by
      exact htelescope
    _ =
        Complex.I •
          ∫ y : ℝ in
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im..
            explicitFormulaRectangleSortedYEndpointAt T ρ (lo + span),
            zetaCompletedExplicitFormulaContourIntegrand f
              ((x : ℂ) + y * Complex.I) := by
      exact congrArg
        (fun y0 : ℝ =>
          Complex.I •
            ∫ y : ℝ in y0..
              explicitFormulaRectangleSortedYEndpointAt T ρ (lo + span),
              zetaCompletedExplicitFormulaContourIntegrand f
                ((x : ℂ) + y * Complex.I))
        hlo
    _ =
        Complex.I •
          ∫ y : ℝ in
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im..
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im,
            zetaCompletedExplicitFormulaContourIntegrand f
              ((x : ℂ) + y * Complex.I) := by
      exact congrArg
        (fun y1 : ℝ =>
          Complex.I •
            ∫ y : ℝ in
              (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im..y1,
              zetaCompletedExplicitFormulaContourIntegrand f
                ((x : ℂ) + y * Complex.I))
        hhi
    _ =
        explicitFormulaRectangleLeftVerticalEndpointDataEdgeIntegral f
          (((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).im,
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).im), x) := by
      rfl

/-- The shifted horizontal subrange over a raw-hole side telescopes to that raw-hole
horizontal coordinate integral. -/
theorem explicitFormulaRectangleRawHoleXSubrangeHorizontalIntegralSum_eq_coordinate
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (y : ℝ)
    (hint : explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ y) :
    explicitFormulaRectangleListSum
        (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) =>
          ∫ x : ℝ in
            explicitFormulaRectangleSortedXEndpointAt F T ρ
              (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + i.1)..
            explicitFormulaRectangleSortedXEndpointAt F T ρ
              (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + (i.1 + 1)),
            zetaCompletedExplicitFormulaContourIntegrand f
              (x + (y : ℂ) * Complex.I))
        (List.ofFn
          (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) => i)) =
      explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
        (((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re,
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re), y) := by
  let lo : ℕ := explicitFormulaRectangleRawHoleXLowerIndex F T ρ a
  let span : ℕ := explicitFormulaRectangleRawHoleXSpanLength F T ρ a
  have htelescope :
      explicitFormulaRectangleListSum
          (fun i : Fin span =>
            ∫ x : ℝ in
              explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + i.1)..
              explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + (i.1 + 1)),
              zetaCompletedExplicitFormulaContourIntegrand f
                (x + (y : ℂ) * Complex.I))
          (List.ofFn (fun i : Fin span => i)) =
        ∫ x : ℝ in
          explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + 0)..
          explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + span),
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + (y : ℂ) * Complex.I) :=
    explicitFormulaRectangleListSum_ofFn_horizontalIntegral_adjacent_shift
      f y
      (explicitFormulaRectangleSortedXEndpointAt F T ρ)
      lo
      (explicitFormulaRectangleRawHoleXShiftedIntegrable_of_sorted
        f F T hρ ha y hint)
  have hlo :
      explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + 0) =
        (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re := by
    calc
      explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + 0) =
          explicitFormulaRectangleSortedXEndpointAt F T ρ lo := by
        exact congrArg
          (fun k : ℕ => explicitFormulaRectangleSortedXEndpointAt F T ρ k)
          (Nat.add_zero lo)
      _ = (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re := by
        exact explicitFormulaRectangleSortedXEndpointAt_rawHoleLowerIndex F T ρ ha
  have hhi :
      explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + span) =
        (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re :=
    explicitFormulaRectangleSortedXEndpointAt_rawHoleLowerIndex_add_spanLength F T hρ ha
  calc
    explicitFormulaRectangleListSum
        (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) =>
          ∫ x : ℝ in
            explicitFormulaRectangleSortedXEndpointAt F T ρ
              (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + i.1)..
            explicitFormulaRectangleSortedXEndpointAt F T ρ
              (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + (i.1 + 1)),
            zetaCompletedExplicitFormulaContourIntegrand f
              (x + (y : ℂ) * Complex.I))
        (List.ofFn
          (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) => i)) =
        ∫ x : ℝ in
          explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + 0)..
          explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + span),
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + (y : ℂ) * Complex.I) := by
      exact htelescope
    _ =
        ∫ x : ℝ in
          (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re..
          explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + span),
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + (y : ℂ) * Complex.I) := by
      exact congrArg
        (fun x0 : ℝ =>
          ∫ x : ℝ in x0..
            explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + span),
            zetaCompletedExplicitFormulaContourIntegrand f
              (x + (y : ℂ) * Complex.I))
        hlo
    _ =
        ∫ x : ℝ in
          (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re..
          (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re,
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + (y : ℂ) * Complex.I) := by
      exact congrArg
        (fun x1 : ℝ =>
          ∫ x : ℝ in
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re..x1,
            zetaCompletedExplicitFormulaContourIntegrand f
              (x + (y : ℂ) * Complex.I))
        hhi
    _ =
        explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral f
          (((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re,
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re), y) := by
      rfl

/-- The shifted horizontal subrange over a raw-hole side telescopes to that raw-hole
top-oriented horizontal coordinate integral. -/
theorem explicitFormulaRectangleRawHoleXSubrangeTopHorizontalIntegralSum_eq_coordinate
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T : ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T)
    (y : ℝ)
    (hint : explicitFormulaRectangleSortedXHorizontalSideIntegrable f F T ρ y) :
    explicitFormulaRectangleListSum
        (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) =>
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
            ((explicitFormulaRectangleSortedXEndpointAt F T ρ
                (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + i.1),
              explicitFormulaRectangleSortedXEndpointAt F T ρ
                (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + (i.1 + 1))), y))
        (List.ofFn
          (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) => i)) =
      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
        (((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re,
            (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re), y) := by
  let lo : ℕ := explicitFormulaRectangleRawHoleXLowerIndex F T ρ a
  let span : ℕ := explicitFormulaRectangleRawHoleXSpanLength F T ρ a
  have htelescope :
      explicitFormulaRectangleListSum
          (fun i : Fin span =>
            ∫ x : ℝ in
              explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + i.1)..
              explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + (i.1 + 1)),
              zetaCompletedExplicitFormulaContourIntegrand f
                (x + (y : ℂ) * Complex.I))
          (List.ofFn (fun i : Fin span => i)) =
        ∫ x : ℝ in
          explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + 0)..
          explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + span),
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + (y : ℂ) * Complex.I) :=
    explicitFormulaRectangleListSum_ofFn_horizontalIntegral_adjacent_shift
      f y
      (explicitFormulaRectangleSortedXEndpointAt F T ρ)
      lo
      (explicitFormulaRectangleRawHoleXShiftedIntegrable_of_sorted
        f F T hρ ha y hint)
  have hlo :
      explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + 0) =
        (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re := by
    calc
      explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + 0) =
          explicitFormulaRectangleSortedXEndpointAt F T ρ lo := by
        exact congrArg
          (fun k : ℕ => explicitFormulaRectangleSortedXEndpointAt F T ρ k)
          (Nat.add_zero lo)
      _ = (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re := by
        exact explicitFormulaRectangleSortedXEndpointAt_rawHoleLowerIndex F T ρ ha
  have hhi :
      explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + span) =
        (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re :=
    explicitFormulaRectangleSortedXEndpointAt_rawHoleLowerIndex_add_spanLength F T hρ ha
  calc
    explicitFormulaRectangleListSum
        (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) =>
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
            ((explicitFormulaRectangleSortedXEndpointAt F T ρ
                (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + i.1),
              explicitFormulaRectangleSortedXEndpointAt F T ρ
                (explicitFormulaRectangleRawHoleXLowerIndex F T ρ a + (i.1 + 1))), y))
        (List.ofFn
          (fun i : Fin (explicitFormulaRectangleRawHoleXSpanLength F T ρ a) => i)) =
        ∫ x : ℝ in
          explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + 0)..
          explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + span),
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + (y : ℂ) * Complex.I) := by
      exact htelescope
    _ =
        ∫ x : ℝ in
          (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re..
          explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + span),
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + (y : ℂ) * Complex.I) := by
      exact congrArg
        (fun x0 : ℝ =>
          ∫ x : ℝ in x0..
            explicitFormulaRectangleSortedXEndpointAt F T ρ (lo + span),
            zetaCompletedExplicitFormulaContourIntegrand f
              (x + (y : ℂ) * Complex.I))
        hlo
    _ =
        ∫ x : ℝ in
          (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re..
          (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re,
          zetaCompletedExplicitFormulaContourIntegrand f
            (x + (y : ℂ) * Complex.I) := by
      exact congrArg
        (fun x1 : ℝ =>
          ∫ x : ℝ in
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re..x1,
            zetaCompletedExplicitFormulaContourIntegrand f
              (x + (y : ℂ) * Complex.I))
        hhi
    _ =
        explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral f
          (((explicitFormulaRectangleRawInscribedSquareLowerCorner ρ a).re,
              (explicitFormulaRectangleRawInscribedSquareUpperCorner ρ a).re), y) := by
      rfl

/-- A horizontal affine edge parameter is continuous on every closed interval. -/
theorem explicitFormulaRectangle_horizontalEdgeParameter_continuousOn
    (y a b : ℝ) :
    ContinuousOn (fun x : ℝ => (x : ℂ) + (y : ℂ) * Complex.I)
      (Set.uIcc a b) :=
  (continuous_ofReal.add continuous_const).continuousOn

/-- A vertical affine edge parameter is continuous on every closed interval. -/
theorem explicitFormulaRectangle_verticalEdgeParameter_continuousOn
    (x a b : ℝ) :
    ContinuousOn (fun y : ℝ => (x : ℂ) + (y : ℂ) * Complex.I)
      (Set.uIcc a b) :=
  (continuous_const.add (continuous_ofReal.mul continuous_const)).continuousOn

/-- Boundary continuity of the completed contour integrand gives interval-integrability
along any horizontal affine edge whose parameter image lies on the contour-family
boundary. -/
theorem explicitFormulaRectangle_horizontalEdgeContourIntegrand_intervalIntegrable_of_boundaryContinuousOn
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T y a b : ℝ}
    (hboundary :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        (explicitFormulaContourFamilyBoundary F T))
    (hmem :
      ∀ x : ℝ, x ∈ Set.uIcc a b →
        (x : ℂ) + (y : ℂ) * Complex.I ∈
          explicitFormulaContourFamilyBoundary F T) :
    IntervalIntegrable
      (fun x : ℝ =>
        zetaCompletedExplicitFormulaContourIntegrand f
          ((x : ℂ) + (y : ℂ) * Complex.I))
      volume a b :=
  (hboundary.comp_continuousOn
    (explicitFormulaRectangle_horizontalEdgeParameter_continuousOn y a b)
    hmem).intervalIntegrable

/-- Boundary continuity of the completed contour integrand gives interval-integrability
along any vertical affine edge whose parameter image lies on the contour-family boundary. -/
theorem explicitFormulaRectangle_verticalEdgeContourIntegrand_intervalIntegrable_of_boundaryContinuousOn
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T x a b : ℝ}
    (hboundary :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        (explicitFormulaContourFamilyBoundary F T))
    (hmem :
      ∀ y : ℝ, y ∈ Set.uIcc a b →
        (x : ℂ) + (y : ℂ) * Complex.I ∈
          explicitFormulaContourFamilyBoundary F T) :
    IntervalIntegrable
      (fun y : ℝ =>
        zetaCompletedExplicitFormulaContourIntegrand f
          ((x : ℂ) + (y : ℂ) * Complex.I))
      volume a b :=
  (hboundary.comp_continuousOn
    (explicitFormulaRectangle_verticalEdgeParameter_continuousOn x a b)
    hmem).intervalIntegrable

/-- Boundary regularity gives interval-integrability along any horizontal affine edge whose
parameter image lies on the contour-family boundary. -/
theorem explicitFormulaRectangle_horizontalEdgeContourIntegrand_intervalIntegrable_of_boundaryRegular
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T y a b : ℝ}
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hmem :
      ∀ x : ℝ, x ∈ Set.uIcc a b →
        (x : ℂ) + (y : ℂ) * Complex.I ∈
          explicitFormulaContourFamilyBoundary F T) :
    IntervalIntegrable
      (fun x : ℝ =>
        zetaCompletedExplicitFormulaContourIntegrand f
          ((x : ℂ) + (y : ℂ) * Complex.I))
      volume a b := by
  have hcont :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        (explicitFormulaContourFamilyBoundary F T) := by
    intro z hz
    exact (hboundary z hz).1.continuousWithinAt
  exact
    explicitFormulaRectangle_horizontalEdgeContourIntegrand_intervalIntegrable_of_boundaryContinuousOn
      f F hcont hmem

/-- Boundary regularity gives interval-integrability along any vertical affine edge whose
parameter image lies on the contour-family boundary. -/
theorem explicitFormulaRectangle_verticalEdgeContourIntegrand_intervalIntegrable_of_boundaryRegular
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    {T x a b : ℝ}
    (hboundary :
      ∀ z : ℂ,
        z ∈ explicitFormulaContourFamilyBoundary F T →
          ContinuousAt
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z ∧
            DifferentiableAt ℂ
              (fun w : ℂ => zetaCompletedExplicitFormulaContourIntegrand f w) z)
    (hmem :
      ∀ y : ℝ, y ∈ Set.uIcc a b →
        (x : ℂ) + (y : ℂ) * Complex.I ∈
          explicitFormulaContourFamilyBoundary F T) :
    IntervalIntegrable
      (fun y : ℝ =>
        zetaCompletedExplicitFormulaContourIntegrand f
          ((x : ℂ) + (y : ℂ) * Complex.I))
      volume a b := by
  have hcont :
      ContinuousOn
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        (explicitFormulaContourFamilyBoundary F T) := by
    intro z hz
    exact (hboundary z hz).1.continuousWithinAt
  exact
    explicitFormulaRectangle_verticalEdgeContourIntegrand_intervalIntegrable_of_boundaryContinuousOn
      f F hcont hmem

/-- The scheduled analytic package supplies boundary regularity, hence horizontal
edge-parameter interval-integrability, once the edge image is known to lie on the scheduled
rectangle boundary. -/
theorem explicitFormulaRectangle_horizontalEdgeContourIntegrand_intervalIntegrable_of_scheduledPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    {y a b : ℝ}
    (hmem :
      ∀ x : ℝ, x ∈ Set.uIcc a b →
        (x : ℂ) + (y : ℂ) * Complex.I ∈
          explicitFormulaContourFamilyBoundary F (h.height_schedule.height u)) :
    IntervalIntegrable
      (fun x : ℝ =>
        zetaCompletedExplicitFormulaContourIntegrand f
          ((x : ℂ) + (y : ℂ) * Complex.I))
      volume a b :=
  explicitFormulaRectangle_horizontalEdgeContourIntegrand_intervalIntegrable_of_boundaryRegular
    f F
    (explicitFormulaRectangleContourIntegrand_boundaryRegular_of_avoidsBoundary
      f F h (h.height_schedule.height u)
      (explicitFormulaScheduledRectangle_avoidsSingularBoundary f F h u))
    hmem

/-- The scheduled analytic package supplies boundary regularity, hence vertical
edge-parameter interval-integrability, once the edge image is known to lie on the scheduled
rectangle boundary. -/
theorem explicitFormulaRectangle_verticalEdgeContourIntegrand_intervalIntegrable_of_scheduledPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u : ℝ)
    {x a b : ℝ}
    (hmem :
      ∀ y : ℝ, y ∈ Set.uIcc a b →
        (x : ℂ) + (y : ℂ) * Complex.I ∈
          explicitFormulaContourFamilyBoundary F (h.height_schedule.height u)) :
    IntervalIntegrable
      (fun y : ℝ =>
        zetaCompletedExplicitFormulaContourIntegrand f
          ((x : ℂ) + (y : ℂ) * Complex.I))
      volume a b :=
  explicitFormulaRectangle_verticalEdgeContourIntegrand_intervalIntegrable_of_boundaryRegular
    f F
    (explicitFormulaRectangleContourIntegrand_boundaryRegular_of_avoidsBoundary
      f F h (h.height_schedule.height u)
      (explicitFormulaScheduledRectangle_avoidsSingularBoundary f F h u))
    hmem

/-- Scheduled analytic package constructor for vertical adjacent-endpoint integrability. -/
theorem explicitFormulaRectangleVerticalAdjacentEndpointIntegrable_of_scheduledPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u x : ℝ)
    (a : ℕ → ℝ) (n : ℕ)
    (hmem :
      ∀ k : ℕ, k < n →
        ∀ y : ℝ, y ∈ Set.uIcc (a k) (a (k + 1)) →
          (x : ℂ) + y * Complex.I ∈
            explicitFormulaContourFamilyBoundary F (h.height_schedule.height u)) :
    explicitFormulaRectangleVerticalAdjacentEndpointIntegrable
      f x a n :=
  fun k hk =>
    explicitFormulaRectangle_verticalEdgeContourIntegrand_intervalIntegrable_of_scheduledPackage
      f F h u (hmem k hk)

/-- Scheduled analytic package constructor for horizontal adjacent-endpoint integrability. -/
theorem explicitFormulaRectangleHorizontalAdjacentEndpointIntegrable_of_scheduledPackage
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (h : ExplicitFormulaFamilyAnalyticPackage f F) (u y : ℝ)
    (a : ℕ → ℝ) (n : ℕ)
    (hmem :
      ∀ k : ℕ, k < n →
        ∀ x : ℝ, x ∈ Set.uIcc (a k) (a (k + 1)) →
          (x : ℂ) + (y : ℂ) * Complex.I ∈
            explicitFormulaContourFamilyBoundary F (h.height_schedule.height u)) :
    explicitFormulaRectangleHorizontalAdjacentEndpointIntegrable
      f y a n :=
  fun k hk =>
    explicitFormulaRectangle_horizontalEdgeContourIntegrand_intervalIntegrable_of_scheduledPackage
      f F h u (hmem k hk)

/-- Recursive list sums commute with a fixed scalar multiple. -/
theorem explicitFormulaRectangleListSum_smul
    {α : Type} (c : ℂ) (g : α → ℂ) :
    ∀ xs : List α,
      explicitFormulaRectangleListSum (fun x : α => c • g x) xs =
        c • explicitFormulaRectangleListSum g xs
  | [] => by
      exact (smul_zero c).symm
  | x :: rest => by
      have htail :
          explicitFormulaRectangleListSum (fun x : α => c • g x) rest =
            c • explicitFormulaRectangleListSum g rest :=
        explicitFormulaRectangleListSum_smul c g rest
      calc
        explicitFormulaRectangleListSum (fun x : α => c • g x) (x :: rest) =
            c • g x +
              explicitFormulaRectangleListSum (fun x : α => c • g x) rest := by
          rfl
        _ =
            c • g x + c • explicitFormulaRectangleListSum g rest := by
          exact congrArg (fun z : ℂ => c • g x + z) htail
        _ =
            c • (g x + explicitFormulaRectangleListSum g rest) := by
          exact (smul_add c (g x) (explicitFormulaRectangleListSum g rest)).symm
        _ =
            c • explicitFormulaRectangleListSum g (x :: rest) := by
          rfl

/-- Vertical adjacent interval integrals telescope once interval-integrability is supplied
on each adjacent subinterval. -/
theorem explicitFormulaRectangleListSum_ofFn_verticalIntegral_adjacent
    (f : ZetaAdmissibleFunction) (x : ℝ)
    {n : ℕ} (a : ℕ → ℝ)
    (hint : explicitFormulaRectangleVerticalAdjacentEndpointIntegrable f x a n) :
    explicitFormulaRectangleListSum
        (fun i : Fin n =>
          Complex.I •
            ∫ y : ℝ in a i.1..a (i.1 + 1),
              zetaCompletedExplicitFormulaContourIntegrand f
                ((x : ℂ) + y * Complex.I))
        (List.ofFn (fun i : Fin n => i)) =
      Complex.I •
        ∫ y : ℝ in a 0..a n,
          zetaCompletedExplicitFormulaContourIntegrand f
            ((x : ℂ) + y * Complex.I) := by
  let φ : ℝ → ℂ :=
    fun y : ℝ =>
      zetaCompletedExplicitFormulaContourIntegrand f
        ((x : ℂ) + y * Complex.I)
  have hsum :
      explicitFormulaRectangleListSum
          (fun i : Fin n =>
            Complex.I •
              ∫ y : ℝ in a i.1..a (i.1 + 1), φ y)
          (List.ofFn (fun i : Fin n => i)) =
        Complex.I •
          explicitFormulaRectangleListSum
            (fun i : Fin n =>
              ∫ y : ℝ in a i.1..a (i.1 + 1), φ y)
            (List.ofFn (fun i : Fin n => i)) :=
    explicitFormulaRectangleListSum_smul
      Complex.I
      (fun i : Fin n => ∫ y : ℝ in a i.1..a (i.1 + 1), φ y)
      (List.ofFn (fun i : Fin n => i))
  have htelescope :
      explicitFormulaRectangleListSum
          (fun i : Fin n =>
            ∫ y : ℝ in a i.1..a (i.1 + 1), φ y)
          (List.ofFn (fun i : Fin n => i)) =
        ∫ y : ℝ in a 0..a n, φ y :=
    explicitFormulaRectangleListSum_ofFn_intervalIntegral_adjacent
      a φ hint
  exact Eq.trans hsum (congrArg (fun z : ℂ => Complex.I • z) htelescope)

/-- Vertical adjacent interval integrals telescope over a shifted finite subdivision
once interval-integrability is supplied on each shifted adjacent subinterval. -/
theorem explicitFormulaRectangleListSum_ofFn_verticalIntegral_adjacent_shift
    (f : ZetaAdmissibleFunction) (x : ℝ)
    {n : ℕ} (a : ℕ → ℝ) (lo : ℕ)
    (hint :
      ∀ k : ℕ, k < n →
        IntervalIntegrable
          (fun y : ℝ =>
            zetaCompletedExplicitFormulaContourIntegrand f
              ((x : ℂ) + y * Complex.I))
          volume
          (a (lo + k)) (a (lo + (k + 1)))) :
    explicitFormulaRectangleListSum
        (fun i : Fin n =>
          Complex.I •
            ∫ y : ℝ in a (lo + i.1)..a (lo + (i.1 + 1)),
              zetaCompletedExplicitFormulaContourIntegrand f
                ((x : ℂ) + y * Complex.I))
        (List.ofFn (fun i : Fin n => i)) =
      Complex.I •
        ∫ y : ℝ in a (lo + 0)..a (lo + n),
          zetaCompletedExplicitFormulaContourIntegrand f
            ((x : ℂ) + y * Complex.I) := by
  let φ : ℝ → ℂ :=
    fun y : ℝ =>
      zetaCompletedExplicitFormulaContourIntegrand f
        ((x : ℂ) + y * Complex.I)
  have hsum :
      explicitFormulaRectangleListSum
          (fun i : Fin n =>
            Complex.I •
              ∫ y : ℝ in a (lo + i.1)..a (lo + (i.1 + 1)), φ y)
          (List.ofFn (fun i : Fin n => i)) =
        Complex.I •
          explicitFormulaRectangleListSum
            (fun i : Fin n =>
              ∫ y : ℝ in a (lo + i.1)..a (lo + (i.1 + 1)), φ y)
            (List.ofFn (fun i : Fin n => i)) :=
    explicitFormulaRectangleListSum_smul
      Complex.I
      (fun i : Fin n =>
        ∫ y : ℝ in a (lo + i.1)..a (lo + (i.1 + 1)), φ y)
      (List.ofFn (fun i : Fin n => i))
  have htelescope :
      explicitFormulaRectangleListSum
          (fun i : Fin n =>
            ∫ y : ℝ in a (lo + i.1)..a (lo + (i.1 + 1)), φ y)
          (List.ofFn (fun i : Fin n => i)) =
        ∫ y : ℝ in a (lo + 0)..a (lo + n), φ y :=
    explicitFormulaRectangleListSum_ofFn_intervalIntegral_adjacent_shift
      a φ lo hint
  exact Eq.trans hsum (congrArg (fun z : ℂ => Complex.I • z) htelescope)

/-- Horizontal adjacent interval integrals telescope once interval-integrability is supplied
on each adjacent subinterval. -/
theorem explicitFormulaRectangleListSum_ofFn_horizontalIntegral_adjacent
    (f : ZetaAdmissibleFunction) (y : ℝ)
    {n : ℕ} (a : ℕ → ℝ)
    (hint : explicitFormulaRectangleHorizontalAdjacentEndpointIntegrable f y a n) :
    explicitFormulaRectangleListSum
        (fun i : Fin n =>
          ∫ x : ℝ in a i.1..a (i.1 + 1),
            zetaCompletedExplicitFormulaContourIntegrand f
              (x + (y : ℂ) * Complex.I))
        (List.ofFn (fun i : Fin n => i)) =
      ∫ x : ℝ in a 0..a n,
        zetaCompletedExplicitFormulaContourIntegrand f
          (x + (y : ℂ) * Complex.I) := by
  exact
    explicitFormulaRectangleListSum_ofFn_intervalIntegral_adjacent
      a
      (fun x : ℝ =>
        zetaCompletedExplicitFormulaContourIntegrand f
          (x + (y : ℂ) * Complex.I))
      hint

/-- Horizontal adjacent interval integrals telescope over a shifted finite subdivision
once interval-integrability is supplied on each shifted adjacent subinterval. -/
theorem explicitFormulaRectangleListSum_ofFn_horizontalIntegral_adjacent_shift
    (f : ZetaAdmissibleFunction) (y : ℝ)
    {n : ℕ} (a : ℕ → ℝ) (lo : ℕ)
    (hint :
      ∀ k : ℕ, k < n →
        IntervalIntegrable
          (fun x : ℝ =>
            zetaCompletedExplicitFormulaContourIntegrand f
              (x + (y : ℂ) * Complex.I))
          volume
          (a (lo + k)) (a (lo + (k + 1)))) :
    explicitFormulaRectangleListSum
        (fun i : Fin n =>
          ∫ x : ℝ in a (lo + i.1)..a (lo + (i.1 + 1)),
            zetaCompletedExplicitFormulaContourIntegrand f
              (x + (y : ℂ) * Complex.I))
        (List.ofFn (fun i : Fin n => i)) =
      ∫ x : ℝ in a (lo + 0)..a (lo + n),
        zetaCompletedExplicitFormulaContourIntegrand f
          (x + (y : ℂ) * Complex.I) := by
  exact
    explicitFormulaRectangleListSum_ofFn_intervalIntegral_adjacent_shift
      a
      (fun x : ℝ =>
        zetaCompletedExplicitFormulaContourIntegrand f
          (x + (y : ℂ) * Complex.I))
      lo
      hint

/-- Recursive list sums commute with a finite sum over a fixed finite set. -/
theorem explicitFormulaRectangleListSum_finset_sum
    {α β : Type} (S : Finset β) (g : α → β → ℂ) :
    ∀ xs : List α,
      explicitFormulaRectangleListSum
          (fun x : α => ∑ b in S, g x b) xs =
        ∑ b in S, explicitFormulaRectangleListSum (fun x : α => g x b) xs
  | [] => by
      exact (Finset.sum_const_zero : (∑ b in S, (0 : ℂ)) = 0).symm
  | x :: rest => by
      have htail :
          explicitFormulaRectangleListSum
              (fun x : α => ∑ b in S, g x b) rest =
            ∑ b in S, explicitFormulaRectangleListSum (fun x : α => g x b) rest :=
        explicitFormulaRectangleListSum_finset_sum S g rest
      calc
        explicitFormulaRectangleListSum
            (fun x : α => ∑ b in S, g x b) (x :: rest) =
            (∑ b in S, g x b) +
              explicitFormulaRectangleListSum
                (fun x : α => ∑ b in S, g x b) rest := by
          rfl
        _ =
            (∑ b in S, g x b) +
              (∑ b in S, explicitFormulaRectangleListSum (fun x : α => g x b) rest) := by
          exact congrArg (fun z : ℂ => (∑ b in S, g x b) + z) htail
        _ =
            ∑ b in S,
              (g x b + explicitFormulaRectangleListSum (fun x : α => g x b) rest) := by
          exact
            (Finset.sum_add_distrib
              (s := S)
              (f := fun b : β => g x b)
              (g := fun b : β =>
                explicitFormulaRectangleListSum (fun x : α => g x b) rest)).symm
        _ =
            ∑ b in S,
              explicitFormulaRectangleListSum (fun x : α => g x b) (x :: rest) := by
          exact Finset.sum_congr rfl (fun b _hb => rfl)

/-- Recursive list sums of fixed scalar multiples of adjacent interval integrals assemble
to the same scalar multiple of the whole endpoint-span integral. -/
theorem explicitFormulaRectangleListSum_ofFn_smul_intervalIntegral_adjacent
    {n : ℕ} (c : ℂ) (a : ℕ → ℝ) (φ : ℝ → ℂ)
    (hint : ∀ k : ℕ, k < n → IntervalIntegrable φ volume (a k) (a (k + 1))) :
    explicitFormulaRectangleListSum
        (fun i : Fin n => c • (∫ x : ℝ in a i.1..a (i.1 + 1), φ x))
        (List.ofFn (fun i : Fin n => i)) =
      c • (∫ x : ℝ in a 0..a n, φ x) := by
  have hsum :
      explicitFormulaRectangleListSum
          (fun i : Fin n => ∫ x : ℝ in a i.1..a (i.1 + 1), φ x)
          (List.ofFn (fun i : Fin n => i)) =
        ∫ x : ℝ in a 0..a n, φ x :=
    explicitFormulaRectangleListSum_ofFn_intervalIntegral_adjacent a φ hint
  have hsmul :
      explicitFormulaRectangleListSum
          (fun i : Fin n => c • (∫ x : ℝ in a i.1..a (i.1 + 1), φ x))
          (List.ofFn (fun i : Fin n => i)) =
        c •
          explicitFormulaRectangleListSum
            (fun i : Fin n => ∫ x : ℝ in a i.1..a (i.1 + 1), φ x)
            (List.ofFn (fun i : Fin n => i)) := by
    exact
      explicitFormulaRectangleListSum_smul
        c
        (fun i : Fin n => ∫ x : ℝ in a i.1..a (i.1 + 1), φ x)
        (List.ofFn (fun i : Fin n => i))
  calc
    explicitFormulaRectangleListSum
        (fun i : Fin n => c • (∫ x : ℝ in a i.1..a (i.1 + 1), φ x))
        (List.ofFn (fun i : Fin n => i)) =
        c •
          explicitFormulaRectangleListSum
            (fun i : Fin n => ∫ x : ℝ in a i.1..a (i.1 + 1), φ x)
            (List.ofFn (fun i : Fin n => i)) := by
      exact hsmul
    _ = c • (∫ x : ℝ in a 0..a n, φ x) := by
      exact congrArg (fun z : ℂ => c • z) hsum

/-- Pointwise equality on a source list transports the local recursive list sum. -/
theorem explicitFormulaRectangleListSum_congr
    {α : Type} {g h : α → ℂ} :
    ∀ xs : List α,
      (∀ x : α, x ∈ xs → g x = h x) →
        explicitFormulaRectangleListSum g xs =
          explicitFormulaRectangleListSum h xs
  | [], _hpoint => by
      rfl
  | x :: rest, hpoint => by
      have hhead : g x = h x :=
        hpoint x (List.mem_cons_self x rest)
      have htail :
          explicitFormulaRectangleListSum g rest =
            explicitFormulaRectangleListSum h rest :=
        explicitFormulaRectangleListSum_congr rest
          (fun y hy =>
            hpoint y (List.mem_cons_of_mem x hy))
      calc
        explicitFormulaRectangleListSum g (x :: rest) =
            g x + explicitFormulaRectangleListSum g rest := by
          rfl
        _ = h x + explicitFormulaRectangleListSum g rest := by
          exact congrArg
            (fun z : ℂ => z + explicitFormulaRectangleListSum g rest)
            hhead
        _ = h x + explicitFormulaRectangleListSum h rest := by
          exact congrArg
            (fun z : ℂ => h x + z)
            htail
        _ = explicitFormulaRectangleListSum h (x :: rest) := by
          rfl

/-- If every summand on a source list is zero, the local recursive list sum is zero. -/
theorem explicitFormulaRectangleListSum_eq_zero_of_forall_mem_eq_zero
    {α : Type} (g : α → ℂ) :
    ∀ xs : List α,
      (∀ x : α, x ∈ xs → g x = 0) →
        explicitFormulaRectangleListSum g xs = 0
  | [], _hzero => by
      rfl
  | x :: rest, hzero => by
      have hhead : g x = 0 :=
        hzero x (List.mem_cons_self x rest)
      have htail :
          explicitFormulaRectangleListSum g rest = 0 :=
        explicitFormulaRectangleListSum_eq_zero_of_forall_mem_eq_zero g rest
          (fun y hy =>
            hzero y (List.mem_cons_of_mem x hy))
      calc
        explicitFormulaRectangleListSum g (x :: rest) =
            g x + explicitFormulaRectangleListSum g rest := by
          rfl
        _ = 0 + explicitFormulaRectangleListSum g rest := by
          exact congrArg
            (fun z : ℂ => z + explicitFormulaRectangleListSum g rest)
            hhead
        _ = 0 + 0 := by
          exact congrArg (fun z : ℂ => 0 + z) htail
        _ = 0 := by
          exact zero_add (0 : ℂ)

/-- A local recursive list sum with a single nonzero selected member evaluates to the
selected value.  The duplicate-free hypothesis is used only to exclude a second copy of
the selected list element in the tail. -/
theorem explicitFormulaRectangleListSum_eq_single_of_nodup
    {α : Type} (p : α → Prop) [DecidablePred p]
    (w : ℂ) :
    ∀ xs : List α,
      xs.Nodup →
        ∀ x₀ : α,
          x₀ ∈ xs →
            p x₀ →
              (∀ x : α, x ∈ xs → p x → x = x₀) →
                explicitFormulaRectangleListSum
                    (fun x : α => if p x then w else 0) xs =
                  w
  | [], hnodup, x₀, hx₀, _hp₀, _hunique => by
      exact False.elim (List.not_mem_nil x₀ hx₀)
  | x :: rest, hnodup, x₀, hx₀, hp₀, hunique => by
      match hx₀ with
      | List.Mem.head _ =>
          have hhead_eq : x = x₀ := rfl
          have hhead_value :
              (if p x then w else 0) = w := by
            exact if_pos hp₀
          have htail_zero :
              explicitFormulaRectangleListSum
                  (fun y : α => if p y then w else 0) rest = 0 := by
            exact
              explicitFormulaRectangleListSum_eq_zero_of_forall_mem_eq_zero
                (fun y : α => if p y then w else 0)
                rest
                (fun y hy =>
                  if hpy : p y then
                    have hy_eq_x₀ : y = x₀ :=
                      hunique y (List.mem_cons_of_mem x hy) hpy
                    have hy_eq_x : y = x :=
                      Eq.trans hy_eq_x₀ hhead_eq.symm
                    have hx_not_mem_tail : x ∉ rest :=
                      hnodup.not_mem
                    False.elim (hx_not_mem_tail (Eq.subst
                      (motive := fun z : α => z ∈ rest)
                      hy_eq_x
                      hy))
                  else
                    if_neg hpy)
          calc
            explicitFormulaRectangleListSum
                (fun y : α => if p y then w else 0) (x :: rest) =
                (if p x then w else 0) +
                  explicitFormulaRectangleListSum
                    (fun y : α => if p y then w else 0) rest := by
              rfl
            _ = w +
                  explicitFormulaRectangleListSum
                    (fun y : α => if p y then w else 0) rest := by
              exact congrArg
                (fun z : ℂ =>
                  z +
                    explicitFormulaRectangleListSum
                      (fun y : α => if p y then w else 0) rest)
                hhead_value
            _ = w + 0 := by
              exact congrArg (fun z : ℂ => w + z) htail_zero
            _ = w := by
              exact add_zero w
      | List.Mem.tail _ hx₀_tail =>
          have hhead_zero : (if p x then w else 0) = 0 := by
            if hpx : p x then
              have hx_eq_x₀ : x = x₀ :=
                hunique x (List.mem_cons_self x rest) hpx
              have hx_not_mem_tail : x ∉ rest :=
                hnodup.not_mem
              exact False.elim
                (hx_not_mem_tail
                  (Eq.subst
                    (motive := fun z : α => z ∈ rest)
                    hx_eq_x₀.symm
                    hx₀_tail))
            else
              exact if_neg hpx
          have htail_nodup : rest.Nodup :=
            hnodup.of_cons
          have htail_unique :
              ∀ y : α, y ∈ rest → p y → y = x₀ :=
            fun y hy hpy =>
              hunique y (List.mem_cons_of_mem x hy) hpy
          have htail_single :
              explicitFormulaRectangleListSum
                  (fun y : α => if p y then w else 0) rest =
                w :=
            explicitFormulaRectangleListSum_eq_single_of_nodup
              p w rest htail_nodup x₀ hx₀_tail hp₀ htail_unique
          calc
            explicitFormulaRectangleListSum
                (fun y : α => if p y then w else 0) (x :: rest) =
                (if p x then w else 0) +
                  explicitFormulaRectangleListSum
                    (fun y : α => if p y then w else 0) rest := by
              rfl
            _ = 0 +
                  explicitFormulaRectangleListSum
                    (fun y : α => if p y then w else 0) rest := by
              exact congrArg
                (fun z : ℂ =>
                  z +
                    explicitFormulaRectangleListSum
                      (fun y : α => if p y then w else 0) rest)
                hhead_zero
            _ =
                explicitFormulaRectangleListSum
                  (fun y : α => if p y then w else 0) rest := by
              exact zero_add
                (explicitFormulaRectangleListSum
                  (fun y : α => if p y then w else 0) rest)
            _ = w := by
              exact htail_single

/-- Adding a constant to the front of a recursive sum can be reassociated across one
outer add. -/
theorem explicitFormulaRectangleListSum_cons_add_assoc
    (a b c : ℂ) :
    a + (b + c) = b + (a + c) := by
  calc
    a + (b + c) = (a + b) + c := by
      exact (add_assoc a b c).symm
    _ = (b + a) + c := by
      exact congrArg (fun z : ℂ => z + c) (add_comm a b)
    _ = b + (a + c) := by
      exact add_assoc b a c

/-- Adding a row-major head row commutes with adding the head column contribution. -/
theorem explicitFormulaRectangleRowColumnHeadAlgebra
    (a b c d : ℂ) :
    a + (b + (c + d)) = (a + b) + (c + d) := by
  exact (add_assoc a b (c + d)).symm

/-- Row-major and column-major recursive double sums over two lists agree. -/
theorem explicitFormulaRectangleRowMajorDoubleSum_eq_columnMajorDoubleSum
    {α β : Type} (g : α → β → ℂ) :
    ∀ xs ys : List α × List β,
      explicitFormulaRectangleRowMajorDoubleSum g xs.1 xs.2 =
        explicitFormulaRectangleColumnMajorDoubleSum g xs.1 xs.2
  | ([], []) => by
      rfl
  | ([], y :: ys) => by
      calc
        explicitFormulaRectangleRowMajorDoubleSum g [] (y :: ys) = 0 := by
          rfl
        _ =
            explicitFormulaRectangleColumnMajorDoubleSum g [] (y :: ys) := by
          rfl
  | (x :: xs, []) => by
      have ih :
          explicitFormulaRectangleRowMajorDoubleSum g xs [] =
            explicitFormulaRectangleColumnMajorDoubleSum g xs [] :=
        explicitFormulaRectangleRowMajorDoubleSum_eq_columnMajorDoubleSum g (xs, [])
      calc
        explicitFormulaRectangleRowMajorDoubleSum g (x :: xs) [] =
            explicitFormulaRectangleListSum (fun y : β => g x y) [] +
              explicitFormulaRectangleRowMajorDoubleSum g xs [] := by
          rfl
        _ = 0 + explicitFormulaRectangleRowMajorDoubleSum g xs [] := by
          rfl
        _ = explicitFormulaRectangleRowMajorDoubleSum g xs [] := by
          exact zero_add (explicitFormulaRectangleRowMajorDoubleSum g xs [])
        _ = explicitFormulaRectangleColumnMajorDoubleSum g xs [] := by
          exact ih
        _ = 0 := by
          rfl
        _ =
            explicitFormulaRectangleColumnMajorDoubleSum g (x :: xs) [] := by
          rfl
  | (x :: xs, y :: ys) => by
      have ih_tail :
          explicitFormulaRectangleRowMajorDoubleSum g xs ys =
            explicitFormulaRectangleColumnMajorDoubleSum g xs ys :=
        explicitFormulaRectangleRowMajorDoubleSum_eq_columnMajorDoubleSum g (xs, ys)
      have ih_row_tail :
          explicitFormulaRectangleRowMajorDoubleSum g xs (y :: ys) =
            explicitFormulaRectangleColumnMajorDoubleSum g xs (y :: ys) :=
        explicitFormulaRectangleRowMajorDoubleSum_eq_columnMajorDoubleSum g (xs, y :: ys)
      have ih_col_tail :
          explicitFormulaRectangleRowMajorDoubleSum g (x :: xs) ys =
            explicitFormulaRectangleColumnMajorDoubleSum g (x :: xs) ys :=
        explicitFormulaRectangleRowMajorDoubleSum_eq_columnMajorDoubleSum g (x :: xs, ys)
      let rowHead : ℂ := g x y
      let rowTail : ℂ :=
        explicitFormulaRectangleListSum (fun y' : β => g x y') ys
      let colTail : ℂ :=
        explicitFormulaRectangleListSum (fun x' : α => g x' y) xs
      let restRows : ℂ := explicitFormulaRectangleRowMajorDoubleSum g xs ys
      let restCols : ℂ := explicitFormulaRectangleColumnMajorDoubleSum g xs ys
      calc
        explicitFormulaRectangleRowMajorDoubleSum g (x :: xs) (y :: ys) =
            (g x y +
                explicitFormulaRectangleListSum (fun y' : β => g x y') ys) +
              explicitFormulaRectangleRowMajorDoubleSum g xs (y :: ys) := by
          rfl
        _ =
            (g x y +
                explicitFormulaRectangleListSum (fun y' : β => g x y') ys) +
              explicitFormulaRectangleColumnMajorDoubleSum g xs (y :: ys) := by
          exact congrArg
            (fun z : ℂ =>
              (g x y +
                  explicitFormulaRectangleListSum (fun y' : β => g x y') ys) + z)
            ih_row_tail
        _ =
            (g x y +
                explicitFormulaRectangleListSum (fun y' : β => g x y') ys) +
              (explicitFormulaRectangleListSum (fun x' : α => g x' y) xs +
                explicitFormulaRectangleColumnMajorDoubleSum g xs ys) := by
          rfl
        _ =
            (g x y +
                explicitFormulaRectangleListSum (fun x' : α => g x' y) xs) +
              (explicitFormulaRectangleListSum (fun y' : β => g x y') ys +
                explicitFormulaRectangleColumnMajorDoubleSum g xs ys) := by
          calc
            (g x y +
                explicitFormulaRectangleListSum (fun y' : β => g x y') ys) +
              (explicitFormulaRectangleListSum (fun x' : α => g x' y) xs +
                explicitFormulaRectangleColumnMajorDoubleSum g xs ys) =
                g x y +
                  (explicitFormulaRectangleListSum (fun y' : β => g x y') ys +
                    (explicitFormulaRectangleListSum (fun x' : α => g x' y) xs +
                      explicitFormulaRectangleColumnMajorDoubleSum g xs ys)) := by
              exact add_assoc
                (g x y)
                (explicitFormulaRectangleListSum (fun y' : β => g x y') ys)
                (explicitFormulaRectangleListSum (fun x' : α => g x' y) xs +
                  explicitFormulaRectangleColumnMajorDoubleSum g xs ys)
            _ =
                g x y +
                  (explicitFormulaRectangleListSum (fun x' : α => g x' y) xs +
                    (explicitFormulaRectangleListSum (fun y' : β => g x y') ys +
                      explicitFormulaRectangleColumnMajorDoubleSum g xs ys)) := by
              exact congrArg
                (fun z : ℂ => g x y + z)
                (explicitFormulaRectangleListSum_cons_add_assoc
                  (explicitFormulaRectangleListSum (fun y' : β => g x y') ys)
                  (explicitFormulaRectangleListSum (fun x' : α => g x' y) xs)
                  (explicitFormulaRectangleColumnMajorDoubleSum g xs ys))
            _ =
                (g x y +
                    explicitFormulaRectangleListSum (fun x' : α => g x' y) xs) +
                  (explicitFormulaRectangleListSum (fun y' : β => g x y') ys +
                    explicitFormulaRectangleColumnMajorDoubleSum g xs ys) := by
              exact (add_assoc
                (g x y)
                (explicitFormulaRectangleListSum (fun x' : α => g x' y) xs)
                (explicitFormulaRectangleListSum (fun y' : β => g x y') ys +
                  explicitFormulaRectangleColumnMajorDoubleSum g xs ys)).symm
        _ =
            (g x y +
                explicitFormulaRectangleListSum (fun x' : α => g x' y) xs) +
              (explicitFormulaRectangleListSum (fun y' : β => g x y') ys +
                explicitFormulaRectangleRowMajorDoubleSum g xs ys) := by
          exact congrArg
            (fun z : ℂ =>
              (g x y +
                  explicitFormulaRectangleListSum (fun x' : α => g x' y) xs) +
                (explicitFormulaRectangleListSum (fun y' : β => g x y') ys + z))
            ih_tail.symm
        _ =
            (g x y +
                explicitFormulaRectangleListSum (fun x' : α => g x' y) xs) +
              explicitFormulaRectangleRowMajorDoubleSum g (x :: xs) ys := by
          rfl
        _ =
            (g x y +
                explicitFormulaRectangleListSum (fun x' : α => g x' y) xs) +
              explicitFormulaRectangleColumnMajorDoubleSum g (x :: xs) ys := by
          exact congrArg
            (fun z : ℂ =>
              (g x y +
                  explicitFormulaRectangleListSum (fun x' : α => g x' y) xs) + z)
            ih_col_tail
        _ =
            explicitFormulaRectangleColumnMajorDoubleSum g (x :: xs) (y :: ys) := by
          rfl

/-- The selected horizontal contribution of a single crossed adjacent-pair cell. If the
cell is omitted by the raw singular coordinate filter, the contribution is zero; if it is
selected, it is the bottom-minus-top contribution of that endpoint datum. -/
noncomputable def explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε) : ℂ :=
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
          ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) -
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
            ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)
  else
    0

/-- Horizontal row contribution is zero over an empty vertical adjacent-pair source list. -/
theorem explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
        f xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) =
      0 :=
  explicitFormulaRectangleSelectedEndpointDataHorizontalContribution_fixedX_nil f xpair

/-- Horizontal row contribution over a cons vertical adjacent-pair source list splits
into the selected single-cell contribution plus the row tail. -/
theorem explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
        f xpair (ypair :: rest) =
      explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
        f xpair ypair +
        explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
          f xpair rest := by
  have hcons :
      explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
          f xpair (ypair :: rest) =
        if homit :
            explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
          (explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
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
                ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) -
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
                  ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)) +
            explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
              f xpair rest
        else
          explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
            f xpair rest :=
    explicitFormulaRectangleSelectedEndpointDataHorizontalContribution_fixedX_cons
      f xpair ypair rest
  if homit :
      explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
    calc
      explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
          f xpair (ypair :: rest) =
          (explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
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
                ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) -
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
                  ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)) +
            explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
              f xpair rest := by
        exact hcons
      _ =
          explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
            f xpair ypair +
          explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
            f xpair rest := by
        rfl
  else
    calc
      explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
          f xpair (ypair :: rest) =
          explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
            f xpair rest := by
        exact hcons
      _ =
          0 +
            explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
              f xpair rest := by
        exact
          (zero_add
            (explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
              f xpair rest)).symm
      _ =
          explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
            f xpair ypair +
          explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
            f xpair rest := by
        rfl

/-- Horizontal row contribution is the recursive generic list sum of selected single-cell
horizontal contributions along the vertical adjacent-pair source list. -/
theorem explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution_eq_listSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    ∀ ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε),
      explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
          f xpair ypairs =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
            explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
              f xpair ypair)
          ypairs
  | [] =>
      explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution_nil f xpair
  | ypair :: rest => by
      have hhead :
          explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
              f xpair (ypair :: rest) =
            explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
                f xpair ypair +
              explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
                f xpair rest :=
        explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution_cons
          f xpair ypair rest
      have htail :
          explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
              f xpair rest =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
                  f xpair ypair)
              rest :=
        explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution_eq_listSum
          f xpair rest
      calc
        explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
            f xpair (ypair :: rest) =
            explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
                f xpair ypair +
              explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
                f xpair rest := by
          exact hhead
        _ =
            explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
                f xpair ypair +
              explicitFormulaRectangleListSum
                (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                  explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
                    f xpair ypair)
                rest := by
          exact congrArg
            (fun z : ℂ =>
              explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
                f xpair ypair + z)
            htail
        _ =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
                  f xpair ypair)
              (ypair :: rest) := by
          rfl

/-- The recursive fixed-row horizontal contribution sum is the row-major double sum of
selected single-cell horizontal contributions. -/
theorem explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum_eq_rowMajorDoubleSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction) :
    ∀ xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε),
      ∀ ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε),
        explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum
            f xpairs ypairs =
          explicitFormulaRectangleRowMajorDoubleSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
              fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
                  f xpair ypair)
            xpairs ypairs
  | [], ypairs => by
      rfl
  | xpair :: rest, ypairs => by
      have hrow :
          explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
              f xpair ypairs =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
                  f xpair ypair)
              ypairs :=
        explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution_eq_listSum
          f xpair ypairs
      have htail :
          explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum
              f rest ypairs =
            explicitFormulaRectangleRowMajorDoubleSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
                fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                  explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
                    f xpair ypair)
              rest ypairs :=
        explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum_eq_rowMajorDoubleSum
          f rest ypairs
      calc
        explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum
            f (xpair :: rest) ypairs =
            explicitFormulaRectangleSelectedEndpointDataHorizontalRowContribution
                f xpair ypairs +
              explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum
                f rest ypairs := by
          rfl
        _ =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
                  f xpair ypair)
              ypairs +
              explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum
                f rest ypairs := by
          exact congrArg
            (fun z : ℂ =>
              z +
                explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum
                  f rest ypairs)
            hrow
        _ =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
                  f xpair ypair)
              ypairs +
              explicitFormulaRectangleRowMajorDoubleSum
                (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
                  fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                    explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
                      f xpair ypair)
                rest ypairs := by
          exact congrArg
            (fun z : ℂ =>
              explicitFormulaRectangleListSum
                (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                  explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
                    f xpair ypair)
                ypairs + z)
            htail
        _ =
            explicitFormulaRectangleRowMajorDoubleSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
                fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                  explicitFormulaRectangleSelectedEndpointDataHorizontalCellContribution
                    f xpair ypair)
              (xpair :: rest) ypairs := by
          rfl

/-- Vertical row contribution is zero over an empty vertical adjacent-pair source list. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution
        f xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) =
      0 :=
  explicitFormulaRectangleSelectedEndpointDataVerticalContribution_fixedX_nil f xpair

/-- Vertical row contribution over a cons vertical adjacent-pair source list splits into
the selected single-cell contribution plus the row tail. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution
        f xpair (ypair :: rest) =
      explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
        f xpair ypair +
        explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution
          f xpair rest := by
  have hcons :
      explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution
          f xpair (ypair :: rest) =
        if homit :
            explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
          (explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
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
                ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) -
            explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
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
                  ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)) +
            explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution
              f xpair rest
        else
          explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution
            f xpair rest :=
    explicitFormulaRectangleSelectedEndpointDataVerticalContribution_fixedX_cons
      f xpair ypair rest
  if homit :
      explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
    calc
      explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution
          f xpair (ypair :: rest) =
          (explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
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
                ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) -
            explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
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
                  ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)) +
            explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution
              f xpair rest := by
        exact hcons
      _ =
          explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
            f xpair ypair +
          explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution
            f xpair rest := by
        rfl
  else
    calc
      explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution
          f xpair (ypair :: rest) =
          explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution
            f xpair rest := by
        exact hcons
      _ =
          0 +
            explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution
              f xpair rest := by
        exact
          (zero_add
            (explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution
              f xpair rest)).symm
      _ =
          explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
            f xpair ypair +
          explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution
            f xpair rest := by
        rfl

/-- Vertical row contribution is the recursive generic list sum of selected single-cell
vertical contributions along the vertical adjacent-pair source list. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution_eq_listSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    ∀ ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε),
      explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution
          f xpair ypairs =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
            explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
              f xpair ypair)
          ypairs
  | [] =>
      explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution_nil f xpair
  | ypair :: rest => by
      have hhead :
          explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution
              f xpair (ypair :: rest) =
            explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                f xpair ypair +
              explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution
                f xpair rest :=
        explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution_cons
          f xpair ypair rest
      have htail :
          explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution
              f xpair rest =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                  f xpair ypair)
              rest :=
        explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution_eq_listSum
          f xpair rest
      calc
        explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution
            f xpair (ypair :: rest) =
            explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                f xpair ypair +
              explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution
                f xpair rest := by
          exact hhead
        _ =
            explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                f xpair ypair +
              explicitFormulaRectangleListSum
                (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                  explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                    f xpair ypair)
                rest := by
          exact congrArg
            (fun z : ℂ =>
              explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                f xpair ypair + z)
            htail
        _ =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                  f xpair ypair)
              (ypair :: rest) := by
          rfl

/-- Fixed-column vertical contribution is the recursive generic list sum of selected
single-cell vertical contributions along the horizontal adjacent-pair source list. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution_eq_listSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε) :
    ∀ xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε),
      explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
          f xpairs ypair =
        explicitFormulaRectangleListSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
            explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
              f xpair ypair)
          xpairs
  | [] =>
      explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution_nil f ypair
  | xpair :: rest => by
      have hhead :
          explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
              f (xpair :: rest) ypair =
            explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                f xpair ypair +
              explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
                f rest ypair := by
        have hcons :=
          explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution_cons
            f xpair rest ypair
        if homit :
            explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
          calc
            explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
                f (xpair :: rest) ypair =
                (explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
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
                      ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) -
                  explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
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
                        ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)) +
                  explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
                    f rest ypair := by
              exact hcons
            _ =
                explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                    f xpair ypair +
                  explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
                    f rest ypair := by
              rfl
        else
          calc
            explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
                f (xpair :: rest) ypair =
                explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
                  f rest ypair := by
              exact hcons
            _ =
                0 +
                  explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
                    f rest ypair := by
              exact
                (zero_add
                  (explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
                    f rest ypair)).symm
            _ =
                explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                    f xpair ypair +
                  explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
                    f rest ypair := by
              rfl
      have htail :
          explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
              f rest ypair =
            explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
                explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                  f xpair ypair)
              rest :=
        explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution_eq_listSum
          f ypair rest
      calc
        explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
            f (xpair :: rest) ypair =
            explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                f xpair ypair +
              explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
                f rest ypair := by
          exact hhead
        _ =
            explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                f xpair ypair +
              explicitFormulaRectangleListSum
                (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
                  explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                    f xpair ypair)
                rest := by
          exact congrArg
            (fun z : ℂ =>
              explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                f xpair ypair + z)
            htail
        _ =
            explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
                explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                  f xpair ypair)
              (xpair :: rest) := by
          rfl

/-- The recursive fixed-row vertical contribution sum is the row-major double sum of
selected single-cell vertical contributions. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum_eq_rowMajorDoubleSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction) :
    ∀ xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε),
      ∀ ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε),
        explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum
            f xpairs ypairs =
          explicitFormulaRectangleRowMajorDoubleSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
              fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                  f xpair ypair)
            xpairs ypairs
  | [], ypairs => by
      rfl
  | xpair :: rest, ypairs => by
      have hrow :
          explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution
              f xpair ypairs =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                  f xpair ypair)
              ypairs :=
        explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution_eq_listSum
          f xpair ypairs
      have htail :
          explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum
              f rest ypairs =
            explicitFormulaRectangleRowMajorDoubleSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
                fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                  explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                    f xpair ypair)
              rest ypairs :=
        explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum_eq_rowMajorDoubleSum
          f rest ypairs
      calc
        explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum
            f (xpair :: rest) ypairs =
            explicitFormulaRectangleSelectedEndpointDataVerticalRowContribution
                f xpair ypairs +
              explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum
                f rest ypairs := by
          rfl
        _ =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                  f xpair ypair)
              ypairs +
              explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum
                f rest ypairs := by
          exact congrArg
            (fun z : ℂ =>
              z +
                explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum
                  f rest ypairs)
            hrow
        _ =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                  f xpair ypair)
              ypairs +
              explicitFormulaRectangleRowMajorDoubleSum
                (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
                  fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                    explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                      f xpair ypair)
                rest ypairs := by
          exact congrArg
            (fun z : ℂ =>
              explicitFormulaRectangleListSum
                (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                  explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                    f xpair ypair)
                ypairs + z)
            htail
        _ =
            explicitFormulaRectangleRowMajorDoubleSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
                fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                  explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                    f xpair ypair)
              (xpair :: rest) ypairs := by
          rfl

/-- The recursive fixed-column vertical contribution sum is the column-major double sum of
selected single-cell vertical contributions. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum_eq_columnMajorDoubleSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) :
    ∀ ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε),
      explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum
          f xpairs ypairs =
        explicitFormulaRectangleColumnMajorDoubleSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
            fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
              explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                f xpair ypair)
          xpairs ypairs
  | [] => by
      rfl
  | ypair :: rest => by
      have hcolumn :
          explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
              f xpairs ypair =
            explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
                explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                  f xpair ypair)
              xpairs :=
        explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution_eq_listSum
          f ypair xpairs
      have htail :
          explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum
              f xpairs rest =
            explicitFormulaRectangleColumnMajorDoubleSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
                fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                  explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                    f xpair ypair)
              xpairs rest :=
        explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum_eq_columnMajorDoubleSum
          f xpairs rest
      calc
        explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum
            f xpairs (ypair :: rest) =
            explicitFormulaRectangleSelectedEndpointDataVerticalColumnContribution
                f xpairs ypair +
              explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum
                f xpairs rest := by
          rfl
        _ =
            explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
                explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                  f xpair ypair)
              xpairs +
              explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum
                f xpairs rest := by
          exact congrArg
            (fun z : ℂ =>
              z +
                explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum
                  f xpairs rest)
            hcolumn
        _ =
            explicitFormulaRectangleListSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
                explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                  f xpair ypair)
              xpairs +
              explicitFormulaRectangleColumnMajorDoubleSum
                (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
                  fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                    explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                      f xpair ypair)
                xpairs rest := by
          exact congrArg
            (fun z : ℂ =>
              explicitFormulaRectangleListSum
                (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
                  explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                    f xpair ypair)
                xpairs + z)
            htail
        _ =
            explicitFormulaRectangleColumnMajorDoubleSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
                fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                  explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                    f xpair ypair)
              xpairs (ypair :: rest) := by
          rfl

/-- The recursive fixed-row vertical contribution sum equals the recursive fixed-column
vertical contribution sum.  Both enumerate the same selected crossed cells, but in
opposite orders; this is the finite Fubini reindexing needed before column telescoping. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum_eq_columnContributionSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum
        f xpairs ypairs =
      explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum
        f xpairs ypairs := by
  have hrow :
      explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum
          f xpairs ypairs =
        explicitFormulaRectangleRowMajorDoubleSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
            fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
              explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                f xpair ypair)
          xpairs ypairs :=
    explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum_eq_rowMajorDoubleSum
      f xpairs ypairs
  have hfubini :
      explicitFormulaRectangleRowMajorDoubleSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
            fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
              explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                f xpair ypair)
          xpairs ypairs =
        explicitFormulaRectangleColumnMajorDoubleSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
            fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
              explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                f xpair ypair)
          xpairs ypairs :=
    explicitFormulaRectangleRowMajorDoubleSum_eq_columnMajorDoubleSum
      (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
        fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
          explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
            f xpair ypair)
      (xpairs, ypairs)
  have hcolumn :
      explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum
          f xpairs ypairs =
        explicitFormulaRectangleColumnMajorDoubleSum
          (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
            fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
              explicitFormulaRectangleSelectedEndpointDataVerticalCellContribution
                f xpair ypair)
          xpairs ypairs :=
    explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum_eq_columnMajorDoubleSum
      f xpairs ypairs
  exact Eq.trans hrow (Eq.trans hfubini hcolumn.symm)

/-- The recursive horizontal row contribution over the sorted selected grid is exactly
the grouped horizontal contribution of the corresponding selected endpoint-data list. -/
theorem explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum_eq_sortedPairListsContribution
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ρ : ℝ) :
    let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
      explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
    let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
      explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
    let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          xpairs ypairs)
    explicitFormulaRectangleSelectedEndpointDataHorizontalRowContributionSum
        f xpairs ypairs =
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        xpairs ypairs)
  exact
    (explicitFormulaRectangleSelectedEndpointDataHorizontalContribution_pairLists_eq_rowSum
      f xpairs ypairs).symm

/-- The recursive vertical column contribution over the sorted selected grid is exactly
the grouped vertical contribution of the corresponding selected endpoint-data list. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum_eq_sortedPairListsContribution
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ρ : ℝ) :
    let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
      explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
    let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
      explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
    let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          xpairs ypairs)
    explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum
        f xpairs ypairs =
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data := by
  let xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :=
    explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ρ
  let ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) :=
    explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ρ
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        xpairs ypairs)
  have hrow :
      explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum
          f xpairs ypairs =
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data :=
    (explicitFormulaRectangleSelectedEndpointDataVerticalContribution_pairLists_eq_rowSum
      f xpairs ypairs).symm
  have hcolumn :
      explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum
          f xpairs ypairs =
        explicitFormulaRectangleSelectedEndpointDataVerticalColumnContributionSum
          f xpairs ypairs :=
    explicitFormulaRectangleSelectedEndpointDataVerticalRowContributionSum_eq_columnContributionSum
      f xpairs ypairs
  exact Eq.trans hcolumn.symm hrow

/-- Early grouped horizontal bridge from sorted selected endpoint-data edge sums to sorted
selected box-coordinate edge sums. -/
theorem explicitFormulaRectangleSelectedEndpointDataHorizontalSortedPairListsContribution_eq_boxCoordinates
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ)) :
    let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          xpairs ypairs)
    let boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
      explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists xpairs ypairs
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data =
      explicitFormulaRectangleBoxBottomEdgeIntegralSum f boxes -
        explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes := by
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        xpairs ypairs)
  let boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
    explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists xpairs ypairs
  have hboxes :
      data.map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ =>
            d.boxEdgeCoordinates) =
        boxes :=
    explicitFormulaRectangleSelectedEndpointDataPairLists_boxEdgeCoordinates xpairs ypairs
  have hbottom :
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data =
        explicitFormulaRectangleBoxBottomEdgeIntegralSum f
          (data.map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ =>
              d.boxEdgeCoordinates)) :=
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum_eq_boxBottomEdgeIntegralSum
      f data
  have htop :
      explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data =
        explicitFormulaRectangleBoxTopEdgeIntegralSum f
          (data.map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ =>
              d.boxEdgeCoordinates)) :=
    explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_eq_boxTopEdgeIntegralSum
      f data
  calc
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data =
        explicitFormulaRectangleBoxBottomEdgeIntegralSum f
            (data.map
              (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ =>
                d.boxEdgeCoordinates)) -
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data := by
      exact congrArg
        (fun z : ℂ => z - explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data)
        hbottom
    _ =
        explicitFormulaRectangleBoxBottomEdgeIntegralSum f
            (data.map
              (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ =>
                d.boxEdgeCoordinates)) -
          explicitFormulaRectangleBoxTopEdgeIntegralSum f
            (data.map
              (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ =>
                d.boxEdgeCoordinates)) := by
      exact congrArg
        (fun z : ℂ =>
          explicitFormulaRectangleBoxBottomEdgeIntegralSum f
              (data.map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ =>
                  d.boxEdgeCoordinates)) - z)
        htop
    _ =
        explicitFormulaRectangleBoxBottomEdgeIntegralSum f boxes -
          explicitFormulaRectangleBoxTopEdgeIntegralSum f
            (data.map
              (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ =>
                d.boxEdgeCoordinates)) := by
      exact congrArg
        (fun z : List ExplicitFormulaRectangleEndpointDataBoxEdge =>
          explicitFormulaRectangleBoxBottomEdgeIntegralSum f z -
            explicitFormulaRectangleBoxTopEdgeIntegralSum f
              (data.map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ =>
                  d.boxEdgeCoordinates)))
        hboxes
    _ =
        explicitFormulaRectangleBoxBottomEdgeIntegralSum f boxes -
          explicitFormulaRectangleBoxTopEdgeIntegralSum f boxes := by
      exact congrArg
        (fun z : List ExplicitFormulaRectangleEndpointDataBoxEdge =>
          explicitFormulaRectangleBoxBottomEdgeIntegralSum f boxes -
            explicitFormulaRectangleBoxTopEdgeIntegralSum f z)
        hboxes

/-- Early grouped vertical bridge from sorted selected endpoint-data edge sums to sorted
selected box-coordinate edge sums. -/
theorem explicitFormulaRectangleSelectedEndpointDataVerticalSortedPairListsContribution_eq_boxCoordinates
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ)) :
    let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          xpairs ypairs)
    let boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
      explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists xpairs ypairs
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data =
      explicitFormulaRectangleBoxRightEdgeIntegralSum f boxes -
        explicitFormulaRectangleBoxLeftEdgeIntegralSum f boxes := by
  let data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ) :=
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
        xpairs ypairs)
  let boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge :=
    explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists xpairs ypairs
  have hboxes :
      data.map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ =>
            d.boxEdgeCoordinates) =
        boxes :=
    explicitFormulaRectangleSelectedEndpointDataPairLists_boxEdgeCoordinates xpairs ypairs
  have hright :
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data =
        explicitFormulaRectangleBoxRightEdgeIntegralSum f
          (data.map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ =>
              d.boxEdgeCoordinates)) :=
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum_eq_boxRightEdgeIntegralSum
      f data
  have hleft :
      explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data =
        explicitFormulaRectangleBoxLeftEdgeIntegralSum f
          (data.map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ =>
              d.boxEdgeCoordinates)) :=
    explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum_eq_boxLeftEdgeIntegralSum
      f data
  calc
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data -
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data =
        explicitFormulaRectangleBoxRightEdgeIntegralSum f
            (data.map
              (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ =>
                d.boxEdgeCoordinates)) -
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data := by
      exact congrArg
        (fun z : ℂ => z - explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data)
        hright
    _ =
        explicitFormulaRectangleBoxRightEdgeIntegralSum f
            (data.map
              (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ =>
                d.boxEdgeCoordinates)) -
          explicitFormulaRectangleBoxLeftEdgeIntegralSum f
            (data.map
              (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ =>
                d.boxEdgeCoordinates)) := by
      exact congrArg
        (fun z : ℂ =>
          explicitFormulaRectangleBoxRightEdgeIntegralSum f
              (data.map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ =>
                  d.boxEdgeCoordinates)) - z)
        hleft
    _ =
        explicitFormulaRectangleBoxRightEdgeIntegralSum f boxes -
          explicitFormulaRectangleBoxLeftEdgeIntegralSum f
            (data.map
              (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ =>
                d.boxEdgeCoordinates)) := by
      exact congrArg
        (fun z : List ExplicitFormulaRectangleEndpointDataBoxEdge =>
          explicitFormulaRectangleBoxRightEdgeIntegralSum f z -
            explicitFormulaRectangleBoxLeftEdgeIntegralSum f
              (data.map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ρ =>
                  d.boxEdgeCoordinates)))
        hboxes
    _ =
        explicitFormulaRectangleBoxRightEdgeIntegralSum f boxes -
          explicitFormulaRectangleBoxLeftEdgeIntegralSum f boxes := by
      exact congrArg
        (fun z : List ExplicitFormulaRectangleEndpointDataBoxEdge =>
          explicitFormulaRectangleBoxRightEdgeIntegralSum f boxes -
            explicitFormulaRectangleBoxLeftEdgeIntegralSum f z)
        hboxes

/-- Horizontal grouped contribution of one selected box-coordinate row. -/
noncomputable def explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ)
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ)) : ℂ :=
  explicitFormulaRectangleBoxBottomEdgeIntegralSum f
      (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs) -
    explicitFormulaRectangleBoxTopEdgeIntegralSum f
      (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs)

/-- Vertical grouped contribution of one selected box-coordinate row. -/
noncomputable def explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ)
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ)) : ℂ :=
  explicitFormulaRectangleBoxRightEdgeIntegralSum f
      (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs) -
    explicitFormulaRectangleBoxLeftEdgeIntegralSum f
      (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs)

/-- Horizontal grouped contribution of one selected box-coordinate cell. -/
noncomputable def explicitFormulaRectangleSelectedBoxCoordinatesHorizontalCellContribution
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) : ℂ :=
  if _homit :
      explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
    explicitFormulaRectangleBoxBottomEdgeIntegral f
        (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
          ExplicitFormulaRectangleEndpointDataBoxEdge) -
      explicitFormulaRectangleBoxTopEdgeIntegral f
        (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
          ExplicitFormulaRectangleEndpointDataBoxEdge)
  else
    0

/-- Vertical grouped contribution of one selected box-coordinate cell. -/
noncomputable def explicitFormulaRectangleSelectedBoxCoordinatesVerticalCellContribution
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) : ℂ :=
  if _homit :
      explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
    explicitFormulaRectangleBoxRightEdgeIntegral f
        (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
          ExplicitFormulaRectangleEndpointDataBoxEdge) -
      explicitFormulaRectangleBoxLeftEdgeIntegral f
        (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
          ExplicitFormulaRectangleEndpointDataBoxEdge)
  else
    0

/-- Fixed-row horizontal box contribution is zero over an empty vertical-pair list. -/
theorem explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution_nil
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :
    explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution
        f xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ)) =
      0 :=
  explicitFormulaRectangleSelectedBoxEdgeCoordinatesHorizontalContribution_fixedX_nil f xpair

/-- Fixed-row vertical box contribution is zero over an empty vertical-pair list. -/
theorem explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution_nil
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :
    explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution
        f xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ)) =
      0 :=
  explicitFormulaRectangleSelectedBoxEdgeCoordinatesVerticalContribution_fixedX_nil f xpair

/-- Fixed-row horizontal box contribution over a cons vertical-pair list splits into the
selected head-cell contribution and the row tail. -/
theorem explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution_cons
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ)) :
    explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution
        f xpair (ypair :: rest) =
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalCellContribution
        f xpair ypair +
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution
          f xpair rest := by
  have hcons :
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution
          f xpair (ypair :: rest) =
        if homit :
            explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
          (explicitFormulaRectangleBoxBottomEdgeIntegral f
              (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
                ExplicitFormulaRectangleEndpointDataBoxEdge) -
            explicitFormulaRectangleBoxTopEdgeIntegral f
              (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
                ExplicitFormulaRectangleEndpointDataBoxEdge)) +
            explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution
              f xpair rest
        else
          explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution
            f xpair rest :=
    explicitFormulaRectangleSelectedBoxEdgeCoordinatesHorizontalContribution_fixedX_cons
      f xpair ypair rest
  if homit :
      explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
    calc
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution
          f xpair (ypair :: rest) =
          (explicitFormulaRectangleBoxBottomEdgeIntegral f
              (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
                ExplicitFormulaRectangleEndpointDataBoxEdge) -
            explicitFormulaRectangleBoxTopEdgeIntegral f
              (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
                ExplicitFormulaRectangleEndpointDataBoxEdge)) +
            explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution
              f xpair rest := by
        exact hcons
      _ =
          explicitFormulaRectangleSelectedBoxCoordinatesHorizontalCellContribution
            f xpair ypair +
          explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution
            f xpair rest := by
        rfl
  else
    calc
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution
          f xpair (ypair :: rest) =
          explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution
            f xpair rest := by
        exact hcons
      _ =
          0 +
            explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution
              f xpair rest := by
        exact
          (zero_add
            (explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution
              f xpair rest)).symm
      _ =
          explicitFormulaRectangleSelectedBoxCoordinatesHorizontalCellContribution
            f xpair ypair +
          explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution
            f xpair rest := by
        rfl

/-- Fixed-row vertical box contribution over a cons vertical-pair list splits into the
selected head-cell contribution and the row tail. -/
theorem explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution_cons
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ)) :
    explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution
        f xpair (ypair :: rest) =
      explicitFormulaRectangleSelectedBoxCoordinatesVerticalCellContribution
        f xpair ypair +
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution
          f xpair rest := by
  have hcons :
      explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution
          f xpair (ypair :: rest) =
        if homit :
            explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
          (explicitFormulaRectangleBoxRightEdgeIntegral f
              (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
                ExplicitFormulaRectangleEndpointDataBoxEdge) -
            explicitFormulaRectangleBoxLeftEdgeIntegral f
              (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
                ExplicitFormulaRectangleEndpointDataBoxEdge)) +
            explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution
              f xpair rest
        else
          explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution
            f xpair rest :=
    explicitFormulaRectangleSelectedBoxEdgeCoordinatesVerticalContribution_fixedX_cons
      f xpair ypair rest
  if homit :
      explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
    calc
      explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution
          f xpair (ypair :: rest) =
          (explicitFormulaRectangleBoxRightEdgeIntegral f
              (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
                ExplicitFormulaRectangleEndpointDataBoxEdge) -
            explicitFormulaRectangleBoxLeftEdgeIntegral f
              (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
                ExplicitFormulaRectangleEndpointDataBoxEdge)) +
            explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution
              f xpair rest := by
        exact hcons
      _ =
          explicitFormulaRectangleSelectedBoxCoordinatesVerticalCellContribution
            f xpair ypair +
          explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution
            f xpair rest := by
        rfl
  else
    calc
      explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution
          f xpair (ypair :: rest) =
          explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution
            f xpair rest := by
        exact hcons
      _ =
          0 +
            explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution
              f xpair rest := by
        exact
          (zero_add
            (explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution
              f xpair rest)).symm
      _ =
          explicitFormulaRectangleSelectedBoxCoordinatesVerticalCellContribution
            f xpair ypair +
          explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution
            f xpair rest := by
        rfl

/-- Fixed-row horizontal box contribution is the recursive list sum of selected
horizontal one-cell contributions. -/
theorem explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution_eq_listSum
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :
    ∀ ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ),
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution
          f xpair ypairs =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            explicitFormulaRectangleSelectedBoxCoordinatesHorizontalCellContribution
              f xpair ypair)
          ypairs
  | [] =>
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution_nil f xpair
  | ypair :: rest => by
      have hhead :
          explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution
              f xpair (ypair :: rest) =
            explicitFormulaRectangleSelectedBoxCoordinatesHorizontalCellContribution
                f xpair ypair +
              explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution
                f xpair rest :=
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution_cons
          f xpair ypair rest
      have htail :
          explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution
              f xpair rest =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                explicitFormulaRectangleSelectedBoxCoordinatesHorizontalCellContribution
                  f xpair ypair)
              rest :=
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution_eq_listSum
          f xpair rest
      calc
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution
            f xpair (ypair :: rest) =
            explicitFormulaRectangleSelectedBoxCoordinatesHorizontalCellContribution
                f xpair ypair +
              explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution
                f xpair rest := by
          exact hhead
        _ =
            explicitFormulaRectangleSelectedBoxCoordinatesHorizontalCellContribution
                f xpair ypair +
              explicitFormulaRectangleListSum
                (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                  explicitFormulaRectangleSelectedBoxCoordinatesHorizontalCellContribution
                    f xpair ypair)
                rest := by
          exact congrArg
            (fun z : ℂ =>
              explicitFormulaRectangleSelectedBoxCoordinatesHorizontalCellContribution
                f xpair ypair + z)
            htail
        _ =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                explicitFormulaRectangleSelectedBoxCoordinatesHorizontalCellContribution
                  f xpair ypair)
              (ypair :: rest) := by
          rfl

/-- Fixed-row vertical box contribution is the recursive list sum of selected vertical
one-cell contributions. -/
theorem explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution_eq_listSum
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) :
    ∀ ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ),
      explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution
          f xpair ypairs =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
            explicitFormulaRectangleSelectedBoxCoordinatesVerticalCellContribution
              f xpair ypair)
          ypairs
  | [] =>
      explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution_nil f xpair
  | ypair :: rest => by
      have hhead :
          explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution
              f xpair (ypair :: rest) =
            explicitFormulaRectangleSelectedBoxCoordinatesVerticalCellContribution
                f xpair ypair +
              explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution
                f xpair rest :=
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution_cons
          f xpair ypair rest
      have htail :
          explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution
              f xpair rest =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                explicitFormulaRectangleSelectedBoxCoordinatesVerticalCellContribution
                  f xpair ypair)
              rest :=
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution_eq_listSum
          f xpair rest
      calc
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution
            f xpair (ypair :: rest) =
            explicitFormulaRectangleSelectedBoxCoordinatesVerticalCellContribution
                f xpair ypair +
              explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution
                f xpair rest := by
          exact hhead
        _ =
            explicitFormulaRectangleSelectedBoxCoordinatesVerticalCellContribution
                f xpair ypair +
              explicitFormulaRectangleListSum
                (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                  explicitFormulaRectangleSelectedBoxCoordinatesVerticalCellContribution
                    f xpair ypair)
                rest := by
          exact congrArg
            (fun z : ℂ =>
              explicitFormulaRectangleSelectedBoxCoordinatesVerticalCellContribution
                f xpair ypair + z)
            htail
        _ =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                explicitFormulaRectangleSelectedBoxCoordinatesVerticalCellContribution
                  f xpair ypair)
              (ypair :: rest) := by
          rfl

/-- Recursive sum of horizontal grouped selected box-coordinate row contributions. -/
noncomputable def explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContributionSum
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ}
    (f : ZetaAdmissibleFunction) :
    List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) →
      List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) → ℂ
  | [], _ypairs => 0
  | xpair :: rest, ypairs =>
      explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution
        f xpair ypairs +
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContributionSum
          f rest ypairs

/-- Recursive sum of vertical grouped selected box-coordinate row contributions. -/
noncomputable def explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContributionSum
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ}
    (f : ZetaAdmissibleFunction) :
    List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ) →
      List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ) → ℂ
  | [], _ypairs => 0
  | xpair :: rest, ypairs =>
      explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution
        f xpair ypairs +
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContributionSum
          f rest ypairs

/-- The direct grouped horizontal box-coordinate sum over selected pair lists is the
recursive sum of fixed-row grouped horizontal contributions. -/
theorem explicitFormulaRectangleSelectedBoxCoordinatesHorizontalContribution_eq_rowSum
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ}
    (f : ZetaAdmissibleFunction) :
    ∀ xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ),
      ∀ ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ),
        explicitFormulaRectangleBoxBottomEdgeIntegralSum f
            (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
              xpairs ypairs) -
          explicitFormulaRectangleBoxTopEdgeIntegralSum f
            (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
              xpairs ypairs) =
            explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContributionSum
              f xpairs ypairs
  | [], ypairs => by
      exact
        explicitFormulaRectangleSelectedBoxEdgeCoordinatesHorizontalContribution_pairLists_nil
          f ypairs
  | xpair :: rest, ypairs => by
      have hsplit :
          explicitFormulaRectangleBoxBottomEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
                (xpair :: rest) ypairs) -
            explicitFormulaRectangleBoxTopEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
                (xpair :: rest) ypairs) =
          (explicitFormulaRectangleBoxBottomEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs) -
            explicitFormulaRectangleBoxTopEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs)) +
          (explicitFormulaRectangleBoxBottomEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs) -
            explicitFormulaRectangleBoxTopEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs)) :=
        explicitFormulaRectangleSelectedBoxEdgeCoordinatesHorizontalContribution_pairLists_cons
          f xpair rest ypairs
      have htail :
          explicitFormulaRectangleBoxBottomEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs) -
            explicitFormulaRectangleBoxTopEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs) =
              explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContributionSum
                f rest ypairs :=
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalContribution_eq_rowSum
          f rest ypairs
      calc
        explicitFormulaRectangleBoxBottomEdgeIntegralSum f
            (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
              (xpair :: rest) ypairs) -
          explicitFormulaRectangleBoxTopEdgeIntegralSum f
            (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
              (xpair :: rest) ypairs) =
          (explicitFormulaRectangleBoxBottomEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs) -
            explicitFormulaRectangleBoxTopEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs)) +
          (explicitFormulaRectangleBoxBottomEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs) -
            explicitFormulaRectangleBoxTopEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs)) := by
          exact hsplit
        _ =
          explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution
              f xpair ypairs +
            (explicitFormulaRectangleBoxBottomEdgeIntegralSum f
                (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs) -
              explicitFormulaRectangleBoxTopEdgeIntegralSum f
                (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs)) := by
          rfl
        _ =
          explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution
              f xpair ypairs +
            explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContributionSum
              f rest ypairs := by
          exact congrArg
            (fun z : ℂ =>
              explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution
                f xpair ypairs + z)
            htail
        _ =
          explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContributionSum
            f (xpair :: rest) ypairs := by
          rfl

/-- The direct grouped vertical box-coordinate sum over selected pair lists is the
recursive sum of fixed-row grouped vertical contributions. -/
theorem explicitFormulaRectangleSelectedBoxCoordinatesVerticalContribution_eq_rowSum
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ}
    (f : ZetaAdmissibleFunction) :
    ∀ xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ),
      ∀ ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ),
        explicitFormulaRectangleBoxRightEdgeIntegralSum f
            (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
              xpairs ypairs) -
          explicitFormulaRectangleBoxLeftEdgeIntegralSum f
            (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
              xpairs ypairs) =
            explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContributionSum
              f xpairs ypairs
  | [], ypairs => by
      exact
        explicitFormulaRectangleSelectedBoxEdgeCoordinatesVerticalContribution_pairLists_nil
          f ypairs
  | xpair :: rest, ypairs => by
      have hsplit :
          explicitFormulaRectangleBoxRightEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
                (xpair :: rest) ypairs) -
            explicitFormulaRectangleBoxLeftEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
                (xpair :: rest) ypairs) =
          (explicitFormulaRectangleBoxRightEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs) -
            explicitFormulaRectangleBoxLeftEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs)) +
          (explicitFormulaRectangleBoxRightEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs) -
            explicitFormulaRectangleBoxLeftEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs)) :=
        explicitFormulaRectangleSelectedBoxEdgeCoordinatesVerticalContribution_pairLists_cons
          f xpair rest ypairs
      have htail :
          explicitFormulaRectangleBoxRightEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs) -
            explicitFormulaRectangleBoxLeftEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs) =
              explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContributionSum
                f rest ypairs :=
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalContribution_eq_rowSum
          f rest ypairs
      calc
        explicitFormulaRectangleBoxRightEdgeIntegralSum f
            (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
              (xpair :: rest) ypairs) -
          explicitFormulaRectangleBoxLeftEdgeIntegralSum f
            (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
              (xpair :: rest) ypairs) =
          (explicitFormulaRectangleBoxRightEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs) -
            explicitFormulaRectangleBoxLeftEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs)) +
          (explicitFormulaRectangleBoxRightEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs) -
            explicitFormulaRectangleBoxLeftEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs)) := by
          exact hsplit
        _ =
          explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution
              f xpair ypairs +
            (explicitFormulaRectangleBoxRightEdgeIntegralSum f
                (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs) -
              explicitFormulaRectangleBoxLeftEdgeIntegralSum f
                (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs)) := by
          rfl
        _ =
          explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution
              f xpair ypairs +
            explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContributionSum
              f rest ypairs := by
          exact congrArg
            (fun z : ℂ =>
              explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution
                f xpair ypairs + z)
            htail
        _ =
          explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContributionSum
            f (xpair :: rest) ypairs := by
          rfl

/-- The recursive horizontal box-coordinate row contribution sum is the row-major double
sum of selected horizontal one-cell box-coordinate contributions. -/
theorem explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContributionSum_eq_rowMajorDoubleSum
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ}
    (f : ZetaAdmissibleFunction) :
    ∀ xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ),
      ∀ ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ),
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContributionSum
            f xpairs ypairs =
          explicitFormulaRectangleRowMajorDoubleSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                explicitFormulaRectangleSelectedBoxCoordinatesHorizontalCellContribution
                  f xpair ypair)
            xpairs ypairs
  | [], ypairs => by
      rfl
  | xpair :: rest, ypairs => by
      have hrow :
          explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution
              f xpair ypairs =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                explicitFormulaRectangleSelectedBoxCoordinatesHorizontalCellContribution
                  f xpair ypair)
              ypairs :=
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution_eq_listSum
          f xpair ypairs
      have htail :
          explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContributionSum
              f rest ypairs =
            explicitFormulaRectangleRowMajorDoubleSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                  explicitFormulaRectangleSelectedBoxCoordinatesHorizontalCellContribution
                    f xpair ypair)
              rest ypairs :=
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContributionSum_eq_rowMajorDoubleSum
          f rest ypairs
      calc
        explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContributionSum
            f (xpair :: rest) ypairs =
            explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContribution
                f xpair ypairs +
              explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContributionSum
                f rest ypairs := by
          rfl
        _ =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                explicitFormulaRectangleSelectedBoxCoordinatesHorizontalCellContribution
                  f xpair ypair)
              ypairs +
              explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContributionSum
                f rest ypairs := by
          exact congrArg
            (fun z : ℂ =>
              z +
                explicitFormulaRectangleSelectedBoxCoordinatesHorizontalRowContributionSum
                  f rest ypairs)
            hrow
        _ =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                explicitFormulaRectangleSelectedBoxCoordinatesHorizontalCellContribution
                  f xpair ypair)
              ypairs +
              explicitFormulaRectangleRowMajorDoubleSum
                (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                  fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                    explicitFormulaRectangleSelectedBoxCoordinatesHorizontalCellContribution
                      f xpair ypair)
                rest ypairs := by
          exact congrArg
            (fun z : ℂ =>
              explicitFormulaRectangleListSum
                (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                  explicitFormulaRectangleSelectedBoxCoordinatesHorizontalCellContribution
                    f xpair ypair)
                ypairs + z)
            htail
        _ =
            explicitFormulaRectangleRowMajorDoubleSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                  explicitFormulaRectangleSelectedBoxCoordinatesHorizontalCellContribution
                    f xpair ypair)
              (xpair :: rest) ypairs := by
          rfl

/-- The recursive vertical box-coordinate row contribution sum is the row-major double
sum of selected vertical one-cell box-coordinate contributions. -/
theorem explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContributionSum_eq_rowMajorDoubleSum
    {F : ExplicitFormulaContourFamily} {T ρ : ℝ}
    (f : ZetaAdmissibleFunction) :
    ∀ xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ),
      ∀ ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ρ),
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContributionSum
            f xpairs ypairs =
          explicitFormulaRectangleRowMajorDoubleSum
            (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
              fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                explicitFormulaRectangleSelectedBoxCoordinatesVerticalCellContribution
                  f xpair ypair)
            xpairs ypairs
  | [], ypairs => by
      rfl
  | xpair :: rest, ypairs => by
      have hrow :
          explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution
              f xpair ypairs =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                explicitFormulaRectangleSelectedBoxCoordinatesVerticalCellContribution
                  f xpair ypair)
              ypairs :=
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution_eq_listSum
          f xpair ypairs
      have htail :
          explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContributionSum
              f rest ypairs =
            explicitFormulaRectangleRowMajorDoubleSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                  explicitFormulaRectangleSelectedBoxCoordinatesVerticalCellContribution
                    f xpair ypair)
              rest ypairs :=
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContributionSum_eq_rowMajorDoubleSum
          f rest ypairs
      calc
        explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContributionSum
            f (xpair :: rest) ypairs =
            explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContribution
                f xpair ypairs +
              explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContributionSum
                f rest ypairs := by
          rfl
        _ =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                explicitFormulaRectangleSelectedBoxCoordinatesVerticalCellContribution
                  f xpair ypair)
              ypairs +
              explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContributionSum
                f rest ypairs := by
          exact congrArg
            (fun z : ℂ =>
              z +
                explicitFormulaRectangleSelectedBoxCoordinatesVerticalRowContributionSum
                  f rest ypairs)
            hrow
        _ =
            explicitFormulaRectangleListSum
              (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                explicitFormulaRectangleSelectedBoxCoordinatesVerticalCellContribution
                  f xpair ypair)
              ypairs +
              explicitFormulaRectangleRowMajorDoubleSum
                (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                  fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                    explicitFormulaRectangleSelectedBoxCoordinatesVerticalCellContribution
                      f xpair ypair)
                rest ypairs := by
          exact congrArg
            (fun z : ℂ =>
              explicitFormulaRectangleListSum
                (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                  explicitFormulaRectangleSelectedBoxCoordinatesVerticalCellContribution
                    f xpair ypair)
                ypairs + z)
            htail
        _ =
            explicitFormulaRectangleRowMajorDoubleSum
              (fun xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ρ =>
                fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ρ =>
                  explicitFormulaRectangleSelectedBoxCoordinatesVerticalCellContribution
                    f xpair ypair)
              (xpair :: rest) ypairs := by
          rfl

/-- Oriented outer horizontal side contribution in the selected box-coordinate
normalization. -/
noncomputable def explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaBottomLineIntegral f (F.rectangle T) -
    zetaCompletedExplicitFormulaTopLineIntegral f (F.rectangle T)

/-- Raw square-hole horizontal side contribution in the selected box-coordinate
normalization. -/
noncomputable def explicitFormulaRectangleSelectedBoxCoordinatesHorizontalHoleSideSum
    (f : ZetaAdmissibleFunction) (T ρ : ℝ) : ℂ :=
  explicitFormulaRectangleRawInscribedSquareEndpointDataBoxBottomEdgeFinsetSum f T ρ -
    explicitFormulaRectangleRawInscribedSquareEndpointDataBoxTopEdgeFinsetSum f T ρ

/-- Oriented outer vertical side contribution in the selected box-coordinate
normalization. -/
noncomputable def explicitFormulaRectangleSelectedBoxCoordinatesVerticalOuterSideSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (T : ℝ) : ℂ :=
  zetaCompletedExplicitFormulaRightLineIntegral f (F.rectangle T) * Complex.I -
    zetaCompletedExplicitFormulaLeftLineIntegral f (F.rectangle T) * Complex.I

/-- Raw square-hole vertical side contribution in the selected box-coordinate
normalization. -/
noncomputable def explicitFormulaRectangleSelectedBoxCoordinatesVerticalHoleSideSum
    (f : ZetaAdmissibleFunction) (T ρ : ℝ) : ℂ :=
  explicitFormulaRectangleRawInscribedSquareEndpointDataBoxRightEdgeFinsetSum f T ρ -
    explicitFormulaRectangleRawInscribedSquareEndpointDataBoxLeftEdgeFinsetSum f T ρ

/-- Exposed horizontal box-coordinate contribution of the sorted selected-cell grid.

This is the semantic finite-grid target for row-major horizontal cancellation: all
internal horizontal sides have canceled, leaving the oriented outer bottom/top sides and
the raw square-hole bottom/top sides. -/
noncomputable def explicitFormulaRectangleSelectedBoxCoordinatesHorizontalExposedSideSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (T ρ : ℝ) : ℂ :=
  explicitFormulaRectangleSelectedBoxCoordinatesHorizontalOuterSideSum f F T -
    explicitFormulaRectangleSelectedBoxCoordinatesHorizontalHoleSideSum f T ρ

/-- Exposed vertical box-coordinate contribution of the sorted selected-cell grid.

This is the semantic finite-grid target for row-major vertical cancellation: all internal
vertical sides have canceled, leaving the oriented outer right/left sides and the raw
square-hole right/left sides. -/
noncomputable def explicitFormulaRectangleSelectedBoxCoordinatesVerticalExposedSideSum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily)
    (T ρ : ℝ) : ℂ :=
  explicitFormulaRectangleSelectedBoxCoordinatesVerticalOuterSideSum f F T -
    explicitFormulaRectangleSelectedBoxCoordinatesVerticalHoleSideSum f T ρ

/-- Moving from grouped outer-minus-hole side sums to the exposed-side target
normal form is pure additive algebra. -/
theorem explicitFormulaRectangleOuterSubHoleSideAlgebra
    (outerLower outerUpper holeLower holeUpper : ℂ) :
    (outerLower - outerUpper) - (holeLower - holeUpper) =
      (outerLower - holeLower) - (outerUpper - holeUpper) := by
  calc
    (outerLower - outerUpper) - (holeLower - holeUpper) =
        (outerLower + -outerUpper) - (holeLower - holeUpper) := by
      exact congrArg
        (fun z : ℂ => z - (holeLower - holeUpper))
        (sub_eq_add_neg outerLower outerUpper)
    _ =
        (outerLower + -outerUpper) + -(holeLower - holeUpper) := by
      exact sub_eq_add_neg (outerLower + -outerUpper) (holeLower - holeUpper)
    _ =
        (outerLower + -outerUpper) + -(holeLower + -holeUpper) := by
      exact congrArg
        (fun z : ℂ => (outerLower + -outerUpper) + -z)
        (sub_eq_add_neg holeLower holeUpper)
    _ =
        (outerLower + -outerUpper) + (-holeLower + -(-holeUpper)) := by
      exact congrArg
        (fun z : ℂ => (outerLower + -outerUpper) + z)
        (neg_add holeLower (-holeUpper))
    _ =
        (outerLower + -outerUpper) + (-holeLower + holeUpper) := by
      exact congrArg
        (fun z : ℂ => (outerLower + -outerUpper) + (-holeLower + z))
        (neg_neg holeUpper)
    _ =
        outerLower + (-outerUpper + (-holeLower + holeUpper)) := by
      exact add_assoc outerLower (-outerUpper) (-holeLower + holeUpper)
    _ =
        outerLower + ((-outerUpper + -holeLower) + holeUpper) := by
      exact congrArg
        (fun z : ℂ => outerLower + z)
        (add_assoc (-outerUpper) (-holeLower) holeUpper).symm
    _ =
        outerLower + ((-holeLower + -outerUpper) + holeUpper) := by
      exact congrArg
        (fun z : ℂ => outerLower + (z + holeUpper))
        (add_comm (-outerUpper) (-holeLower))
    _ =
        outerLower + (-holeLower + (-outerUpper + holeUpper)) := by
      exact congrArg
        (fun z : ℂ => outerLower + z)
        (add_assoc (-holeLower) (-outerUpper) holeUpper)
    _ =
        (outerLower + -holeLower) + (-outerUpper + holeUpper) := by
      exact (add_assoc outerLower (-holeLower) (-outerUpper + holeUpper)).symm
    _ =
        (outerLower - holeLower) + (-outerUpper + holeUpper) := by
      exact congrArg
        (fun z : ℂ => z + (-outerUpper + holeUpper))
        (sub_eq_add_neg outerLower holeLower).symm
    _ =
        (outerLower - holeLower) + -(outerUpper + -holeUpper) := by
      exact congrArg
        (fun z : ℂ => (outerLower - holeLower) + z)
        (by
          calc
            -outerUpper + holeUpper = -outerUpper + -(-holeUpper) := by
              exact congrArg (fun z : ℂ => -outerUpper + z) (neg_neg holeUpper).symm
            _ = -(outerUpper + -holeUpper) := by
              exact (neg_add outerUpper (-holeUpper)).symm)
    _ =
        (outerLower - holeLower) + -(outerUpper - holeUpper) := by
      exact congrArg
        (fun z : ℂ => (outerLower - holeLower) + -z)
        (sub_eq_add_neg outerUpper holeUpper).symm
    _ =
        (outerLower - holeLower) - (outerUpper - holeUpper) := by
      exact
        (sub_eq_add_neg
          (outerLower - holeLower)
          (outerUpper - holeUpper)).symm

/-- Recursive list sums distribute across pointwise subtraction. -/
theorem explicitFormulaRectangleListSum_sub
    {α : Type} (left right : α → ℂ) :
    ∀ xs : List α,
      explicitFormulaRectangleListSum (fun x : α => left x - right x) xs =
        explicitFormulaRectangleListSum left xs -
          explicitFormulaRectangleListSum right xs
  | [] => by
      rfl
  | x :: rest => by
      have htail :
          explicitFormulaRectangleListSum (fun x : α => left x - right x) rest =
            explicitFormulaRectangleListSum left rest -
              explicitFormulaRectangleListSum right rest :=
        explicitFormulaRectangleListSum_sub left right rest
      calc
        explicitFormulaRectangleListSum (fun x : α => left x - right x) (x :: rest) =
            (left x - right x) +
              explicitFormulaRectangleListSum (fun x : α => left x - right x) rest := by
          rfl
        _ =
            (left x - right x) +
              (explicitFormulaRectangleListSum left rest -
                explicitFormulaRectangleListSum right rest) := by
          exact congrArg (fun z : ℂ => (left x - right x) + z) htail
        _ =
            (left x + explicitFormulaRectangleListSum left rest) -
              (right x + explicitFormulaRectangleListSum right rest) := by
          exact
            (explicitFormulaRectangleBoxHorizontalContribution_consAlgebra
              (left x)
              (right x)
              (explicitFormulaRectangleListSum left rest)
              (explicitFormulaRectangleListSum right rest)).symm
        _ =
            explicitFormulaRectangleListSum left (x :: rest) -
              explicitFormulaRectangleListSum right (x :: rest) := by
          rfl

/-- Recursive list sum of the constant zero function is zero. -/
theorem explicitFormulaRectangleListSum_zero
    {α : Type} :
    ∀ xs : List α,
      explicitFormulaRectangleListSum (fun _x : α => (0 : ℂ)) xs = 0
  | [] => by
      rfl
  | x :: rest => by
      have htail :
          explicitFormulaRectangleListSum (fun _x : α => (0 : ℂ)) rest = 0 :=
        explicitFormulaRectangleListSum_zero rest
      calc
        explicitFormulaRectangleListSum (fun _x : α => (0 : ℂ)) (x :: rest) =
            0 + explicitFormulaRectangleListSum (fun _x : α => (0 : ℂ)) rest := by
          rfl
        _ = 0 + 0 := by
          exact congrArg (fun z : ℂ => 0 + z) htail
        _ = 0 := by
          exact zero_add 0

/-- Elementary additive cancellation: if `a + b = c`, then `a = c - b`. -/
theorem explicitFormulaRectangle_add_eq_to_eq_sub
    (a b c : ℂ) (h : a + b = c) :
    a = c - b := by
  calc
    a = (a + b) - b := by
      exact (add_sub_cancel_right a b).symm
    _ = c - b := by
      exact congrArg (fun z : ℂ => z - b) h

/-- A recursive list sum splits into the part selected by a decidable predicate and the
part rejected by that predicate. -/
theorem explicitFormulaRectangleListSum_select_add_reject
    {α : Type} (P : α → Prop) [DecidablePred P] (g : α → ℂ) :
    ∀ xs : List α,
      explicitFormulaRectangleListSum
          (fun x : α => if _h : P x then g x else 0) xs +
        explicitFormulaRectangleListSum
          (fun x : α => if _h : P x then 0 else g x) xs =
        explicitFormulaRectangleListSum g xs
  | [] => by
      rfl
  | x :: rest => by
      have htail :
          explicitFormulaRectangleListSum
              (fun x : α => if _h : P x then g x else 0) rest +
            explicitFormulaRectangleListSum
              (fun x : α => if _h : P x then 0 else g x) rest =
            explicitFormulaRectangleListSum g rest :=
        explicitFormulaRectangleListSum_select_add_reject P g rest
      by_cases hx : P x
      · calc
          explicitFormulaRectangleListSum
              (fun x : α => if _h : P x then g x else 0) (x :: rest) +
            explicitFormulaRectangleListSum
              (fun x : α => if _h : P x then 0 else g x) (x :: rest) =
              (g x +
                  explicitFormulaRectangleListSum
                    (fun x : α => if _h : P x then g x else 0) rest) +
                (0 +
                  explicitFormulaRectangleListSum
                    (fun x : α => if _h : P x then 0 else g x) rest) := by
            rfl
          _ =
              (g x +
                  explicitFormulaRectangleListSum
                    (fun x : α => if _h : P x then g x else 0) rest) +
                explicitFormulaRectangleListSum
                  (fun x : α => if _h : P x then 0 else g x) rest := by
            exact congrArg
              (fun z : ℂ =>
                (g x +
                    explicitFormulaRectangleListSum
                      (fun x : α => if _h : P x then g x else 0) rest) + z)
              (zero_add
                (explicitFormulaRectangleListSum
                  (fun x : α => if _h : P x then 0 else g x) rest))
          _ =
              g x +
                (explicitFormulaRectangleListSum
                    (fun x : α => if _h : P x then g x else 0) rest +
                  explicitFormulaRectangleListSum
                    (fun x : α => if _h : P x then 0 else g x) rest) := by
            exact
              (add_assoc
                (g x)
                (explicitFormulaRectangleListSum
                  (fun x : α => if _h : P x then g x else 0) rest)
                (explicitFormulaRectangleListSum
                  (fun x : α => if _h : P x then 0 else g x) rest))
          _ = g x + explicitFormulaRectangleListSum g rest := by
            exact congrArg (fun z : ℂ => g x + z) htail
          _ = explicitFormulaRectangleListSum g (x :: rest) := by
            rfl
      · calc
          explicitFormulaRectangleListSum
              (fun x : α => if _h : P x then g x else 0) (x :: rest) +
            explicitFormulaRectangleListSum
              (fun x : α => if _h : P x then 0 else g x) (x :: rest) =
              (0 +
                  explicitFormulaRectangleListSum
                    (fun x : α => if _h : P x then g x else 0) rest) +
                (g x +
                  explicitFormulaRectangleListSum
                    (fun x : α => if _h : P x then 0 else g x) rest) := by
            rfl
          _ =
              explicitFormulaRectangleListSum
                    (fun x : α => if _h : P x then g x else 0) rest +
                (g x +
                  explicitFormulaRectangleListSum
                    (fun x : α => if _h : P x then 0 else g x) rest) := by
            exact congrArg
              (fun z : ℂ =>
                z +
                  (g x +
                    explicitFormulaRectangleListSum
                      (fun x : α => if _h : P x then 0 else g x) rest))
              (zero_add
                (explicitFormulaRectangleListSum
                  (fun x : α => if _h : P x then g x else 0) rest))
          _ =
              g x +
                (explicitFormulaRectangleListSum
                    (fun x : α => if _h : P x then g x else 0) rest +
                  explicitFormulaRectangleListSum
                    (fun x : α => if _h : P x then 0 else g x) rest) := by
            calc
              explicitFormulaRectangleListSum
                    (fun x : α => if _h : P x then g x else 0) rest +
                (g x +
                  explicitFormulaRectangleListSum
                    (fun x : α => if _h : P x then 0 else g x) rest) =
                  (explicitFormulaRectangleListSum
                      (fun x : α => if _h : P x then g x else 0) rest +
                    g x) +
                    explicitFormulaRectangleListSum
                      (fun x : α => if _h : P x then 0 else g x) rest := by
                exact
                  (add_assoc
                    (explicitFormulaRectangleListSum
                      (fun x : α => if _h : P x then g x else 0) rest)
                    (g x)
                    (explicitFormulaRectangleListSum
                      (fun x : α => if _h : P x then 0 else g x) rest)).symm
              _ =
                  (g x +
                    explicitFormulaRectangleListSum
                      (fun x : α => if _h : P x then g x else 0) rest) +
                    explicitFormulaRectangleListSum
                      (fun x : α => if _h : P x then 0 else g x) rest := by
                exact congrArg
                  (fun z : ℂ =>
                    z +
                      explicitFormulaRectangleListSum
                        (fun x : α => if _h : P x then 0 else g x) rest)
                  (add_comm
                    (explicitFormulaRectangleListSum
                      (fun x : α => if _h : P x then g x else 0) rest)
                    (g x))
              _ =
                  g x +
                    (explicitFormulaRectangleListSum
                        (fun x : α => if _h : P x then g x else 0) rest +
                      explicitFormulaRectangleListSum
                        (fun x : α => if _h : P x then 0 else g x) rest) := by
                exact
                  add_assoc
                    (g x)
                    (explicitFormulaRectangleListSum
                      (fun x : α => if _h : P x then g x else 0) rest)
                    (explicitFormulaRectangleListSum
                      (fun x : α => if _h : P x then 0 else g x) rest)
          _ = g x + explicitFormulaRectangleListSum g rest := by
            exact congrArg (fun z : ℂ => g x + z) htail
          _ = explicitFormulaRectangleListSum g (x :: rest) := by
            rfl

/-- The selected part of a recursive list sum is the total sum minus the rejected part. -/
theorem explicitFormulaRectangleListSum_select_eq_total_sub_reject
    {α : Type} (P : α → Prop) [DecidablePred P] (g : α → ℂ)
    (xs : List α) :
    explicitFormulaRectangleListSum
        (fun x : α => if _h : P x then g x else 0) xs =
      explicitFormulaRectangleListSum g xs -
        explicitFormulaRectangleListSum
          (fun x : α => if _h : P x then 0 else g x) xs :=
  explicitFormulaRectangle_add_eq_to_eq_sub
    (explicitFormulaRectangleListSum
      (fun x : α => if _h : P x then g x else 0) xs)
    (explicitFormulaRectangleListSum
      (fun x : α => if _h : P x then 0 else g x) xs)
    (explicitFormulaRectangleListSum g xs)
    (explicitFormulaRectangleListSum_select_add_reject P g xs)

/-- Paired selected scans are paired total scans with the paired rejected scans removed. -/

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
