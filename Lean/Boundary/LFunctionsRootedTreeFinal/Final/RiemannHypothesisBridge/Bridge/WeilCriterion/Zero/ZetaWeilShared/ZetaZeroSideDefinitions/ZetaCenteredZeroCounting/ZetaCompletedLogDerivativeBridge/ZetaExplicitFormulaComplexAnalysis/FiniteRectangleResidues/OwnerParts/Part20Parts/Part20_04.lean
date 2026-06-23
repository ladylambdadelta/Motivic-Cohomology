import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part20Parts.Part20_03

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
## Part20 04: SelectedCoordinateLists
-/

def explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε) →
      List ExplicitFormulaRectangleHorizontalEndpointDataEdge
  | [] => []
  | ypair :: rest =>
      if _homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        ((xpair.x₀, xpair.x₁), ypair.y₀) ::
          explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair rest
      else
        explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair rest

/-- Top horizontal coordinate labels selected from one fixed horizontal adjacent-pair row,
with the same coordinate-omission filter as the selected cell list. -/
def explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε) →
      List ExplicitFormulaRectangleHorizontalEndpointDataEdge
  | [] => []
  | ypair :: rest =>
      if _homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        ((xpair.x₀, xpair.x₁), ypair.y₁) ::
          explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair rest
      else
        explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair rest

/-- Selected bottom coordinate labels over a fixed horizontal span are an ordinary
filtered recursive sum. -/
theorem explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX_integralSum_eq_listSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    ∀ ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε),
      explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair ypairs) =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
            if _homit :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁), ypair.y₀)
            else
              0)
          ypairs
  | [] => by
      rfl
  | ypair :: rest => by
      by_cases homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair
      · exact congrArg
          (fun z : ℂ =>
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
              f ((xpair.x₀, xpair.x₁), ypair.y₀) + z)
          (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX_integralSum_eq_listSum
            f xpair rest)
      · calc
          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX
                xpair (ypair :: rest)) =
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
                (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair rest) := by
            rfl
          _ =
              explicitFormulaRectangleListSum
                (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                  if _homit :
                      explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission
                        xpair ypair then
                    explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                      f ((xpair.x₀, xpair.x₁), ypair.y₀)
                  else
                    0)
                rest := by
            exact
              explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX_integralSum_eq_listSum
                f xpair rest
          _ =
              0 +
                explicitFormulaRectangleListSum
                  (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                    if _homit :
                        explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission
                          xpair ypair then
                      explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                        f ((xpair.x₀, xpair.x₁), ypair.y₀)
                    else
                      0)
                  rest := by
            exact (zero_add _).symm

/-- Selected top coordinate labels over a fixed horizontal span are an ordinary filtered
recursive sum. -/
theorem explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX_integralSum_eq_listSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    ∀ ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε),
      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
          (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair ypairs) =
        explicitFormulaRectangleListSum
          (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
            if _homit :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁), ypair.y₁)
            else
              0)
          ypairs
  | [] => by
      rfl
  | ypair :: rest => by
      by_cases homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair
      · exact congrArg
          (fun z : ℂ =>
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
              f ((xpair.x₀, xpair.x₁), ypair.y₁) + z)
          (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX_integralSum_eq_listSum
            f xpair rest)
      · calc
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
              (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX
                xpair (ypair :: rest)) =
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
                (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair rest) := by
            rfl
          _ =
              explicitFormulaRectangleListSum
                (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                  if _homit :
                      explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission
                        xpair ypair then
                    explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                      f ((xpair.x₀, xpair.x₁), ypair.y₁)
                  else
                    0)
                rest := by
            exact
              explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX_integralSum_eq_listSum
                f xpair rest
          _ =
              0 +
                explicitFormulaRectangleListSum
                  (fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                    if _homit :
                        explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission
                          xpair ypair then
                      explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                        f ((xpair.x₀, xpair.x₁), ypair.y₁)
                    else
                      0)
                  rest := by
            exact (zero_add _).symm

/-- The selected endpoint-data list for one fixed horizontal row has exactly the selected
bottom horizontal coordinate labels. -/
theorem explicitFormulaRectangleSelectedEndpointDataFixedX_bottomEdgeCoordinates
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    ∀ ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε),
      (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair ypairs)).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.bottomEdgeCoordinates) =
        explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair ypairs
  | [] => rfl
  | ypair :: rest =>
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        congrArg
          (fun edges : List ExplicitFormulaRectangleHorizontalEndpointDataEdge =>
            ((xpair.x₀, xpair.x₁), ypair.y₀) :: edges)
          (explicitFormulaRectangleSelectedEndpointDataFixedX_bottomEdgeCoordinates
            xpair rest)
      else
        explicitFormulaRectangleSelectedEndpointDataFixedX_bottomEdgeCoordinates
          xpair rest

/-- The selected endpoint-data list for one fixed horizontal row has exactly the selected
top horizontal coordinate labels. -/
theorem explicitFormulaRectangleSelectedEndpointDataFixedX_topEdgeCoordinates
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    ∀ ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε),
      (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair ypairs)).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.topEdgeCoordinates) =
        explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair ypairs
  | [] => rfl
  | ypair :: rest =>
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        congrArg
          (fun edges : List ExplicitFormulaRectangleHorizontalEndpointDataEdge =>
            ((xpair.x₀, xpair.x₁), ypair.y₁) :: edges)
          (explicitFormulaRectangleSelectedEndpointDataFixedX_topEdgeCoordinates
            xpair rest)
      else
        explicitFormulaRectangleSelectedEndpointDataFixedX_topEdgeCoordinates
          xpair rest

/-- Bottom horizontal coordinate labels selected from crossed adjacent-pair lists. -/
def explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfPairLists
    {F : ExplicitFormulaContourFamily} {T ε : ℝ} :
    List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) →
      List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε) →
        List ExplicitFormulaRectangleHorizontalEndpointDataEdge
  | [], _ypairs => []
  | xpair :: rest, ypairs =>
      explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair ypairs ++
        explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfPairLists rest ypairs

/-- Top horizontal coordinate labels selected from crossed adjacent-pair lists. -/
def explicitFormulaRectangleSelectedTopEdgeCoordinatesOfPairLists
    {F : ExplicitFormulaContourFamily} {T ε : ℝ} :
    List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) →
      List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε) →
        List ExplicitFormulaRectangleHorizontalEndpointDataEdge
  | [], _ypairs => []
  | xpair :: rest, ypairs =>
      explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair ypairs ++
        explicitFormulaRectangleSelectedTopEdgeCoordinatesOfPairLists rest ypairs

/-- The selected endpoint-data list for crossed adjacent-pair lists has exactly the
selected bottom horizontal coordinate labels. -/
theorem explicitFormulaRectangleSelectedEndpointDataPairLists_bottomEdgeCoordinates
    {F : ExplicitFormulaContourFamily} {T ε : ℝ} :
    ∀ (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
      (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)),
      (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          xpairs ypairs)).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.bottomEdgeCoordinates) =
        explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfPairLists xpairs ypairs
  | [], ypairs => rfl
  | xpair :: rest, ypairs =>
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
      have hcells :
          explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              (xpair :: rest) ypairs =
            explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
              xpair ypairs ++
              explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
                rest ypairs := by
        rfl
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
      have hlist : whole = firstRow ++ remaining := by
        exact
          Eq.trans
            (congrArg
              (fun cells : List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε) =>
                explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells cells)
              hcells)
            hmap
      calc
        whole.map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
              d.bottomEdgeCoordinates) =
            (firstRow ++ remaining).map
              (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                d.bottomEdgeCoordinates) := by
          exact
            congrArg
              (fun data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) =>
                data.map
                  (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                    d.bottomEdgeCoordinates))
              hlist
        _ =
            firstRow.map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.bottomEdgeCoordinates) ++
              remaining.map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.bottomEdgeCoordinates) := by
          exact
            List.map_append
              (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                d.bottomEdgeCoordinates)
              firstRow
              remaining
        _ =
            explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair ypairs ++
              remaining.map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.bottomEdgeCoordinates) := by
          exact
            congrArg
              (fun edges : List ExplicitFormulaRectangleHorizontalEndpointDataEdge =>
                edges ++ remaining.map
                    (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                      d.bottomEdgeCoordinates))
              (explicitFormulaRectangleSelectedEndpointDataFixedX_bottomEdgeCoordinates
                xpair ypairs)
        _ =
            explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair ypairs ++
              explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfPairLists rest ypairs := by
          exact
            congrArg
              (fun edges : List ExplicitFormulaRectangleHorizontalEndpointDataEdge =>
                explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair ypairs ++
                  edges)
              (explicitFormulaRectangleSelectedEndpointDataPairLists_bottomEdgeCoordinates
                rest ypairs)

/-- The selected endpoint-data list for crossed adjacent-pair lists has exactly the
selected top horizontal coordinate labels. -/
theorem explicitFormulaRectangleSelectedEndpointDataPairLists_topEdgeCoordinates
    {F : ExplicitFormulaContourFamily} {T ε : ℝ} :
    ∀ (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
      (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)),
      (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          xpairs ypairs)).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.topEdgeCoordinates) =
        explicitFormulaRectangleSelectedTopEdgeCoordinatesOfPairLists xpairs ypairs
  | [], ypairs => rfl
  | xpair :: rest, ypairs =>
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
      have hcells :
          explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              (xpair :: rest) ypairs =
            explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
              xpair ypairs ++
              explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
                rest ypairs := by
        rfl
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
      have hlist : whole = firstRow ++ remaining := by
        exact
          Eq.trans
            (congrArg
              (fun cells : List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε) =>
                explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells cells)
              hcells)
            hmap
      calc
        whole.map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
              d.topEdgeCoordinates) =
            (firstRow ++ remaining).map
              (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                d.topEdgeCoordinates) := by
          exact
            congrArg
              (fun data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) =>
                data.map
                  (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                    d.topEdgeCoordinates))
              hlist
        _ =
            firstRow.map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.topEdgeCoordinates) ++
              remaining.map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.topEdgeCoordinates) := by
          exact
            List.map_append
              (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                d.topEdgeCoordinates)
              firstRow
              remaining
        _ =
            explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair ypairs ++
              remaining.map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.topEdgeCoordinates) := by
          exact
            congrArg
              (fun edges : List ExplicitFormulaRectangleHorizontalEndpointDataEdge =>
                edges ++ remaining.map
                    (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                      d.topEdgeCoordinates))
              (explicitFormulaRectangleSelectedEndpointDataFixedX_topEdgeCoordinates
                xpair ypairs)
        _ =
            explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair ypairs ++
              explicitFormulaRectangleSelectedTopEdgeCoordinatesOfPairLists rest ypairs := by
          exact
            congrArg
              (fun edges : List ExplicitFormulaRectangleHorizontalEndpointDataEdge =>
                explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair ypairs ++
                  edges)
              (explicitFormulaRectangleSelectedEndpointDataPairLists_topEdgeCoordinates
                rest ypairs)

/-- Left vertical coordinate labels selected from one fixed horizontal adjacent-pair row,
with the same coordinate-omission filter as the selected cell list. -/
def explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedX
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε) →
      List ExplicitFormulaRectangleVerticalEndpointDataEdge
  | [] => []
  | ypair :: rest =>
      if _homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        ((ypair.y₀, ypair.y₁), xpair.x₀) ::
          explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedX xpair rest
      else
        explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedX xpair rest

/-- Right vertical coordinate labels selected from one fixed horizontal adjacent-pair row,
with the same coordinate-omission filter as the selected cell list. -/
def explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedX
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε) →
      List ExplicitFormulaRectangleVerticalEndpointDataEdge
  | [] => []
  | ypair :: rest =>
      if _homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        ((ypair.y₀, ypair.y₁), xpair.x₁) ::
          explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedX xpair rest
      else
        explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedX xpair rest

/-- The selected endpoint-data list for one fixed horizontal row has exactly the selected
left vertical coordinate labels. -/
theorem explicitFormulaRectangleSelectedEndpointDataFixedX_leftEdgeCoordinates
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    ∀ ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε),
      (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair ypairs)).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.leftEdgeCoordinates) =
        explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedX xpair ypairs
  | [] => rfl
  | ypair :: rest =>
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        congrArg
          (fun edges : List ExplicitFormulaRectangleVerticalEndpointDataEdge =>
            ((ypair.y₀, ypair.y₁), xpair.x₀) :: edges)
          (explicitFormulaRectangleSelectedEndpointDataFixedX_leftEdgeCoordinates
            xpair rest)
      else
        explicitFormulaRectangleSelectedEndpointDataFixedX_leftEdgeCoordinates
          xpair rest

/-- The selected endpoint-data list for one fixed horizontal row has exactly the selected
right vertical coordinate labels. -/
theorem explicitFormulaRectangleSelectedEndpointDataFixedX_rightEdgeCoordinates
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    ∀ ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε),
      (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair ypairs)).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.rightEdgeCoordinates) =
        explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedX xpair ypairs
  | [] => rfl
  | ypair :: rest =>
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        congrArg
          (fun edges : List ExplicitFormulaRectangleVerticalEndpointDataEdge =>
            ((ypair.y₀, ypair.y₁), xpair.x₁) :: edges)
          (explicitFormulaRectangleSelectedEndpointDataFixedX_rightEdgeCoordinates
            xpair rest)
      else
        explicitFormulaRectangleSelectedEndpointDataFixedX_rightEdgeCoordinates
          xpair rest

/-- Left vertical coordinate labels selected from crossed adjacent-pair lists. -/
def explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfPairLists
    {F : ExplicitFormulaContourFamily} {T ε : ℝ} :
    List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) →
      List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε) →
        List ExplicitFormulaRectangleVerticalEndpointDataEdge
  | [], _ypairs => []
  | xpair :: rest, ypairs =>
      explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedX xpair ypairs ++
        explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfPairLists rest ypairs

/-- Right vertical coordinate labels selected from crossed adjacent-pair lists. -/
def explicitFormulaRectangleSelectedRightEdgeCoordinatesOfPairLists
    {F : ExplicitFormulaContourFamily} {T ε : ℝ} :
    List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) →
      List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε) →
        List ExplicitFormulaRectangleVerticalEndpointDataEdge
  | [], _ypairs => []
  | xpair :: rest, ypairs =>
      explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedX xpair ypairs ++
        explicitFormulaRectangleSelectedRightEdgeCoordinatesOfPairLists rest ypairs

/-- The selected endpoint-data list for crossed adjacent-pair lists has exactly the
selected left vertical coordinate labels. -/
theorem explicitFormulaRectangleSelectedEndpointDataPairLists_leftEdgeCoordinates
    {F : ExplicitFormulaContourFamily} {T ε : ℝ} :
    ∀ (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
      (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)),
      (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          xpairs ypairs)).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.leftEdgeCoordinates) =
        explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfPairLists xpairs ypairs
  | [], ypairs => rfl
  | xpair :: rest, ypairs =>
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
      have hcells :
          explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              (xpair :: rest) ypairs =
            explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
              xpair ypairs ++
              explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
                rest ypairs := by
        rfl
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
      have hlist : whole = firstRow ++ remaining := by
        exact
          Eq.trans
            (congrArg
              (fun cells : List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε) =>
                explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells cells)
              hcells)
            hmap
      calc
        whole.map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
              d.leftEdgeCoordinates) =
            (firstRow ++ remaining).map
              (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                d.leftEdgeCoordinates) := by
          exact
            congrArg
              (fun data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) =>
                data.map
                  (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                    d.leftEdgeCoordinates))
              hlist
        _ =
            firstRow.map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.leftEdgeCoordinates) ++
              remaining.map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.leftEdgeCoordinates) := by
          exact
            List.map_append
              (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                d.leftEdgeCoordinates)
              firstRow
              remaining
        _ =
            explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedX xpair ypairs ++
              remaining.map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.leftEdgeCoordinates) := by
          exact
            congrArg
              (fun edges : List ExplicitFormulaRectangleVerticalEndpointDataEdge =>
                edges ++ remaining.map
                    (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                      d.leftEdgeCoordinates))
              (explicitFormulaRectangleSelectedEndpointDataFixedX_leftEdgeCoordinates
                xpair ypairs)
        _ =
            explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedX xpair ypairs ++
              explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfPairLists rest ypairs := by
          exact
            congrArg
              (fun edges : List ExplicitFormulaRectangleVerticalEndpointDataEdge =>
                explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedX xpair ypairs ++
                  edges)
              (explicitFormulaRectangleSelectedEndpointDataPairLists_leftEdgeCoordinates
                rest ypairs)

/-- The selected endpoint-data list for crossed adjacent-pair lists has exactly the
selected right vertical coordinate labels. -/
theorem explicitFormulaRectangleSelectedEndpointDataPairLists_rightEdgeCoordinates
    {F : ExplicitFormulaContourFamily} {T ε : ℝ} :
    ∀ (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
      (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)),
      (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          xpairs ypairs)).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.rightEdgeCoordinates) =
        explicitFormulaRectangleSelectedRightEdgeCoordinatesOfPairLists xpairs ypairs
  | [], ypairs => rfl
  | xpair :: rest, ypairs =>
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
      have hcells :
          explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              (xpair :: rest) ypairs =
            explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
              xpair ypairs ++
              explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
                rest ypairs := by
        rfl
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
      have hlist : whole = firstRow ++ remaining := by
        exact
          Eq.trans
            (congrArg
              (fun cells : List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε) =>
                explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells cells)
              hcells)
            hmap
      calc
        whole.map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
              d.rightEdgeCoordinates) =
            (firstRow ++ remaining).map
              (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                d.rightEdgeCoordinates) := by
          exact
            congrArg
              (fun data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) =>
                data.map
                  (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                    d.rightEdgeCoordinates))
              hlist
        _ =
            firstRow.map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.rightEdgeCoordinates) ++
              remaining.map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.rightEdgeCoordinates) := by
          exact
            List.map_append
              (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                d.rightEdgeCoordinates)
              firstRow
              remaining
        _ =
            explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedX xpair ypairs ++
              remaining.map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.rightEdgeCoordinates) := by
          exact
            congrArg
              (fun edges : List ExplicitFormulaRectangleVerticalEndpointDataEdge =>
                edges ++ remaining.map
                    (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                      d.rightEdgeCoordinates))
              (explicitFormulaRectangleSelectedEndpointDataFixedX_rightEdgeCoordinates
                xpair ypairs)
        _ =
            explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedX xpair ypairs ++
              explicitFormulaRectangleSelectedRightEdgeCoordinatesOfPairLists rest ypairs := by
          exact
            congrArg
              (fun edges : List ExplicitFormulaRectangleVerticalEndpointDataEdge =>
                explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedX xpair ypairs ++
                  edges)
              (explicitFormulaRectangleSelectedEndpointDataPairLists_rightEdgeCoordinates
                rest ypairs)

/-- Full box labels selected from one fixed horizontal adjacent-pair row, with the same
coordinate-omission filter as the selected cell list. -/
def explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε) →
      List ExplicitFormulaRectangleEndpointDataBoxEdge
  | [] => []
  | ypair :: rest =>
      if _homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        ((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) ::
          explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest
      else
        explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest

/-- The selected endpoint-data list for one fixed horizontal row has exactly the selected
full box labels. -/
theorem explicitFormulaRectangleSelectedEndpointDataFixedX_boxEdgeCoordinates
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    ∀ ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε),
      (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair ypairs)).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.boxEdgeCoordinates) =
        explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs
  | [] => rfl
  | ypair :: rest =>
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        congrArg
          (fun edges : List ExplicitFormulaRectangleEndpointDataBoxEdge =>
            ((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :: edges)
          (explicitFormulaRectangleSelectedEndpointDataFixedX_boxEdgeCoordinates
            xpair rest)
      else
        explicitFormulaRectangleSelectedEndpointDataFixedX_boxEdgeCoordinates
          xpair rest

/-- Full box labels selected from crossed adjacent-pair lists. -/
def explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
    {F : ExplicitFormulaContourFamily} {T ε : ℝ} :
    List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) →
      List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε) →
        List ExplicitFormulaRectangleEndpointDataBoxEdge
  | [], _ypairs => []
  | xpair :: rest, ypairs =>
      explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs ++
        explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs

/-- The selected endpoint-data list for crossed adjacent-pair lists has exactly the
selected full box labels. -/
theorem explicitFormulaRectangleSelectedEndpointDataPairLists_boxEdgeCoordinates
    {F : ExplicitFormulaContourFamily} {T ε : ℝ} :
    ∀ (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
      (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)),
      (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          xpairs ypairs)).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.boxEdgeCoordinates) =
        explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists xpairs ypairs
  | [], ypairs => rfl
  | xpair :: rest, ypairs =>
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
      have hcells :
          explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              (xpair :: rest) ypairs =
            explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
              xpair ypairs ++
              explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
                rest ypairs := by
        rfl
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
      have hlist : whole = firstRow ++ remaining := by
        exact
          Eq.trans
            (congrArg
              (fun cells : List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε) =>
                explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells cells)
              hcells)
            hmap
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
              hlist
        _ =
            firstRow.map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.boxEdgeCoordinates) ++
              remaining.map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.boxEdgeCoordinates) := by
          exact
            List.map_append
              (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                d.boxEdgeCoordinates)
              firstRow
              remaining
        _ =
            explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs ++
              remaining.map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.boxEdgeCoordinates) := by
          exact
            congrArg
              (fun edges : List ExplicitFormulaRectangleEndpointDataBoxEdge =>
                edges ++ remaining.map
                    (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                      d.boxEdgeCoordinates))
              (explicitFormulaRectangleSelectedEndpointDataFixedX_boxEdgeCoordinates
                xpair ypairs)
        _ =
            explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs ++
              explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs := by
          exact
            congrArg
              (fun edges : List ExplicitFormulaRectangleEndpointDataBoxEdge =>
                explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs ++
                  edges)
              (explicitFormulaRectangleSelectedEndpointDataPairLists_boxEdgeCoordinates
                rest ypairs)

/-- The canonical selected endpoint-data list has exactly the selected full box labels
from the sorted adjacent endpoint-pair lists. -/

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
