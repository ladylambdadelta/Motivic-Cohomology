import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part20Parts.Part20_04

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
## Part20 05: SelectedEndpointDataRecursions
-/

attribute [local instance] Classical.propDecidable

theorem explicitFormulaRectangleSelectedEndpointData_boxEdgeCoordinates_eq_sortedPairLists
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    (explicitFormulaRectangleSelectedEndpointData F T ε).map
        (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
          d.boxEdgeCoordinates) =
      explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε) :=
  explicitFormulaRectangleSelectedEndpointDataPairLists_boxEdgeCoordinates
    (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
    (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)

/-- The endpoint-data list of a retained fixed-horizontal selected head cell is the
head endpoint datum followed by the selected tail endpoint-data list. -/
theorem explicitFormulaRectangleSelectedEndpointDataFixedX_cons_of_omission
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))
    (homit :
      explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair) :
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair (ypair :: rest)) =
      ({ xpair := xpair
         ypair := ypair
         homit := homit } :
          ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData ::
        explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
            xpair rest) := by
  exact
    congrArg
      (fun cells : List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε) =>
        explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells cells)
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX_cons_of_omission
        xpair ypair rest homit)

/-- The endpoint-data list of a rejected fixed-horizontal selected head cell is exactly
the selected tail endpoint-data list. -/
theorem explicitFormulaRectangleSelectedEndpointDataFixedX_skip_of_not_omission
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))
    (homit :
      ¬ explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair) :
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair (ypair :: rest)) =
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair rest) := by
  exact
    congrArg
      (fun cells : List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε) =>
        explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells cells)
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX_skip_of_not_omission
        xpair ypair rest homit)

/-- A retained fixed-horizontal selected box-coordinate head conses its box label. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX_cons_of_omission
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))
    (homit :
      explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair) :
    explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest) =
      ((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) ::
        explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest :=
  if_pos homit

/-- A rejected fixed-horizontal selected box-coordinate head is skipped. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX_skip_of_not_omission
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))
    (homit :
      ¬ explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair) :
    explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest) =
      explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest :=
  if_neg homit

/-- Generic cons recursion for a list functional on selected fixed-horizontal endpoint
data. -/
theorem explicitFormulaRectangleSelectedEndpointDataFixedX_listFunctional_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))
    (S : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) → ℂ)
    (H : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε → ℂ)
    (hcons :
      ∀ (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)
        (tail : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)),
        S (d :: tail) = H d + S tail) :
    S (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair (ypair :: rest))) =
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        H
          (({ xpair := xpair
              ypair := ypair
              homit := homit } :
                ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData) +
          S (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
              xpair rest))
      else
        S (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
            xpair rest)) := by
  if homit :
      explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
    calc
      S (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
            xpair (ypair :: rest))) =
        S
          (({ xpair := xpair
              ypair := ypair
              homit := homit } :
                ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData ::
            explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
              (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                xpair rest)) := by
        exact congrArg S
          (explicitFormulaRectangleSelectedEndpointDataFixedX_cons_of_omission
            xpair ypair rest homit)
      _ =
        H
            (({ xpair := xpair
                ypair := ypair
                homit := homit } :
                  ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData) +
          S (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
              xpair rest)) := by
        exact hcons
          (({ xpair := xpair
              ypair := ypair
              homit := homit } :
                ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData)
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
              xpair rest))
      _ =
        if homit :
            explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
          H
            (({ xpair := xpair
                ypair := ypair
                homit := homit } :
                  ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData) +
            S (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
              (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                xpair rest))
        else
          S (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
              xpair rest)) := by
        show
          H
              (({ xpair := xpair
                  ypair := ypair
                  homit := homit } :
                    ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData) +
                S (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                  (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                    xpair rest)) =
            (if hselected :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              H
                (({ xpair := xpair
                    ypair := ypair
                    homit := hselected } :
                      ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData) +
                  S (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                    (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                      xpair rest))
            else
              S (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                  xpair rest)))
        exact
          (dif_pos
            (c := explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair)
            (α := ℂ)
            (t := fun hselected =>
              H
                (({ xpair := xpair
                    ypair := ypair
                    homit := hselected } :
                      ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData) +
                  S (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                    (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                      xpair rest)))
            (e := fun _ =>
              S (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                  xpair rest)))
            homit).symm
  else
    calc
      S (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
            xpair (ypair :: rest))) =
        S (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
            xpair rest)) := by
        exact congrArg S
          (explicitFormulaRectangleSelectedEndpointDataFixedX_skip_of_not_omission
            xpair ypair rest homit)
      _ =
        if homit :
            explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
          H
            (({ xpair := xpair
                ypair := ypair
                homit := homit } :
                  ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData) +
            S (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
              (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                xpair rest))
        else
          S (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
              xpair rest)) := by
        show
          S (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
              (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                xpair rest)) =
            (if hselected :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              H
                (({ xpair := xpair
                    ypair := ypair
                    homit := hselected } :
                      ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData) +
                  S (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                    (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                      xpair rest))
            else
              S (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                  xpair rest)))
        exact
          (dif_neg
            (c := explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair)
            (α := ℂ)
            (t := fun hselected =>
              H
                (({ xpair := xpair
                    ypair := ypair
                    homit := hselected } :
                      ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData) +
                  S (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                    (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                      xpair rest)))
            (e := fun _ =>
              S (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                  xpair rest)))
            homit).symm

/-- Generic cons recursion for a list functional on selected fixed-horizontal full-box
coordinate labels. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX_listFunctional_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))
    (S : List ExplicitFormulaRectangleEndpointDataBoxEdge → ℂ)
    (H : ExplicitFormulaRectangleEndpointDataBoxEdge → ℂ)
    (hcons :
      ∀ (box : ExplicitFormulaRectangleEndpointDataBoxEdge)
        (tail : List ExplicitFormulaRectangleEndpointDataBoxEdge),
        S (box :: tail) = H box + S tail) :
    S (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) =
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        H (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
            ExplicitFormulaRectangleEndpointDataBoxEdge) +
          S (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest)
      else
        S (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) := by
  if homit :
      explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
    calc
      S (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) =
        S ((((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
              ExplicitFormulaRectangleEndpointDataBoxEdge) ::
            explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) := by
        exact congrArg S
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX_cons_of_omission
            xpair ypair rest homit)
      _ =
        H (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
            ExplicitFormulaRectangleEndpointDataBoxEdge) +
          S (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) := by
        exact hcons
          (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
            ExplicitFormulaRectangleEndpointDataBoxEdge)
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest)
      _ =
        if homit :
            explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
          H (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
              ExplicitFormulaRectangleEndpointDataBoxEdge) +
            S (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest)
        else
          S (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) :=
        (if_pos homit).symm
  else
    calc
      S (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) =
        S (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) := by
        exact congrArg S
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX_skip_of_not_omission
            xpair ypair rest homit)
      _ =
        if homit :
            explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
          H (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
              ExplicitFormulaRectangleEndpointDataBoxEdge) +
            S (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest)
        else
          S (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) :=
        (if_neg homit).symm

/-- The selected fixed-horizontal row bottom-edge sum follows the coordinate-omission
filter at the head vertical adjacent pair. -/
theorem explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum_selectedFixedX_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
            xpair (ypair :: rest))) =
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
          (({ xpair := xpair
              ypair := ypair
              homit := homit } :
                ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData) +
          explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
            (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
              (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                xpair rest))
      else
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
              xpair rest)) := by
  exact
    explicitFormulaRectangleSelectedEndpointDataFixedX_listFunctional_cons
      xpair ypair rest
      (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f)
      (explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f)
      (fun d tail => rfl)

/-- The selected fixed-horizontal row top-edge sum follows the coordinate-omission
filter at the head vertical adjacent pair. -/
theorem explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_selectedFixedX_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
            xpair (ypair :: rest))) =
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f
          (({ xpair := xpair
              ypair := ypair
              homit := homit } :
                ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData) +
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
            (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
              (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                xpair rest))
      else
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
              xpair rest)) := by
  exact
    explicitFormulaRectangleSelectedEndpointDataFixedX_listFunctional_cons
      xpair ypair rest
      (explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f)
      (explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f)
      (fun d tail => rfl)

/-- The selected fixed-horizontal row right-edge sum follows the coordinate-omission
filter at the head vertical adjacent pair. -/
theorem explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum_selectedFixedX_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
            xpair (ypair :: rest))) =
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f
          (({ xpair := xpair
              ypair := ypair
              homit := homit } :
                ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData) +
          explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
            (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
              (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                xpair rest))
      else
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
              xpair rest)) := by
  exact
    explicitFormulaRectangleSelectedEndpointDataFixedX_listFunctional_cons
      xpair ypair rest
      (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f)
      (explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f)
      (fun d tail => rfl)

/-- The selected fixed-horizontal row left-edge sum follows the coordinate-omission
filter at the head vertical adjacent pair. -/
theorem explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum_selectedFixedX_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
            xpair (ypair :: rest))) =
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f
          (({ xpair := xpair
              ypair := ypair
              homit := homit } :
                ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData) +
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
            (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
              (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                xpair rest))
      else
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
              xpair rest)) := by
  exact
    explicitFormulaRectangleSelectedEndpointDataFixedX_listFunctional_cons
      xpair ypair rest
      (explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f)
      (explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f)
      (fun d tail => rfl)

/-- The selected fixed-horizontal row box-boundary sum follows the coordinate-omission
filter at the head vertical adjacent pair. -/
theorem explicitFormulaRectangleEndpointDataBoxBoundarySum_selectedFixedX_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleEndpointDataBoxBoundarySum f
        ((explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
            xpair (ypair :: rest))).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.boxEdgeCoordinates)) =
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (explicitFormulaRectangleEndpointDataBoxLowerCorner
              (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
                ExplicitFormulaRectangleEndpointDataBoxEdge))
            (explicitFormulaRectangleEndpointDataBoxUpperCorner
              (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
                ExplicitFormulaRectangleEndpointDataBoxEdge)) +
          explicitFormulaRectangleEndpointDataBoxBoundarySum f
            ((explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
              (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                xpair rest)).map
              (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                d.boxEdgeCoordinates))
      else
        explicitFormulaRectangleEndpointDataBoxBoundarySum f
          ((explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
              xpair rest)).map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
              d.boxEdgeCoordinates)) := by
  exact
    explicitFormulaRectangleSelectedEndpointDataFixedX_listFunctional_cons
      xpair ypair rest
      (fun data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) =>
        explicitFormulaRectangleEndpointDataBoxBoundarySum f
          (data.map
            (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
              d.boxEdgeCoordinates)))
      (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
        finiteRectangleSubdivisionCellBoundaryIntegral
          (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
          (explicitFormulaRectangleEndpointDataBoxLowerCorner d.boxEdgeCoordinates)
          (explicitFormulaRectangleEndpointDataBoxUpperCorner d.boxEdgeCoordinates))
      (fun d tail => rfl)

/-- The selected fixed-horizontal row is empty over the empty vertical-pair list. -/
theorem explicitFormulaRectangleSelectedEndpointDataFixedX_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))) =
      ([] : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)) := by
  rfl

/-- The selected fixed-horizontal row has zero bottom-edge sum over an empty vertical-pair
source list. -/
theorem explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum_selectedFixedX_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
            xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)))) =
      0 := by
  rfl

/-- The selected fixed-horizontal row has zero top-edge sum over an empty vertical-pair
source list. -/
theorem explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_selectedFixedX_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
            xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)))) =
      0 := by
  rfl

/-- The selected fixed-horizontal row has zero right-edge sum over an empty vertical-pair
source list. -/
theorem explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum_selectedFixedX_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
            xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)))) =
      0 := by
  rfl

/-- The selected fixed-horizontal row has zero left-edge sum over an empty vertical-pair
source list. -/
theorem explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum_selectedFixedX_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
            xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)))) =
      0 := by
  rfl

/-- The selected fixed-horizontal row has zero box-boundary sum over an empty vertical-pair
source list. -/
theorem explicitFormulaRectangleEndpointDataBoxBoundarySum_selectedFixedX_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    explicitFormulaRectangleEndpointDataBoxBoundarySum f
        ((explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
            xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)))).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.boxEdgeCoordinates)) =
      0 := by
  rfl

/-- The selected bottom-edge sum over a cons horizontal adjacent-pair list splits into the
selected row for the head pair plus the selected remaining rows. -/
theorem explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum_selectedPairLists_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (rest : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    let firstRow : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair ypairs)
    let remaining : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          rest ypairs)
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
            (xpair :: rest) ypairs)) =
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f firstRow +
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f remaining := by
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
  exact
    Eq.trans
      (congrArg
        (fun data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) =>
          explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data)
        hlist)
      (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum_append
        f firstRow remaining)

/-- The selected top-edge sum over a cons horizontal adjacent-pair list splits into the
selected row for the head pair plus the selected remaining rows. -/
theorem explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_selectedPairLists_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (rest : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    let firstRow : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair ypairs)
    let remaining : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          rest ypairs)
    explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
            (xpair :: rest) ypairs)) =
      explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f firstRow +
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f remaining := by
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
  exact
    Eq.trans
      (congrArg
        (fun data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) =>
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data)
        hlist)
      (explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_append
        f firstRow remaining)

/-- The selected right-edge sum over a cons horizontal adjacent-pair list splits into the
selected row for the head pair plus the selected remaining rows. -/
theorem explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum_selectedPairLists_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (rest : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    let firstRow : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair ypairs)
    let remaining : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          rest ypairs)
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
            (xpair :: rest) ypairs)) =
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f firstRow +
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f remaining := by
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
  exact
    Eq.trans
      (congrArg
        (fun data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) =>
          explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data)
        hlist)
      (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum_append
        f firstRow remaining)

/-- The selected left-edge sum over a cons horizontal adjacent-pair list splits into the
selected row for the head pair plus the selected remaining rows. -/
theorem explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum_selectedPairLists_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (rest : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    let firstRow : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair ypairs)
    let remaining : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          rest ypairs)
    explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
            (xpair :: rest) ypairs)) =
      explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f firstRow +
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f remaining := by
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
  exact
    Eq.trans
      (congrArg
        (fun data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) =>
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data)
        hlist)
      (explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum_append
        f firstRow remaining)

/-- The canonical selected endpoint-data list unfolds to the selected crossed list built
from the sorted horizontal and vertical adjacent endpoint pairs. -/
theorem explicitFormulaRectangleSelectedEndpointData_eq_sortedPairLists
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    explicitFormulaRectangleSelectedEndpointData F T ε =
      explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)) := by
  rfl

/-- The canonical selected endpoint-data list has exactly the selected bottom horizontal
coordinate labels from the sorted adjacent endpoint-pair lists. -/
theorem explicitFormulaRectangleSelectedEndpointData_bottomEdgeCoordinates_eq_sortedPairLists
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    (explicitFormulaRectangleSelectedEndpointData F T ε).map
        (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
          d.bottomEdgeCoordinates) =
      explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfPairLists
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε) :=
  explicitFormulaRectangleSelectedEndpointDataPairLists_bottomEdgeCoordinates
    (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
    (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)

/-- The canonical selected endpoint-data list has exactly the selected top horizontal
coordinate labels from the sorted adjacent endpoint-pair lists. -/
theorem explicitFormulaRectangleSelectedEndpointData_topEdgeCoordinates_eq_sortedPairLists
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    (explicitFormulaRectangleSelectedEndpointData F T ε).map
        (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
          d.topEdgeCoordinates) =
      explicitFormulaRectangleSelectedTopEdgeCoordinatesOfPairLists
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε) :=
  explicitFormulaRectangleSelectedEndpointDataPairLists_topEdgeCoordinates
    (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
    (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)

/-- A bottom horizontal coordinate label from canonical selected endpoint data comes from
a selected endpoint datum carrying the coordinate-omission proof. -/
theorem explicitFormulaRectangleSelectedEndpointData_bottomEdgeCoordinates_mem_omission
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    {edge : ExplicitFormulaRectangleHorizontalEndpointDataEdge}
    (hedge :
      edge ∈ (explicitFormulaRectangleSelectedEndpointData F T ε).map
        (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
          d.bottomEdgeCoordinates)) :
    ∃ d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε,
      d ∈ explicitFormulaRectangleSelectedEndpointData F T ε ∧
        d.bottomEdgeCoordinates = edge ∧
          ∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a.re ∉ Set.uIcc d.x₀ d.x₁ ∨
                a.im ∉ Set.uIcc d.y₀ d.y₁ := by
  match List.mem_map.mp hedge with
  | ⟨d, hd, hedge_eq⟩ =>
      exact
        ⟨d, hd, hedge_eq,
          explicitFormulaRectangleSelectedEndpointData_coordinateOmission hd⟩

/-- A top horizontal coordinate label from canonical selected endpoint data comes from a
selected endpoint datum carrying the coordinate-omission proof. -/
theorem explicitFormulaRectangleSelectedEndpointData_topEdgeCoordinates_mem_omission
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    {edge : ExplicitFormulaRectangleHorizontalEndpointDataEdge}
    (hedge :
      edge ∈ (explicitFormulaRectangleSelectedEndpointData F T ε).map
        (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
          d.topEdgeCoordinates)) :
    ∃ d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε,
      d ∈ explicitFormulaRectangleSelectedEndpointData F T ε ∧
        d.topEdgeCoordinates = edge ∧
          ∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a.re ∉ Set.uIcc d.x₀ d.x₁ ∨
                a.im ∉ Set.uIcc d.y₀ d.y₁ := by
  match List.mem_map.mp hedge with
  | ⟨d, hd, hedge_eq⟩ =>
      exact
        ⟨d, hd, hedge_eq,
          explicitFormulaRectangleSelectedEndpointData_coordinateOmission hd⟩

/-- Mapping endpoint-data cells to full box coordinates is the same as mapping the
underlying adjacent-pair cells to their rectangular endpoint-pair box. -/
theorem explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells_boxEdgeCoordinates
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (cells : List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε)) :
    (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells cells).map
        (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
          d.boxEdgeCoordinates) =
      cells.map
        (fun c : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε =>
          ((c.xpair.x₀, c.xpair.x₁), (c.ypair.y₀, c.ypair.y₁))) := by
  induction cells with
  | nil => rfl
  | cons c rest ih =>
      exact
        congrArg
          (fun tail : List ExplicitFormulaRectangleEndpointDataBoxEdge =>
            ((c.xpair.x₀, c.xpair.x₁), (c.ypair.y₀, c.ypair.y₁)) :: tail)
          ih

/-- The canonical selected endpoint-data full-box list is the selected adjacent-pair cell
list mapped to its rectangular endpoint-pair box. -/
theorem explicitFormulaRectangleSelectedEndpointData_boxEdgeCoordinates
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    (explicitFormulaRectangleSelectedEndpointData F T ε).map
        (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
          d.boxEdgeCoordinates) =
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCells F T ε).map
        (fun c : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε =>
          ((c.xpair.x₀, c.xpair.x₁), (c.ypair.y₀, c.ypair.y₁))) := by
  exact
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells_boxEdgeCoordinates
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCells F T ε)

/-- A selected endpoint-data full-box label comes from a selected endpoint datum carrying
the coordinate-omission proof. -/
theorem explicitFormulaRectangleSelectedEndpointData_boxEdgeCoordinates_mem_omission
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    {box : ExplicitFormulaRectangleEndpointDataBoxEdge}
    (hbox :
      box ∈ (explicitFormulaRectangleSelectedEndpointData F T ε).map
        (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
          d.boxEdgeCoordinates)) :
    ∃ d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε,
      d ∈ explicitFormulaRectangleSelectedEndpointData F T ε ∧
        d.boxEdgeCoordinates = box ∧
          ∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a.re ∉ Set.uIcc d.x₀ d.x₁ ∨
                a.im ∉ Set.uIcc d.y₀ d.y₁ := by
  match List.mem_map.mp hbox with
  | ⟨d, hd, hbox_eq⟩ =>
      exact
        ⟨d, hd, hbox_eq,
          explicitFormulaRectangleSelectedEndpointData_coordinateOmission hd⟩

/-- The selected endpoint-data boundary sum is exactly the box-boundary sum of the
selected endpoint-data box-coordinate list. -/
theorem explicitFormulaRectangleSelectedEndpointData_boundarySum_eq_boxBoundarySum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    explicitFormulaRectangleRegularGridEndpointDataBoundarySum f
        (explicitFormulaRectangleSelectedEndpointData F T ε) =
      explicitFormulaRectangleEndpointDataBoxBoundarySum f
        ((explicitFormulaRectangleSelectedEndpointData F T ε).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.boxEdgeCoordinates)) :=
  explicitFormulaRectangleRegularGridEndpointDataBoundarySum_eq_boxBoundarySum
    f (explicitFormulaRectangleSelectedEndpointData F T ε)

/-- The selected endpoint-data box-boundary sum is the selected endpoint-data boundary sum,
with the equality oriented for box-collapse replacement. -/
theorem explicitFormulaRectangleSelectedEndpointData_boxBoundarySum_eq_boundarySum
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    explicitFormulaRectangleEndpointDataBoxBoundarySum f
        ((explicitFormulaRectangleSelectedEndpointData F T ε).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.boxEdgeCoordinates)) =
      explicitFormulaRectangleRegularGridEndpointDataBoundarySum f
        (explicitFormulaRectangleSelectedEndpointData F T ε) :=
  (explicitFormulaRectangleSelectedEndpointData_boundarySum_eq_boxBoundarySum
    f F T ε).symm

/-- The canonical selected endpoint-data box-boundary sum is the box-boundary sum over
the selected full box labels obtained from the sorted adjacent endpoint-pair lists. -/
theorem explicitFormulaRectangleSelectedEndpointData_boxBoundarySum_eq_sortedPairLists
    (f : ZetaAdmissibleFunction) (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    explicitFormulaRectangleEndpointDataBoxBoundarySum f
        ((explicitFormulaRectangleSelectedEndpointData F T ε).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.boxEdgeCoordinates)) =
      explicitFormulaRectangleEndpointDataBoxBoundarySum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
          (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
          (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)) := by
  exact
    congrArg
      (fun boxes : List ExplicitFormulaRectangleEndpointDataBoxEdge =>
        explicitFormulaRectangleEndpointDataBoxBoundarySum f boxes)
      (explicitFormulaRectangleSelectedEndpointData_boxEdgeCoordinates_eq_sortedPairLists
        F T ε)

/-- Box-boundary sum over selected full box labels for one fixed horizontal row follows
the coordinate-omission filter at the head vertical adjacent pair. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesBoundarySum_fixedX_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleEndpointDataBoxBoundarySum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) =
      if _homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            (explicitFormulaRectangleEndpointDataBoxLowerCorner
              (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
                ExplicitFormulaRectangleEndpointDataBoxEdge))
            (explicitFormulaRectangleEndpointDataBoxUpperCorner
              (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
                ExplicitFormulaRectangleEndpointDataBoxEdge)) +
          explicitFormulaRectangleEndpointDataBoxBoundarySum f
            (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest)
      else
        explicitFormulaRectangleEndpointDataBoxBoundarySum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) := by
  exact
    explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX_listFunctional_cons
      xpair ypair rest
      (explicitFormulaRectangleEndpointDataBoxBoundarySum f)
      (fun box : ExplicitFormulaRectangleEndpointDataBoxEdge =>
        finiteRectangleSubdivisionCellBoundaryIntegral
          (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
          (explicitFormulaRectangleEndpointDataBoxLowerCorner box)
          (explicitFormulaRectangleEndpointDataBoxUpperCorner box))
      (fun box tail => rfl)

/-- Bottom side-sum over selected full box labels for one fixed horizontal row follows the
coordinate-omission filter at the head vertical adjacent pair. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesBottomEdgeIntegralSum_fixedX_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleBoxBottomEdgeIntegralSum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) =
      if _homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        explicitFormulaRectangleBoxBottomEdgeIntegral f
            (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
              ExplicitFormulaRectangleEndpointDataBoxEdge) +
          explicitFormulaRectangleBoxBottomEdgeIntegralSum f
            (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest)
      else
        explicitFormulaRectangleBoxBottomEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) := by
  exact
    explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX_listFunctional_cons
      xpair ypair rest
      (explicitFormulaRectangleBoxBottomEdgeIntegralSum f)
      (explicitFormulaRectangleBoxBottomEdgeIntegral f)
      (fun box tail => rfl)

/-- Top side-sum over selected full box labels for one fixed horizontal row follows the
coordinate-omission filter at the head vertical adjacent pair. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesTopEdgeIntegralSum_fixedX_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleBoxTopEdgeIntegralSum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) =
      if _homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        explicitFormulaRectangleBoxTopEdgeIntegral f
            (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
              ExplicitFormulaRectangleEndpointDataBoxEdge) +
          explicitFormulaRectangleBoxTopEdgeIntegralSum f
            (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest)
      else
        explicitFormulaRectangleBoxTopEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) := by
  exact
    explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX_listFunctional_cons
      xpair ypair rest
      (explicitFormulaRectangleBoxTopEdgeIntegralSum f)
      (explicitFormulaRectangleBoxTopEdgeIntegral f)
      (fun box tail => rfl)

/-- Right side-sum over selected full box labels for one fixed horizontal row follows the
coordinate-omission filter at the head vertical adjacent pair. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesRightEdgeIntegralSum_fixedX_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleBoxRightEdgeIntegralSum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) =
      if _homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        explicitFormulaRectangleBoxRightEdgeIntegral f
            (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
              ExplicitFormulaRectangleEndpointDataBoxEdge) +
          explicitFormulaRectangleBoxRightEdgeIntegralSum f
            (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest)
      else
        explicitFormulaRectangleBoxRightEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) := by
  exact
    explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX_listFunctional_cons
      xpair ypair rest
      (explicitFormulaRectangleBoxRightEdgeIntegralSum f)
      (explicitFormulaRectangleBoxRightEdgeIntegral f)
      (fun box tail => rfl)

/-- Left side-sum over selected full box labels for one fixed horizontal row follows the
coordinate-omission filter at the head vertical adjacent pair. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesLeftEdgeIntegralSum_fixedX_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleBoxLeftEdgeIntegralSum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair (ypair :: rest)) =
      if _homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        explicitFormulaRectangleBoxLeftEdgeIntegral f
            (((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :
              ExplicitFormulaRectangleEndpointDataBoxEdge) +
          explicitFormulaRectangleBoxLeftEdgeIntegralSum f
            (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest)
      else
        explicitFormulaRectangleBoxLeftEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest) := by
  exact
    explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX_listFunctional_cons
      xpair ypair rest
      (explicitFormulaRectangleBoxLeftEdgeIntegralSum f)
      (explicitFormulaRectangleBoxLeftEdgeIntegral f)
      (fun box tail => rfl)

/-- Box-boundary sum over selected full box labels for one fixed horizontal row is zero
over the empty vertical adjacent-pair list. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesBoundarySum_fixedX_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    explicitFormulaRectangleEndpointDataBoxBoundarySum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX
          xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))) =
      0 := by
  rfl

/-- Bottom side-sum over selected full box labels for one fixed horizontal row is zero
over the empty vertical adjacent-pair list. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesBottomEdgeIntegralSum_fixedX_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    explicitFormulaRectangleBoxBottomEdgeIntegralSum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX
          xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))) =
      0 := by
  rfl

/-- Top side-sum over selected full box labels for one fixed horizontal row is zero over
the empty vertical adjacent-pair list. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesTopEdgeIntegralSum_fixedX_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    explicitFormulaRectangleBoxTopEdgeIntegralSum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX
          xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))) =
      0 := by
  rfl

/-- Right side-sum over selected full box labels for one fixed horizontal row is zero
over the empty vertical adjacent-pair list. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesRightEdgeIntegralSum_fixedX_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    explicitFormulaRectangleBoxRightEdgeIntegralSum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX
          xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))) =
      0 := by
  rfl

/-- Left side-sum over selected full box labels for one fixed horizontal row is zero over
the empty vertical adjacent-pair list. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesLeftEdgeIntegralSum_fixedX_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    explicitFormulaRectangleBoxLeftEdgeIntegralSum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX
          xpair ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))) =
      0 := by
  rfl

/-- Box-boundary sum over selected full box labels for crossed adjacent-pair lists splits
into the selected fixed-row boundary sum plus the remaining rows. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesBoundarySum_pairLists_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (rest : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleEndpointDataBoxBoundarySum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
          (xpair :: rest) ypairs) =
      explicitFormulaRectangleEndpointDataBoxBoundarySum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs) +
        explicitFormulaRectangleEndpointDataBoxBoundarySum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs) := by
  exact
    explicitFormulaRectangleEndpointDataBoxBoundarySum_append
      f
      (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs)
      (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs)

/-- Bottom side-sum over selected full box labels for crossed adjacent-pair lists splits
into the selected fixed-row side sum plus the remaining rows. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesBottomEdgeIntegralSum_pairLists_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (rest : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleBoxBottomEdgeIntegralSum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
          (xpair :: rest) ypairs) =
      explicitFormulaRectangleBoxBottomEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs) +
        explicitFormulaRectangleBoxBottomEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs) := by
  exact
    explicitFormulaRectangleBoxBottomEdgeIntegralSum_append
      f
      (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs)
      (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs)

/-- Top side-sum over selected full box labels for crossed adjacent-pair lists splits
into the selected fixed-row side sum plus the remaining rows. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesTopEdgeIntegralSum_pairLists_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (rest : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleBoxTopEdgeIntegralSum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
          (xpair :: rest) ypairs) =
      explicitFormulaRectangleBoxTopEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs) +
        explicitFormulaRectangleBoxTopEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs) := by
  exact
    explicitFormulaRectangleBoxTopEdgeIntegralSum_append
      f
      (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs)
      (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs)

/-- Right side-sum over selected full box labels for crossed adjacent-pair lists splits
into the selected fixed-row side sum plus the remaining rows. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesRightEdgeIntegralSum_pairLists_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (rest : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleBoxRightEdgeIntegralSum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
          (xpair :: rest) ypairs) =
      explicitFormulaRectangleBoxRightEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs) +
        explicitFormulaRectangleBoxRightEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs) := by
  exact
    explicitFormulaRectangleBoxRightEdgeIntegralSum_append
      f
      (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs)
      (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs)

/-- Left side-sum over selected full box labels for crossed adjacent-pair lists splits
into the selected fixed-row side sum plus the remaining rows. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesLeftEdgeIntegralSum_pairLists_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (rest : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleBoxLeftEdgeIntegralSum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
          (xpair :: rest) ypairs) =
      explicitFormulaRectangleBoxLeftEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs) +
        explicitFormulaRectangleBoxLeftEdgeIntegralSum f
          (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs) := by
  exact
    explicitFormulaRectangleBoxLeftEdgeIntegralSum_append
      f
      (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair ypairs)
      (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists rest ypairs)

/-- Box-boundary sum over selected full box labels for an empty horizontal adjacent-pair
list is zero. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesBoundarySum_pairLists_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleEndpointDataBoxBoundarySum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
          ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) ypairs) =
      0 := by
  rfl

/-- Bottom side-sum over selected full box labels for an empty horizontal adjacent-pair
list is zero. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesBottomEdgeIntegralSum_pairLists_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleBoxBottomEdgeIntegralSum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
          ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) ypairs) =
      0 := by
  rfl

/-- Top side-sum over selected full box labels for an empty horizontal adjacent-pair list
is zero. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesTopEdgeIntegralSum_pairLists_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleBoxTopEdgeIntegralSum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
          ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) ypairs) =
      0 := by
  rfl

/-- Right side-sum over selected full box labels for an empty horizontal adjacent-pair
list is zero. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesRightEdgeIntegralSum_pairLists_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleBoxRightEdgeIntegralSum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
          ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) ypairs) =
      0 := by
  rfl

/-- Left side-sum over selected full box labels for an empty horizontal adjacent-pair list
is zero. -/
theorem explicitFormulaRectangleSelectedBoxEdgeCoordinatesLeftEdgeIntegralSum_pairLists_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) :
    explicitFormulaRectangleBoxLeftEdgeIntegralSum f
        (explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfPairLists
          ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) ypairs) =
      0 := by
  rfl


end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
