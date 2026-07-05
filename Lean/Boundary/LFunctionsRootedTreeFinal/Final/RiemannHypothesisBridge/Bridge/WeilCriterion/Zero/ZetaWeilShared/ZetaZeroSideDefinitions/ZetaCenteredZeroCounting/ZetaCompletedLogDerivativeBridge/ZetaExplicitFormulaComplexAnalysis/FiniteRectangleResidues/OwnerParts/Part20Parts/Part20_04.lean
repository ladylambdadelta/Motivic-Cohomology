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

noncomputable def explicitFormulaRectangleListSum {α : Type}
    (g : α → ℂ) : List α → ℂ
  | [] => 0
  | x :: rest => g x + explicitFormulaRectangleListSum g rest

/-- The selected adjacent-cell row conses the proof-carrying cell in the retained
coordinate-omission branch. -/
theorem explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX_cons_of_omission
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))
    (homit :
      explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair) :
    explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
        xpair (ypair :: rest) =
      ({ xpair := xpair
         ypair := ypair
         homit := homit } :
          ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε) ::
        explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair rest := by
  exact
    Eq.trans
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX_cons_eq
        xpair ypair rest)
      (dif_pos homit)

/-- The selected adjacent-cell row skips the head vertical pair in the rejected
coordinate-omission branch. -/
theorem explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX_skip_of_not_omission
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))
    (homit :
      ¬ explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair) :
    explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
        xpair (ypair :: rest) =
      explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
        xpair rest := by
  exact
    Eq.trans
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX_cons_eq
        xpair ypair rest)
      (dif_neg homit)

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
      exact Eq.refl _
  | ypair :: rest => by
      match inferInstanceAs
          (Decidable
            (explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair)) with
      | isTrue homit =>
        let scan : ExplicitFormulaRectangleYAdjacentEndpointPair T ε → ℂ :=
          fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
            if _homit :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁), ypair.y₀)
            else
              0
        let head : ℂ :=
          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
            f ((xpair.x₀, xpair.x₁), ypair.y₀)
        let tailEdges : List ExplicitFormulaRectangleHorizontalEndpointDataEdge :=
          explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair rest
        have hselected :
            explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX
                xpair (ypair :: rest) =
              ((xpair.x₀, xpair.x₁), ypair.y₀) :: tailEdges :=
          if_pos homit
        have hhead : scan ypair = head :=
          if_pos homit
        have htail :
            explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f tailEdges =
              explicitFormulaRectangleListSum scan rest :=
          explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX_integralSum_eq_listSum
            f xpair rest
        have hcons :
            explicitFormulaRectangleListSum scan (ypair :: rest) =
              head + explicitFormulaRectangleListSum scan rest := by
          calc
            explicitFormulaRectangleListSum scan (ypair :: rest) =
                scan ypair + explicitFormulaRectangleListSum scan rest := by
              exact Eq.refl _
            _ = head + explicitFormulaRectangleListSum scan rest := by
              exact congrArg
                (fun z : ℂ => z + explicitFormulaRectangleListSum scan rest)
                hhead
        calc
          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX
                xpair (ypair :: rest)) =
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
                (((xpair.x₀, xpair.x₁), ypair.y₀) :: tailEdges) := by
            exact congrArg
              (fun edges : List ExplicitFormulaRectangleHorizontalEndpointDataEdge =>
                explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f edges)
              hselected
          _ = head +
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f tailEdges := by
            exact Eq.refl _
          _ = head + explicitFormulaRectangleListSum scan rest := by
            exact congrArg (fun z : ℂ => head + z) htail
          _ = explicitFormulaRectangleListSum scan (ypair :: rest) := hcons.symm
      | isFalse homit =>
        calc
          explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
              (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX
                xpair (ypair :: rest)) =
              explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f
                (explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair rest) := by
            exact congrArg
              (fun edges : List ExplicitFormulaRectangleHorizontalEndpointDataEdge =>
                explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegralSum f edges)
              (if_neg homit)
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
                (ypair :: rest) := by
            let scan : ExplicitFormulaRectangleYAdjacentEndpointPair T ε → ℂ :=
              fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                if _homit :
                    explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission
                      xpair ypair then
                  explicitFormulaRectangleBottomHorizontalEndpointDataEdgeIntegral
                    f ((xpair.x₀, xpair.x₁), ypair.y₀)
                else
                  0
            have hhead : scan ypair = 0 :=
              if_neg homit
            calc
              0 + explicitFormulaRectangleListSum scan rest =
                  scan ypair + explicitFormulaRectangleListSum scan rest := by
                exact congrArg
                  (fun z : ℂ => z + explicitFormulaRectangleListSum scan rest)
                  hhead.symm
              _ = explicitFormulaRectangleListSum scan (ypair :: rest) := by
                exact Eq.refl _

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
      exact Eq.refl _
  | ypair :: rest => by
      match inferInstanceAs
          (Decidable
            (explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair)) with
      | isTrue homit =>
        let scan : ExplicitFormulaRectangleYAdjacentEndpointPair T ε → ℂ :=
          fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
            if _homit :
                explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                f ((xpair.x₀, xpair.x₁), ypair.y₁)
            else
              0
        let head : ℂ :=
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
            f ((xpair.x₀, xpair.x₁), ypair.y₁)
        let tailEdges : List ExplicitFormulaRectangleHorizontalEndpointDataEdge :=
          explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair rest
        have hselected :
            explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX
                xpair (ypair :: rest) =
              ((xpair.x₀, xpair.x₁), ypair.y₁) :: tailEdges :=
          if_pos homit
        have hhead : scan ypair = head :=
          if_pos homit
        have htail :
            explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f tailEdges =
              explicitFormulaRectangleListSum scan rest :=
          explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX_integralSum_eq_listSum
            f xpair rest
        have hcons :
            explicitFormulaRectangleListSum scan (ypair :: rest) =
              head + explicitFormulaRectangleListSum scan rest := by
          calc
            explicitFormulaRectangleListSum scan (ypair :: rest) =
                scan ypair + explicitFormulaRectangleListSum scan rest := by
              exact Eq.refl _
            _ = head + explicitFormulaRectangleListSum scan rest := by
              exact congrArg
                (fun z : ℂ => z + explicitFormulaRectangleListSum scan rest)
                hhead
        calc
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
              (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX
                xpair (ypair :: rest)) =
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
                (((xpair.x₀, xpair.x₁), ypair.y₁) :: tailEdges) := by
            exact congrArg
              (fun edges : List ExplicitFormulaRectangleHorizontalEndpointDataEdge =>
                explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f edges)
              hselected
          _ = head +
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f tailEdges := by
            exact Eq.refl _
          _ = head + explicitFormulaRectangleListSum scan rest := by
            exact congrArg (fun z : ℂ => head + z) htail
          _ = explicitFormulaRectangleListSum scan (ypair :: rest) := hcons.symm
      | isFalse homit =>
        calc
          explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
              (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX
                xpair (ypair :: rest)) =
              explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f
                (explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair rest) := by
            exact congrArg
              (fun edges : List ExplicitFormulaRectangleHorizontalEndpointDataEdge =>
                explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegralSum f edges)
              (if_neg homit)
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
                (ypair :: rest) := by
            let scan : ExplicitFormulaRectangleYAdjacentEndpointPair T ε → ℂ :=
              fun ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε =>
                if _homit :
                    explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission
                      xpair ypair then
                  explicitFormulaRectangleTopHorizontalEndpointDataEdgeIntegral
                    f ((xpair.x₀, xpair.x₁), ypair.y₁)
                else
                  0
            have hhead : scan ypair = 0 :=
              if_neg homit
            calc
              0 + explicitFormulaRectangleListSum scan rest =
                  scan ypair + explicitFormulaRectangleListSum scan rest := by
                exact congrArg
                  (fun z : ℂ => z + explicitFormulaRectangleListSum scan rest)
                  hhead.symm
              _ = explicitFormulaRectangleListSum scan (ypair :: rest) := by
                exact Eq.refl _

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
  | [] => by exact Eq.refl _
  | ypair :: rest =>
      by
        match inferInstanceAs
            (Decidable
              (explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair)) with
        | isTrue homit =>
          let cell : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε :=
            { xpair := xpair
              ypair := ypair
              homit := homit }
          have hcells :
              explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                  xpair (ypair :: rest) =
                cell ::
                  explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                    xpair rest :=
            explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX_cons_of_omission
              xpair ypair rest homit
          have hcoords :
              explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX
                  xpair (ypair :: rest) =
                ((xpair.x₀, xpair.x₁), ypair.y₀) ::
                  explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair rest :=
            if_pos homit
          calc
            (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
              (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                xpair (ypair :: rest))).map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.bottomEdgeCoordinates) =
              (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                (cell ::
                  explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                    xpair rest)).map
                  (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                    d.bottomEdgeCoordinates) := by
              exact congrArg
                (fun cells : List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε) =>
                  (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                    cells).map
                    (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                      d.bottomEdgeCoordinates))
                hcells
            _ =
                ((xpair.x₀, xpair.x₁), ypair.y₀) ::
                  (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                    (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                      xpair rest)).map
                    (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                      d.bottomEdgeCoordinates) := by
              exact Eq.refl _
            _ =
                ((xpair.x₀, xpair.x₁), ypair.y₀) ::
                  explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair rest := by
              exact congrArg
                (fun edges : List ExplicitFormulaRectangleHorizontalEndpointDataEdge =>
                  ((xpair.x₀, xpair.x₁), ypair.y₀) :: edges)
                (explicitFormulaRectangleSelectedEndpointDataFixedX_bottomEdgeCoordinates
                  xpair rest)
            _ =
                explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX
                  xpair (ypair :: rest) := hcoords.symm
        | isFalse homit =>
          have hcells :
              explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                  xpair (ypair :: rest) =
                explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                  xpair rest :=
            explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX_skip_of_not_omission
              xpair ypair rest homit
          have hcoords :
              explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX
                  xpair (ypair :: rest) =
                explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX xpair rest :=
            if_neg homit
          calc
            (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
              (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                xpair (ypair :: rest))).map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.bottomEdgeCoordinates) =
              (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                  xpair rest)).map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.bottomEdgeCoordinates) := by
              exact congrArg
                (fun cells : List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε) =>
                  (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                    cells).map
                    (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                      d.bottomEdgeCoordinates))
                hcells
            _ =
                explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX
                  xpair rest :=
              explicitFormulaRectangleSelectedEndpointDataFixedX_bottomEdgeCoordinates
                xpair rest
            _ =
                explicitFormulaRectangleSelectedBottomEdgeCoordinatesOfFixedX
                  xpair (ypair :: rest) := hcoords.symm

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
  | [] => by exact Eq.refl _
  | ypair :: rest =>
      by
        match inferInstanceAs
            (Decidable
              (explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair)) with
        | isTrue homit =>
          let cell : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε :=
            { xpair := xpair
              ypair := ypair
              homit := homit }
          have hcells :
              explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                  xpair (ypair :: rest) =
                cell ::
                  explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                    xpair rest :=
            explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX_cons_of_omission
              xpair ypair rest homit
          have hcoords :
              explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX
                  xpair (ypair :: rest) =
                ((xpair.x₀, xpair.x₁), ypair.y₁) ::
                  explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair rest :=
            if_pos homit
          calc
            (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
              (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                xpair (ypair :: rest))).map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.topEdgeCoordinates) =
              (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                (cell ::
                  explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                    xpair rest)).map
                  (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                    d.topEdgeCoordinates) := by
              exact congrArg
                (fun cells : List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε) =>
                  (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                    cells).map
                    (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                      d.topEdgeCoordinates))
                hcells
            _ =
                ((xpair.x₀, xpair.x₁), ypair.y₁) ::
                  (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                    (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                      xpair rest)).map
                    (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                      d.topEdgeCoordinates) := by
              exact Eq.refl _
            _ =
                ((xpair.x₀, xpair.x₁), ypair.y₁) ::
                  explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair rest := by
              exact congrArg
                (fun edges : List ExplicitFormulaRectangleHorizontalEndpointDataEdge =>
                  ((xpair.x₀, xpair.x₁), ypair.y₁) :: edges)
                (explicitFormulaRectangleSelectedEndpointDataFixedX_topEdgeCoordinates
                  xpair rest)
            _ =
                explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX
                  xpair (ypair :: rest) := hcoords.symm
        | isFalse homit =>
          have hcells :
              explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                  xpair (ypair :: rest) =
                explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                  xpair rest :=
            explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX_skip_of_not_omission
              xpair ypair rest homit
          have hcoords :
              explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX
                  xpair (ypair :: rest) =
                explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX xpair rest :=
            if_neg homit
          calc
            (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
              (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                xpair (ypair :: rest))).map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.topEdgeCoordinates) =
              (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                  xpair rest)).map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.topEdgeCoordinates) := by
              exact congrArg
                (fun cells : List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε) =>
                  (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                    cells).map
                    (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                      d.topEdgeCoordinates))
                hcells
            _ =
                explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX
                  xpair rest :=
              explicitFormulaRectangleSelectedEndpointDataFixedX_topEdgeCoordinates
                xpair rest
            _ =
                explicitFormulaRectangleSelectedTopEdgeCoordinatesOfFixedX
                  xpair (ypair :: rest) := hcoords.symm

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
  | [], ypairs => by exact Eq.refl _
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
        exact Eq.refl _
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
  | [], ypairs => by exact Eq.refl _
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
        exact Eq.refl _
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
  | [] => by exact Eq.refl _
  | ypair :: rest =>
      by
        match inferInstanceAs
            (Decidable
              (explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair)) with
        | isTrue homit =>
          let cell : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε :=
            { xpair := xpair
              ypair := ypair
              homit := homit }
          have hcells :
              explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                  xpair (ypair :: rest) =
                cell ::
                  explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                    xpair rest :=
            explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX_cons_of_omission
              xpair ypair rest homit
          have hcoords :
              explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedX
                  xpair (ypair :: rest) =
                ((ypair.y₀, ypair.y₁), xpair.x₀) ::
                  explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedX xpair rest :=
            if_pos homit
          calc
            (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
              (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                xpair (ypair :: rest))).map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.leftEdgeCoordinates) =
              (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                (cell ::
                  explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                    xpair rest)).map
                  (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                    d.leftEdgeCoordinates) := by
              exact congrArg
                (fun cells : List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε) =>
                  (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                    cells).map
                    (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                      d.leftEdgeCoordinates))
                hcells
            _ =
                ((ypair.y₀, ypair.y₁), xpair.x₀) ::
                  (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                    (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                      xpair rest)).map
                    (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                      d.leftEdgeCoordinates) := by
              exact Eq.refl _
            _ =
                ((ypair.y₀, ypair.y₁), xpair.x₀) ::
                  explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedX xpair rest := by
              exact congrArg
                (fun edges : List ExplicitFormulaRectangleVerticalEndpointDataEdge =>
                  ((ypair.y₀, ypair.y₁), xpair.x₀) :: edges)
                (explicitFormulaRectangleSelectedEndpointDataFixedX_leftEdgeCoordinates
                  xpair rest)
            _ =
                explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedX
                  xpair (ypair :: rest) := hcoords.symm
        | isFalse homit =>
          have hcells :
              explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                  xpair (ypair :: rest) =
                explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                  xpair rest :=
            explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX_skip_of_not_omission
              xpair ypair rest homit
          have hcoords :
              explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedX
                  xpair (ypair :: rest) =
                explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedX xpair rest :=
            if_neg homit
          calc
            (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
              (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                xpair (ypair :: rest))).map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.leftEdgeCoordinates) =
              (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                  xpair rest)).map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.leftEdgeCoordinates) := by
              exact congrArg
                (fun cells : List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε) =>
                  (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                    cells).map
                    (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                      d.leftEdgeCoordinates))
                hcells
            _ =
                explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedX
                  xpair rest :=
              explicitFormulaRectangleSelectedEndpointDataFixedX_leftEdgeCoordinates
                xpair rest
            _ =
                explicitFormulaRectangleSelectedLeftEdgeCoordinatesOfFixedX
                  xpair (ypair :: rest) := hcoords.symm

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
  | [] => by exact Eq.refl _
  | ypair :: rest =>
      by
        match inferInstanceAs
            (Decidable
              (explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair)) with
        | isTrue homit =>
          let cell : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε :=
            { xpair := xpair
              ypair := ypair
              homit := homit }
          have hcells :
              explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                  xpair (ypair :: rest) =
                cell ::
                  explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                    xpair rest :=
            explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX_cons_of_omission
              xpair ypair rest homit
          have hcoords :
              explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedX
                  xpair (ypair :: rest) =
                ((ypair.y₀, ypair.y₁), xpair.x₁) ::
                  explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedX xpair rest :=
            if_pos homit
          calc
            (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
              (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                xpair (ypair :: rest))).map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.rightEdgeCoordinates) =
              (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                (cell ::
                  explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                    xpair rest)).map
                  (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                    d.rightEdgeCoordinates) := by
              exact congrArg
                (fun cells : List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε) =>
                  (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                    cells).map
                    (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                      d.rightEdgeCoordinates))
                hcells
            _ =
                ((ypair.y₀, ypair.y₁), xpair.x₁) ::
                  (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                    (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                      xpair rest)).map
                    (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                      d.rightEdgeCoordinates) := by
              exact Eq.refl _
            _ =
                ((ypair.y₀, ypair.y₁), xpair.x₁) ::
                  explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedX xpair rest := by
              exact congrArg
                (fun edges : List ExplicitFormulaRectangleVerticalEndpointDataEdge =>
                  ((ypair.y₀, ypair.y₁), xpair.x₁) :: edges)
                (explicitFormulaRectangleSelectedEndpointDataFixedX_rightEdgeCoordinates
                  xpair rest)
            _ =
                explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedX
                  xpair (ypair :: rest) := hcoords.symm
        | isFalse homit =>
          have hcells :
              explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                  xpair (ypair :: rest) =
                explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                  xpair rest :=
            explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX_skip_of_not_omission
              xpair ypair rest homit
          have hcoords :
              explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedX
                  xpair (ypair :: rest) =
                explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedX xpair rest :=
            if_neg homit
          calc
            (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
              (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                xpair (ypair :: rest))).map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.rightEdgeCoordinates) =
              (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                  xpair rest)).map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.rightEdgeCoordinates) := by
              exact congrArg
                (fun cells : List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε) =>
                  (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                    cells).map
                    (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                      d.rightEdgeCoordinates))
                hcells
            _ =
                explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedX
                  xpair rest :=
              explicitFormulaRectangleSelectedEndpointDataFixedX_rightEdgeCoordinates
                xpair rest
            _ =
                explicitFormulaRectangleSelectedRightEdgeCoordinatesOfFixedX
                  xpair (ypair :: rest) := hcoords.symm

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
  | [], ypairs => by exact Eq.refl _
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
        exact Eq.refl _
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
  | [], ypairs => by exact Eq.refl _
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
        exact Eq.refl _
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
  | [] => by exact Eq.refl _
  | ypair :: rest =>
      by
        match inferInstanceAs
            (Decidable
              (explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair)) with
        | isTrue homit =>
          let cell : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε :=
            { xpair := xpair
              ypair := ypair
              homit := homit }
          have hcells :
              explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                  xpair (ypair :: rest) =
                cell ::
                  explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                    xpair rest :=
            explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX_cons_of_omission
              xpair ypair rest homit
          have hcoords :
              explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX
                  xpair (ypair :: rest) =
                ((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) ::
                  explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest :=
            if_pos homit
          calc
            (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
              (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                xpair (ypair :: rest))).map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.boxEdgeCoordinates) =
              (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                (cell ::
                  explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                    xpair rest)).map
                  (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                    d.boxEdgeCoordinates) := by
              exact congrArg
                (fun cells : List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε) =>
                  (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                    cells).map
                    (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                      d.boxEdgeCoordinates))
                hcells
            _ =
                ((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) ::
                  (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                    (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                      xpair rest)).map
                    (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                      d.boxEdgeCoordinates) := by
              exact Eq.refl _
            _ =
                ((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) ::
                  explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest := by
              exact congrArg
                (fun edges : List ExplicitFormulaRectangleEndpointDataBoxEdge =>
                  ((xpair.x₀, xpair.x₁), (ypair.y₀, ypair.y₁)) :: edges)
                (explicitFormulaRectangleSelectedEndpointDataFixedX_boxEdgeCoordinates
                  xpair rest)
            _ =
                explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX
                  xpair (ypair :: rest) := hcoords.symm
        | isFalse homit =>
          have hcells :
              explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                  xpair (ypair :: rest) =
                explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                  xpair rest :=
            explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX_skip_of_not_omission
              xpair ypair rest homit
          have hcoords :
              explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX
                  xpair (ypair :: rest) =
                explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX xpair rest :=
            if_neg homit
          calc
            (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
              (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                xpair (ypair :: rest))).map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.boxEdgeCoordinates) =
              (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                  xpair rest)).map
                (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                  d.boxEdgeCoordinates) := by
              exact congrArg
                (fun cells : List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε) =>
                  (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
                    cells).map
                    (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
                      d.boxEdgeCoordinates))
                hcells
            _ =
                explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX
                  xpair rest :=
              explicitFormulaRectangleSelectedEndpointDataFixedX_boxEdgeCoordinates
                xpair rest
            _ =
                explicitFormulaRectangleSelectedBoxEdgeCoordinatesOfFixedX
                  xpair (ypair :: rest) := hcoords.symm

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
  | [], ypairs => by exact Eq.refl _
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
        exact Eq.refl _
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

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
