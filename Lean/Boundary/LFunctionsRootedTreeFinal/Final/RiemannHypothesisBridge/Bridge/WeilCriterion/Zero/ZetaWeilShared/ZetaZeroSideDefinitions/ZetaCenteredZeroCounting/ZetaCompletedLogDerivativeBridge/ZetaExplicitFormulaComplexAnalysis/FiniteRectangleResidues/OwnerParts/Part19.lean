import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part18

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

/-- Top-edge sum over the endpoint-data list for a fixed horizontal adjacent pair and a
cons vertical adjacent-pair list splits into the first top edge and the remaining row
top-edge sum. -/
theorem explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_fixedX_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))
    (homit :
      ∀ ypair' : ExplicitFormulaRectangleYAdjacentEndpointPair T ε,
        ypair' ∈ ypair :: rest →
          ∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a.re ∉ [[xpair.x₀, xpair.x₁]] ∨
                a.im ∉ [[ypair'.y₀, ypair'.y₁]]) :
    explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
            xpair (ypair :: rest) homit)) =
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
          homit := homit ypair (List.mem_cons_self ypair rest) } :
            ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) +
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
              xpair rest
              (fun ypair' hy' =>
                homit ypair' (List.mem_cons_of_mem ypair hy')))) := by
  rfl

/-- Top-edge sum over the endpoint-data list for a fixed horizontal adjacent pair and an
empty vertical adjacent-pair list is zero. -/
theorem explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_fixedX_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (homit :
      ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε,
        ypair ∈
          ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) →
          ∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a.re ∉ [[xpair.x₀, xpair.x₁]] ∨
                a.im ∉ [[ypair.y₀, ypair.y₁]]) :
    explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
            xpair [] homit)) = 0 := by
  rfl

/-- Top-edge sum over a cons horizontal adjacent-pair list splits into the first row
top-edge sum plus the recursively constructed remaining rows. -/
theorem explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_adjacentPairLists_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (rest : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))
    (homit :
      ∀ xpair' : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε,
        xpair' ∈ xpair :: rest →
          ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε,
            ypair ∈ ypairs →
              ∀ a : ℂ,
                a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a.re ∉ [[xpair'.x₀, xpair'.x₁]] ∨
                    a.im ∉ [[ypair.y₀, ypair.y₁]]) :
    explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
          (xpair :: rest) ypairs homit) =
      explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
            xpair ypairs
            (fun ypair hy =>
              homit xpair (List.mem_cons_self xpair rest) ypair hy))) +
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
            rest ypairs
            (fun xpair' hx' ypair hy =>
              homit xpair' (List.mem_cons_of_mem xpair hx') ypair hy)) := by
  have hlist :
      explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
          (xpair :: rest) ypairs homit =
        explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
            xpair ypairs
            (fun ypair hy =>
              homit xpair (List.mem_cons_self xpair rest) ypair hy)) ++
          explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
            rest ypairs
            (fun xpair' hx' ypair hy =>
              homit xpair' (List.mem_cons_of_mem xpair hx') ypair hy) :=
    explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists_cons
      xpair rest ypairs homit
  calc
    explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
          (xpair :: rest) ypairs homit) =
      explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
            xpair ypairs
            (fun ypair hy =>
              homit xpair (List.mem_cons_self xpair rest) ypair hy)) ++
          explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
            rest ypairs
            (fun xpair' hx' ypair hy =>
              homit xpair' (List.mem_cons_of_mem xpair hx') ypair hy)) := by
      exact congrArg
        (fun data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) =>
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f data)
        hlist
    _ =
      explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
            xpair ypairs
            (fun ypair hy =>
              homit xpair (List.mem_cons_self xpair rest) ypair hy))) +
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
            rest ypairs
            (fun xpair' hx' ypair hy =>
              homit xpair' (List.mem_cons_of_mem xpair hx') ypair hy)) := by
      exact
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_append
          f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
              xpair ypairs
              (fun ypair hy =>
                homit xpair (List.mem_cons_self xpair rest) ypair hy)))
          (explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
            rest ypairs
            (fun xpair' hx' ypair hy =>
              homit xpair' (List.mem_cons_of_mem xpair hx') ypair hy))

/-- The endpoint-data right-edge sum is additive under list append. -/
theorem explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum_append
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (left right : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)) :
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f (left ++ right) =
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f left +
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f right := by
  induction left with
  | nil =>
      calc
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f ([] ++ right) =
            explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f right := by
          rfl
        _ =
            explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f [] +
              explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f right := by
          exact
            (zero_add
              (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f right)).symm
  | cons d rest ih =>
      calc
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum
            f ((d :: rest) ++ right) =
          explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f d +
            explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f (rest ++ right) := by
          rfl
        _ =
          explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f d +
            (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f rest +
              explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f right) := by
          exact congrArg
            (fun x : ℂ =>
              explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f d + x)
            ih
        _ =
          (explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f d +
            explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f rest) +
              explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f right := by
          exact
            (add_assoc
              (explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f d)
              (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f rest)
              (explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f right)).symm
        _ =
          explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f (d :: rest) +
            explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f right := by
          rfl

/-- Right-edge sum over the endpoint-data list for a fixed horizontal adjacent pair and
a cons vertical adjacent-pair list splits into the first right edge and the remaining
row right-edge sum. -/
theorem explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum_fixedX_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))
    (homit :
      ∀ ypair' : ExplicitFormulaRectangleYAdjacentEndpointPair T ε,
        ypair' ∈ ypair :: rest →
          ∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a.re ∉ [[xpair.x₀, xpair.x₁]] ∨
                a.im ∉ [[ypair'.y₀, ypair'.y₁]]) :
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
            xpair (ypair :: rest) homit)) =
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
          homit := homit ypair (List.mem_cons_self ypair rest) } :
            ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) +
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
              xpair rest
              (fun ypair' hy' =>
                homit ypair' (List.mem_cons_of_mem ypair hy')))) := by
  rfl

/-- Right-edge sum over the endpoint-data list for a fixed horizontal adjacent pair and
an empty vertical adjacent-pair list is zero. -/
theorem explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum_fixedX_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (homit :
      ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε,
        ypair ∈
          ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) →
          ∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a.re ∉ [[xpair.x₀, xpair.x₁]] ∨
                a.im ∉ [[ypair.y₀, ypair.y₁]]) :
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
            xpair [] homit)) = 0 := by
  rfl

/-- Right-edge sum over a cons horizontal adjacent-pair list splits into the first row
right-edge sum plus the recursively constructed remaining rows. -/
theorem explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum_adjacentPairLists_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (rest : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))
    (homit :
      ∀ xpair' : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε,
        xpair' ∈ xpair :: rest →
          ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε,
            ypair ∈ ypairs →
              ∀ a : ℂ,
                a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a.re ∉ [[xpair'.x₀, xpair'.x₁]] ∨
                    a.im ∉ [[ypair.y₀, ypair.y₁]]) :
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
          (xpair :: rest) ypairs homit) =
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
            xpair ypairs
            (fun ypair hy =>
              homit xpair (List.mem_cons_self xpair rest) ypair hy))) +
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
            rest ypairs
            (fun xpair' hx' ypair hy =>
              homit xpair' (List.mem_cons_of_mem xpair hx') ypair hy)) := by
  have hlist :
      explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
          (xpair :: rest) ypairs homit =
        explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
            xpair ypairs
            (fun ypair hy =>
              homit xpair (List.mem_cons_self xpair rest) ypair hy)) ++
          explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
            rest ypairs
            (fun xpair' hx' ypair hy =>
              homit xpair' (List.mem_cons_of_mem xpair hx') ypair hy) :=
    explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists_cons
      xpair rest ypairs homit
  calc
    explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
          (xpair :: rest) ypairs homit) =
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
            xpair ypairs
            (fun ypair hy =>
              homit xpair (List.mem_cons_self xpair rest) ypair hy)) ++
          explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
            rest ypairs
            (fun xpair' hx' ypair hy =>
              homit xpair' (List.mem_cons_of_mem xpair hx') ypair hy)) := by
      exact congrArg
        (fun data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) =>
          explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f data)
        hlist
    _ =
      explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
            xpair ypairs
            (fun ypair hy =>
              homit xpair (List.mem_cons_self xpair rest) ypair hy))) +
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
            rest ypairs
            (fun xpair' hx' ypair hy =>
              homit xpair' (List.mem_cons_of_mem xpair hx') ypair hy)) := by
      exact
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum_append
          f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
              xpair ypairs
              (fun ypair hy =>
                homit xpair (List.mem_cons_self xpair rest) ypair hy)))
          (explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
            rest ypairs
            (fun xpair' hx' ypair hy =>
              homit xpair' (List.mem_cons_of_mem xpair hx') ypair hy))

/-- The endpoint-data left-edge sum is additive under list append. -/
theorem explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum_append
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (left right : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)) :
    explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f (left ++ right) =
      explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f left +
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f right := by
  induction left with
  | nil =>
      calc
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f ([] ++ right) =
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f right := by
          rfl
        _ =
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f [] +
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f right := by
          exact
            (zero_add
              (explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f right)).symm
  | cons d rest ih =>
      calc
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum
            f ((d :: rest) ++ right) =
          explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f d +
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f (rest ++ right) := by
          rfl
        _ =
          explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f d +
            (explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f rest +
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f right) := by
          exact congrArg
            (fun x : ℂ =>
              explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f d + x)
            ih
        _ =
          (explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f d +
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f rest) +
              explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f right := by
          exact
            (add_assoc
              (explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f d)
              (explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f rest)
              (explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f right)).symm
        _ =
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f (d :: rest) +
            explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f right := by
          rfl

/-- Left-edge sum over the endpoint-data list for a fixed horizontal adjacent pair and
a cons vertical adjacent-pair list splits into the first left edge and the remaining
row left-edge sum. -/
theorem explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum_fixedX_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (rest : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))
    (homit :
      ∀ ypair' : ExplicitFormulaRectangleYAdjacentEndpointPair T ε,
        ypair' ∈ ypair :: rest →
          ∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a.re ∉ [[xpair.x₀, xpair.x₁]] ∨
                a.im ∉ [[ypair'.y₀, ypair'.y₁]]) :
    explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
            xpair (ypair :: rest) homit)) =
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
          homit := homit ypair (List.mem_cons_self ypair rest) } :
            ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) +
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
              xpair rest
              (fun ypair' hy' =>
                homit ypair' (List.mem_cons_of_mem ypair hy')))) := by
  rfl

/-- Left-edge sum over the endpoint-data list for a fixed horizontal adjacent pair and
an empty vertical adjacent-pair list is zero. -/
theorem explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum_fixedX_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (homit :
      ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε,
        ypair ∈
          ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) →
          ∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a.re ∉ [[xpair.x₀, xpair.x₁]] ∨
                a.im ∉ [[ypair.y₀, ypair.y₁]]) :
    explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
            xpair [] homit)) = 0 := by
  rfl

/-- Left-edge sum over a cons horizontal adjacent-pair list splits into the first row
left-edge sum plus the recursively constructed remaining rows. -/
theorem explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum_adjacentPairLists_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (rest : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))
    (homit :
      ∀ xpair' : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε,
        xpair' ∈ xpair :: rest →
          ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε,
            ypair ∈ ypairs →
              ∀ a : ℂ,
                a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a.re ∉ [[xpair'.x₀, xpair'.x₁]] ∨
                    a.im ∉ [[ypair.y₀, ypair.y₁]]) :
    explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
          (xpair :: rest) ypairs homit) =
      explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
            xpair ypairs
            (fun ypair hy =>
              homit xpair (List.mem_cons_self xpair rest) ypair hy))) +
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
            rest ypairs
            (fun xpair' hx' ypair hy =>
              homit xpair' (List.mem_cons_of_mem xpair hx') ypair hy)) := by
  have hlist :
      explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
          (xpair :: rest) ypairs homit =
        explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
            xpair ypairs
            (fun ypair hy =>
              homit xpair (List.mem_cons_self xpair rest) ypair hy)) ++
          explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
            rest ypairs
            (fun xpair' hx' ypair hy =>
              homit xpair' (List.mem_cons_of_mem xpair hx') ypair hy) :=
    explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists_cons
      xpair rest ypairs homit
  calc
    explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
          (xpair :: rest) ypairs homit) =
      explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
            xpair ypairs
            (fun ypair hy =>
              homit xpair (List.mem_cons_self xpair rest) ypair hy)) ++
          explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
            rest ypairs
            (fun xpair' hx' ypair hy =>
              homit xpair' (List.mem_cons_of_mem xpair hx') ypair hy)) := by
      exact congrArg
        (fun data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) =>
          explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f data)
        hlist
    _ =
      explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
            xpair ypairs
            (fun ypair hy =>
              homit xpair (List.mem_cons_self xpair rest) ypair hy))) +
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
            rest ypairs
            (fun xpair' hx' ypair hy =>
              homit xpair' (List.mem_cons_of_mem xpair hx') ypair hy)) := by
      exact
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum_append
          f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
              xpair ypairs
              (fun ypair hy =>
                homit xpair (List.mem_cons_self xpair rest) ypair hy)))
          (explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
            rest ypairs
            (fun xpair' hx' ypair hy =>
              homit xpair' (List.mem_cons_of_mem xpair hx') ypair hy))

/-- Two horizontally adjacent endpoint-data cells cancel their common vertical edge once
the right edge of the left cell is identified with the left edge of the right cell. -/
theorem explicitFormulaRectangleRegularGridEndpointData_twoHorizontalCells_verticalEdgeCancel
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (leftCell rightCell : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)
    (hshared :
      explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f leftCell =
        explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f rightCell) :
    (explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f leftCell -
        explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f leftCell) +
        (explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f rightCell -
          explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f rightCell) =
      explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f rightCell -
        explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f leftCell := by
  let A : ℂ := explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f leftCell
  let B : ℂ := explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f leftCell
  let C : ℂ := explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f rightCell
  let D : ℂ := explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f rightCell
  have hBD : B = D := hshared
  calc
    (B - A) + (C - D) = (B - A) + (C - B) := by
      exact congrArg (fun z : ℂ => (B - A) + (C - z)) hBD.symm
    _ = (C - B) + (B - A) := by
      exact add_comm (B - A) (C - B)
    _ = C - A := by
      exact finiteRectangleSubdivisionSharedHorizontalEdges_cancel C B A

/-- Two vertically adjacent endpoint-data cells cancel their common horizontal edge once
the top edge of the lower cell is identified with the bottom edge of the upper cell. -/
theorem explicitFormulaRectangleRegularGridEndpointData_twoVerticalCells_horizontalEdgeCancel
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (lowerCell upperCell : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)
    (hshared :
      explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f lowerCell =
        explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f upperCell) :
    (explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f lowerCell -
        explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f lowerCell) +
        (explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f upperCell -
          explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f upperCell) =
      explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f lowerCell -
        explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f upperCell := by
  let A : ℂ := explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f lowerCell
  let B : ℂ := explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f lowerCell
  let C : ℂ := explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f upperCell
  let D : ℂ := explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f upperCell
  have hBC : B = C := hshared
  calc
    (A - B) + (C - D) = (A - B) + (B - D) := by
      exact congrArg (fun z : ℂ => (A - B) + (z - D)) hBC.symm
    _ = A - D := by
      exact finiteRectangleSubdivisionSharedHorizontalEdges_cancel A B D

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
