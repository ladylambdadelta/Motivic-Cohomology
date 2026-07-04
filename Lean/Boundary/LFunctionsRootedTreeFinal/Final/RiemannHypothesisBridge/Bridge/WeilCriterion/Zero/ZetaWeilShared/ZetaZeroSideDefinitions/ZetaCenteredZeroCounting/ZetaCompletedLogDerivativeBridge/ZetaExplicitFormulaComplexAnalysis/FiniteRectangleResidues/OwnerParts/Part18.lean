import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part17

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

/-- Every regular grid cell in the constructed list comes from a concrete adjacent
endpoint datum in the input list. -/
theorem explicitFormulaRectangleRegularGridCellListOfEndpointData_mem
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε))
    {c : ExplicitFormulaRectangleRegularGridCell F T ε}
    (hc : c ∈ explicitFormulaRectangleRegularGridCellListOfEndpointData data) :
    ∃ d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε,
      d ∈ data ∧ d.toRegularGridCell = c :=
  List.mem_map.mp hc

/-- Boundary contribution of a single proof-carrying adjacent endpoint datum. -/
noncomputable def explicitFormulaRectangleRegularGridCellEndpointDataBoundary
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) : ℂ :=
  finiteRectangleSubdivisionCellBoundaryIntegral
    (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
    ((d.x₀ : ℂ) + (d.y₀ : ℂ) * Complex.I)
    ((d.x₁ : ℂ) + (d.y₁ : ℂ) * Complex.I)

/-- Boundary sum over a concrete finite list of proof-carrying adjacent endpoint data.
This is the constructive list-level counterpart of the regular-grid `Finset` sum. -/
noncomputable def explicitFormulaRectangleRegularGridEndpointDataBoundarySum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction) :
    List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) → ℂ
  | [] => 0
  | d :: rest =>
      explicitFormulaRectangleRegularGridCellEndpointDataBoundary f d +
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum f rest

/-- The endpoint-data boundary sum over the empty list is zero. -/
theorem explicitFormulaRectangleRegularGridEndpointDataBoundarySum_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction) :
    explicitFormulaRectangleRegularGridEndpointDataBoundarySum
      (F := F) (T := T) (ε := ε) f [] = 0 := by
  rfl

/-- The endpoint-data boundary sum over a cons list splits into the first selected cell
boundary and the remaining endpoint-data boundary sum. -/
theorem explicitFormulaRectangleRegularGridEndpointDataBoundarySum_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)
    (rest : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)) :
    explicitFormulaRectangleRegularGridEndpointDataBoundarySum f (d :: rest) =
      explicitFormulaRectangleRegularGridCellEndpointDataBoundary f d +
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum f rest := by
  rfl

/-- The endpoint-data boundary sum is additive under list append. -/
theorem explicitFormulaRectangleRegularGridEndpointDataBoundarySum_append
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (left right : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)) :
    explicitFormulaRectangleRegularGridEndpointDataBoundarySum f (left ++ right) =
      explicitFormulaRectangleRegularGridEndpointDataBoundarySum f left +
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum f right := by
  induction left with
  | nil =>
      calc
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum f ([] ++ right) =
            explicitFormulaRectangleRegularGridEndpointDataBoundarySum f right := by
          rfl
        _ =
            explicitFormulaRectangleRegularGridEndpointDataBoundarySum f [] +
              explicitFormulaRectangleRegularGridEndpointDataBoundarySum f right := by
          exact
            (zero_add
              (explicitFormulaRectangleRegularGridEndpointDataBoundarySum f right)).symm
  | cons d rest ih =>
      calc
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum
            f ((d :: rest) ++ right) =
          explicitFormulaRectangleRegularGridCellEndpointDataBoundary f d +
            explicitFormulaRectangleRegularGridEndpointDataBoundarySum f (rest ++ right) := by
          rfl
        _ =
          explicitFormulaRectangleRegularGridCellEndpointDataBoundary f d +
            (explicitFormulaRectangleRegularGridEndpointDataBoundarySum f rest +
              explicitFormulaRectangleRegularGridEndpointDataBoundarySum f right) := by
          exact congrArg
            (fun x : ℂ =>
              explicitFormulaRectangleRegularGridCellEndpointDataBoundary f d + x)
            ih
        _ =
          (explicitFormulaRectangleRegularGridCellEndpointDataBoundary f d +
            explicitFormulaRectangleRegularGridEndpointDataBoundarySum f rest) +
              explicitFormulaRectangleRegularGridEndpointDataBoundarySum f right := by
          exact
            (add_assoc
              (explicitFormulaRectangleRegularGridCellEndpointDataBoundary f d)
              (explicitFormulaRectangleRegularGridEndpointDataBoundarySum f rest)
              (explicitFormulaRectangleRegularGridEndpointDataBoundarySum f right)).symm
        _ =
          explicitFormulaRectangleRegularGridEndpointDataBoundarySum f (d :: rest) +
            explicitFormulaRectangleRegularGridEndpointDataBoundarySum f right := by
          rfl

/-- Boundary sum over the endpoint-data list for a cons horizontal adjacent-pair list
splits into the first fixed-horizontal row plus the recursively constructed remaining
rows. -/
theorem explicitFormulaRectangleRegularGridEndpointDataBoundarySum_adjacentPairLists_cons
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
                  a.re ∉ Set.uIcc xpair'.x₀ xpair'.x₁ ∨
                    a.im ∉ Set.uIcc ypair.y₀ ypair.y₁) :
    explicitFormulaRectangleRegularGridEndpointDataBoundarySum f
        (explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
          (xpair :: rest) ypairs homit) =
      explicitFormulaRectangleRegularGridEndpointDataBoundarySum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
            xpair ypairs
            (fun ypair hy =>
              homit xpair (List.mem_cons_self xpair rest) ypair hy))) +
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum f
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
    explicitFormulaRectangleRegularGridEndpointDataBoundarySum f
        (explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
          (xpair :: rest) ypairs homit) =
      explicitFormulaRectangleRegularGridEndpointDataBoundarySum f
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
          explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data)
        hlist
    _ =
      explicitFormulaRectangleRegularGridEndpointDataBoundarySum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
            xpair ypairs
            (fun ypair hy =>
              homit xpair (List.mem_cons_self xpair rest) ypair hy))) +
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum f
          (explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
            rest ypairs
            (fun xpair' hx' ypair hy =>
              homit xpair' (List.mem_cons_of_mem xpair hx') ypair hy)) := by
      exact
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum_append
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

/-- Boundary sum over the endpoint-data list for a fixed horizontal adjacent pair and a
cons vertical adjacent-pair list splits into the first cell and the remaining row. -/
theorem explicitFormulaRectangleRegularGridEndpointDataBoundarySum_fixedX_cons
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
              a.re ∉ Set.uIcc xpair.x₀ xpair.x₁ ∨
                a.im ∉ Set.uIcc ypair'.y₀ ypair'.y₁) :
    explicitFormulaRectangleRegularGridEndpointDataBoundarySum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
            xpair (ypair :: rest) homit)) =
      explicitFormulaRectangleRegularGridCellEndpointDataBoundary f
        (({ xpair := xpair
            ypair := ypair
            homit := homit ypair (List.mem_cons_self ypair rest) } :
              ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData) +
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
              xpair rest
              (fun ypair' hy' =>
                homit ypair' (List.mem_cons_of_mem ypair hy')))) := by
  rfl

/-- Boundary sum over the endpoint-data list for a fixed horizontal adjacent pair and an
empty vertical adjacent-pair list is zero. -/
theorem explicitFormulaRectangleRegularGridEndpointDataBoundarySum_fixedX_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (homit :
      ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε,
        ypair ∈
          ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) →
          ∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a.re ∉ Set.uIcc xpair.x₀ xpair.x₁ ∨
                a.im ∉ Set.uIcc ypair.y₀ ypair.y₁) :
    explicitFormulaRectangleRegularGridEndpointDataBoundarySum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
            xpair [] homit)) = 0 := by
  rfl

/-- A concrete endpoint-data boundary list sums to zero when every listed regular-cell
boundary vanishes. -/
theorem explicitFormulaRectangleRegularGridEndpointDataBoundarySum_eq_zero_of_forall_mem
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε))
    (hcell :
      ∀ d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε,
        d ∈ data →
          explicitFormulaRectangleRegularGridCellEndpointDataBoundary f d = 0) :
    explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data = 0 := by
  induction data with
  | nil =>
      exact explicitFormulaRectangleRegularGridEndpointDataBoundarySum_nil f
  | cons d rest ih =>
      have hd_zero :
          explicitFormulaRectangleRegularGridCellEndpointDataBoundary f d = 0 :=
        hcell d (List.mem_cons_self d rest)
      have hrest_zero :
          explicitFormulaRectangleRegularGridEndpointDataBoundarySum f rest = 0 :=
        ih
          (fun e he =>
            hcell e (List.mem_cons_of_mem d he))
      calc
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum f (d :: rest) =
            explicitFormulaRectangleRegularGridCellEndpointDataBoundary f d +
              explicitFormulaRectangleRegularGridEndpointDataBoundarySum f rest := by
          exact explicitFormulaRectangleRegularGridEndpointDataBoundarySum_cons f d rest
        _ = 0 + explicitFormulaRectangleRegularGridEndpointDataBoundarySum f rest := by
          exact congrArg
            (fun x : ℂ => x + explicitFormulaRectangleRegularGridEndpointDataBoundarySum f rest)
            hd_zero
        _ = 0 + 0 := by
          exact congrArg (fun x : ℂ => 0 + x) hrest_zero
        _ = 0 := by
          exact zero_add 0

/-- Bottom horizontal edge contribution of one endpoint-data cell. -/
noncomputable def explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) : ℂ :=
  ∫ x : ℝ in
      ((d.x₀ : ℂ) + (d.y₀ : ℂ) * Complex.I).re..
        ((d.x₁ : ℂ) + (d.y₁ : ℂ) * Complex.I).re,
    zetaCompletedExplicitFormulaContourIntegrand f
      (x + ((d.x₀ : ℂ) + (d.y₀ : ℂ) * Complex.I).im * Complex.I)

/-- Top horizontal edge contribution of one endpoint-data cell. -/
noncomputable def explicitFormulaRectangleRegularGridCellEndpointDataTopEdge
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) : ℂ :=
  ∫ x : ℝ in
      ((d.x₀ : ℂ) + (d.y₀ : ℂ) * Complex.I).re..
        ((d.x₁ : ℂ) + (d.y₁ : ℂ) * Complex.I).re,
    zetaCompletedExplicitFormulaContourIntegrand f
      (x + ((d.x₁ : ℂ) + (d.y₁ : ℂ) * Complex.I).im * Complex.I)

/-- Tangent-oriented right vertical edge contribution of one endpoint-data cell. -/
noncomputable def explicitFormulaRectangleRegularGridCellEndpointDataRightEdge
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) : ℂ :=
  Complex.I •
    ∫ y : ℝ in
      ((d.x₀ : ℂ) + (d.y₀ : ℂ) * Complex.I).im..
        ((d.x₁ : ℂ) + (d.y₁ : ℂ) * Complex.I).im,
      zetaCompletedExplicitFormulaContourIntegrand f
        (((d.x₁ : ℂ) + (d.y₁ : ℂ) * Complex.I).re + y * Complex.I)

/-- Tangent-oriented left vertical edge contribution of one endpoint-data cell. -/
noncomputable def explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) : ℂ :=
  Complex.I •
    ∫ y : ℝ in
      ((d.x₀ : ℂ) + (d.y₀ : ℂ) * Complex.I).im..
        ((d.x₁ : ℂ) + (d.y₁ : ℂ) * Complex.I).im,
      zetaCompletedExplicitFormulaContourIntegrand f
        (((d.x₀ : ℂ) + (d.y₀ : ℂ) * Complex.I).re + y * Complex.I)

/-- One endpoint-data boundary decomposes into its four oriented edge contributions. -/
theorem explicitFormulaRectangleRegularGridCellEndpointDataBoundary_eq_edges
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :
    explicitFormulaRectangleRegularGridCellEndpointDataBoundary f d =
      explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f d -
        explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f d +
          (explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f d -
            explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f d) := by
  let b : ℂ := explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f d
  let t : ℂ := explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f d
  let r : ℂ := explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f d
  let l : ℂ := explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f d
  change (b - t + r) - l = b - t + (r - l)
  calc
    (b - t + r) - l = (b - t + r) + -l := by
      exact sub_eq_add_neg (b - t + r) l
    _ = b - t + (r + -l) := by
      exact add_assoc (b - t) r (-l)
    _ = b - t + (r - l) := by
      exact congrArg
        (fun z : ℂ => b - t + z)
        (sub_eq_add_neg r l).symm

/-- List sum of endpoint-data bottom edges. -/
noncomputable def explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction) :
    List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) → ℂ
  | [] => 0
  | d :: rest =>
      explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f d +
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f rest

/-- List sum of endpoint-data top edges. -/
noncomputable def explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction) :
    List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) → ℂ
  | [] => 0
  | d :: rest =>
      explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f d +
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f rest

/-- List sum of endpoint-data tangent-oriented right edges. -/
noncomputable def explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction) :
    List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) → ℂ
  | [] => 0
  | d :: rest =>
      explicitFormulaRectangleRegularGridCellEndpointDataRightEdge f d +
        explicitFormulaRectangleRegularGridEndpointDataRightEdgeSum f rest

/-- List sum of endpoint-data tangent-oriented left edges. -/
noncomputable def explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction) :
    List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) → ℂ
  | [] => 0
  | d :: rest =>
      explicitFormulaRectangleRegularGridCellEndpointDataLeftEdge f d +
        explicitFormulaRectangleRegularGridEndpointDataLeftEdgeSum f rest

/-- The endpoint-data bottom-edge sum is additive under list append. -/
theorem explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum_append
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (left right : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)) :
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f (left ++ right) =
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f left +
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f right := by
  induction left with
  | nil =>
      calc
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f ([] ++ right) =
            explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f right := by
          rfl
        _ =
            explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f [] +
              explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f right := by
          exact
            (zero_add
              (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f right)).symm
  | cons d rest ih =>
      calc
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum
            f ((d :: rest) ++ right) =
          explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f d +
            explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f (rest ++ right) := by
          rfl
        _ =
          explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f d +
            (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f rest +
              explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f right) := by
          exact congrArg
            (fun x : ℂ =>
              explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f d + x)
            ih
        _ =
          (explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f d +
            explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f rest) +
              explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f right := by
          exact
            (add_assoc
              (explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f d)
              (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f rest)
              (explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f right)).symm
        _ =
          explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f (d :: rest) +
            explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f right := by
          rfl

/-- Bottom-edge sum over the endpoint-data list for a fixed horizontal adjacent pair and
a cons vertical adjacent-pair list splits into the first bottom edge and the remaining
row bottom-edge sum. -/
theorem explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum_fixedX_cons
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
              a.re ∉ Set.uIcc xpair.x₀ xpair.x₁ ∨
                a.im ∉ Set.uIcc ypair'.y₀ ypair'.y₁) :
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
            xpair (ypair :: rest) homit)) =
      explicitFormulaRectangleRegularGridCellEndpointDataBottomEdge f
        (({ xpair := xpair
            ypair := ypair
            homit := homit ypair (List.mem_cons_self ypair rest) } :
              ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε).toEndpointData) +
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
            (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
              xpair rest
              (fun ypair' hy' =>
                homit ypair' (List.mem_cons_of_mem ypair hy')))) := by
  rfl

/-- Bottom-edge sum over the endpoint-data list for a fixed horizontal adjacent pair and
an empty vertical adjacent-pair list is zero. -/
theorem explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum_fixedX_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (homit :
      ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε,
        ypair ∈
          ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) →
          ∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a.re ∉ Set.uIcc xpair.x₀ xpair.x₁ ∨
                a.im ∉ Set.uIcc ypair.y₀ ypair.y₁) :
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
            xpair [] homit)) = 0 := by
  rfl

/-- Bottom-edge sum over a cons horizontal adjacent-pair list splits into the first row
bottom-edge sum plus the recursively constructed remaining rows. -/
theorem explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum_adjacentPairLists_cons
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
                  a.re ∉ Set.uIcc xpair'.x₀ xpair'.x₁ ∨
                    a.im ∉ Set.uIcc ypair.y₀ ypair.y₁) :
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
          (xpair :: rest) ypairs homit) =
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
            xpair ypairs
            (fun ypair hy =>
              homit xpair (List.mem_cons_self xpair rest) ypair hy))) +
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
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
    explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
          (xpair :: rest) ypairs homit) =
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
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
          explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f data)
        hlist
    _ =
      explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
          (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
            xpair ypairs
            (fun ypair hy =>
              homit xpair (List.mem_cons_self xpair rest) ypair hy))) +
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum f
          (explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
            rest ypairs
            (fun xpair' hx' ypair hy =>
              homit xpair' (List.mem_cons_of_mem xpair hx') ypair hy)) := by
      exact
        explicitFormulaRectangleRegularGridEndpointDataBottomEdgeSum_append
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

/-- The endpoint-data top-edge sum is additive under list append. -/
theorem explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum_append
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (left right : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)) :
    explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f (left ++ right) =
      explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f left +
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f right := by
  induction left with
  | nil =>
      calc
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f ([] ++ right) =
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f right := by
          rfl
        _ =
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f [] +
              explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f right := by
          exact
            (zero_add
              (explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f right)).symm
  | cons d rest ih =>
      calc
        explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum
            f ((d :: rest) ++ right) =
          explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f d +
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f (rest ++ right) := by
          rfl
        _ =
          explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f d +
            (explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f rest +
              explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f right) := by
          exact congrArg
            (fun x : ℂ =>
              explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f d + x)
            ih
        _ =
          (explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f d +
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f rest) +
              explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f right := by
          exact
            (add_assoc
              (explicitFormulaRectangleRegularGridCellEndpointDataTopEdge f d)
              (explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f rest)
              (explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f right)).symm
        _ =
          explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f (d :: rest) +
            explicitFormulaRectangleRegularGridEndpointDataTopEdgeSum f right := by
          rfl

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
