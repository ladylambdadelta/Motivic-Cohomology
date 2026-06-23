import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part20

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

/-- The grid index of a regular cell constructed from adjacent endpoints is the four
endpoint coordinates used in the constructor. -/
theorem explicitFormulaRectangleRegularGridCellOfAdjacentEndpoints_cell
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (x₀ x₁ y₀ y₁ : ℝ)
    (hx₀ : x₀ ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε)
    (hx₁ : x₁ ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε)
    (hy₀ : y₀ ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε)
    (hy₁ : y₁ ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε)
    (hx_order : x₀ < x₁)
    (hy_order : y₀ < y₁)
    (hx_adj : explicitFormulaRectangleNoIntermediateXEndpoint F T ε x₀ x₁)
    (hy_adj : explicitFormulaRectangleNoIntermediateYEndpoint T ε y₀ y₁)
    (homit :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          a.re ∉ [[x₀, x₁]] ∨ a.im ∉ [[y₀, y₁]]) :
    (explicitFormulaRectangleRegularGridCellOfAdjacentEndpoints
      F T ε x₀ x₁ y₀ y₁ hx₀ hx₁ hy₀ hy₁
      hx_order hy_order hx_adj hy_adj homit).cell =
      ((x₀, x₁), (y₀, y₁)) := by
  rfl

/-- Lower-left corner of a proof-carrying regular grid cell. -/
def ExplicitFormulaRectangleRegularGridCell.lower
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularGridCell F T ε) : ℂ :=
  explicitFormulaRectangleGridCellLower c.cell

/-- Upper-right corner of a proof-carrying regular grid cell. -/
def ExplicitFormulaRectangleRegularGridCell.upper
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularGridCell F T ε) : ℂ :=
  explicitFormulaRectangleGridCellUpper c.cell

/-- Lower corner of a regular grid cell constructed from adjacent endpoints. -/
theorem explicitFormulaRectangleRegularGridCellOfAdjacentEndpoints_lower
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (x₀ x₁ y₀ y₁ : ℝ)
    (hx₀ : x₀ ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε)
    (hx₁ : x₁ ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε)
    (hy₀ : y₀ ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε)
    (hy₁ : y₁ ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε)
    (hx_order : x₀ < x₁)
    (hy_order : y₀ < y₁)
    (hx_adj : explicitFormulaRectangleNoIntermediateXEndpoint F T ε x₀ x₁)
    (hy_adj : explicitFormulaRectangleNoIntermediateYEndpoint T ε y₀ y₁)
    (homit :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          a.re ∉ [[x₀, x₁]] ∨ a.im ∉ [[y₀, y₁]]) :
    (explicitFormulaRectangleRegularGridCellOfAdjacentEndpoints
      F T ε x₀ x₁ y₀ y₁ hx₀ hx₁ hy₀ hy₁
      hx_order hy_order hx_adj hy_adj homit).lower =
      (x₀ : ℂ) + (y₀ : ℂ) * Complex.I := by
  rfl

/-- Upper corner of a regular grid cell constructed from adjacent endpoints. -/
theorem explicitFormulaRectangleRegularGridCellOfAdjacentEndpoints_upper
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (x₀ x₁ y₀ y₁ : ℝ)
    (hx₀ : x₀ ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε)
    (hx₁ : x₁ ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε)
    (hy₀ : y₀ ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε)
    (hy₁ : y₁ ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε)
    (hx_order : x₀ < x₁)
    (hy_order : y₀ < y₁)
    (hx_adj : explicitFormulaRectangleNoIntermediateXEndpoint F T ε x₀ x₁)
    (hy_adj : explicitFormulaRectangleNoIntermediateYEndpoint T ε y₀ y₁)
    (homit :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          a.re ∉ [[x₀, x₁]] ∨ a.im ∉ [[y₀, y₁]]) :
    (explicitFormulaRectangleRegularGridCellOfAdjacentEndpoints
      F T ε x₀ x₁ y₀ y₁ hx₀ hx₁ hy₀ hy₁
      hx_order hy_order hx_adj hy_adj homit).upper =
      (x₁ : ℂ) + (y₁ : ℂ) * Complex.I := by
  rfl

/-- The endpoint-data boundary contribution is the same cell-boundary integral as the
corresponding proof-carrying regular-grid cell. -/
theorem explicitFormulaRectangleRegularGridCellEndpointDataBoundary_eq_toRegularGridCellBoundary
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :
    explicitFormulaRectangleRegularGridCellEndpointDataBoundary f d =
      finiteRectangleSubdivisionCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        d.toRegularGridCell.lower
        d.toRegularGridCell.upper := by
  rfl

/-- The proof-carrying regular-grid cell boundary integral folds back to the endpoint-data
boundary contribution. -/
theorem explicitFormulaRectangleRegularGridCellBoundary_eq_endpointDataBoundary
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :
    finiteRectangleSubdivisionCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        d.toRegularGridCell.lower
        d.toRegularGridCell.upper =
      explicitFormulaRectangleRegularGridCellEndpointDataBoundary f d := by
  exact
    (explicitFormulaRectangleRegularGridCellEndpointDataBoundary_eq_toRegularGridCellBoundary
      f d).symm

/-- Boundary sum over a concrete list of proof-carrying regular grid cells.  This is the
list-level analogue of the `Finset` regular-grid boundary sum and does not require
`DecidableEq` on proof-carrying cells. -/
noncomputable def explicitFormulaRectangleRegularGridCellBoundaryListSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction) :
    List (ExplicitFormulaRectangleRegularGridCell F T ε) → ℂ
  | [] => 0
  | c :: rest =>
      finiteRectangleSubdivisionCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        c.lower c.upper +
          explicitFormulaRectangleRegularGridCellBoundaryListSum f rest

/-- The regular-grid-cell boundary sum over the empty list is zero. -/
theorem explicitFormulaRectangleRegularGridCellBoundaryListSum_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction) :
    explicitFormulaRectangleRegularGridCellBoundaryListSum
      (F := F) (T := T) (ε := ε) f [] = 0 := by
  rfl

/-- The regular-grid-cell boundary sum over a cons list splits into the first selected
cell boundary and the remaining list boundary sum. -/
theorem explicitFormulaRectangleRegularGridCellBoundaryListSum_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (c : ExplicitFormulaRectangleRegularGridCell F T ε)
    (rest : List (ExplicitFormulaRectangleRegularGridCell F T ε)) :
    explicitFormulaRectangleRegularGridCellBoundaryListSum f (c :: rest) =
      finiteRectangleSubdivisionCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        c.lower c.upper +
          explicitFormulaRectangleRegularGridCellBoundaryListSum f rest := by
  rfl

/-- Duplicate-safe finite carrier associated to a concrete regular-cell list whose
underlying multiset has already been proved nodup.  This is the owner bridge from the
constructive list representation to a `Finset`; it performs no deduplication and requires
no decidable equality on proof-carrying cells. -/
def explicitFormulaRectangleRegularGridCellFinsetOfNodupList
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (cells : List (ExplicitFormulaRectangleRegularGridCell F T ε))
    (hnodup :
      (cells : Multiset (ExplicitFormulaRectangleRegularGridCell F T ε)).Nodup) :
    Finset (ExplicitFormulaRectangleRegularGridCell F T ε) :=
  ⟨cells, hnodup⟩

/-- The duplicate-safe finite carrier has exactly the supplied list as its underlying
multiset. -/
theorem explicitFormulaRectangleRegularGridCellFinsetOfNodupList_val
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (cells : List (ExplicitFormulaRectangleRegularGridCell F T ε))
    (hnodup :
      (cells : Multiset (ExplicitFormulaRectangleRegularGridCell F T ε)).Nodup) :
    (explicitFormulaRectangleRegularGridCellFinsetOfNodupList cells hnodup).val =
      (cells : Multiset (ExplicitFormulaRectangleRegularGridCell F T ε)) := by
  rfl

/-- The concrete regular-cell boundary list sum is the ordinary list sum of the associated
cell-boundary function. -/
theorem explicitFormulaRectangleRegularGridCellBoundaryListSum_eq_list_sum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (cells : List (ExplicitFormulaRectangleRegularGridCell F T ε)) :
    explicitFormulaRectangleRegularGridCellBoundaryListSum f cells =
      (cells.map
        (fun c : ExplicitFormulaRectangleRegularGridCell F T ε =>
          finiteRectangleSubdivisionCellBoundaryIntegral
            (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
            c.lower c.upper)).sum := by
  induction cells with
  | nil =>
      rfl
  | cons c rest ih =>
      calc
        explicitFormulaRectangleRegularGridCellBoundaryListSum f (c :: rest) =
            finiteRectangleSubdivisionCellBoundaryIntegral
                (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                c.lower c.upper +
              explicitFormulaRectangleRegularGridCellBoundaryListSum f rest := by
          rfl
        _ =
            finiteRectangleSubdivisionCellBoundaryIntegral
                (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                c.lower c.upper +
              (rest.map
                (fun c : ExplicitFormulaRectangleRegularGridCell F T ε =>
                  finiteRectangleSubdivisionCellBoundaryIntegral
                    (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                    c.lower c.upper)).sum := by
          exact congrArg
            (fun x : ℂ =>
              finiteRectangleSubdivisionCellBoundaryIntegral
                  (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                  c.lower c.upper + x)
            ih
        _ =
            ((c :: rest).map
              (fun c : ExplicitFormulaRectangleRegularGridCell F T ε =>
                finiteRectangleSubdivisionCellBoundaryIntegral
                  (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                  c.lower c.upper)).sum := by
          rfl

/-- A nodup concrete regular-cell list has the same boundary sum as its duplicate-safe
`Finset.mk` carrier.  This is the list/`Finset` boundary-sum bridge needed by the
proof-carrying-cell subdivision path. -/
theorem explicitFormulaRectangleRegularGridCellBoundaryListSum_eq_boundarySum_finsetOfNodupList
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (cells : List (ExplicitFormulaRectangleRegularGridCell F T ε))
    (hnodup :
      (cells : Multiset (ExplicitFormulaRectangleRegularGridCell F T ε)).Nodup) :
    explicitFormulaRectangleRegularGridCellBoundaryListSum f cells =
      explicitFormulaRectangleRegularGridCellBoundarySum f
        (explicitFormulaRectangleRegularGridCellFinsetOfNodupList cells hnodup) := by
  let B : ExplicitFormulaRectangleRegularGridCell F T ε → ℂ :=
    fun c =>
      finiteRectangleSubdivisionCellBoundaryIntegral
        (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
        c.lower c.upper
  have hlist :
      explicitFormulaRectangleRegularGridCellBoundaryListSum f cells =
        (cells.map B).sum :=
    explicitFormulaRectangleRegularGridCellBoundaryListSum_eq_list_sum f cells
  have hfinset :
      explicitFormulaRectangleRegularGridCellBoundarySum f
          (explicitFormulaRectangleRegularGridCellFinsetOfNodupList cells hnodup) =
        ((cells : Multiset (ExplicitFormulaRectangleRegularGridCell F T ε)).map B).sum := by
    calc
      explicitFormulaRectangleRegularGridCellBoundarySum f
          (explicitFormulaRectangleRegularGridCellFinsetOfNodupList cells hnodup) =
          ∑ c in explicitFormulaRectangleRegularGridCellFinsetOfNodupList cells hnodup,
            B c := by
        rfl
      _ = ((cells : Multiset (ExplicitFormulaRectangleRegularGridCell F T ε)).map B).sum := by
        exact Finset.sum_mk
          (cells : Multiset (ExplicitFormulaRectangleRegularGridCell F T ε))
          hnodup B
  calc
    explicitFormulaRectangleRegularGridCellBoundaryListSum f cells =
        (cells.map B).sum := hlist
    _ = ((cells : Multiset (ExplicitFormulaRectangleRegularGridCell F T ε)).map B).sum := by
      rfl
    _ =
        explicitFormulaRectangleRegularGridCellBoundarySum f
          (explicitFormulaRectangleRegularGridCellFinsetOfNodupList cells hnodup) := by
      exact hfinset.symm

/-- Fold a subdivision equality stated over a nodup concrete regular-cell list to the
regular-grid `Finset` boundary-sum normalization. -/
theorem explicitFormulaRectangleRegularGridCellBoundarySum_eq_of_nodup_cellBoundaryListSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (cells : List (ExplicitFormulaRectangleRegularGridCell F T ε))
    (hnodup :
      (cells : Multiset (ExplicitFormulaRectangleRegularGridCell F T ε)).Nodup)
    {X : ℂ}
    (h :
      X = explicitFormulaRectangleRegularGridCellBoundaryListSum f cells) :
    X =
      explicitFormulaRectangleRegularGridCellBoundarySum f
        (explicitFormulaRectangleRegularGridCellFinsetOfNodupList cells hnodup) :=
  Eq.trans h
    (explicitFormulaRectangleRegularGridCellBoundaryListSum_eq_boundarySum_finsetOfNodupList
      f cells hnodup)

/-- Mapping endpoint data to proof-carrying regular cells preserves the concrete boundary
sum.  This is the list-level replacement for quotienting the endpoint-data construction
through a filtered `Finset`. -/
theorem explicitFormulaRectangleRegularGridEndpointDataBoundarySum_eq_cellBoundaryListSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)) :
    explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data =
      explicitFormulaRectangleRegularGridCellBoundaryListSum f
        (explicitFormulaRectangleRegularGridCellListOfEndpointData data) := by
  induction data with
  | nil =>
      calc
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum f [] = 0 := by
          exact explicitFormulaRectangleRegularGridEndpointDataBoundarySum_nil f
        _ =
            explicitFormulaRectangleRegularGridCellBoundaryListSum
              f (explicitFormulaRectangleRegularGridCellListOfEndpointData
                ([] : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε))) := by
          exact
            (explicitFormulaRectangleRegularGridCellBoundaryListSum_nil
              (F := F) (T := T) (ε := ε) f).symm
  | cons d rest ih =>
      calc
        explicitFormulaRectangleRegularGridEndpointDataBoundarySum f (d :: rest) =
            explicitFormulaRectangleRegularGridCellEndpointDataBoundary f d +
              explicitFormulaRectangleRegularGridEndpointDataBoundarySum f rest := by
          exact explicitFormulaRectangleRegularGridEndpointDataBoundarySum_cons f d rest
        _ =
            finiteRectangleSubdivisionCellBoundaryIntegral
                (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                d.toRegularGridCell.lower d.toRegularGridCell.upper +
              explicitFormulaRectangleRegularGridEndpointDataBoundarySum f rest := by
          exact congrArg
            (fun x : ℂ =>
              x + explicitFormulaRectangleRegularGridEndpointDataBoundarySum f rest)
            (explicitFormulaRectangleRegularGridCellEndpointDataBoundary_eq_toRegularGridCellBoundary
              f d)
        _ =
            finiteRectangleSubdivisionCellBoundaryIntegral
                (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                d.toRegularGridCell.lower d.toRegularGridCell.upper +
              explicitFormulaRectangleRegularGridCellBoundaryListSum f
                (explicitFormulaRectangleRegularGridCellListOfEndpointData rest) := by
          exact congrArg
            (fun x : ℂ =>
              finiteRectangleSubdivisionCellBoundaryIntegral
                  (fun z : ℂ => zetaCompletedExplicitFormulaContourIntegrand f z)
                  d.toRegularGridCell.lower d.toRegularGridCell.upper + x)
            ih
        _ =
            explicitFormulaRectangleRegularGridCellBoundaryListSum f
              (explicitFormulaRectangleRegularGridCellListOfEndpointData (d :: rest)) := by
          exact
            (explicitFormulaRectangleRegularGridCellBoundaryListSum_cons
              f d.toRegularGridCell
              (explicitFormulaRectangleRegularGridCellListOfEndpointData rest)).symm

/-- Transport a concrete regular-cell list subdivision equality to the endpoint-data
boundary-sum normalization. -/
theorem explicitFormulaRectangleRegularGridEndpointDataBoundarySum_eq_of_cellBoundaryListSum
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε))
    {X : ℂ}
    (h :
      X =
        explicitFormulaRectangleRegularGridCellBoundaryListSum f
          (explicitFormulaRectangleRegularGridCellListOfEndpointData data)) :
    X = explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data := by
  exact Eq.trans h
    (explicitFormulaRectangleRegularGridEndpointDataBoundarySum_eq_cellBoundaryListSum
      f data).symm

/-- Fold a subdivision equality stated over endpoint data to the duplicate-safe `Finset`
boundary-sum normalization, provided the associated regular-cell list is nodup. -/
theorem explicitFormulaRectangleRegularGridCellBoundarySum_eq_of_endpointDataBoundarySum_nodup
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε))
    (hnodup :
      (explicitFormulaRectangleRegularGridCellListOfEndpointData data :
        Multiset (ExplicitFormulaRectangleRegularGridCell F T ε)).Nodup)
    {X : ℂ}
    (h :
      X = explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data) :
    X =
      explicitFormulaRectangleRegularGridCellBoundarySum f
        (explicitFormulaRectangleRegularGridCellFinsetOfNodupList
          (explicitFormulaRectangleRegularGridCellListOfEndpointData data)
          hnodup) := by
  have hcellList :
      explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data =
        explicitFormulaRectangleRegularGridCellBoundaryListSum f
          (explicitFormulaRectangleRegularGridCellListOfEndpointData data) :=
    explicitFormulaRectangleRegularGridEndpointDataBoundarySum_eq_cellBoundaryListSum
      f data
  have hXList :
      X =
        explicitFormulaRectangleRegularGridCellBoundaryListSum f
          (explicitFormulaRectangleRegularGridCellListOfEndpointData data) :=
    Eq.trans h hcellList
  exact
    explicitFormulaRectangleRegularGridCellBoundarySum_eq_of_nodup_cellBoundaryListSum
      f
      (explicitFormulaRectangleRegularGridCellListOfEndpointData data)
      hnodup hXList

/-- Endpoint-data subdivision plus nodup of the associated regular-cell list supplies the
regular-grid `Finset` boundary-sum witness. -/
theorem explicitFormulaRectangleRegularGridCellBoundarySum_exists_of_endpointDataBoundarySum_nodup
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε))
    (hnodup :
      (explicitFormulaRectangleRegularGridCellListOfEndpointData data :
        Multiset (ExplicitFormulaRectangleRegularGridCell F T ε)).Nodup)
    {X : ℂ}
    (h :
      X = explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data) :
    ∃ cells : Finset (ExplicitFormulaRectangleRegularGridCell F T ε),
      X = explicitFormulaRectangleRegularGridCellBoundarySum f cells :=
  ⟨explicitFormulaRectangleRegularGridCellFinsetOfNodupList
      (explicitFormulaRectangleRegularGridCellListOfEndpointData data)
      hnodup,
    explicitFormulaRectangleRegularGridCellBoundarySum_eq_of_endpointDataBoundarySum_nodup
      f data hnodup h⟩

/-- Proof-carrying regular grid cells are extensional in their underlying grid-cell index. -/
theorem ExplicitFormulaRectangleRegularGridCell.ext_cell
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c d : ExplicitFormulaRectangleRegularGridCell F T ε)
    (hcell : c.cell = d.cell) :
    c = d := by
  cases c with
  | mk ccell cmem creg =>
      cases d with
      | mk dcell dmem dreg =>
          cases hcell
          have hmem : cmem = dmem :=
            proof_irrel cmem dmem
          have hreg : creg = dreg :=
            proof_irrel creg dreg
          cases hmem
          cases hreg
          rfl

/-- The regular cell associated to endpoint data has the endpoint tuple as underlying
grid-cell index. -/
theorem ExplicitFormulaRectangleRegularGridCellEndpointData.toRegularGridCell_cell
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :
    d.toRegularGridCell.cell = ((d.x₀, d.x₁), (d.y₀, d.y₁)) := by
  rfl

/-- A nodup endpoint-data list maps to a nodup proof-carrying regular-cell list. -/
theorem explicitFormulaRectangleRegularGridCellListOfEndpointData_multiset_nodup
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε))
    (hnodup :
      (data : Multiset (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)).Nodup) :
    (explicitFormulaRectangleRegularGridCellListOfEndpointData data :
      Multiset (ExplicitFormulaRectangleRegularGridCell F T ε)).Nodup := by
  exact
    hnodup.map
      ExplicitFormulaRectangleRegularGridCellEndpointData.toRegularGridCell_injective

/-- A duplicate-free endpoint-data list, stated in `List.Nodup` form, gives a duplicate-free
regular-cell multiset after mapping endpoint data to proof-carrying regular cells. -/
theorem explicitFormulaRectangleRegularGridCellListOfEndpointData_nodup_of_list_nodup
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε))
    (hnodup : data.Nodup) :
    (explicitFormulaRectangleRegularGridCellListOfEndpointData data :
      Multiset (ExplicitFormulaRectangleRegularGridCell F T ε)).Nodup :=
  explicitFormulaRectangleRegularGridCellListOfEndpointData_multiset_nodup
    data
    (show
      (data : Multiset (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)).Nodup
      from hnodup)

/-- Endpoint-data subdivision plus `List.Nodup` of the endpoint-data list supplies the
regular-grid `Finset` boundary-sum witness. -/
theorem explicitFormulaRectangleRegularGridCellBoundarySum_exists_of_endpointDataBoundarySum_list_nodup
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (f : ZetaAdmissibleFunction)
    (data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε))
    (hnodup : data.Nodup)
    {X : ℂ}
    (h :
      X = explicitFormulaRectangleRegularGridEndpointDataBoundarySum f data) :
    ∃ cells : Finset (ExplicitFormulaRectangleRegularGridCell F T ε),
      X = explicitFormulaRectangleRegularGridCellBoundarySum f cells :=
  explicitFormulaRectangleRegularGridCellBoundarySum_exists_of_endpointDataBoundarySum_nodup
    f data
    (explicitFormulaRectangleRegularGridCellListOfEndpointData_nodup_of_list_nodup
      data hnodup)
    h

/-- A list-level endpoint-data nodup proof is the multiset-level nodup proof used by the
duplicate-safe `Finset.mk` bridge. -/
theorem explicitFormulaRectangleRegularGridCellEndpointData_multiset_nodup_of_list_nodup
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε))
    (hnodup : data.Nodup) :
    (data : Multiset (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)).Nodup :=
  hnodup

/-- The endpoint-data list built from horizontal and vertical adjacent-pair lists is
multiset-nodup when the two input adjacent-pair lists are list-nodup. -/
theorem explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists_multiset_nodup
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))
    (homit :
      ∀ xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε,
        xpair ∈ xpairs →
          ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε,
            ypair ∈ ypairs →
              ∀ a : ℂ,
                a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a.re ∉ [[xpair.x₀, xpair.x₁]] ∨
                    a.im ∉ [[ypair.y₀, ypair.y₁]])
    (hxnodup : xpairs.Nodup) (hynodup : ypairs.Nodup) :
    (explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
        xpairs ypairs homit :
      Multiset (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)).Nodup :=
  explicitFormulaRectangleRegularGridCellEndpointData_multiset_nodup_of_list_nodup
    (explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
      xpairs ypairs homit)
    (explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists_nodup
      xpairs ypairs homit hxnodup hynodup)

/-- The endpoint-data list built from sorted adjacent endpoint-pair lists is
multiset-nodup. -/
theorem explicitFormulaRectangleEndpointDataListOfSortedAdjacentEndpointPairs_multiset_nodup
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (homit :
      ∀ xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε,
        xpair ∈ explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε →
          ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε,
            ypair ∈ explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε →
              ∀ a : ℂ,
                a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a.re ∉ [[xpair.x₀, xpair.x₁]] ∨
                    a.im ∉ [[ypair.y₀, ypair.y₁]]) :
    (explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
        (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
        (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)
        homit :
      Multiset (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)).Nodup :=
  explicitFormulaRectangleRegularGridCellEndpointData_multiset_nodup_of_list_nodup
    (explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
      (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
      (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)
      homit)
    (explicitFormulaRectangleEndpointDataListOfSortedAdjacentEndpointPairs_nodup
      F T ε homit)

/-- A proof-carrying regular grid cell avoids the raw singular carrier. -/
theorem ExplicitFormulaRectangleRegularGridCell.not_mem_rawSingularCoordinates
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularGridCell F T ε)
    {z : ℂ}
    (hz :
      z ∈
        ([[ c.lower.re, c.upper.re ]] ×ℂ
            [[ c.lower.im, c.upper.im ]])) :
    z ∉ explicitFormulaRectangleRawSingularCoordinates T :=
  explicitFormulaRectangleGridCellRegularComplement_not_mem_rawSingularCoordinates
    F T ε c.cell c.regular hz

/-- Coordinate omission stored by a proof-carrying regular grid cell, transported to the
named complex lower and upper corners of the cell. -/
theorem ExplicitFormulaRectangleRegularGridCell.coordinateOmission
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularGridCell F T ε)
    {a : ℂ}
    (ha : a ∈ explicitFormulaRectangleRawSingularCoordinates T) :
    a.re ∉ [[ c.lower.re, c.upper.re ]] ∨
      a.im ∉ [[ c.lower.im, c.upper.im ]] :=
  explicitFormulaRectangleGridCell_coordinateOmission_transport
    c.cell a (c.regular.2 a ha)

/-- Every point of the closed rectangle of a proof-carrying regular grid cell avoids the
raw singular-coordinate carrier. -/
theorem ExplicitFormulaRectangleRegularGridCell.closedCell_not_mem_rawSingularCoordinates
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularGridCell F T ε)
    {z : ℂ}
    (hz : z ∈ ([[ c.lower.re, c.upper.re ]] ×ℂ [[ c.lower.im, c.upper.im ]])) :
    z ∉ explicitFormulaRectangleRawSingularCoordinates T :=
  explicitFormulaRectangleSubdivisionCell_not_mem_rawSingularCoordinates_of_coordinate_omission
    T c.lower c.upper
    (fun a ha => c.coordinateOmission ha)
    hz

/-- Every point of the open rectangle of a proof-carrying regular grid cell avoids the raw
singular-coordinate carrier. -/
theorem ExplicitFormulaRectangleRegularGridCell.openCell_not_mem_rawSingularCoordinates
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularGridCell F T ε)
    {z : ℂ}
    (hz :
      z ∈ Set.Ioo (min c.lower.re c.upper.re)
            (max c.lower.re c.upper.re) ×ℂ
          Set.Ioo (min c.lower.im c.upper.im)
            (max c.lower.im c.upper.im)) :
    z ∉ explicitFormulaRectangleRawSingularCoordinates T :=
  c.closedCell_not_mem_rawSingularCoordinates
    (finiteRectangleSubdivisionOpenCell_subset_closedCell c.lower c.upper hz)

/-- Endpoint membership data carried by a selected regular grid cell. -/
theorem ExplicitFormulaRectangleRegularGridCell.endpoint_mem
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularGridCell F T ε) :
    c.cell.1.1 ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε ∧
      c.cell.1.2 ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε ∧
        c.cell.2.1 ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε ∧
          c.cell.2.2 ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε :=
  explicitFormulaRectangleInscribedSquareSubdivisionCandidateCells_mem
    F T ε c.mem_candidate

/-- The lower horizontal coordinate of a regular grid cell lies in the closed outer
horizontal span under closed-radius controls. -/
theorem ExplicitFormulaRectangleRegularGridCell.lower_re_mem_horizontal_uIcc_of_closedRadiusControls
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularGridCell F T ε)
    (hε : 0 ≤ ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) :
    c.lower.re ∈ [[F.c, 1 - F.c]] := by
  have hx :
      c.cell.1.1 ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε :=
    c.endpoint_mem.1
  have hcell :
      c.cell.1.1 ∈ [[F.c, 1 - F.c]] :=
    explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints_mem_horizontal_uIcc_of_closedRadiusControls
      F T ε hε hclosed hx
  exact
    Eq.subst
      (motive := fun x : ℝ => x ∈ [[F.c, 1 - F.c]])
      (explicitFormulaRectangleGridCellLower_re c.cell).symm
      hcell

/-- The upper horizontal coordinate of a regular grid cell lies in the closed outer
horizontal span under closed-radius controls. -/
theorem ExplicitFormulaRectangleRegularGridCell.upper_re_mem_horizontal_uIcc_of_closedRadiusControls
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularGridCell F T ε)
    (hε : 0 ≤ ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) :
    c.upper.re ∈ [[F.c, 1 - F.c]] := by
  have hx :
      c.cell.1.2 ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε :=
    c.endpoint_mem.2.1
  have hcell :
      c.cell.1.2 ∈ [[F.c, 1 - F.c]] :=
    explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints_mem_horizontal_uIcc_of_closedRadiusControls
      F T ε hε hclosed hx
  exact
    Eq.subst
      (motive := fun x : ℝ => x ∈ [[F.c, 1 - F.c]])
      (explicitFormulaRectangleGridCellUpper_re c.cell).symm
      hcell

/-- The lower vertical coordinate of a regular grid cell lies in the closed height interval
under closed-radius controls. -/
theorem ExplicitFormulaRectangleRegularGridCell.lower_im_mem_vertical_Icc_of_closedRadiusControls
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularGridCell F T ε)
    (hT_nonneg : 0 ≤ T)
    (hε : 0 ≤ ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) :
    c.lower.im ∈ Set.Icc (-T) T := by
  have hy :
      c.cell.2.1 ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε :=
    c.endpoint_mem.2.2.1
  have hcell :
      c.cell.2.1 ∈ Set.Icc (-T) T :=
    explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints_mem_vertical_Icc_of_closedRadiusControls
      F T ε hT_nonneg hε hclosed hy
  exact
    Eq.subst
      (motive := fun y : ℝ => y ∈ Set.Icc (-T) T)
      (explicitFormulaRectangleGridCellLower_im c.cell).symm
      hcell

/-- The upper vertical coordinate of a regular grid cell lies in the closed height interval
under closed-radius controls. -/
theorem ExplicitFormulaRectangleRegularGridCell.upper_im_mem_vertical_Icc_of_closedRadiusControls
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularGridCell F T ε)
    (hT_nonneg : 0 ≤ T)
    (hε : 0 ≤ ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) :
    c.upper.im ∈ Set.Icc (-T) T := by
  have hy :
      c.cell.2.2 ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε :=
    c.endpoint_mem.2.2.2
  have hcell :
      c.cell.2.2 ∈ Set.Icc (-T) T :=
    explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints_mem_vertical_Icc_of_closedRadiusControls
      F T ε hT_nonneg hε hclosed hy
  exact
    Eq.subst
      (motive := fun y : ℝ => y ∈ Set.Icc (-T) T)
      (explicitFormulaRectangleGridCellUpper_im c.cell).symm
      hcell

/-- A regular grid cell selected from the inscribed-square endpoint carrier is contained in
the closed outer rectangle box under the selected closed-radius controls. -/
theorem ExplicitFormulaRectangleRegularGridCell.closedCell_subset_outerClosedCell_of_closedRadiusControls
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularGridCell F T ε)
    (hT_nonneg : 0 ≤ T)
    (hε : 0 ≤ ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T) :
    ([[ c.lower.re, c.upper.re ]] ×ℂ [[ c.lower.im, c.upper.im ]]) ⊆
      ([[F.c, 1 - F.c]] ×ℂ Set.Icc (-T) T) := by
  intro z hz
  have hre_lower :
      c.lower.re ∈ [[F.c, 1 - F.c]] :=
    c.lower_re_mem_horizontal_uIcc_of_closedRadiusControls hε hclosed
  have hre_upper :
      c.upper.re ∈ [[F.c, 1 - F.c]] :=
    c.upper_re_mem_horizontal_uIcc_of_closedRadiusControls hε hclosed
  have him_lower :
      c.lower.im ∈ Set.Icc (-T) T :=
    c.lower_im_mem_vertical_Icc_of_closedRadiusControls hT_nonneg hε hclosed
  have him_upper :
      c.upper.im ∈ Set.Icc (-T) T :=
    c.upper_im_mem_vertical_Icc_of_closedRadiusControls hT_nonneg hε hclosed
  have hz_re : z.re ∈ [[F.c, 1 - F.c]] :=
    Set.uIcc_subset_uIcc hre_lower hre_upper hz.1
  have hz_im : z.im ∈ Set.Icc (-T) T :=
    Set.uIcc_subset_Icc him_lower him_upper hz.2
  exact And.intro hz_re hz_im

/-- The vertical coordinate of an open regular grid cell point is strictly inside the
height interval under the selected closed-radius controls. -/
theorem ExplicitFormulaRectangleRegularGridCell.openCell_im_mem_vertical_Ioo_of_closedRadiusControls
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularGridCell F T ε)
    (hT_nonneg : 0 ≤ T)
    (hε : 0 ≤ ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    {z : ℂ}
    (hz :
      z ∈ Set.Ioo (min c.lower.re c.upper.re)
            (max c.lower.re c.upper.re) ×ℂ
          Set.Ioo (min c.lower.im c.upper.im)
            (max c.lower.im c.upper.im)) :
    z.im ∈ Set.Ioo (-T) T := by
  have him_lower :
      c.lower.im ∈ Set.Icc (-T) T :=
    c.lower_im_mem_vertical_Icc_of_closedRadiusControls hT_nonneg hε hclosed
  have him_upper :
      c.upper.im ∈ Set.Icc (-T) T :=
    c.upper_im_mem_vertical_Icc_of_closedRadiusControls hT_nonneg hε hclosed
  have hmin_lower : -T ≤ min c.lower.im c.upper.im :=
    le_min him_lower.1 him_upper.1
  have hmax_upper : max c.lower.im c.upper.im ≤ T :=
    max_le him_lower.2 him_upper.2
  exact
    And.intro
      (lt_of_le_of_lt hmin_lower hz.2.1)
      (lt_of_lt_of_le hz.2.2 hmax_upper)

/-- The horizontal coordinate of an open regular grid cell point is strictly inside the
outer horizontal span under the selected closed-radius controls. -/
theorem ExplicitFormulaRectangleRegularGridCell.openCell_re_mem_horizontal_uIoo_of_closedRadiusControls
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularGridCell F T ε)
    (hε : 0 ≤ ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    {z : ℂ}
    (hz :
      z ∈ Set.Ioo (min c.lower.re c.upper.re)
            (max c.lower.re c.upper.re) ×ℂ
          Set.Ioo (min c.lower.im c.upper.im)
            (max c.lower.im c.upper.im)) :
    z.re ∈ Set.uIoo F.c (1 - F.c) := by
  have hre_lower :
      c.lower.re ∈ [[F.c, 1 - F.c]] :=
    c.lower_re_mem_horizontal_uIcc_of_closedRadiusControls hε hclosed
  have hre_upper :
      c.upper.re ∈ [[F.c, 1 - F.c]] :=
    c.upper_re_mem_horizontal_uIcc_of_closedRadiusControls hε hclosed
  have hmin_lower : F.c ⊓ (1 - F.c) ≤ min c.lower.re c.upper.re :=
    le_min hre_lower.1 hre_upper.1
  have hmax_upper : max c.lower.re c.upper.re ≤ F.c ⊔ (1 - F.c) :=
    max_le hre_lower.2 hre_upper.2
  unfold Set.uIoo
  exact
    And.intro
      (lt_of_le_of_lt hmin_lower hz.1.1)
      (lt_of_lt_of_le hz.1.2 hmax_upper)

/-- An open point of a regular grid cell lies in the contour-family interior under the
selected closed-radius controls. -/
theorem ExplicitFormulaRectangleRegularGridCell.openCell_mem_interior_of_closedRadiusControls
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularGridCell F T ε)
    (hT_nonneg : 0 ≤ T)
    (hε : 0 ≤ ε)
    (hclosed :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          Metric.closedBall a ε ⊆ explicitFormulaContourFamilyInterior F T)
    {z : ℂ}
    (hz :
      z ∈ Set.Ioo (min c.lower.re c.upper.re)
            (max c.lower.re c.upper.re) ×ℂ
          Set.Ioo (min c.lower.im c.upper.im)
            (max c.lower.im c.upper.im)) :
    z ∈ explicitFormulaContourFamilyInterior F T :=
  And.intro
    (c.openCell_re_mem_horizontal_uIoo_of_closedRadiusControls hε hclosed hz)
    (c.openCell_im_mem_vertical_Ioo_of_closedRadiusControls hT_nonneg hε hclosed hz)

/-- A point with real coordinate on the right vertical side and vertical coordinate in the
height interval lies on the contour-family boundary. -/
theorem explicitFormulaContourFamilyBoundary_mem_of_re_eq_right
    (F : ExplicitFormulaContourFamily) (T : ℝ) {z : ℂ}
    (hre : z.re = F.c)
    (him : z.im ∈ Set.Icc (-T) T) :
    z ∈ explicitFormulaContourFamilyBoundary F T := by
  have hpath_re :
      (zetaCompletedExplicitFormulaRightPath (F.rectangle T) z.im).re = z.re :=
    Eq.trans (zetaCompletedExplicitFormulaRightPath_re (F.rectangle T) z.im) hre.symm
  have hpath_im :
      (zetaCompletedExplicitFormulaRightPath (F.rectangle T) z.im).im = z.im :=
    zetaCompletedExplicitFormulaRightPath_im (F.rectangle T) z.im
  have hz_eq :
      z = zetaCompletedExplicitFormulaRightPath (F.rectangle T) z.im :=
    (Complex.ext hpath_re.symm hpath_im.symm)
  exact Or.inl (Exists.intro z.im (And.intro him hz_eq))

/-- A point with real coordinate on the left vertical side and vertical coordinate in the
height interval lies on the contour-family boundary. -/
theorem explicitFormulaContourFamilyBoundary_mem_of_re_eq_left
    (F : ExplicitFormulaContourFamily) (T : ℝ) {z : ℂ}
    (hre : z.re = 1 - F.c)
    (him : z.im ∈ Set.Icc (-T) T) :
    z ∈ explicitFormulaContourFamilyBoundary F T := by
  have hpath_re :
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) z.im).re = z.re :=
    Eq.trans (zetaCompletedExplicitFormulaLeftPath_re (F.rectangle T) z.im) hre.symm
  have hpath_im :
      (zetaCompletedExplicitFormulaLeftPath (F.rectangle T) z.im).im = z.im :=
    zetaCompletedExplicitFormulaLeftPath_im (F.rectangle T) z.im
  have hz_eq :
      z = zetaCompletedExplicitFormulaLeftPath (F.rectangle T) z.im :=
    (Complex.ext hpath_re.symm hpath_im.symm)
  exact Or.inr (Or.inl (Exists.intro z.im (And.intro him hz_eq)))

/-- A point with imaginary coordinate on the top horizontal side and horizontal coordinate
in the closed outer span lies on the contour-family boundary. -/
theorem explicitFormulaContourFamilyBoundary_mem_of_im_eq_top
    (F : ExplicitFormulaContourFamily) (T : ℝ) {z : ℂ}
    (hre : z.re ∈ [[F.c, 1 - F.c]])
    (him : z.im = T) :
    z ∈ explicitFormulaContourFamilyBoundary F T := by
  have hpath_re :
      (zetaCompletedExplicitFormulaTopPath (F.rectangle T) z.re).re = z.re :=
    zetaCompletedExplicitFormulaTopPath_re_eq (F.rectangle T) z.re
  have hpath_im :
      (zetaCompletedExplicitFormulaTopPath (F.rectangle T) z.re).im = z.im :=
    Eq.trans (zetaCompletedExplicitFormulaTopPath_im (F.rectangle T) z.re) him.symm
  have hz_eq :
      z = zetaCompletedExplicitFormulaTopPath (F.rectangle T) z.re :=
    (Complex.ext hpath_re.symm hpath_im.symm)
  exact Or.inr (Or.inr (Or.inl (Exists.intro z.re (And.intro hre hz_eq))))

/-- A point with imaginary coordinate on the bottom horizontal side and horizontal
coordinate in the closed outer span lies on the contour-family boundary. -/
theorem explicitFormulaContourFamilyBoundary_mem_of_im_eq_bottom
    (F : ExplicitFormulaContourFamily) (T : ℝ) {z : ℂ}
    (hre : z.re ∈ [[F.c, 1 - F.c]])
    (him : z.im = -T) :
    z ∈ explicitFormulaContourFamilyBoundary F T := by
  have hpath_re :
      (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) z.re).re = z.re :=
    zetaCompletedExplicitFormulaBottomPath_re_eq (F.rectangle T) z.re
  have hpath_im :
      (zetaCompletedExplicitFormulaBottomPath (F.rectangle T) z.re).im = z.im :=
    Eq.trans (zetaCompletedExplicitFormulaBottomPath_im (F.rectangle T) z.re) him.symm
  have hz_eq :
      z = zetaCompletedExplicitFormulaBottomPath (F.rectangle T) z.re :=
    (Complex.ext hpath_re.symm hpath_im.symm)
  exact Or.inr (Or.inr (Or.inr (Exists.intro z.re (And.intro hre hz_eq))))

/-- A point in the closed outer rectangle box is either in the contour-family interior or
on the contour-family boundary. -/
theorem explicitFormulaContourFamily_closedBox_mem_interior_or_boundary
    (F : ExplicitFormulaContourFamily) (T : ℝ) {z : ℂ}
    (hre : z.re ∈ [[F.c, 1 - F.c]])
    (him : z.im ∈ Set.Icc (-T) T) :
    z ∈ explicitFormulaContourFamilyInterior F T ∨
      z ∈ explicitFormulaContourFamilyBoundary F T := by
  have hhorizontal_order : 1 - F.c ≤ F.c :=
    le_of_lt (lt_trans F.one_sub_c_neg F.c_pos)
  have hreIcc : z.re ∈ Set.Icc (1 - F.c) F.c :=
    Eq.subst
      (motive := fun s : Set ℝ => z.re ∈ s)
      (Set.uIcc_of_ge hhorizontal_order)
      hre
  match Set.eq_endpoints_or_mem_Ioo_of_mem_Icc hreIcc with
  | Or.inl hre_left =>
      exact Or.inr
        (explicitFormulaContourFamilyBoundary_mem_of_re_eq_left
          F T hre_left him)
  | Or.inr hright_or_open =>
      match hright_or_open with
      | Or.inl hre_right =>
          exact Or.inr
            (explicitFormulaContourFamilyBoundary_mem_of_re_eq_right
              F T hre_right him)
      | Or.inr hre_open_Icc =>
          have hre_open : z.re ∈ Set.uIoo F.c (1 - F.c) :=
            Set.Ioo_subset_uIoo' hre_open_Icc
          match Set.eq_endpoints_or_mem_Ioo_of_mem_Icc him with
          | Or.inl him_bottom =>
              exact Or.inr
                (explicitFormulaContourFamilyBoundary_mem_of_im_eq_bottom
                  F T hre him_bottom)
          | Or.inr htop_or_open =>
              match htop_or_open with
              | Or.inl him_top =>
                  exact Or.inr
                    (explicitFormulaContourFamilyBoundary_mem_of_im_eq_top
                      F T hre him_top)
              | Or.inr him_open =>
                  exact Or.inl (And.intro hre_open him_open)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
