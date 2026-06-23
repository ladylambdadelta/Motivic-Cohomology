import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part16

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

/-- The finite grid-cell candidate carrier determined by the outer rectangle sides and the
sides of the finite family of raw inscribed-square holes. -/
noncomputable def explicitFormulaRectangleInscribedSquareSubdivisionCandidateCells
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    Finset ExplicitFormulaRectangleGridCellIndex :=
  ((explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε).product
      (explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε)).product
    ((explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε).product
      (explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε))

/-- Membership in the candidate grid-cell carrier records all four endpoints in their
respective endpoint carriers. -/
theorem explicitFormulaRectangleInscribedSquareSubdivisionCandidateCells_mem
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    {c : ExplicitFormulaRectangleGridCellIndex}
    (hc :
      c ∈ explicitFormulaRectangleInscribedSquareSubdivisionCandidateCells F T ε) :
    c.1.1 ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε ∧
      c.1.2 ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε ∧
        c.2.1 ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε ∧
          c.2.2 ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε := by
  have hprod :
      c.1 ∈
          (explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε).product
            (explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε) ∧
        c.2 ∈
          (explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε).product
            (explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε) :=
    Finset.mem_product.mp hc
  have hx :
      c.1.1 ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε ∧
        c.1.2 ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε :=
    Finset.mem_product.mp hprod.1
  have hy :
      c.2.1 ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε ∧
        c.2.2 ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε :=
    Finset.mem_product.mp hprod.2
  exact And.intro hx.1 (And.intro hx.2 (And.intro hy.1 hy.2))

/-- Four endpoint memberships assemble a candidate grid-cell membership. -/
theorem explicitFormulaRectangleInscribedSquareSubdivisionCandidateCells_mem_of_endpoints
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    {c : ExplicitFormulaRectangleGridCellIndex}
    (hx₀ : c.1.1 ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε)
    (hx₁ : c.1.2 ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε)
    (hy₀ : c.2.1 ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε)
    (hy₁ : c.2.2 ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε) :
    c ∈ explicitFormulaRectangleInscribedSquareSubdivisionCandidateCells F T ε := by
  exact
    Finset.mem_product.mpr
      (And.intro
        (Finset.mem_product.mpr (And.intro hx₀ hx₁))
        (Finset.mem_product.mpr (And.intro hy₀ hy₁)))

/-- Candidate grid-cell membership is exactly membership of all four endpoint coordinates
in their corresponding finite endpoint carriers. -/
theorem explicitFormulaRectangleInscribedSquareSubdivisionCandidateCells_mem_iff
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (c : ExplicitFormulaRectangleGridCellIndex) :
    c ∈ explicitFormulaRectangleInscribedSquareSubdivisionCandidateCells F T ε ↔
      c.1.1 ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε ∧
        c.1.2 ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε ∧
          c.2.1 ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε ∧
            c.2.2 ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε := by
  exact
    Iff.intro
      (fun hc =>
        explicitFormulaRectangleInscribedSquareSubdivisionCandidateCells_mem
          F T ε hc)
      (fun hendpoints =>
        explicitFormulaRectangleInscribedSquareSubdivisionCandidateCells_mem_of_endpoints
          F T ε hendpoints.1 hendpoints.2.1 hendpoints.2.2.1 hendpoints.2.2.2)

/-- The first horizontal endpoint of a candidate cell belongs to the horizontal endpoint
carrier. -/
theorem explicitFormulaRectangleInscribedSquareSubdivisionCandidateCells_mem_xLower
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    {c : ExplicitFormulaRectangleGridCellIndex}
    (hc : c ∈ explicitFormulaRectangleInscribedSquareSubdivisionCandidateCells F T ε) :
    c.1.1 ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε :=
  (explicitFormulaRectangleInscribedSquareSubdivisionCandidateCells_mem F T ε hc).1

/-- The second horizontal endpoint of a candidate cell belongs to the horizontal endpoint
carrier. -/
theorem explicitFormulaRectangleInscribedSquareSubdivisionCandidateCells_mem_xUpper
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    {c : ExplicitFormulaRectangleGridCellIndex}
    (hc : c ∈ explicitFormulaRectangleInscribedSquareSubdivisionCandidateCells F T ε) :
    c.1.2 ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε :=
  (explicitFormulaRectangleInscribedSquareSubdivisionCandidateCells_mem F T ε hc).2.1

/-- The first vertical endpoint of a candidate cell belongs to the vertical endpoint
carrier. -/
theorem explicitFormulaRectangleInscribedSquareSubdivisionCandidateCells_mem_yLower
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    {c : ExplicitFormulaRectangleGridCellIndex}
    (hc : c ∈ explicitFormulaRectangleInscribedSquareSubdivisionCandidateCells F T ε) :
    c.2.1 ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε :=
  (explicitFormulaRectangleInscribedSquareSubdivisionCandidateCells_mem F T ε hc).2.2.1

/-- The second vertical endpoint of a candidate cell belongs to the vertical endpoint
carrier. -/
theorem explicitFormulaRectangleInscribedSquareSubdivisionCandidateCells_mem_yUpper
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    {c : ExplicitFormulaRectangleGridCellIndex}
    (hc : c ∈ explicitFormulaRectangleInscribedSquareSubdivisionCandidateCells F T ε) :
    c.2.2 ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε :=
  (explicitFormulaRectangleInscribedSquareSubdivisionCandidateCells_mem F T ε hc).2.2.2

/-- Coordinate-omission for a real grid cell index transports to coordinate-omission for
the associated complex rectangular subdivision cell. -/
theorem explicitFormulaRectangleGridCell_coordinateOmission_transport
    (c : ExplicitFormulaRectangleGridCellIndex) (a : ℂ)
    (homit :
      a.re ∉ [[ c.1.1, c.1.2 ]] ∨
        a.im ∉ [[ c.2.1, c.2.2 ]]) :
    a.re ∉
        [[ (explicitFormulaRectangleGridCellLower c).re,
          (explicitFormulaRectangleGridCellUpper c).re ]] ∨
      a.im ∉
        [[ (explicitFormulaRectangleGridCellLower c).im,
          (explicitFormulaRectangleGridCellUpper c).im ]] := by
  match homit with
  | Or.inl hre_omit =>
      exact Or.inl
        (fun hre_mem =>
          hre_omit
            (finiteRectangle_mem_uIcc_congr_endpoints
              (explicitFormulaRectangleGridCellLower_re c)
              (explicitFormulaRectangleGridCellUpper_re c)
              hre_mem))
  | Or.inr him_omit =>
      exact Or.inr
        (fun him_mem =>
          him_omit
            (finiteRectangle_mem_uIcc_congr_endpoints
              (explicitFormulaRectangleGridCellLower_im c)
              (explicitFormulaRectangleGridCellUpper_im c)
              him_mem))

/-- A complex grid cell avoids the raw singular carrier when its real endpoint intervals
omit each raw singular center in at least one coordinate. -/
theorem explicitFormulaRectangleGridCell_not_mem_rawSingularCoordinates_of_coordinate_omission
    (T : ℝ) (c : ExplicitFormulaRectangleGridCellIndex)
    (homit :
      ∀ a : ℂ,
        a ∈ explicitFormulaRectangleRawSingularCoordinates T →
          a.re ∉ [[ c.1.1, c.1.2 ]] ∨
            a.im ∉ [[ c.2.1, c.2.2 ]])
    {z : ℂ}
    (hz :
      z ∈
        ([[ (explicitFormulaRectangleGridCellLower c).re,
          (explicitFormulaRectangleGridCellUpper c).re ]] ×ℂ
            [[ (explicitFormulaRectangleGridCellLower c).im,
              (explicitFormulaRectangleGridCellUpper c).im ]])) :
    z ∉ explicitFormulaRectangleRawSingularCoordinates T :=
  explicitFormulaRectangleSubdivisionCell_not_mem_rawSingularCoordinates_of_coordinate_omission
    T
    (explicitFormulaRectangleGridCellLower c)
    (explicitFormulaRectangleGridCellUpper c)
    (fun a ha =>
      explicitFormulaRectangleGridCell_coordinateOmission_transport c a (homit a ha))
    hz

/-- A grid cell index has positively oriented coordinate intervals. -/
def explicitFormulaRectangleGridCellOrdered
    (c : ExplicitFormulaRectangleGridCellIndex) : Prop :=
  c.1.1 < c.1.2 ∧ c.2.1 < c.2.2

/-- A horizontal endpoint pair has no endpoint strictly between its two endpoints. -/
def explicitFormulaRectangleNoIntermediateXEndpoint
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) (x₀ x₁ : ℝ) : Prop :=
  ∀ x : ℝ,
    x ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε →
      x₀ < x → x < x₁ → False

/-- A vertical endpoint pair has no endpoint strictly between its two endpoints. -/
def explicitFormulaRectangleNoIntermediateYEndpoint
    (T ε : ℝ) (y₀ y₁ : ℝ) : Prop :=
  ∀ y : ℝ,
    y ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε →
      y₀ < y → y < y₁ → False

/-- A grid cell index is adjacent in both coordinate directions for the endpoint carriers
of the finite inscribed-square subdivision. -/
def explicitFormulaRectangleGridCellAdjacent
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (c : ExplicitFormulaRectangleGridCellIndex) : Prop :=
  explicitFormulaRectangleGridCellOrdered c ∧
    explicitFormulaRectangleNoIntermediateXEndpoint F T ε c.1.1 c.1.2 ∧
      explicitFormulaRectangleNoIntermediateYEndpoint T ε c.2.1 c.2.2

/-- A grid cell index is a regular complement cell if it is adjacent and each raw singular
center is omitted by at least one of its coordinate intervals. -/
def explicitFormulaRectangleGridCellRegularComplement
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (c : ExplicitFormulaRectangleGridCellIndex) : Prop :=
  explicitFormulaRectangleGridCellAdjacent F T ε c ∧
    ∀ a : ℂ,
      a ∈ explicitFormulaRectangleRawSingularCoordinates T →
        a.re ∉ [[ c.1.1, c.1.2 ]] ∨
          a.im ∉ [[ c.2.1, c.2.2 ]]

/-- A regular complement grid cell avoids the raw singular carrier. -/
theorem explicitFormulaRectangleGridCellRegularComplement_not_mem_rawSingularCoordinates
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (c : ExplicitFormulaRectangleGridCellIndex)
    (hregular : explicitFormulaRectangleGridCellRegularComplement F T ε c)
    {z : ℂ}
    (hz :
      z ∈
        ([[ (explicitFormulaRectangleGridCellLower c).re,
          (explicitFormulaRectangleGridCellUpper c).re ]] ×ℂ
            [[ (explicitFormulaRectangleGridCellLower c).im,
              (explicitFormulaRectangleGridCellUpper c).im ]])) :
    z ∉ explicitFormulaRectangleRawSingularCoordinates T :=
  explicitFormulaRectangleGridCell_not_mem_rawSingularCoordinates_of_coordinate_omission
    T c hregular.2 hz

/-- Proof-carrying regular grid cell selected from the finite endpoint candidate carrier.
This avoids filtering a `Finset` by undecidable real-order predicates while keeping the
cell itself tied to the concrete finite candidate carrier. -/
structure ExplicitFormulaRectangleRegularGridCell
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) where
  cell : ExplicitFormulaRectangleGridCellIndex
  mem_candidate :
    cell ∈ explicitFormulaRectangleInscribedSquareSubdivisionCandidateCells F T ε
  regular : explicitFormulaRectangleGridCellRegularComplement F T ε cell

/-- Construct a proof-carrying regular grid cell from four concrete adjacent subdivision
endpoints and the raw-center omission proof.  This is the owner-level constructor used by
the eventual complement subdivision; it avoids filtering by undecidable real predicates. -/
def explicitFormulaRectangleRegularGridCellOfAdjacentEndpoints
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
    ExplicitFormulaRectangleRegularGridCell F T ε :=
  { cell := ((x₀, x₁), (y₀, y₁))
    mem_candidate :=
      Finset.mem_product.mpr
        (And.intro
          (Finset.mem_product.mpr (And.intro hx₀ hx₁))
          (Finset.mem_product.mpr (And.intro hy₀ hy₁)))
    regular :=
      And.intro
        (And.intro
          (And.intro hx_order hy_order)
          (And.intro hx_adj hy_adj))
        homit }

/-- Proof-carrying adjacent endpoint data for one regular complement grid cell.  A finite
list of these records is the non-filtering representation of the concrete complement-cell
subdivision. -/
structure ExplicitFormulaRectangleRegularGridCellEndpointData
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) where
  x₀ x₁ y₀ y₁ : ℝ
  hx₀ : x₀ ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε
  hx₁ : x₁ ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε
  hy₀ : y₀ ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε
  hy₁ : y₁ ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε
  hx_order : x₀ < x₁
  hy_order : y₀ < y₁
  hx_adj : explicitFormulaRectangleNoIntermediateXEndpoint F T ε x₀ x₁
  hy_adj : explicitFormulaRectangleNoIntermediateYEndpoint T ε y₀ y₁
  homit :
    ∀ a : ℂ,
      a ∈ explicitFormulaRectangleRawSingularCoordinates T →
        a.re ∉ [[x₀, x₁]] ∨ a.im ∉ [[y₀, y₁]]

/-- Endpoint-data records are extensional in their four real endpoints; all remaining
fields are proof fields. -/
theorem ExplicitFormulaRectangleRegularGridCellEndpointData.ext_endpoints
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (d e : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)
    (hx₀ : d.x₀ = e.x₀) (hx₁ : d.x₁ = e.x₁)
    (hy₀ : d.y₀ = e.y₀) (hy₁ : d.y₁ = e.y₁) :
    d = e := by
  cases d with
  | mk dx₀ dx₁ dy₀ dy₁ dhx₀ dhx₁ dhy₀ dhy₁ dhx_order dhy_order dhx_adj dhy_adj dhomit =>
      cases e with
      | mk ex₀ ex₁ ey₀ ey₁ ehx₀ ehx₁ ehy₀ ehy₁ ehx_order ehy_order ehx_adj ehy_adj ehomit =>
          cases hx₀
          cases hx₁
          cases hy₀
          cases hy₁
          have hhx₀ : dhx₀ = ehx₀ := proof_irrel dhx₀ ehx₀
          have hhx₁ : dhx₁ = ehx₁ := proof_irrel dhx₁ ehx₁
          have hhy₀ : dhy₀ = ehy₀ := proof_irrel dhy₀ ehy₀
          have hhy₁ : dhy₁ = ehy₁ := proof_irrel dhy₁ ehy₁
          have hhx_order : dhx_order = ehx_order :=
            proof_irrel dhx_order ehx_order
          have hhy_order : dhy_order = ehy_order :=
            proof_irrel dhy_order ehy_order
          have hhx_adj : dhx_adj = ehx_adj := proof_irrel dhx_adj ehx_adj
          have hhy_adj : dhy_adj = ehy_adj := proof_irrel dhy_adj ehy_adj
          have hhomit : dhomit = ehomit := proof_irrel dhomit ehomit
          cases hhx₀
          cases hhx₁
          cases hhy₀
          cases hhy₁
          cases hhx_order
          cases hhy_order
          cases hhx_adj
          cases hhy_adj
          cases hhomit
          rfl

/-- Proof-carrying adjacent horizontal endpoint pair from the concrete subdivision
endpoint carrier. -/
structure ExplicitFormulaRectangleXAdjacentEndpointPair
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) where
  x₀ x₁ : ℝ
  hx₀ : x₀ ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε
  hx₁ : x₁ ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε
  hx_order : x₀ < x₁
  hx_adj : explicitFormulaRectangleNoIntermediateXEndpoint F T ε x₀ x₁

/-- Proof-carrying adjacent vertical endpoint pair from the concrete subdivision endpoint
carrier. -/
structure ExplicitFormulaRectangleYAdjacentEndpointPair
    (T ε : ℝ) where
  y₀ y₁ : ℝ
  hy₀ : y₀ ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε
  hy₁ : y₁ ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε
  hy_order : y₀ < y₁
  hy_adj : explicitFormulaRectangleNoIntermediateYEndpoint T ε y₀ y₁

/-- The sorted horizontal endpoint carrier used to produce adjacent horizontal endpoint
pairs. -/
noncomputable def explicitFormulaRectangleSortedXEndpoints
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) : List ℝ :=
  (explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε).sort (· ≤ ·)

/-- The sorted vertical endpoint carrier used to produce adjacent vertical endpoint
pairs. -/
noncomputable def explicitFormulaRectangleSortedYEndpoints
    (T ε : ℝ) : List ℝ :=
  (explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε).sort (· ≤ ·)

/-- A sorted horizontal endpoint carrier is strictly sorted, because it comes from a
finite set with no duplicate endpoint values. -/
theorem explicitFormulaRectangleSortedXEndpoints_sorted_lt
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    (explicitFormulaRectangleSortedXEndpoints F T ε).Sorted (· < ·) := by
  exact
    Finset.sort_sorted_lt
      (explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε)

/-- A sorted vertical endpoint carrier is strictly sorted, because it comes from a finite
set with no duplicate endpoint values. -/
theorem explicitFormulaRectangleSortedYEndpoints_sorted_lt
    (T ε : ℝ) :
    (explicitFormulaRectangleSortedYEndpoints T ε).Sorted (· < ·) := by
  exact
    Finset.sort_sorted_lt
      (explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε)

/-- A sorted horizontal endpoint carrier is weakly sorted. -/
theorem explicitFormulaRectangleSortedXEndpoints_sorted_le
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    (explicitFormulaRectangleSortedXEndpoints F T ε).Sorted (· ≤ ·) := by
  exact
    Finset.sort_sorted (· ≤ ·)
      (explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε)

/-- A sorted vertical endpoint carrier is weakly sorted. -/
theorem explicitFormulaRectangleSortedYEndpoints_sorted_le
    (T ε : ℝ) :
    (explicitFormulaRectangleSortedYEndpoints T ε).Sorted (· ≤ ·) := by
  exact
    Finset.sort_sorted (· ≤ ·)
      (explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε)

/-- Membership in the sorted horizontal endpoint list is membership in the horizontal
endpoint carrier. -/
theorem explicitFormulaRectangleSortedXEndpoints_mem_iff
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) (x : ℝ) :
    x ∈ explicitFormulaRectangleSortedXEndpoints F T ε ↔
      x ∈ explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε := by
  exact Finset.mem_sort

/-- Membership in the sorted vertical endpoint list is membership in the vertical
endpoint carrier. -/
theorem explicitFormulaRectangleSortedYEndpoints_mem_iff
    (T ε : ℝ) (y : ℝ) :
    y ∈ explicitFormulaRectangleSortedYEndpoints T ε ↔
      y ∈ explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε := by
  exact Finset.mem_sort

/-- Adjacent indices in the sorted horizontal endpoint carrier have no horizontal
endpoint strictly between them. -/
theorem explicitFormulaRectangleSortedXEndpoints_noIntermediate_get_succ
    (F : ExplicitFormulaContourFamily) (T ε : ℝ)
    (i : Fin ((explicitFormulaRectangleSortedXEndpoints F T ε).length - 1)) :
    explicitFormulaRectangleNoIntermediateXEndpoint F T ε
      ((explicitFormulaRectangleSortedXEndpoints F T ε).get
        ⟨i.1,
          lt_trans (Nat.lt_succ_self i.1)
            ((Nat.lt_sub_iff_add_lt (a := i.1) (b := 1)
              (c := (explicitFormulaRectangleSortedXEndpoints F T ε).length)).mp i.2)⟩)
      ((explicitFormulaRectangleSortedXEndpoints F T ε).get
        ⟨i.1 + 1,
          ((Nat.lt_sub_iff_add_lt (a := i.1) (b := 1)
            (c := (explicitFormulaRectangleSortedXEndpoints F T ε).length)).mp i.2)⟩) := by
  intro x hx hx_lower hx_upper
  let xs := explicitFormulaRectangleSortedXEndpoints F T ε
  have hx_mem_xs : x ∈ xs :=
    (explicitFormulaRectangleSortedXEndpoints_mem_iff F T ε x).mpr hx
  let j : Fin xs.length := ⟨xs.indexOf x, List.indexOf_lt_length.mpr hx_mem_xs⟩
  let i₀ : Fin xs.length :=
    ⟨i.1,
      lt_trans (Nat.lt_succ_self i.1)
        ((Nat.lt_sub_iff_add_lt (a := i.1) (b := 1) (c := xs.length)).mp i.2)⟩
  let i₁ : Fin xs.length :=
    ⟨i.1 + 1,
      ((Nat.lt_sub_iff_add_lt (a := i.1) (b := 1) (c := xs.length)).mp i.2)⟩
  have hj_get : xs.get j = x :=
    List.indexOf_get (List.indexOf_lt_length.mpr hx_mem_xs)
  by_cases hji : j ≤ i₀
  · have hx_le_lower : x ≤ xs.get i₀ := by
      calc
        x = xs.get j := hj_get.symm
        _ ≤ xs.get i₀ :=
          (explicitFormulaRectangleSortedXEndpoints_sorted_le F T ε).rel_get_of_le hji
    exact (not_lt_of_ge hx_le_lower) hx_lower
  · have hi_lt_j : i₀ < j :=
      lt_of_not_ge hji
    have hi₁_le_j : i₁ ≤ j :=
      Nat.succ_le_of_lt hi_lt_j
    have hupper_le_x : xs.get i₁ ≤ x := by
      calc
        xs.get i₁ ≤ xs.get j :=
          (explicitFormulaRectangleSortedXEndpoints_sorted_le F T ε).rel_get_of_le hi₁_le_j
        _ = x := hj_get
    exact (not_lt_of_ge hupper_le_x) hx_upper

/-- Adjacent indices in the sorted vertical endpoint carrier have no vertical endpoint
strictly between them. -/
theorem explicitFormulaRectangleSortedYEndpoints_noIntermediate_get_succ
    (T ε : ℝ)
    (i : Fin ((explicitFormulaRectangleSortedYEndpoints T ε).length - 1)) :
    explicitFormulaRectangleNoIntermediateYEndpoint T ε
      ((explicitFormulaRectangleSortedYEndpoints T ε).get
        ⟨i.1,
          lt_trans (Nat.lt_succ_self i.1)
            ((Nat.lt_sub_iff_add_lt (a := i.1) (b := 1)
              (c := (explicitFormulaRectangleSortedYEndpoints T ε).length)).mp i.2)⟩)
      ((explicitFormulaRectangleSortedYEndpoints T ε).get
        ⟨i.1 + 1,
          ((Nat.lt_sub_iff_add_lt (a := i.1) (b := 1)
            (c := (explicitFormulaRectangleSortedYEndpoints T ε).length)).mp i.2)⟩) := by
  intro y hy hy_lower hy_upper
  let ys := explicitFormulaRectangleSortedYEndpoints T ε
  have hy_mem_ys : y ∈ ys :=
    (explicitFormulaRectangleSortedYEndpoints_mem_iff T ε y).mpr hy
  let j : Fin ys.length := ⟨ys.indexOf y, List.indexOf_lt_length.mpr hy_mem_ys⟩
  let i₀ : Fin ys.length :=
    ⟨i.1,
      lt_trans (Nat.lt_succ_self i.1)
        ((Nat.lt_sub_iff_add_lt (a := i.1) (b := 1) (c := ys.length)).mp i.2)⟩
  let i₁ : Fin ys.length :=
    ⟨i.1 + 1,
      ((Nat.lt_sub_iff_add_lt (a := i.1) (b := 1) (c := ys.length)).mp i.2)⟩
  have hj_get : ys.get j = y :=
    List.indexOf_get (List.indexOf_lt_length.mpr hy_mem_ys)
  by_cases hji : j ≤ i₀
  · have hy_le_lower : y ≤ ys.get i₀ := by
      calc
        y = ys.get j := hj_get.symm
        _ ≤ ys.get i₀ :=
          (explicitFormulaRectangleSortedYEndpoints_sorted_le T ε).rel_get_of_le hji
    exact (not_lt_of_ge hy_le_lower) hy_lower
  · have hi_lt_j : i₀ < j :=
      lt_of_not_ge hji
    have hi₁_le_j : i₁ ≤ j :=
      Nat.succ_le_of_lt hi_lt_j
    have hupper_le_y : ys.get i₁ ≤ y := by
      calc
        ys.get i₁ ≤ ys.get j :=
          (explicitFormulaRectangleSortedYEndpoints_sorted_le T ε).rel_get_of_le hi₁_le_j
        _ = y := hj_get
    exact (not_lt_of_ge hupper_le_y) hy_upper

/-- Horizontal adjacent endpoint pairs obtained by taking consecutive entries of the
sorted finite horizontal endpoint carrier. -/
noncomputable def explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :=
  let xs := explicitFormulaRectangleSortedXEndpoints F T ε
  List.ofFn
    (fun i : Fin (xs.length - 1) =>
      let i₀ : Fin xs.length :=
        ⟨i.1,
          lt_trans (Nat.lt_succ_self i.1)
            ((Nat.lt_sub_iff_add_lt (a := i.1) (b := 1) (c := xs.length)).mp i.2)⟩
      let i₁ : Fin xs.length :=
        ⟨i.1 + 1,
          ((Nat.lt_sub_iff_add_lt (a := i.1) (b := 1) (c := xs.length)).mp i.2)⟩
      { x₀ := xs.get i₀
        x₁ := xs.get i₁
        hx₀ :=
          (explicitFormulaRectangleSortedXEndpoints_mem_iff F T ε (xs.get i₀)).mp
            (List.get_mem xs i₀ i₀.2)
        hx₁ :=
          (explicitFormulaRectangleSortedXEndpoints_mem_iff F T ε (xs.get i₁)).mp
            (List.get_mem xs i₁ i₁.2)
        hx_order :=
          (explicitFormulaRectangleSortedXEndpoints_sorted_lt F T ε).rel_get_of_lt
            (show i₀ < i₁ from Nat.lt_succ_self i.1)
        hx_adj :=
          explicitFormulaRectangleSortedXEndpoints_noIntermediate_get_succ F T ε i })

/-- Vertical adjacent endpoint pairs obtained by taking consecutive entries of the sorted
finite vertical endpoint carrier. -/
noncomputable def explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints
    (T ε : ℝ) :
    List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε) :=
  let ys := explicitFormulaRectangleSortedYEndpoints T ε
  List.ofFn
    (fun i : Fin (ys.length - 1) =>
      let i₀ : Fin ys.length :=
        ⟨i.1,
          lt_trans (Nat.lt_succ_self i.1)
            ((Nat.lt_sub_iff_add_lt (a := i.1) (b := 1) (c := ys.length)).mp i.2)⟩
      let i₁ : Fin ys.length :=
        ⟨i.1 + 1,
          ((Nat.lt_sub_iff_add_lt (a := i.1) (b := 1) (c := ys.length)).mp i.2)⟩
      { y₀ := ys.get i₀
        y₁ := ys.get i₁
        hy₀ :=
          (explicitFormulaRectangleSortedYEndpoints_mem_iff T ε (ys.get i₀)).mp
            (List.get_mem ys i₀ i₀.2)
        hy₁ :=
          (explicitFormulaRectangleSortedYEndpoints_mem_iff T ε (ys.get i₁)).mp
            (List.get_mem ys i₁ i₁.2)
        hy_order :=
          (explicitFormulaRectangleSortedYEndpoints_sorted_lt T ε).rel_get_of_lt
            (show i₀ < i₁ from Nat.lt_succ_self i.1)
        hy_adj :=
          explicitFormulaRectangleSortedYEndpoints_noIntermediate_get_succ T ε i })

/-- Coordinate projection of the sorted horizontal adjacent endpoint-pair list. -/
noncomputable def explicitFormulaRectangleXAdjacentEndpointPairCoordinatesFromSortedEndpoints
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) : List (ℝ × ℝ) :=
  let xs := explicitFormulaRectangleSortedXEndpoints F T ε
  List.ofFn
    (fun i : Fin (xs.length - 1) =>
      let i₀ : Fin xs.length :=
        ⟨i.1,
          lt_trans (Nat.lt_succ_self i.1)
            ((Nat.lt_sub_iff_add_lt (a := i.1) (b := 1) (c := xs.length)).mp i.2)⟩
      let i₁ : Fin xs.length :=
        ⟨i.1 + 1,
          ((Nat.lt_sub_iff_add_lt (a := i.1) (b := 1) (c := xs.length)).mp i.2)⟩
      (xs.get i₀, xs.get i₁))

/-- Coordinate projection of the sorted vertical adjacent endpoint-pair list. -/
noncomputable def explicitFormulaRectangleYAdjacentEndpointPairCoordinatesFromSortedEndpoints
    (T ε : ℝ) : List (ℝ × ℝ) :=
  let ys := explicitFormulaRectangleSortedYEndpoints T ε
  List.ofFn
    (fun i : Fin (ys.length - 1) =>
      let i₀ : Fin ys.length :=
        ⟨i.1,
          lt_trans (Nat.lt_succ_self i.1)
            ((Nat.lt_sub_iff_add_lt (a := i.1) (b := 1) (c := ys.length)).mp i.2)⟩
      let i₁ : Fin ys.length :=
        ⟨i.1 + 1,
          ((Nat.lt_sub_iff_add_lt (a := i.1) (b := 1) (c := ys.length)).mp i.2)⟩
      (ys.get i₀, ys.get i₁))

/-- Consecutive coordinate pairs from the sorted horizontal endpoint carrier are
duplicate-free. -/
theorem explicitFormulaRectangleXAdjacentEndpointPairCoordinatesFromSortedEndpoints_nodup
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    (explicitFormulaRectangleXAdjacentEndpointPairCoordinatesFromSortedEndpoints F T ε).Nodup := by
  let xs := explicitFormulaRectangleSortedXEndpoints F T ε
  let mkPair : Fin (xs.length - 1) → ℝ × ℝ :=
    fun i =>
      let i₀ : Fin xs.length :=
        ⟨i.1,
          lt_trans (Nat.lt_succ_self i.1)
            ((Nat.lt_sub_iff_add_lt (a := i.1) (b := 1) (c := xs.length)).mp i.2)⟩
      let i₁ : Fin xs.length :=
        ⟨i.1 + 1,
          ((Nat.lt_sub_iff_add_lt (a := i.1) (b := 1) (c := xs.length)).mp i.2)⟩
      (xs.get i₀, xs.get i₁)
  have hmk_inj : Function.Injective mkPair := by
    intro i j hij
    let i₀ : Fin xs.length :=
      ⟨i.1,
        lt_trans (Nat.lt_succ_self i.1)
          ((Nat.lt_sub_iff_add_lt (a := i.1) (b := 1) (c := xs.length)).mp i.2)⟩
    let j₀ : Fin xs.length :=
      ⟨j.1,
        lt_trans (Nat.lt_succ_self j.1)
          ((Nat.lt_sub_iff_add_lt (a := j.1) (b := 1) (c := xs.length)).mp j.2)⟩
    have hfirst : xs.get i₀ = xs.get j₀ :=
      congrArg Prod.fst hij
    have hfin : i₀ = j₀ :=
      (Finset.sort_nodup (· ≤ ·)
        (explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε)).get_inj_iff.mp
        hfirst
    exact Fin.ext (congrArg Fin.val hfin)
  exact List.nodup_ofFn_ofInjective hmk_inj

/-- Consecutive coordinate pairs from the sorted vertical endpoint carrier are
duplicate-free. -/
theorem explicitFormulaRectangleYAdjacentEndpointPairCoordinatesFromSortedEndpoints_nodup
    (T ε : ℝ) :
    (explicitFormulaRectangleYAdjacentEndpointPairCoordinatesFromSortedEndpoints T ε).Nodup := by
  let ys := explicitFormulaRectangleSortedYEndpoints T ε
  let mkPair : Fin (ys.length - 1) → ℝ × ℝ :=
    fun i =>
      let i₀ : Fin ys.length :=
        ⟨i.1,
          lt_trans (Nat.lt_succ_self i.1)
            ((Nat.lt_sub_iff_add_lt (a := i.1) (b := 1) (c := ys.length)).mp i.2)⟩
      let i₁ : Fin ys.length :=
        ⟨i.1 + 1,
          ((Nat.lt_sub_iff_add_lt (a := i.1) (b := 1) (c := ys.length)).mp i.2)⟩
      (ys.get i₀, ys.get i₁)
  have hmk_inj : Function.Injective mkPair := by
    intro i j hij
    let i₀ : Fin ys.length :=
      ⟨i.1,
        lt_trans (Nat.lt_succ_self i.1)
          ((Nat.lt_sub_iff_add_lt (a := i.1) (b := 1) (c := ys.length)).mp i.2)⟩
    let j₀ : Fin ys.length :=
      ⟨j.1,
        lt_trans (Nat.lt_succ_self j.1)
          ((Nat.lt_sub_iff_add_lt (a := j.1) (b := 1) (c := ys.length)).mp j.2)⟩
    have hfirst : ys.get i₀ = ys.get j₀ :=
      congrArg Prod.fst hij
    have hfin : i₀ = j₀ :=
      (Finset.sort_nodup (· ≤ ·)
        (explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε)).get_inj_iff.mp
        hfirst
    exact Fin.ext (congrArg Fin.val hfin)
  exact List.nodup_ofFn_ofInjective hmk_inj

/-- Horizontal adjacent endpoint-pair records are extensional in their two concrete
endpoint coordinates; the remaining fields are proof fields. -/
theorem ExplicitFormulaRectangleXAdjacentEndpointPair.ext_endpoints
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (p q : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (hx₀ : p.x₀ = q.x₀) (hx₁ : p.x₁ = q.x₁) :
    p = q := by
  cases p with
  | mk px₀ px₁ phx₀ phx₁ phx_order phx_adj =>
      cases q with
      | mk qx₀ qx₁ qhx₀ qhx₁ qhx_order qhx_adj =>
          cases hx₀
          cases hx₁
          have hhx₀ : phx₀ = qhx₀ :=
            proof_irrel phx₀ qhx₀
          have hhx₁ : phx₁ = qhx₁ :=
            proof_irrel phx₁ qhx₁
          have hhx_order : phx_order = qhx_order :=
            proof_irrel phx_order qhx_order
          have hhx_adj : phx_adj = qhx_adj :=
            proof_irrel phx_adj qhx_adj
          cases hhx₀
          cases hhx₁
          cases hhx_order
          cases hhx_adj
          rfl

/-- Vertical adjacent endpoint-pair records are extensional in their two concrete
endpoint coordinates; the remaining fields are proof fields. -/
theorem ExplicitFormulaRectangleYAdjacentEndpointPair.ext_endpoints
    {T ε : ℝ}
    (p q : ExplicitFormulaRectangleYAdjacentEndpointPair T ε)
    (hy₀ : p.y₀ = q.y₀) (hy₁ : p.y₁ = q.y₁) :
    p = q := by
  cases p with
  | mk py₀ py₁ phy₀ phy₁ phy_order phy_adj =>
      cases q with
      | mk qy₀ qy₁ qhy₀ qhy₁ qhy_order qhy_adj =>
          cases hy₀
          cases hy₁
          have hhy₀ : phy₀ = qhy₀ :=
            proof_irrel phy₀ qhy₀
          have hhy₁ : phy₁ = qhy₁ :=
            proof_irrel phy₁ qhy₁
          have hhy_order : phy_order = qhy_order :=
            proof_irrel phy_order qhy_order
          have hhy_adj : phy_adj = qhy_adj :=
            proof_irrel phy_adj qhy_adj
          cases hhy₀
          cases hhy₁
          cases hhy_order
          cases hhy_adj
          rfl

/-- The sorted horizontal adjacent endpoint-pair list is duplicate-free as a list of
proof-carrying records. -/
theorem explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints_nodup
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε).Nodup := by
  let xs := explicitFormulaRectangleSortedXEndpoints F T ε
  let mkPair : Fin (xs.length - 1) →
      ExplicitFormulaRectangleXAdjacentEndpointPair F T ε :=
    fun i =>
      let i₀ : Fin xs.length :=
        ⟨i.1,
          lt_trans (Nat.lt_succ_self i.1)
            ((Nat.lt_sub_iff_add_lt (a := i.1) (b := 1) (c := xs.length)).mp i.2)⟩
      let i₁ : Fin xs.length :=
        ⟨i.1 + 1,
          ((Nat.lt_sub_iff_add_lt (a := i.1) (b := 1) (c := xs.length)).mp i.2)⟩
      { x₀ := xs.get i₀
        x₁ := xs.get i₁
        hx₀ :=
          (explicitFormulaRectangleSortedXEndpoints_mem_iff F T ε (xs.get i₀)).mp
            (List.get_mem xs i₀ i₀.2)
        hx₁ :=
          (explicitFormulaRectangleSortedXEndpoints_mem_iff F T ε (xs.get i₁)).mp
            (List.get_mem xs i₁ i₁.2)
        hx_order :=
          (explicitFormulaRectangleSortedXEndpoints_sorted_lt F T ε).rel_get_of_lt
            (show i₀ < i₁ from Nat.lt_succ_self i.1)
        hx_adj :=
          explicitFormulaRectangleSortedXEndpoints_noIntermediate_get_succ F T ε i }
  have hmk_inj : Function.Injective mkPair := by
    intro i j hij
    let i₀ : Fin xs.length :=
      ⟨i.1,
        lt_trans (Nat.lt_succ_self i.1)
          ((Nat.lt_sub_iff_add_lt (a := i.1) (b := 1) (c := xs.length)).mp i.2)⟩
    let j₀ : Fin xs.length :=
      ⟨j.1,
        lt_trans (Nat.lt_succ_self j.1)
          ((Nat.lt_sub_iff_add_lt (a := j.1) (b := 1) (c := xs.length)).mp j.2)⟩
    have hfirst : xs.get i₀ = xs.get j₀ :=
      congrArg ExplicitFormulaRectangleXAdjacentEndpointPair.x₀ hij
    have hfin : i₀ = j₀ :=
      (Finset.sort_nodup (· ≤ ·)
        (explicitFormulaRectangleInscribedSquareSubdivisionXEndpoints F T ε)).get_inj_iff.mp
        hfirst
    exact Fin.ext (congrArg Fin.val hfin)
  exact List.nodup_ofFn_ofInjective hmk_inj

/-- The sorted vertical adjacent endpoint-pair list is duplicate-free as a list of
proof-carrying records. -/
theorem explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints_nodup
    (T ε : ℝ) :
    (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε).Nodup := by
  let ys := explicitFormulaRectangleSortedYEndpoints T ε
  let mkPair : Fin (ys.length - 1) →
      ExplicitFormulaRectangleYAdjacentEndpointPair T ε :=
    fun i =>
      let i₀ : Fin ys.length :=
        ⟨i.1,
          lt_trans (Nat.lt_succ_self i.1)
            ((Nat.lt_sub_iff_add_lt (a := i.1) (b := 1) (c := ys.length)).mp i.2)⟩
      let i₁ : Fin ys.length :=
        ⟨i.1 + 1,
          ((Nat.lt_sub_iff_add_lt (a := i.1) (b := 1) (c := ys.length)).mp i.2)⟩
      { y₀ := ys.get i₀
        y₁ := ys.get i₁
        hy₀ :=
          (explicitFormulaRectangleSortedYEndpoints_mem_iff T ε (ys.get i₀)).mp
            (List.get_mem ys i₀ i₀.2)
        hy₁ :=
          (explicitFormulaRectangleSortedYEndpoints_mem_iff T ε (ys.get i₁)).mp
            (List.get_mem ys i₁ i₁.2)
        hy_order :=
          (explicitFormulaRectangleSortedYEndpoints_sorted_lt T ε).rel_get_of_lt
            (show i₀ < i₁ from Nat.lt_succ_self i.1)
        hy_adj :=
          explicitFormulaRectangleSortedYEndpoints_noIntermediate_get_succ T ε i }
  have hmk_inj : Function.Injective mkPair := by
    intro i j hij
    let i₀ : Fin ys.length :=
      ⟨i.1,
        lt_trans (Nat.lt_succ_self i.1)
          ((Nat.lt_sub_iff_add_lt (a := i.1) (b := 1) (c := ys.length)).mp i.2)⟩
    let j₀ : Fin ys.length :=
      ⟨j.1,
        lt_trans (Nat.lt_succ_self j.1)
          ((Nat.lt_sub_iff_add_lt (a := j.1) (b := 1) (c := ys.length)).mp j.2)⟩
    have hfirst : ys.get i₀ = ys.get j₀ :=
      congrArg ExplicitFormulaRectangleYAdjacentEndpointPair.y₀ hij
    have hfin : i₀ = j₀ :=
      (Finset.sort_nodup (· ≤ ·)
        (explicitFormulaRectangleInscribedSquareSubdivisionYEndpoints T ε)).get_inj_iff.mp
        hfirst
    exact Fin.ext (congrArg Fin.val hfin)
  exact List.nodup_ofFn_ofInjective hmk_inj

/-- A proof-carrying adjacent horizontal/vertical endpoint-pair cell whose closed
coordinate rectangle omits every raw singular coordinate. -/
structure ExplicitFormulaRectangleRegularAdjacentEndpointPairCell
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) where
  xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε
  ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε
  homit :
    ∀ a : ℂ,
      a ∈ explicitFormulaRectangleRawSingularCoordinates T →
        a.re ∉ [[xpair.x₀, xpair.x₁]] ∨
          a.im ∉ [[ypair.y₀, ypair.y₁]]

/-- Convert a proof-carrying adjacent-pair cell into the endpoint-data record consumed by
the endpoint-data boundary-sum path. -/
def ExplicitFormulaRectangleRegularAdjacentEndpointPairCell.toEndpointData
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε) :
    ExplicitFormulaRectangleRegularGridCellEndpointData F T ε :=
  { x₀ := c.xpair.x₀
    x₁ := c.xpair.x₁
    y₀ := c.ypair.y₀
    y₁ := c.ypair.y₁
    hx₀ := c.xpair.hx₀
    hx₁ := c.xpair.hx₁
    hy₀ := c.ypair.hy₀
    hy₁ := c.ypair.hy₁
    hx_order := c.xpair.hx_order
    hy_order := c.ypair.hy_order
    hx_adj := c.xpair.hx_adj
    hy_adj := c.ypair.hy_adj
    homit := c.homit }

/-- Convert a concrete list of proof-carrying adjacent-pair cells into endpoint data,
without filtering or requiring equality on proof-carrying records. -/
def explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (cells : List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε)) :
    List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
  cells.map
    (fun c : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε =>
      c.toEndpointData)

/-- The endpoint-data list constructed from adjacent-pair cells has the same length as the
input proof-carrying cell list. -/
theorem explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells_length
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (cells : List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε)) :
    (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells cells).length =
      cells.length :=
  List.length_map
    (fun c : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε =>
      c.toEndpointData)
    cells

/-- Every endpoint datum constructed from adjacent-pair cells comes from a concrete
proof-carrying adjacent-pair cell in the input list. -/
theorem explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells_mem
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (cells : List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε))
    {d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε}
    (hd :
      d ∈ explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        cells) :
    ∃ c : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε,
      c ∈ cells ∧ c.toEndpointData = d :=
  List.mem_map.mp hd

/-- A regular adjacent-pair cell is extensional in its horizontal and vertical adjacent
endpoint-pair records; the omission field is a proof field. -/
theorem ExplicitFormulaRectangleRegularAdjacentEndpointPairCell.ext_pairs
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c d : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε)
    (hxpair : c.xpair = d.xpair) (hypair : c.ypair = d.ypair) :
    c = d := by
  cases c with
  | mk cx cy chomit =>
      cases d with
      | mk dx dy dhomit =>
          cases hxpair
          cases hypair
          have hhomit : chomit = dhomit :=
            proof_irrel chomit dhomit
          cases hhomit
          rfl

/-- The adjacent-pair-cell-to-endpoint-data map is injective: endpoint data records
remember the two adjacent endpoint-pair records up to proof irrelevance. -/
theorem ExplicitFormulaRectangleRegularAdjacentEndpointPairCell.toEndpointData_injective
    {F : ExplicitFormulaContourFamily} {T ε : ℝ} :
    Function.Injective
      (fun c : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε =>
        c.toEndpointData) := by
  intro c d h
  have hx₀ : c.xpair.x₀ = d.xpair.x₀ :=
    congrArg ExplicitFormulaRectangleRegularGridCellEndpointData.x₀ h
  have hx₁ : c.xpair.x₁ = d.xpair.x₁ :=
    congrArg ExplicitFormulaRectangleRegularGridCellEndpointData.x₁ h
  have hy₀ : c.ypair.y₀ = d.ypair.y₀ :=
    congrArg ExplicitFormulaRectangleRegularGridCellEndpointData.y₀ h
  have hy₁ : c.ypair.y₁ = d.ypair.y₁ :=
    congrArg ExplicitFormulaRectangleRegularGridCellEndpointData.y₁ h
  have hxpair : c.xpair = d.xpair :=
    ExplicitFormulaRectangleXAdjacentEndpointPair.ext_endpoints c.xpair d.xpair hx₀ hx₁
  have hypair : c.ypair = d.ypair :=
    ExplicitFormulaRectangleYAdjacentEndpointPair.ext_endpoints c.ypair d.ypair hy₀ hy₁
  exact ExplicitFormulaRectangleRegularAdjacentEndpointPairCell.ext_pairs c d hxpair hypair

/-- Mapping duplicate-free adjacent-pair cells to endpoint data preserves
duplicate-freeness. -/
theorem explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells_nodup
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (cells : List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε))
    (hnodup : cells.Nodup) :
    (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells cells).Nodup := by
  exact
    hnodup.map
      ExplicitFormulaRectangleRegularAdjacentEndpointPairCell.toEndpointData_injective

/-- The coordinate-omission predicate that selects genuine complement cells from crossed
adjacent endpoint-pair rectangles.  A cell is retained exactly when it is not contained in
any raw inscribed-square deletion box. -/
def explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε) : Prop :=
  ∀ a : ℂ,
    a ∈ explicitFormulaRectangleRawSingularCoordinates T →
      ¬
        ((explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).re ≤ xpair.x₀ ∧
          xpair.x₁ ≤ (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).re ∧
            (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).im ≤ ypair.y₀ ∧
              ypair.y₁ ≤ (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).im)

/-- A proof-carrying adjacent-pair cell exposes the coordinate-omission proof stored in
its `homit` field. -/
theorem ExplicitFormulaRectangleRegularAdjacentEndpointPairCell.coordinateOmission
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε) :
    explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission c.xpair c.ypair :=
  c.homit

/-- For one horizontal adjacent endpoint pair, select exactly those vertical adjacent-pair
cells satisfying the coordinate-omission predicate. -/
noncomputable def explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε) →
      List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε)
  | [] => []
  | ypair :: rest =>
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        { xpair := xpair
          ypair := ypair
          homit := homit } ::
          explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
            xpair rest
      else
        explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair rest

/-- Membership in a selected fixed-horizontal-pair row records membership of the carried
vertical adjacent-pair in the source vertical-pair list. -/
theorem explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX_mem_ypair
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    ∀ (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))
      (c : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε),
        c ∈ explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair ypairs →
          c.ypair ∈ ypairs
  | [], c, hc => False.elim (List.not_mem_nil c hc)
  | ypair :: rest, c, hc =>
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        match hc with
        | Or.inl hhead =>
            Eq.subst
              (motive := fun c' :
                  ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε =>
                c'.ypair ∈ ypair :: rest)
              hhead.symm
              (List.mem_cons_self ypair rest)
        | Or.inr htail =>
            List.mem_cons_of_mem ypair
              (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX_mem_ypair
                xpair rest c htail)
      else
        List.mem_cons_of_mem ypair
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX_mem_ypair
            xpair rest c hc)

/-- Membership in a selected fixed-horizontal-pair row records the fixed horizontal
adjacent-pair carried by every selected cell in that row. -/
theorem explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX_mem_xpair
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    ∀ (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))
      (c : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε),
        c ∈ explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair ypairs →
          c.xpair = xpair
  | [], c, hc => False.elim (List.not_mem_nil c hc)
  | ypair :: rest, c, hc =>
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        match hc with
        | Or.inl hhead =>
            Eq.subst
              (motive := fun c' :
                  ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε =>
                c'.xpair = xpair)
              hhead.symm
              rfl
        | Or.inr htail =>
            explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX_mem_xpair
              xpair rest c htail
      else
        explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX_mem_xpair
          xpair rest c hc

/-- For a fixed horizontal adjacent-pair, coordinate-omission selection preserves
duplicate-freeness of the vertical adjacent-pair source list. -/
theorem explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX_nodup
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    ∀ (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)),
      ypairs.Nodup →
        (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
          xpair ypairs).Nodup
  | [], hynodup => List.nodup_nil
  | ypair :: rest, hynodup =>
      have hy_not_mem_rest : ypair ∉ rest :=
        (List.nodup_cons.mp hynodup).1
      have hrest_nodup : rest.Nodup :=
        (List.nodup_cons.mp hynodup).2
      have htail_nodup :
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
            xpair rest).Nodup :=
        explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX_nodup
          xpair rest hrest_nodup
      if homit :
          explicitFormulaRectangleAdjacentEndpointPairCoordinateOmission xpair ypair then
        have hhead_not_tail :
            { xpair := xpair
              ypair := ypair
              homit := homit } ∉
              explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
                xpair rest := by
          intro hmem
          have hy_tail : ypair ∈ rest :=
            explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX_mem_ypair
              xpair rest
              { xpair := xpair
                ypair := ypair
                homit := homit }
              hmem
          exact hy_not_mem_rest hy_tail
        exact List.nodup_cons.mpr (And.intro hhead_not_tail htail_nodup)
      else
        exact htail_nodup

/-- Select the genuine complement cells from the crossed adjacent endpoint-pair lists by
testing the coordinate-omission predicate cell-by-cell. -/
noncomputable def explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
    {F : ExplicitFormulaContourFamily} {T ε : ℝ} :
    List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) →
      List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε) →
        List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε)
  | [], _ypairs => []
  | xpair :: rest, ypairs =>
      explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
        xpair ypairs ++
        explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          rest ypairs

/-- Membership in the selected crossed adjacent-pair cell list records membership of the
carried horizontal adjacent-pair in the source horizontal-pair list. -/
theorem explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists_mem_xpair
    {F : ExplicitFormulaContourFamily} {T ε : ℝ} :
    ∀ (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
      (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))
      (c : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε),
        c ∈ explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          xpairs ypairs →
          c.xpair ∈ xpairs
  | [], ypairs, c, hc => False.elim (List.not_mem_nil c hc)
  | xpair :: rest, ypairs, c, hc =>
      match List.mem_append.mp hc with
      | Or.inl hrow =>
          have hx : c.xpair = xpair :=
            explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX_mem_xpair
              xpair ypairs c hrow
          Eq.subst
            (motive := fun x : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
              x ∈ xpair :: rest)
            hx.symm
            (List.mem_cons_self xpair rest)
      | Or.inr htail =>
          List.mem_cons_of_mem xpair
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists_mem_xpair
              rest ypairs c htail)

/-- Membership in the selected crossed adjacent-pair cell list records membership of the
carried vertical adjacent-pair in the source vertical-pair list. -/
theorem explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists_mem_ypair
    {F : ExplicitFormulaContourFamily} {T ε : ℝ} :
    ∀ (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
      (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))
      (c : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε),
        c ∈ explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
          xpairs ypairs →
          c.ypair ∈ ypairs
  | [], ypairs, c, hc => False.elim (List.not_mem_nil c hc)
  | xpair :: rest, ypairs, c, hc =>
      match List.mem_append.mp hc with
      | Or.inl hrow =>
          explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX_mem_ypair
            xpair ypairs c hrow
      | Or.inr htail =>
          explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists_mem_ypair
            rest ypairs c htail

/-- Coordinate-omission selection over crossed adjacent endpoint-pair lists is
duplicate-free when the two source adjacent-pair lists are duplicate-free. -/
theorem explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists_nodup
    {F : ExplicitFormulaContourFamily} {T ε : ℝ} :
    ∀ (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
      (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)),
        xpairs.Nodup →
          ypairs.Nodup →
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              xpairs ypairs).Nodup
  | [], ypairs, hxnodup, hynodup => List.nodup_nil
  | xpair :: rest, ypairs, hxnodup, hynodup =>
      have hx_not_mem_rest : xpair ∉ rest :=
        (List.nodup_cons.mp hxnodup).1
      have hrest_nodup : rest.Nodup :=
        (List.nodup_cons.mp hxnodup).2
      have hrow_nodup :
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
            xpair ypairs).Nodup :=
        explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX_nodup
          xpair ypairs hynodup
      have htail_nodup :
          (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
            rest ypairs).Nodup :=
        explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists_nodup
          rest ypairs hrest_nodup hynodup
      have hdisjoint :
          List.Disjoint
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX
              xpair ypairs)
            (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
              rest ypairs) := by
        intro c hcrow hctail
        have hxrow : c.xpair = xpair :=
          explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfFixedX_mem_xpair
            xpair ypairs c hcrow
        have hxtail : c.xpair ∈ rest :=
          explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists_mem_xpair
            rest ypairs c hctail
        exact
          hx_not_mem_rest
            (Eq.subst
              (motive := fun x : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
                x ∈ rest)
              hxrow
              hxtail)
      exact List.Nodup.append hrow_nodup htail_nodup hdisjoint

/-- The canonical selected complement-cell list from sorted adjacent endpoint pairs. -/
noncomputable def explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCells
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε) :=
  explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists
    (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
    (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)

/-- The canonical selected complement-cell list is duplicate-free. -/
theorem explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCells_nodup
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCells F T ε).Nodup := by
  exact
    explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists_nodup
      (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
      (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)
      (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints_nodup F T ε)
      (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints_nodup T ε)

/-- Endpoint data for the canonical selected complement cells. -/
noncomputable def explicitFormulaRectangleSelectedEndpointData
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
  explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
    (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCells F T ε)

/-- The selected endpoint-data list is duplicate-free. -/
theorem explicitFormulaRectangleSelectedEndpointData_nodup
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    (explicitFormulaRectangleSelectedEndpointData F T ε).Nodup := by
  exact
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells_nodup
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCells F T ε)
      (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCells_nodup F T ε)

/-- Every selected endpoint datum comes from a concrete selected adjacent-pair cell. -/
theorem explicitFormulaRectangleSelectedEndpointData_mem_cell
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    {d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε}
    (hd : d ∈ explicitFormulaRectangleSelectedEndpointData F T ε) :
    ∃ c : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε,
      c ∈ explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCells F T ε ∧
        c.toEndpointData = d :=
  explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells_mem
    (explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCells F T ε) hd

/-- The horizontal adjacent-pair underlying a selected endpoint datum belongs to the
canonical sorted horizontal adjacent-pair list. -/
theorem explicitFormulaRectangleSelectedEndpointData_mem_xpair
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    {d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε}
    (hd : d ∈ explicitFormulaRectangleSelectedEndpointData F T ε) :
    ∃ c : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε,
      c.toEndpointData = d ∧
        c.xpair ∈ explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε := by
  match explicitFormulaRectangleSelectedEndpointData_mem_cell hd with
  | ⟨c, hc, hcd⟩ =>
      exact
        ⟨c, hcd,
          explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists_mem_xpair
            (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)
            c hc⟩

/-- The vertical adjacent-pair underlying a selected endpoint datum belongs to the canonical
sorted vertical adjacent-pair list. -/
theorem explicitFormulaRectangleSelectedEndpointData_mem_ypair
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    {d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε}
    (hd : d ∈ explicitFormulaRectangleSelectedEndpointData F T ε) :
    ∃ c : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε,
      c.toEndpointData = d ∧
        c.ypair ∈ explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε := by
  match explicitFormulaRectangleSelectedEndpointData_mem_cell hd with
  | ⟨c, hc, hcd⟩ =>
      exact
        ⟨c, hcd,
          explicitFormulaRectangleSelectedRegularAdjacentEndpointPairCellsOfPairLists_mem_ypair
            (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
            (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)
            c hc⟩

/-- A selected endpoint datum omits every raw singular coordinate from at least one of
its two coordinate intervals. -/
theorem explicitFormulaRectangleSelectedEndpointData_coordinateOmission
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    {d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε}
    (hd : d ∈ explicitFormulaRectangleSelectedEndpointData F T ε) :
    ∀ a : ℂ,
      a ∈ explicitFormulaRectangleRawSingularCoordinates T →
        a.re ∉ [[d.x₀, d.x₁]] ∨
          a.im ∉ [[d.y₀, d.y₁]] := by
  match explicitFormulaRectangleSelectedEndpointData_mem_cell hd with
  | ⟨c, _hc, hcd⟩ =>
      exact
        Eq.subst
          (motive := fun d' : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            ∀ a : ℂ,
              a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a.re ∉ [[d'.x₀, d'.x₁]] ∨
                  a.im ∉ [[d'.y₀, d'.y₁]])
          hcd
          (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell.coordinateOmission c)

/-- For one horizontal adjacent endpoint pair, construct the proof-carrying regular cells
obtained by crossing it with a concrete list of vertical adjacent endpoint pairs.  The
raw-center omission proof is supplied for each listed vertical pair and stored in the
resulting cell record. -/
def explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) →
      (∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε,
        ypair ∈ ypairs →
          ∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a.re ∉ [[xpair.x₀, xpair.x₁]] ∨
                a.im ∉ [[ypair.y₀, ypair.y₁]]) →
        List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε)
  | [], _ => []
  | ypair :: rest, homit =>
      { xpair := xpair
        ypair := ypair
        homit := homit ypair (List.mem_cons_self ypair rest) } ::
        explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
          xpair rest
          (fun ypair' hy' =>
            homit ypair' (List.mem_cons_of_mem ypair hy'))

/-- The fixed-horizontal-pair constructor is empty over the empty vertical-pair list. -/
theorem explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)
    (homit :
      ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε,
        ypair ∈
          ([] : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) →
          ∀ a : ℂ,
            a ∈ explicitFormulaRectangleRawSingularCoordinates T →
              a.re ∉ [[xpair.x₀, xpair.x₁]] ∨
                a.im ∉ [[ypair.y₀, ypair.y₁]]) :
    explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
      xpair [] homit = [] := by
  rfl

/-- The fixed-horizontal-pair constructor over a cons vertical-pair list stores the first
proof-carrying rectangle and then recurses over the remaining vertical pairs. -/
theorem explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
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
    explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
        xpair (ypair :: rest) homit =
      { xpair := xpair
        ypair := ypair
        homit := homit ypair (List.mem_cons_self ypair rest) } ::
        explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
          xpair rest
          (fun ypair' hy' =>
            homit ypair' (List.mem_cons_of_mem ypair hy')) := by
  rfl

/-- Membership in a fixed-horizontal-pair row records membership of the carried vertical
adjacent-pair in the source vertical-pair list. -/
theorem explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX_mem_ypair
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    ∀ (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))
      (homit :
        ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε,
          ypair ∈ ypairs →
            ∀ a : ℂ,
              a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a.re ∉ [[xpair.x₀, xpair.x₁]] ∨
                  a.im ∉ [[ypair.y₀, ypair.y₁]])
      (c : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε),
        c ∈ explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
          xpair ypairs homit →
          c.ypair ∈ ypairs
  | [], homit, c, hc => False.elim (List.not_mem_nil c hc)
  | ypair :: rest, homit, c, hc =>
      match hc with
      | Or.inl hhead =>
          Eq.subst
            (motive := fun c' : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε =>
              c'.ypair ∈ ypair :: rest)
            hhead.symm
            (List.mem_cons_self ypair rest)
      | Or.inr htail =>
          List.mem_cons_of_mem ypair
            (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX_mem_ypair
              xpair rest
              (fun ypair' hy' =>
                homit ypair' (List.mem_cons_of_mem ypair hy'))
              c htail)

/-- Membership in a fixed-horizontal-pair row records the fixed horizontal adjacent-pair
carried by every cell in that row. -/
theorem explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX_mem_xpair
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    ∀ (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))
      (homit :
        ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε,
          ypair ∈ ypairs →
            ∀ a : ℂ,
              a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a.re ∉ [[xpair.x₀, xpair.x₁]] ∨
                  a.im ∉ [[ypair.y₀, ypair.y₁]])
      (c : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε),
        c ∈ explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
          xpair ypairs homit →
          c.xpair = xpair
  | [], homit, c, hc => False.elim (List.not_mem_nil c hc)
  | ypair :: rest, homit, c, hc =>
      match hc with
      | Or.inl hhead =>
          Eq.subst
            (motive := fun c' : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε =>
              c'.xpair = xpair)
            hhead.symm
            rfl
      | Or.inr htail =>
          explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX_mem_xpair
            xpair rest
            (fun ypair' hy' =>
              homit ypair' (List.mem_cons_of_mem ypair hy'))
            c htail

/-- For a fixed horizontal adjacent-pair, the row of regular adjacent-pair cells is
duplicate-free whenever the source vertical adjacent-pair list is duplicate-free. -/
theorem explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX_nodup
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    ∀ (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))
      (homit :
        ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε,
          ypair ∈ ypairs →
            ∀ a : ℂ,
              a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a.re ∉ [[xpair.x₀, xpair.x₁]] ∨
                  a.im ∉ [[ypair.y₀, ypair.y₁]]),
        ypairs.Nodup →
          (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
            xpair ypairs homit).Nodup
  | [], homit, hynodup => List.nodup_nil
  | ypair :: rest, homit, hynodup =>
      have hy_not_mem_rest : ypair ∉ rest :=
        (List.nodup_cons.mp hynodup).1
      have hrest_nodup : rest.Nodup :=
        (List.nodup_cons.mp hynodup).2
      have htail_nodup :
          (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
            xpair rest
            (fun ypair' hy' =>
              homit ypair' (List.mem_cons_of_mem ypair hy'))).Nodup :=
        explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX_nodup
          xpair rest
          (fun ypair' hy' =>
            homit ypair' (List.mem_cons_of_mem ypair hy'))
          hrest_nodup
      have hhead_not_tail :
          { xpair := xpair
            ypair := ypair
            homit := homit ypair (List.mem_cons_self ypair rest) } ∉
            explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
              xpair rest
              (fun ypair' hy' =>
                homit ypair' (List.mem_cons_of_mem ypair hy')) := by
        intro hmem
        have hy_tail :
            ypair ∈ rest :=
          explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX_mem_ypair
            xpair rest
            (fun ypair' hy' =>
              homit ypair' (List.mem_cons_of_mem ypair hy'))
            { xpair := xpair
              ypair := ypair
              homit := homit ypair (List.mem_cons_self ypair rest) }
            hmem
        exact hy_not_mem_rest hy_tail
      exact List.nodup_cons.mpr (And.intro hhead_not_tail htail_nodup)

/-- Construct the full proof-carrying regular adjacent-pair cell list from concrete
horizontal and vertical adjacent-pair lists.  The construction is recursive and
proof-carrying, avoiding `Finset` filtering and equality on the cell records. -/
def explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfPairLists
    {F : ExplicitFormulaContourFamily} {T ε : ℝ} :
    (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) →
      (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε)) →
        (∀ xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε,
          xpair ∈ xpairs →
            ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε,
              ypair ∈ ypairs →
                ∀ a : ℂ,
                  a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                    a.re ∉ [[xpair.x₀, xpair.x₁]] ∨
                      a.im ∉ [[ypair.y₀, ypair.y₁]]) →
          List (ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε)
  | [], _ypairs, _ => []
  | xpair :: rest, ypairs, homit =>
      explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
        xpair ypairs
        (fun ypair hy =>
          homit xpair (List.mem_cons_self xpair rest) ypair hy) ++
        explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfPairLists
          rest ypairs
          (fun xpair' hx' ypair hy =>
            homit xpair' (List.mem_cons_of_mem xpair hx') ypair hy)

/-- The full adjacent-pair cell constructor is empty over the empty horizontal-pair list. -/
theorem explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfPairLists_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))
    (homit :
      ∀ xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε,
        xpair ∈
          ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) →
          ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε,
            ypair ∈ ypairs →
              ∀ a : ℂ,
                a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a.re ∉ [[xpair.x₀, xpair.x₁]] ∨
                    a.im ∉ [[ypair.y₀, ypair.y₁]]) :
    explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfPairLists
      [] ypairs homit = [] := by
  rfl

/-- The full adjacent-pair cell constructor over a cons horizontal-pair list appends the
fixed-row construction for the first horizontal pair to the recursively constructed
remaining rows. -/
theorem explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfPairLists_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
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
    explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfPairLists
        (xpair :: rest) ypairs homit =
      explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
        xpair ypairs
        (fun ypair hy =>
          homit xpair (List.mem_cons_self xpair rest) ypair hy) ++
        explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfPairLists
          rest ypairs
          (fun xpair' hx' ypair hy =>
            homit xpair' (List.mem_cons_of_mem xpair hx') ypair hy) := by
  rfl

/-- Membership in the full crossed adjacent-pair cell list records membership of the
carried horizontal adjacent-pair in the source horizontal-pair list. -/
theorem explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfPairLists_mem_xpair
    {F : ExplicitFormulaContourFamily} {T ε : ℝ} :
    ∀ (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
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
      (c : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε),
        c ∈ explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfPairLists
          xpairs ypairs homit →
          c.xpair ∈ xpairs
  | [], ypairs, homit, c, hc => False.elim (List.not_mem_nil c hc)
  | xpair :: rest, ypairs, homit, c, hc =>
      match List.mem_append.mp hc with
      | Or.inl hrow =>
          have hx : c.xpair = xpair :=
            explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX_mem_xpair
              xpair ypairs
              (fun ypair hy =>
                homit xpair (List.mem_cons_self xpair rest) ypair hy)
              c hrow
          Eq.subst
            (motive := fun x : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
              x ∈ xpair :: rest)
            hx.symm
            (List.mem_cons_self xpair rest)
      | Or.inr htail =>
          List.mem_cons_of_mem xpair
            (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfPairLists_mem_xpair
              rest ypairs
              (fun xpair' hx' ypair hy =>
                homit xpair' (List.mem_cons_of_mem xpair hx') ypair hy)
              c htail)

/-- The full crossed regular adjacent-pair cell list is duplicate-free when the source
horizontal and vertical adjacent-pair lists are duplicate-free. -/
theorem explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfPairLists_nodup
    {F : ExplicitFormulaContourFamily} {T ε : ℝ} :
    ∀ (xpairs : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε))
      (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))
      (homit :
        ∀ xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε,
          xpair ∈ xpairs →
            ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε,
              ypair ∈ ypairs →
                ∀ a : ℂ,
                  a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                    a.re ∉ [[xpair.x₀, xpair.x₁]] ∨
                      a.im ∉ [[ypair.y₀, ypair.y₁]]),
        xpairs.Nodup →
          ypairs.Nodup →
            (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfPairLists
              xpairs ypairs homit).Nodup
  | [], ypairs, homit, hxnodup, hynodup => List.nodup_nil
  | xpair :: rest, ypairs, homit, hxnodup, hynodup =>
      have hx_not_mem_rest : xpair ∉ rest :=
        (List.nodup_cons.mp hxnodup).1
      have hrest_nodup : rest.Nodup :=
        (List.nodup_cons.mp hxnodup).2
      have hrow_nodup :
          (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
            xpair ypairs
            (fun ypair hy =>
              homit xpair (List.mem_cons_self xpair rest) ypair hy)).Nodup :=
        explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX_nodup
          xpair ypairs
          (fun ypair hy =>
            homit xpair (List.mem_cons_self xpair rest) ypair hy)
          hynodup
      have htail_nodup :
          (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfPairLists
            rest ypairs
            (fun xpair' hx' ypair hy =>
              homit xpair' (List.mem_cons_of_mem xpair hx') ypair hy)).Nodup :=
        explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfPairLists_nodup
          rest ypairs
          (fun xpair' hx' ypair hy =>
            homit xpair' (List.mem_cons_of_mem xpair hx') ypair hy)
          hrest_nodup hynodup
      have hdisjoint :
          List.Disjoint
            (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
              xpair ypairs
              (fun ypair hy =>
                homit xpair (List.mem_cons_self xpair rest) ypair hy))
            (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfPairLists
              rest ypairs
              (fun xpair' hx' ypair hy =>
                homit xpair' (List.mem_cons_of_mem xpair hx') ypair hy)) := by
        intro c hcrow hctail
        have hxrow : c.xpair = xpair :=
          explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX_mem_xpair
            xpair ypairs
            (fun ypair hy =>
              homit xpair (List.mem_cons_self xpair rest) ypair hy)
            c hcrow
        have hxtail : c.xpair ∈ rest :=
          explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfPairLists_mem_xpair
            rest ypairs
            (fun xpair' hx' ypair hy =>
              homit xpair' (List.mem_cons_of_mem xpair hx') ypair hy)
            c hctail
        exact
          hx_not_mem_rest
            (Eq.subst
              (motive := fun x : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε =>
                x ∈ rest)
              hxrow
              hxtail)
      exact List.Nodup.append hrow_nodup htail_nodup hdisjoint

/-- Endpoint-data list obtained from concrete horizontal and vertical adjacent-pair lists,
with the regularity proof carried at construction time. -/
def explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
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
                    a.im ∉ [[ypair.y₀, ypair.y₁]]) :
    List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
  explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
    (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfPairLists
      xpairs ypairs homit)

/-- Endpoint-data lists obtained from duplicate-free horizontal and vertical adjacent
endpoint-pair lists are duplicate-free. -/
theorem explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists_nodup
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
      xpairs ypairs homit).Nodup := by
  exact
    explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells_nodup
      (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfPairLists
        xpairs ypairs homit)
      (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfPairLists_nodup
        xpairs ypairs homit hxnodup hynodup)

/-- Endpoint-data list produced from the sorted horizontal and vertical adjacent endpoint
pair lists.  The omission proof is still supplied cellwise, but the endpoint-pair lists
come canonically from the finite endpoint carriers. -/
noncomputable def explicitFormulaRectangleEndpointDataListOfSortedAdjacentEndpointPairs
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (homit :
      ∀ xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε,
        xpair ∈ explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε →
          ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε,
            ypair ∈ explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε →
              ∀ a : ℂ,
                a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a.re ∉ [[xpair.x₀, xpair.x₁]] ∨
                    a.im ∉ [[ypair.y₀, ypair.y₁]]) :
    List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :=
  explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
    (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
    (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)
    homit

/-- The endpoint-data list produced from the sorted adjacent endpoint-pair lists is
duplicate-free. -/
theorem explicitFormulaRectangleEndpointDataListOfSortedAdjacentEndpointPairs_nodup
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (homit :
      ∀ xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε,
        xpair ∈ explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε →
          ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε,
            ypair ∈ explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε →
              ∀ a : ℂ,
                a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a.re ∉ [[xpair.x₀, xpair.x₁]] ∨
                    a.im ∉ [[ypair.y₀, ypair.y₁]]) :
    (explicitFormulaRectangleEndpointDataListOfSortedAdjacentEndpointPairs
      (F := F) (T := T) (ε := ε) homit).Nodup := by
  exact
    explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists_nodup
      (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints F T ε)
      (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints T ε)
      homit
      (explicitFormulaRectangleXAdjacentEndpointPairsFromSortedEndpoints_nodup F T ε)
      (explicitFormulaRectangleYAdjacentEndpointPairsFromSortedEndpoints_nodup T ε)

/-- Coordinate label of a horizontal endpoint-data edge: the horizontal span and the
height of the edge. -/
abbrev ExplicitFormulaRectangleHorizontalEndpointDataEdge : Type :=
  (ℝ × ℝ) × ℝ

/-- Coordinate label of a vertical endpoint-data edge: the vertical span and the real
coordinate of the edge. -/
abbrev ExplicitFormulaRectangleVerticalEndpointDataEdge : Type :=
  (ℝ × ℝ) × ℝ

/-- Bottom horizontal edge coordinates of one endpoint-data cell. -/
def ExplicitFormulaRectangleRegularGridCellEndpointData.bottomEdgeCoordinates
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :
    ExplicitFormulaRectangleHorizontalEndpointDataEdge :=
  ((d.x₀, d.x₁), d.y₀)

/-- Top horizontal edge coordinates of one endpoint-data cell. -/
def ExplicitFormulaRectangleRegularGridCellEndpointData.topEdgeCoordinates
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :
    ExplicitFormulaRectangleHorizontalEndpointDataEdge :=
  ((d.x₀, d.x₁), d.y₁)

/-- Left vertical edge coordinates of one endpoint-data cell. -/
def ExplicitFormulaRectangleRegularGridCellEndpointData.leftEdgeCoordinates
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :
    ExplicitFormulaRectangleVerticalEndpointDataEdge :=
  ((d.y₀, d.y₁), d.x₀)

/-- Right vertical edge coordinates of one endpoint-data cell. -/
def ExplicitFormulaRectangleRegularGridCellEndpointData.rightEdgeCoordinates
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :
    ExplicitFormulaRectangleVerticalEndpointDataEdge :=
  ((d.y₀, d.y₁), d.x₁)

/-- A bottom edge of endpoint data produced from an adjacent-pair cell is exactly the
horizontal adjacent-pair span at the lower vertical endpoint. -/
theorem ExplicitFormulaRectangleRegularAdjacentEndpointPairCell.toEndpointData_bottomEdgeCoordinates
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε) :
    c.toEndpointData.bottomEdgeCoordinates =
      ((c.xpair.x₀, c.xpair.x₁), c.ypair.y₀) := by
  rfl

/-- A top edge of endpoint data produced from an adjacent-pair cell is exactly the
horizontal adjacent-pair span at the upper vertical endpoint. -/
theorem ExplicitFormulaRectangleRegularAdjacentEndpointPairCell.toEndpointData_topEdgeCoordinates
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε) :
    c.toEndpointData.topEdgeCoordinates =
      ((c.xpair.x₀, c.xpair.x₁), c.ypair.y₁) := by
  rfl

/-- A left edge of endpoint data produced from an adjacent-pair cell is exactly the
vertical adjacent-pair span at the lower horizontal endpoint. -/
theorem ExplicitFormulaRectangleRegularAdjacentEndpointPairCell.toEndpointData_leftEdgeCoordinates
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε) :
    c.toEndpointData.leftEdgeCoordinates =
      ((c.ypair.y₀, c.ypair.y₁), c.xpair.x₀) := by
  rfl

/-- A right edge of endpoint data produced from an adjacent-pair cell is exactly the
vertical adjacent-pair span at the upper horizontal endpoint. -/
theorem ExplicitFormulaRectangleRegularAdjacentEndpointPairCell.toEndpointData_rightEdgeCoordinates
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (c : ExplicitFormulaRectangleRegularAdjacentEndpointPairCell F T ε) :
    c.toEndpointData.rightEdgeCoordinates =
      ((c.ypair.y₀, c.ypair.y₁), c.xpair.x₁) := by
  rfl

/-- Bottom edge coordinates for one fixed horizontal adjacent-pair row. -/
def explicitFormulaRectangleBottomEdgeCoordinatesOfFixedX
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε) →
      List ExplicitFormulaRectangleHorizontalEndpointDataEdge
  | [] => []
  | ypair :: rest =>
      ((xpair.x₀, xpair.x₁), ypair.y₀) ::
        explicitFormulaRectangleBottomEdgeCoordinatesOfFixedX xpair rest

/-- Top edge coordinates for one fixed horizontal adjacent-pair row. -/
def explicitFormulaRectangleTopEdgeCoordinatesOfFixedX
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε) →
      List ExplicitFormulaRectangleHorizontalEndpointDataEdge
  | [] => []
  | ypair :: rest =>
      ((xpair.x₀, xpair.x₁), ypair.y₁) ::
        explicitFormulaRectangleTopEdgeCoordinatesOfFixedX xpair rest

/-- Left edge coordinates for one fixed horizontal adjacent-pair row. -/
def explicitFormulaRectangleLeftEdgeCoordinatesOfFixedX
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε) →
      List ExplicitFormulaRectangleVerticalEndpointDataEdge
  | [] => []
  | ypair :: rest =>
      ((ypair.y₀, ypair.y₁), xpair.x₀) ::
        explicitFormulaRectangleLeftEdgeCoordinatesOfFixedX xpair rest

/-- Right edge coordinates for one fixed horizontal adjacent-pair row. -/
def explicitFormulaRectangleRightEdgeCoordinatesOfFixedX
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε) →
      List ExplicitFormulaRectangleVerticalEndpointDataEdge
  | [] => []
  | ypair :: rest =>
      ((ypair.y₀, ypair.y₁), xpair.x₁) ::
        explicitFormulaRectangleRightEdgeCoordinatesOfFixedX xpair rest

/-- The endpoint-data list for one fixed horizontal row has the expected bottom edge
coordinate list. -/
theorem explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells_fixedX_bottomEdges
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    ∀ (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))
      (homit :
        ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε,
          ypair ∈ ypairs →
            ∀ a : ℂ,
              a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a.re ∉ [[xpair.x₀, xpair.x₁]] ∨
                  a.im ∉ [[ypair.y₀, ypair.y₁]]),
      (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
          xpair ypairs homit)).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.bottomEdgeCoordinates) =
        explicitFormulaRectangleBottomEdgeCoordinatesOfFixedX xpair ypairs
  | [], homit => rfl
  | ypair :: rest, homit =>
      congrArg
        (fun edges : List ExplicitFormulaRectangleHorizontalEndpointDataEdge =>
          ((xpair.x₀, xpair.x₁), ypair.y₀) :: edges)
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells_fixedX_bottomEdges
          xpair rest
          (fun ypair' hy' =>
            homit ypair' (List.mem_cons_of_mem ypair hy')))

/-- The endpoint-data list for one fixed horizontal row has the expected top edge
coordinate list. -/
theorem explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells_fixedX_topEdges
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    ∀ (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))
      (homit :
        ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε,
          ypair ∈ ypairs →
            ∀ a : ℂ,
              a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a.re ∉ [[xpair.x₀, xpair.x₁]] ∨
                  a.im ∉ [[ypair.y₀, ypair.y₁]]),
      (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
          xpair ypairs homit)).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.topEdgeCoordinates) =
        explicitFormulaRectangleTopEdgeCoordinatesOfFixedX xpair ypairs
  | [], homit => rfl
  | ypair :: rest, homit =>
      congrArg
        (fun edges : List ExplicitFormulaRectangleHorizontalEndpointDataEdge =>
          ((xpair.x₀, xpair.x₁), ypair.y₁) :: edges)
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells_fixedX_topEdges
          xpair rest
          (fun ypair' hy' =>
            homit ypair' (List.mem_cons_of_mem ypair hy')))

/-- The endpoint-data list for one fixed horizontal row has the expected left edge
coordinate list. -/
theorem explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells_fixedX_leftEdges
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    ∀ (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))
      (homit :
        ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε,
          ypair ∈ ypairs →
            ∀ a : ℂ,
              a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a.re ∉ [[xpair.x₀, xpair.x₁]] ∨
                  a.im ∉ [[ypair.y₀, ypair.y₁]]),
      (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
          xpair ypairs homit)).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.leftEdgeCoordinates) =
        explicitFormulaRectangleLeftEdgeCoordinatesOfFixedX xpair ypairs
  | [], homit => rfl
  | ypair :: rest, homit =>
      congrArg
        (fun edges : List ExplicitFormulaRectangleVerticalEndpointDataEdge =>
          ((ypair.y₀, ypair.y₁), xpair.x₀) :: edges)
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells_fixedX_leftEdges
          xpair rest
          (fun ypair' hy' =>
            homit ypair' (List.mem_cons_of_mem ypair hy')))

/-- The endpoint-data list for one fixed horizontal row has the expected right edge
coordinate list. -/
theorem explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells_fixedX_rightEdges
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε) :
    ∀ (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))
      (homit :
        ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε,
          ypair ∈ ypairs →
            ∀ a : ℂ,
              a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                a.re ∉ [[xpair.x₀, xpair.x₁]] ∨
                  a.im ∉ [[ypair.y₀, ypair.y₁]]),
      (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells
        (explicitFormulaRectangleRegularAdjacentEndpointPairCellsOfFixedX
          xpair ypairs homit)).map
          (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
            d.rightEdgeCoordinates) =
        explicitFormulaRectangleRightEdgeCoordinatesOfFixedX xpair ypairs
  | [], homit => rfl
  | ypair :: rest, homit =>
      congrArg
        (fun edges : List ExplicitFormulaRectangleVerticalEndpointDataEdge =>
          ((ypair.y₀, ypair.y₁), xpair.x₁) :: edges)
        (explicitFormulaRectangleEndpointDataListOfRegularAdjacentEndpointPairCells_fixedX_rightEdges
          xpair rest
          (fun ypair' hy' =>
            homit ypair' (List.mem_cons_of_mem ypair hy')))

/-- A cell whose lower vertical endpoint is the bottom outer rectangle side contributes a
bottom edge on the outer boundary. -/
theorem ExplicitFormulaRectangleRegularGridCellEndpointData.bottomEdgeCoordinates_eq_outerBottom
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)
    (hy : d.y₀ = -T) :
    d.bottomEdgeCoordinates = ((d.x₀, d.x₁), -T) := by
  exact congrArg (fun y : ℝ => ((d.x₀, d.x₁), y)) hy

/-- A cell whose upper vertical endpoint is the top outer rectangle side contributes a
top edge on the outer boundary. -/
theorem ExplicitFormulaRectangleRegularGridCellEndpointData.topEdgeCoordinates_eq_outerTop
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)
    (hy : d.y₁ = T) :
    d.topEdgeCoordinates = ((d.x₀, d.x₁), T) := by
  exact congrArg (fun y : ℝ => ((d.x₀, d.x₁), y)) hy

/-- A cell whose lower horizontal endpoint is the left outer rectangle side contributes a
left edge on the outer boundary. -/
theorem ExplicitFormulaRectangleRegularGridCellEndpointData.leftEdgeCoordinates_eq_outerLeft
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)
    (hx : d.x₀ = F.c) :
    d.leftEdgeCoordinates = ((d.y₀, d.y₁), F.c) := by
  exact congrArg (fun x : ℝ => ((d.y₀, d.y₁), x)) hx

/-- A cell whose upper horizontal endpoint is the right outer rectangle side contributes a
right edge on the outer boundary. -/
theorem ExplicitFormulaRectangleRegularGridCellEndpointData.rightEdgeCoordinates_eq_outerRight
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)
    (hx : d.x₁ = 1 - F.c) :
    d.rightEdgeCoordinates = ((d.y₀, d.y₁), 1 - F.c) := by
  exact congrArg (fun x : ℝ => ((d.y₀, d.y₁), x)) hx

/-- A cell whose lower horizontal endpoint is an inscribed-square left side contributes a
left edge on that hole boundary. -/
theorem ExplicitFormulaRectangleRegularGridCellEndpointData.leftEdgeCoordinates_eq_holeLeft
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)
    {a : ℂ}
    (hx : d.x₀ = (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).re) :
    d.leftEdgeCoordinates =
      ((d.y₀, d.y₁), (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).re) := by
  exact congrArg (fun x : ℝ => ((d.y₀, d.y₁), x)) hx

/-- A cell whose upper horizontal endpoint is an inscribed-square right side contributes
a right edge on that hole boundary. -/
theorem ExplicitFormulaRectangleRegularGridCellEndpointData.rightEdgeCoordinates_eq_holeRight
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)
    {a : ℂ}
    (hx : d.x₁ = (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).re) :
    d.rightEdgeCoordinates =
      ((d.y₀, d.y₁), (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).re) := by
  exact congrArg (fun x : ℝ => ((d.y₀, d.y₁), x)) hx

/-- A cell whose lower vertical endpoint is an inscribed-square bottom side contributes a
bottom edge on that hole boundary. -/
theorem ExplicitFormulaRectangleRegularGridCellEndpointData.bottomEdgeCoordinates_eq_holeBottom
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)
    {a : ℂ}
    (hy : d.y₀ = (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).im) :
    d.bottomEdgeCoordinates =
      ((d.x₀, d.x₁), (explicitFormulaRectangleRawInscribedSquareLowerCorner ε a).im) := by
  exact congrArg (fun y : ℝ => ((d.x₀, d.x₁), y)) hy

/-- A cell whose upper vertical endpoint is an inscribed-square top side contributes a top
edge on that hole boundary. -/
theorem ExplicitFormulaRectangleRegularGridCellEndpointData.topEdgeCoordinates_eq_holeTop
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)
    {a : ℂ}
    (hy : d.y₁ = (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).im) :
    d.topEdgeCoordinates =
      ((d.x₀, d.x₁), (explicitFormulaRectangleRawInscribedSquareUpperCorner ε a).im) := by
  exact congrArg (fun y : ℝ => ((d.x₀, d.x₁), y)) hy

/-- The endpoint-data list constructed from an empty horizontal adjacent-pair list is
empty. -/
theorem explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists_nil
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (ypairs : List (ExplicitFormulaRectangleYAdjacentEndpointPair T ε))
    (homit :
      ∀ xpair : ExplicitFormulaRectangleXAdjacentEndpointPair F T ε,
        xpair ∈
          ([] : List (ExplicitFormulaRectangleXAdjacentEndpointPair F T ε)) →
          ∀ ypair : ExplicitFormulaRectangleYAdjacentEndpointPair T ε,
            ypair ∈ ypairs →
              ∀ a : ℂ,
                a ∈ explicitFormulaRectangleRawSingularCoordinates T →
                  a.re ∉ [[xpair.x₀, xpair.x₁]] ∨
                    a.im ∉ [[ypair.y₀, ypair.y₁]]) :
    explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists
      [] ypairs homit = [] := by
  rfl

/-- The endpoint-data list constructed from a cons horizontal adjacent-pair list is the
endpoint-data list for the first horizontal row appended to the recursive endpoint-data
list for the remaining rows. -/
theorem explicitFormulaRectangleEndpointDataListOfAdjacentEndpointPairLists_cons
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
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
            homit xpair' (List.mem_cons_of_mem xpair hx') ypair hy) := by
  rfl

/-- Convert one proof-carrying adjacent endpoint datum into the corresponding regular
grid cell. -/
def ExplicitFormulaRectangleRegularGridCellEndpointData.toRegularGridCell
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε) :
    ExplicitFormulaRectangleRegularGridCell F T ε :=
  explicitFormulaRectangleRegularGridCellOfAdjacentEndpoints
    F T ε d.x₀ d.x₁ d.y₀ d.y₁ d.hx₀ d.hx₁ d.hy₀ d.hy₁
    d.hx_order d.hy_order d.hx_adj d.hy_adj d.homit

/-- Convert a finite list of proof-carrying adjacent endpoint data into the corresponding
finite list of regular grid cells, without filtering or choosing witnesses. -/
def explicitFormulaRectangleRegularGridCellListOfEndpointData
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)) :
    List (ExplicitFormulaRectangleRegularGridCell F T ε) :=
  data.map
    (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
      d.toRegularGridCell)

/-- The regular-grid-cell list constructed from endpoint data has the same length as the
input endpoint-data list. -/
theorem explicitFormulaRectangleRegularGridCellListOfEndpointData_length
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε)) :
    (explicitFormulaRectangleRegularGridCellListOfEndpointData data).length =
      data.length :=
  List.length_map
    (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
      d.toRegularGridCell)
    data

/-- The endpoint-data-to-regular-grid-cell map is injective: the regular grid cell
remembers exactly the four endpoint coordinates, and endpoint-data proof fields are
proof-irrelevant. -/
theorem ExplicitFormulaRectangleRegularGridCellEndpointData.toRegularGridCell_injective
    {F : ExplicitFormulaContourFamily} {T ε : ℝ} :
    Function.Injective
      (fun d : ExplicitFormulaRectangleRegularGridCellEndpointData F T ε =>
        d.toRegularGridCell) := by
  intro d e h
  have hcell : d.toRegularGridCell.cell = e.toRegularGridCell.cell :=
    congrArg ExplicitFormulaRectangleRegularGridCell.cell h
  have hx₀ : d.x₀ = e.x₀ :=
    congrArg (fun c : ExplicitFormulaRectangleGridCellIndex => c.1.1) hcell
  have hx₁ : d.x₁ = e.x₁ :=
    congrArg (fun c : ExplicitFormulaRectangleGridCellIndex => c.1.2) hcell
  have hy₀ : d.y₀ = e.y₀ :=
    congrArg (fun c : ExplicitFormulaRectangleGridCellIndex => c.2.1) hcell
  have hy₁ : d.y₁ = e.y₁ :=
    congrArg (fun c : ExplicitFormulaRectangleGridCellIndex => c.2.2) hcell
  exact
    ExplicitFormulaRectangleRegularGridCellEndpointData.ext_endpoints
      d e hx₀ hx₁ hy₀ hy₁

/-- Mapping duplicate-free endpoint data to regular grid cells preserves
duplicate-freeness. -/
theorem explicitFormulaRectangleRegularGridCellListOfEndpointData_nodup
    {F : ExplicitFormulaContourFamily} {T ε : ℝ}
    (data : List (ExplicitFormulaRectangleRegularGridCellEndpointData F T ε))
    (hnodup : data.Nodup) :
    (explicitFormulaRectangleRegularGridCellListOfEndpointData data).Nodup := by
  exact
    hnodup.map
      ExplicitFormulaRectangleRegularGridCellEndpointData.toRegularGridCell_injective

/-- The regular-grid-cell list associated to the selected endpoint data is
duplicate-free in the multiset form consumed by the complement-subdivision bridge. -/
theorem explicitFormulaRectangleSelectedEndpointData_regularGridCellList_nodup
    (F : ExplicitFormulaContourFamily) (T ε : ℝ) :
    (explicitFormulaRectangleRegularGridCellListOfEndpointData
        (explicitFormulaRectangleSelectedEndpointData F T ε) :
      Multiset (ExplicitFormulaRectangleRegularGridCell F T ε)).Nodup := by
  exact
    explicitFormulaRectangleRegularGridCellListOfEndpointData_nodup
      (explicitFormulaRectangleSelectedEndpointData F T ε)
      (explicitFormulaRectangleSelectedEndpointData_nodup F T ε)

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
