import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.FiniteRectangleResidues.OwnerParts.Part10

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

/-- Cons-step algebra for endpoint-data boundary decompositions: adding one cell's four
edge contributions to already grouped edge sums gives the grouped edge sums for the
extended list. -/
theorem finiteRectangleSubdivisionEndpointBoundary_consEdgeAlgebra
    (bottom top right left bottomSum topSum rightSum leftSum : ℂ) :
    (bottom - top + (right - left)) +
        (bottomSum - topSum + (rightSum - leftSum)) =
      (bottom + bottomSum) - (top + topSum) +
        ((right + rightSum) - (left + leftSum)) := by
  have hgroup :
      (bottom - top + (right - left)) +
          (bottomSum - topSum + (rightSum - leftSum)) =
        ((bottom - top) + (bottomSum - topSum)) +
          ((right - left) + (rightSum - leftSum)) := by
    calc
      (bottom - top + (right - left)) +
          (bottomSum - topSum + (rightSum - leftSum)) =
          ((bottom - top) + (right - left)) +
            ((bottomSum - topSum) + (rightSum - leftSum)) := by
        rfl
      _ =
          ((bottom - top) + (bottomSum - topSum)) +
            ((right - left) + (rightSum - leftSum)) := by
        exact
          finiteRectangleSubdivision_add_two_add_two_group_pairs
            (bottom - top) (bottomSum - topSum)
            (right - left) (rightSum - leftSum)
  have hbottom_top :
      (bottom - top) + (bottomSum - topSum) =
        (bottom + bottomSum) - (top + topSum) := by
    calc
      (bottom - top) + (bottomSum - topSum) =
          (bottom + -top) + (bottomSum + -topSum) := by
        exact congrArg₂ Add.add
          (sub_eq_add_neg bottom top)
          (sub_eq_add_neg bottomSum topSum)
      _ = (bottom + bottomSum) + (-top + -topSum) := by
        exact
          finiteRectangleSubdivision_add_two_add_two_group_pairs
            bottom bottomSum (-top) (-topSum)
      _ = (bottom + bottomSum) + (-(top + topSum)) := by
        exact congrArg
          (fun z : ℂ => (bottom + bottomSum) + z)
          (neg_add top topSum).symm
      _ = (bottom + bottomSum) - (top + topSum) := by
        exact (sub_eq_add_neg (bottom + bottomSum) (top + topSum)).symm
  have hright_left :
      (right - left) + (rightSum - leftSum) =
        (right + rightSum) - (left + leftSum) := by
    calc
      (right - left) + (rightSum - leftSum) =
          (right + -left) + (rightSum + -leftSum) := by
        exact congrArg₂ Add.add
          (sub_eq_add_neg right left)
          (sub_eq_add_neg rightSum leftSum)
      _ = (right + rightSum) + (-left + -leftSum) := by
        exact
          finiteRectangleSubdivision_add_two_add_two_group_pairs
            right rightSum (-left) (-leftSum)
      _ = (right + rightSum) + (-(left + leftSum)) := by
        exact congrArg
          (fun z : ℂ => (right + rightSum) + z)
          (neg_add left leftSum).symm
      _ = (right + rightSum) - (left + leftSum) := by
        exact (sub_eq_add_neg (right + rightSum) (left + leftSum)).symm
  calc
    (bottom - top + (right - left)) +
        (bottomSum - topSum + (rightSum - leftSum)) =
        ((bottom - top) + (bottomSum - topSum)) +
          ((right - left) + (rightSum - leftSum)) := by
      exact hgroup
    _ =
        ((bottom + bottomSum) - (top + topSum)) +
          ((right - left) + (rightSum - leftSum)) := by
      exact congrArg
        (fun z : ℂ => z + ((right - left) + (rightSum - leftSum)))
        hbottom_top
    _ =
        ((bottom + bottomSum) - (top + topSum)) +
          ((right + rightSum) - (left + leftSum)) := by
      exact congrArg
        (fun z : ℂ => ((bottom + bottomSum) - (top + topSum)) + z)
        hright_left
    _ =
      (bottom + bottomSum) - (top + topSum) +
        ((right + rightSum) - (left + leftSum)) := by
      rfl

/-- Finite telescoping of consecutive horizontal edge differences. -/
theorem finiteRectangleSubdivisionHorizontalEdgeDifferences_sum_range
    (edge : ℕ → ℂ)
    (n : ℕ) :
    (∑ k in Finset.range n, (edge k - edge (k + 1))) =
      edge 0 - edge n := by
  induction n with
  | zero =>
      calc
        (∑ k in Finset.range 0, (edge k - edge (k + 1))) = 0 := by
          rfl
        _ = edge 0 - edge 0 := by
          exact (sub_self (edge 0)).symm
  | succ n ih =>
      have hrange :
          (∑ k in Finset.range (n + 1), (edge k - edge (k + 1))) =
            (∑ k in Finset.range n, (edge k - edge (k + 1))) +
              (edge n - edge (n + 1)) :=
        Finset.sum_range_succ
          (fun k : ℕ => edge k - edge (k + 1))
          n
      calc
        (∑ k in Finset.range (n + 1), (edge k - edge (k + 1))) =
            (∑ k in Finset.range n, (edge k - edge (k + 1))) +
              (edge n - edge (n + 1)) :=
          hrange
        _ = (edge 0 - edge n) + (edge n - edge (n + 1)) := by
          exact congrArg
            (fun z : ℂ => z + (edge n - edge (n + 1)))
            ih
        _ = edge 0 - edge (n + 1) := by
          exact finiteRectangleSubdivisionSharedHorizontalEdges_cancel
            (edge 0) (edge n) (edge (n + 1))

/-- Finite telescoping of consecutive vertical edge differences with the tangent factor. -/
theorem finiteRectangleSubdivisionVerticalEdgeDifferences_sum_range
    (edge : ℕ → ℂ)
    (n : ℕ) :
    (∑ k in Finset.range n,
        (Complex.I • edge (k + 1) - Complex.I • edge k)) =
      Complex.I • edge n - Complex.I • edge 0 := by
  induction n with
  | zero =>
      calc
        (∑ k in Finset.range 0,
            (Complex.I • edge (k + 1) - Complex.I • edge k)) = 0 := by
          rfl
        _ = Complex.I • edge 0 - Complex.I • edge 0 := by
          exact (sub_self (Complex.I • edge 0)).symm
  | succ n ih =>
      have hrange :
          (∑ k in Finset.range (n + 1),
              (Complex.I • edge (k + 1) - Complex.I • edge k)) =
            (∑ k in Finset.range n,
              (Complex.I • edge (k + 1) - Complex.I • edge k)) +
              (Complex.I • edge (n + 1) - Complex.I • edge n) :=
        Finset.sum_range_succ
          (fun k : ℕ => Complex.I • edge (k + 1) - Complex.I • edge k)
          n
      calc
        (∑ k in Finset.range (n + 1),
            (Complex.I • edge (k + 1) - Complex.I • edge k)) =
            (∑ k in Finset.range n,
              (Complex.I • edge (k + 1) - Complex.I • edge k)) +
              (Complex.I • edge (n + 1) - Complex.I • edge n) :=
          hrange
        _ =
            (Complex.I • edge n - Complex.I • edge 0) +
              (Complex.I • edge (n + 1) - Complex.I • edge n) := by
          exact congrArg
            (fun z : ℂ => z + (Complex.I • edge (n + 1) - Complex.I • edge n))
            ih
        _ = Complex.I • edge (n + 1) - Complex.I • edge 0 := by
          exact finiteRectangleSubdivisionSharedVerticalEdges_cancel
            (edge 0) (edge n) (edge (n + 1))

/-- Boundary algebra for a finite horizontal row of cells.

Each cell contributes a bottom edge, a top edge, and the vertical difference between
consecutive grid lines.  Summing across the row cancels all internal vertical edges and
leaves only the rightmost minus leftmost vertical side. -/
theorem finiteRectangleSubdivisionRowBoundary_sum_range
    (bottom top vertical : ℕ → ℂ)
    (n : ℕ) :
    (∑ k in Finset.range n,
        (bottom k - top k +
          (Complex.I • vertical (k + 1) - Complex.I • vertical k))) =
      (∑ k in Finset.range n, bottom k) -
        (∑ k in Finset.range n, top k) +
          (Complex.I • vertical n - Complex.I • vertical 0) := by
  let B : ℂ := ∑ k in Finset.range n, bottom k
  let U : ℂ := ∑ k in Finset.range n, top k
  let V : ℂ :=
    ∑ k in Finset.range n,
      (Complex.I • vertical (k + 1) - Complex.I • vertical k)
  have hsplit :
      (∑ k in Finset.range n,
          (bottom k - top k +
            (Complex.I • vertical (k + 1) - Complex.I • vertical k))) =
        (∑ k in Finset.range n, (bottom k - top k)) + V := by
    exact
      Finset.sum_add_distrib
        (s := Finset.range n)
        (f := fun k : ℕ => bottom k - top k)
        (g := fun k : ℕ =>
          Complex.I • vertical (k + 1) - Complex.I • vertical k)
  have hbottom_top :
      (∑ k in Finset.range n, (bottom k - top k)) = B - U := by
    calc
      (∑ k in Finset.range n, (bottom k - top k)) =
          (∑ k in Finset.range n, (bottom k + -top k)) := by
        exact Finset.sum_congr rfl
          (fun k _hk => sub_eq_add_neg (bottom k) (top k))
      _ =
          (∑ k in Finset.range n, bottom k) +
            (∑ k in Finset.range n, -top k) := by
        exact Finset.sum_add_distrib
          (s := Finset.range n)
          (f := bottom)
          (g := fun k : ℕ => -top k)
      _ =
          (∑ k in Finset.range n, bottom k) +
            -(∑ k in Finset.range n, top k) := by
        exact congrArg
          (fun z : ℂ => (∑ k in Finset.range n, bottom k) + z)
          (Finset.sum_neg_distrib)
      _ = B - U := by
        exact (sub_eq_add_neg B U).symm
  have hvertical :
      V = Complex.I • vertical n - Complex.I • vertical 0 :=
    finiteRectangleSubdivisionVerticalEdgeDifferences_sum_range vertical n
  calc
    (∑ k in Finset.range n,
        (bottom k - top k +
          (Complex.I • vertical (k + 1) - Complex.I • vertical k))) =
        (∑ k in Finset.range n, (bottom k - top k)) + V :=
      hsplit
    _ = (B - U) + V := by
      exact congrArg (fun z : ℂ => z + V) hbottom_top
    _ = (B - U) + (Complex.I • vertical n - Complex.I • vertical 0) := by
      exact congrArg (fun z : ℂ => (B - U) + z) hvertical
    _ =
        (∑ k in Finset.range n, bottom k) -
          (∑ k in Finset.range n, top k) +
            (Complex.I • vertical n - Complex.I • vertical 0) := rfl

/-- Boundary algebra for a finite vertical column of cells.

Each cell contributes the horizontal difference between consecutive grid lines plus its
right and left side contributions.  Summing up the column cancels all internal horizontal
edges and leaves only the bottom-minus-top contribution, with side sums grouped. -/
theorem finiteRectangleSubdivisionColumnBoundary_sum_range
    (horizontal right left : ℕ → ℂ)
    (n : ℕ) :
    (∑ k in Finset.range n,
        (horizontal k - horizontal (k + 1) + right k - left k)) =
      horizontal 0 - horizontal n +
        (∑ k in Finset.range n, right k) -
          (∑ k in Finset.range n, left k) := by
  let H : ℂ :=
    ∑ k in Finset.range n, (horizontal k - horizontal (k + 1))
  let R : ℂ := ∑ k in Finset.range n, right k
  let L : ℂ := ∑ k in Finset.range n, left k
  have hsplit :
      (∑ k in Finset.range n,
          (horizontal k - horizontal (k + 1) + right k - left k)) =
        H + (∑ k in Finset.range n, (right k - left k)) := by
    exact
      Finset.sum_add_distrib
        (s := Finset.range n)
        (f := fun k : ℕ => horizontal k - horizontal (k + 1))
        (g := fun k : ℕ => right k - left k)
  have hright_left :
      (∑ k in Finset.range n, (right k - left k)) = R - L := by
    calc
      (∑ k in Finset.range n, (right k - left k)) =
          (∑ k in Finset.range n, (right k + -left k)) := by
        exact Finset.sum_congr rfl
          (fun k _hk => sub_eq_add_neg (right k) (left k))
      _ =
          (∑ k in Finset.range n, right k) +
            (∑ k in Finset.range n, -left k) := by
        exact Finset.sum_add_distrib
          (s := Finset.range n)
          (f := right)
          (g := fun k : ℕ => -left k)
      _ =
          (∑ k in Finset.range n, right k) +
            -(∑ k in Finset.range n, left k) := by
        exact congrArg
          (fun z : ℂ => (∑ k in Finset.range n, right k) + z)
          (Finset.sum_neg_distrib)
      _ = R - L := by
        exact (sub_eq_add_neg R L).symm
  have hhorizontal :
      H = horizontal 0 - horizontal n :=
    finiteRectangleSubdivisionHorizontalEdgeDifferences_sum_range horizontal n
  calc
    (∑ k in Finset.range n,
        (horizontal k - horizontal (k + 1) + right k - left k)) =
        H + (∑ k in Finset.range n, (right k - left k)) :=
      hsplit
    _ = H + (R - L) := by
      exact congrArg (fun z : ℂ => H + z) hright_left
    _ = (horizontal 0 - horizontal n) + (R - L) := by
      exact congrArg (fun z : ℂ => z + (R - L)) hhorizontal
    _ =
        horizontal 0 - horizontal n +
          (∑ k in Finset.range n, right k) -
            (∑ k in Finset.range n, left k) := by
      exact
        (sub_eq_add_neg
          (horizontal 0 - horizontal n + R)
          L).symm

/-- A finite horizontal row of cell boundaries collapses to one row boundary once the
bottom and top edge sums have already been split into the corresponding outer edges. -/
theorem finiteRectangleSubdivisionRowBoundary_sum_range_of_edge_splits
    (bottom top vertical : ℕ → ℂ)
    (n : ℕ)
    (bottomOuter topOuter : ℂ)
    (hbottom : (∑ k in Finset.range n, bottom k) = bottomOuter)
    (htop : (∑ k in Finset.range n, top k) = topOuter) :
    (∑ k in Finset.range n,
        (bottom k - top k +
          (Complex.I • vertical (k + 1) - Complex.I • vertical k))) =
      bottomOuter - topOuter +
        (Complex.I • vertical n - Complex.I • vertical 0) := by
  calc
    (∑ k in Finset.range n,
        (bottom k - top k +
          (Complex.I • vertical (k + 1) - Complex.I • vertical k))) =
      (∑ k in Finset.range n, bottom k) -
        (∑ k in Finset.range n, top k) +
          (Complex.I • vertical n - Complex.I • vertical 0) := by
      exact finiteRectangleSubdivisionRowBoundary_sum_range bottom top vertical n
    _ =
      bottomOuter -
        (∑ k in Finset.range n, top k) +
          (Complex.I • vertical n - Complex.I • vertical 0) := by
      exact congrArg
        (fun z : ℂ =>
          z - (∑ k in Finset.range n, top k) +
            (Complex.I • vertical n - Complex.I • vertical 0))
        hbottom
    _ =
      bottomOuter - topOuter +
        (Complex.I • vertical n - Complex.I • vertical 0) := by
      exact congrArg
        (fun z : ℂ =>
          bottomOuter - z +
            (Complex.I • vertical n - Complex.I • vertical 0))
        htop

/-- A finite vertical column of cell boundaries collapses to one column boundary once the
right and left edge sums have already been split into the corresponding outer side
integrals. -/
theorem finiteRectangleSubdivisionColumnBoundary_sum_range_of_edge_splits
    (horizontal right left : ℕ → ℂ)
    (n : ℕ)
    (rightOuter leftOuter : ℂ)
    (hright : (∑ k in Finset.range n, right k) = rightOuter)
    (hleft : (∑ k in Finset.range n, left k) = leftOuter) :
    (∑ k in Finset.range n,
        (horizontal k - horizontal (k + 1) + right k - left k)) =
      horizontal 0 - horizontal n + rightOuter - leftOuter := by
  calc
    (∑ k in Finset.range n,
        (horizontal k - horizontal (k + 1) + right k - left k)) =
      horizontal 0 - horizontal n +
        (∑ k in Finset.range n, right k) -
          (∑ k in Finset.range n, left k) := by
      exact finiteRectangleSubdivisionColumnBoundary_sum_range horizontal right left n
    _ =
      horizontal 0 - horizontal n + rightOuter -
          (∑ k in Finset.range n, left k) := by
      exact congrArg
        (fun z : ℂ =>
          horizontal 0 - horizontal n + z -
            (∑ k in Finset.range n, left k))
        hright
    _ =
      horizontal 0 - horizontal n + rightOuter - leftOuter := by
      exact congrArg
        (fun z : ℂ => horizontal 0 - horizontal n + rightOuter - z)
        hleft

/-- A finite grid assembled row-by-row collapses each row to its outer horizontal
edge sums and its two vertical endpoint sides. -/
theorem finiteRectangleSubdivisionGridRowsBoundary_sum_range_of_edge_splits
    (bottom top vertical : ℕ → ℕ → ℂ)
    (rows cols : ℕ)
    (bottomOuter topOuter : ℕ → ℂ)
    (hbottom :
      ∀ j : ℕ, j ∈ Finset.range rows →
        (∑ k in Finset.range cols, bottom j k) = bottomOuter j)
    (htop :
      ∀ j : ℕ, j ∈ Finset.range rows →
        (∑ k in Finset.range cols, top j k) = topOuter j) :
    (∑ j in Finset.range rows,
      ∑ k in Finset.range cols,
        (bottom j k - top j k +
          (Complex.I • vertical j (k + 1) - Complex.I • vertical j k))) =
      ∑ j in Finset.range rows,
        (bottomOuter j - topOuter j +
          (Complex.I • vertical j cols - Complex.I • vertical j 0)) := by
  exact Finset.sum_congr rfl
    (fun j hj =>
      finiteRectangleSubdivisionRowBoundary_sum_range_of_edge_splits
        (bottom j) (top j) (vertical j) cols
        (bottomOuter j) (topOuter j)
        (hbottom j hj) (htop j hj))

/-- A finite grid assembled column-by-column collapses each column to its outer
vertical side sums and its two horizontal endpoint edges. -/
theorem finiteRectangleSubdivisionGridColumnsBoundary_sum_range_of_edge_splits
    (horizontal right left : ℕ → ℕ → ℂ)
    (cols rows : ℕ)
    (rightOuter leftOuter : ℕ → ℂ)
    (hright :
      ∀ i : ℕ, i ∈ Finset.range cols →
        (∑ k in Finset.range rows, right i k) = rightOuter i)
    (hleft :
      ∀ i : ℕ, i ∈ Finset.range cols →
        (∑ k in Finset.range rows, left i k) = leftOuter i) :
    (∑ i in Finset.range cols,
      ∑ k in Finset.range rows,
        (horizontal i k - horizontal i (k + 1) + right i k - left i k)) =
      ∑ i in Finset.range cols,
        (horizontal i 0 - horizontal i rows + rightOuter i - leftOuter i) := by
  exact Finset.sum_congr rfl
    (fun i hi =>
      finiteRectangleSubdivisionColumnBoundary_sum_range_of_edge_splits
        (horizontal i) (right i) (left i) rows
        (rightOuter i) (leftOuter i)
        (hright i hi) (hleft i hi))

/-- Summing collapsed row boundaries groups the outer horizontal sums and the two
vertical side sums.  This is the row-wise endpoint algebra used after all internal
vertical grid edges have cancelled. -/
theorem finiteRectangleSubdivisionCollapsedRowsBoundary_sum_range
    (bottom top right left : ℕ → ℂ)
    (rows : ℕ) :
    (∑ j in Finset.range rows,
        (bottom j - top j + (Complex.I • right j - Complex.I • left j))) =
      (∑ j in Finset.range rows, bottom j) -
        (∑ j in Finset.range rows, top j) +
          ((∑ j in Finset.range rows, Complex.I • right j) -
            (∑ j in Finset.range rows, Complex.I • left j)) := by
  let B : ℂ := ∑ j in Finset.range rows, bottom j
  let U : ℂ := ∑ j in Finset.range rows, top j
  let R : ℂ := ∑ j in Finset.range rows, Complex.I • right j
  let L : ℂ := ∑ j in Finset.range rows, Complex.I • left j
  have hsplit :
      (∑ j in Finset.range rows,
          (bottom j - top j + (Complex.I • right j - Complex.I • left j))) =
        (∑ j in Finset.range rows, (bottom j - top j)) +
          (∑ j in Finset.range rows,
            (Complex.I • right j - Complex.I • left j)) := by
    exact
      Finset.sum_add_distrib
        (s := Finset.range rows)
        (f := fun j : ℕ => bottom j - top j)
        (g := fun j : ℕ => Complex.I • right j - Complex.I • left j)
  have hbottom_top :
      (∑ j in Finset.range rows, (bottom j - top j)) = B - U := by
    calc
      (∑ j in Finset.range rows, (bottom j - top j)) =
          (∑ j in Finset.range rows, (bottom j + -top j)) := by
        exact Finset.sum_congr rfl
          (fun j _hj => sub_eq_add_neg (bottom j) (top j))
      _ =
          (∑ j in Finset.range rows, bottom j) +
            (∑ j in Finset.range rows, -top j) := by
        exact Finset.sum_add_distrib
          (s := Finset.range rows)
          (f := bottom)
          (g := fun j : ℕ => -top j)
      _ =
          (∑ j in Finset.range rows, bottom j) +
            -(∑ j in Finset.range rows, top j) := by
        exact congrArg
          (fun z : ℂ => (∑ j in Finset.range rows, bottom j) + z)
          (Finset.sum_neg_distrib)
      _ = B - U := by
        exact (sub_eq_add_neg B U).symm
  have hright_left :
      (∑ j in Finset.range rows,
        (Complex.I • right j - Complex.I • left j)) = R - L := by
    calc
      (∑ j in Finset.range rows,
          (Complex.I • right j - Complex.I • left j)) =
          (∑ j in Finset.range rows,
            (Complex.I • right j + -(Complex.I • left j))) := by
        exact Finset.sum_congr rfl
          (fun j _hj => sub_eq_add_neg (Complex.I • right j) (Complex.I • left j))
      _ =
          (∑ j in Finset.range rows, Complex.I • right j) +
            (∑ j in Finset.range rows, -(Complex.I • left j)) := by
        exact Finset.sum_add_distrib
          (s := Finset.range rows)
          (f := fun j : ℕ => Complex.I • right j)
          (g := fun j : ℕ => -(Complex.I • left j))
      _ =
          (∑ j in Finset.range rows, Complex.I • right j) +
            -(∑ j in Finset.range rows, Complex.I • left j) := by
        exact congrArg
          (fun z : ℂ => (∑ j in Finset.range rows, Complex.I • right j) + z)
          (Finset.sum_neg_distrib)
      _ = R - L := by
        exact (sub_eq_add_neg R L).symm
  calc
    (∑ j in Finset.range rows,
        (bottom j - top j + (Complex.I • right j - Complex.I • left j))) =
        (∑ j in Finset.range rows, (bottom j - top j)) +
          (∑ j in Finset.range rows,
            (Complex.I • right j - Complex.I • left j)) := by
      exact hsplit
    _ = (B - U) +
          (∑ j in Finset.range rows,
            (Complex.I • right j - Complex.I • left j)) := by
      exact congrArg
        (fun z : ℂ =>
          z + (∑ j in Finset.range rows,
            (Complex.I • right j - Complex.I • left j)))
        hbottom_top
    _ = (B - U) + (R - L) := by
      exact congrArg (fun z : ℂ => (B - U) + z) hright_left
    _ =
      (∑ j in Finset.range rows, bottom j) -
        (∑ j in Finset.range rows, top j) +
          ((∑ j in Finset.range rows, Complex.I • right j) -
            (∑ j in Finset.range rows, Complex.I • left j)) := by
      rfl

/-- Collapsed row boundaries with all four edge families already identified with their
outer edge integrals. -/
theorem finiteRectangleSubdivisionCollapsedRowsBoundary_sum_range_of_edge_splits
    (bottom top right left : ℕ → ℂ)
    (rows : ℕ)
    (bottomOuter topOuter rightOuter leftOuter : ℂ)
    (hbottom : (∑ j in Finset.range rows, bottom j) = bottomOuter)
    (htop : (∑ j in Finset.range rows, top j) = topOuter)
    (hright : (∑ j in Finset.range rows, right j) = rightOuter)
    (hleft : (∑ j in Finset.range rows, left j) = leftOuter) :
    (∑ j in Finset.range rows,
        (bottom j - top j + (Complex.I • right j - Complex.I • left j))) =
      bottomOuter - topOuter + (Complex.I • rightOuter - Complex.I • leftOuter) := by
  have hrow :
      (∑ j in Finset.range rows,
          (bottom j - top j + (Complex.I • right j - Complex.I • left j))) =
        (∑ j in Finset.range rows, bottom j) -
          (∑ j in Finset.range rows, top j) +
            ((∑ j in Finset.range rows, Complex.I • right j) -
              (∑ j in Finset.range rows, Complex.I • left j)) :=
    finiteRectangleSubdivisionCollapsedRowsBoundary_sum_range
      bottom top right left rows
  have hright_smul :
      (∑ j in Finset.range rows, Complex.I • right j) = Complex.I • rightOuter := by
    calc
      (∑ j in Finset.range rows, Complex.I • right j) =
          Complex.I • (∑ j in Finset.range rows, right j) := by
        exact
          (Finset.smul_sum
            (s := Finset.range rows)
            (f := right)
            (r := Complex.I)).symm
      _ = Complex.I • rightOuter := by
        exact congrArg (fun z : ℂ => Complex.I • z) hright
  have hleft_smul :
      (∑ j in Finset.range rows, Complex.I • left j) = Complex.I • leftOuter := by
    calc
      (∑ j in Finset.range rows, Complex.I • left j) =
          Complex.I • (∑ j in Finset.range rows, left j) := by
        exact
          (Finset.smul_sum
            (s := Finset.range rows)
            (f := left)
            (r := Complex.I)).symm
      _ = Complex.I • leftOuter := by
        exact congrArg (fun z : ℂ => Complex.I • z) hleft
  calc
    (∑ j in Finset.range rows,
        (bottom j - top j + (Complex.I • right j - Complex.I • left j))) =
        (∑ j in Finset.range rows, bottom j) -
          (∑ j in Finset.range rows, top j) +
            ((∑ j in Finset.range rows, Complex.I • right j) -
              (∑ j in Finset.range rows, Complex.I • left j)) := by
      exact hrow
    _ =
        bottomOuter -
          (∑ j in Finset.range rows, top j) +
            ((∑ j in Finset.range rows, Complex.I • right j) -
              (∑ j in Finset.range rows, Complex.I • left j)) := by
      exact congrArg
        (fun z : ℂ =>
          z - (∑ j in Finset.range rows, top j) +
            ((∑ j in Finset.range rows, Complex.I • right j) -
              (∑ j in Finset.range rows, Complex.I • left j)))
        hbottom
    _ =
        bottomOuter - topOuter +
            ((∑ j in Finset.range rows, Complex.I • right j) -
              (∑ j in Finset.range rows, Complex.I • left j)) := by
      exact congrArg
        (fun z : ℂ =>
          bottomOuter - z +
            ((∑ j in Finset.range rows, Complex.I • right j) -
              (∑ j in Finset.range rows, Complex.I • left j)))
        htop
    _ =
        bottomOuter - topOuter +
            (Complex.I • rightOuter -
              (∑ j in Finset.range rows, Complex.I • left j)) := by
      exact congrArg
        (fun z : ℂ =>
          bottomOuter - topOuter +
            (z - (∑ j in Finset.range rows, Complex.I • left j)))
        hright_smul
    _ =
        bottomOuter - topOuter +
          (Complex.I • rightOuter - Complex.I • leftOuter) := by
      exact congrArg
        (fun z : ℂ =>
          bottomOuter - topOuter + (Complex.I • rightOuter - z))
        hleft_smul

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
