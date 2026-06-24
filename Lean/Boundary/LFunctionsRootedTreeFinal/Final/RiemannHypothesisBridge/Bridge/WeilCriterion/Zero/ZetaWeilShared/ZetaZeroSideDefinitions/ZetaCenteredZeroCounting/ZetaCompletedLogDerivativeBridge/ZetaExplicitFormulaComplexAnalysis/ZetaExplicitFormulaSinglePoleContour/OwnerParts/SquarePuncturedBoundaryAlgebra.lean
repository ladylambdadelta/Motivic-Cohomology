import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.Zero.ZetaWeilShared.ZetaZeroSideDefinitions.ZetaCenteredZeroCounting.ZetaCompletedLogDerivativeBridge.ZetaExplicitFormulaComplexAnalysis.ZetaExplicitFormulaSinglePoleContour.OwnerParts.Core

/-!
# Additive algebra for the one-pole square-punctured boundary

This file owns the pure additive identities used to assemble the oriented edge
bookkeeping theorem

`outer standard boundary - inner square boundary = four-cell boundary sum`.

The lemmas are stated over a general additive commutative group when possible,
so the contour proof only has to substitute the edge integrals into named
algebraic normal forms.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open Complex
open Filter
open MeasureTheory
open scoped Topology

namespace ZetaAdmissibleFunction

/-- Rebracket two four-edge boundary expressions grouped as
bottom-minus-top plus right-minus-left. -/
theorem zetaExplicitFormulaOnePole_add_four_edge_groups
    {G : Type*} [AddCommGroup G]
    (bottom top right left bottom' top' right' left' : G) :
    (bottom - top + (right - left)) +
        (bottom' - top' + (right' - left')) =
      (bottom + bottom') - (top + top') +
        ((right + right') - (left + left')) := by
  have hgroup :
      (bottom - top + (right - left)) +
          (bottom' - top' + (right' - left')) =
        ((bottom - top) + (bottom' - top')) +
          ((right - left) + (right' - left')) := by
    calc
      (bottom - top + (right - left)) +
          (bottom' - top' + (right' - left')) =
          ((bottom - top) + (right - left)) +
            ((bottom' - top') + (right' - left')) := by
        rfl
      _ =
          ((bottom - top) + (bottom' - top')) +
            ((right - left) + (right' - left')) := by
        exact
          add_add_add_comm
            (bottom - top) (right - left)
            (bottom' - top') (right' - left')
  have hhorizontal :
      (bottom - top) + (bottom' - top') =
        (bottom + bottom') - (top + top') := by
    calc
      (bottom - top) + (bottom' - top') =
          (bottom + -top) + (bottom' + -top') := by
        exact congrArg₂ Add.add
          (sub_eq_add_neg bottom top)
          (sub_eq_add_neg bottom' top')
      _ = (bottom + bottom') + (-top + -top') := by
        exact add_add_add_comm bottom (-top) bottom' (-top')
      _ = (bottom + bottom') + (-(top + top')) := by
        exact congrArg
          (fun z : G => (bottom + bottom') + z)
          (neg_add top top').symm
      _ = (bottom + bottom') - (top + top') := by
        exact (sub_eq_add_neg (bottom + bottom') (top + top')).symm
  have hvertical :
      (right - left) + (right' - left') =
        (right + right') - (left + left') := by
    calc
      (right - left) + (right' - left') =
          (right + -left) + (right' + -left') := by
        exact congrArg₂ Add.add
          (sub_eq_add_neg right left)
          (sub_eq_add_neg right' left')
      _ = (right + right') + (-left + -left') := by
        exact add_add_add_comm right (-left) right' (-left')
      _ = (right + right') + (-(left + left')) := by
        exact congrArg
          (fun z : G => (right + right') + z)
          (neg_add left left').symm
      _ = (right + right') - (left + left') := by
        exact (sub_eq_add_neg (right + right') (left + left')).symm
  calc
    (bottom - top + (right - left)) +
        (bottom' - top' + (right' - left')) =
        ((bottom - top) + (bottom' - top')) +
          ((right - left) + (right' - left')) := by
      exact hgroup
    _ =
        ((bottom + bottom') - (top + top')) +
          ((right - left) + (right' - left')) := by
      exact congrArg
        (fun z : G => z + ((right - left) + (right' - left')))
        hhorizontal
    _ =
        ((bottom + bottom') - (top + top')) +
          ((right + right') - (left + left')) := by
      exact congrArg
        (fun z : G => ((bottom + bottom') - (top + top')) + z)
        hvertical
    _ =
      (bottom + bottom') - (top + top') +
        ((right + right') - (left + left')) := by
      rfl

/-- Subtracting an inner four-edge boundary from an outer four-edge boundary
is the same as adding the outer boundary to the negated inner boundary. -/
theorem zetaExplicitFormulaOnePole_outer_sub_inner_four_edges
    {G : Type*} [AddCommGroup G]
    (outerBottom outerTop outerRight outerLeft
      innerBottom innerTop innerRight innerLeft : G) :
    (outerBottom - outerTop + (outerRight - outerLeft)) -
        (innerBottom - innerTop + (innerRight - innerLeft)) =
      (outerBottom - outerTop + (outerRight - outerLeft)) +
        ((-innerBottom) - (-innerTop) +
          ((-innerRight) - (-innerLeft))) := by
  have hneg :
      - (innerBottom - innerTop + (innerRight - innerLeft)) =
        (-innerBottom) - (-innerTop) +
          ((-innerRight) - (-innerLeft)) := by
    calc
      - (innerBottom - innerTop + (innerRight - innerLeft)) =
          -(innerBottom - innerTop) + -(innerRight - innerLeft) := by
        exact neg_add (innerBottom - innerTop) (innerRight - innerLeft)
      _ = (innerTop - innerBottom) + -(innerRight - innerLeft) := by
        exact congrArg
          (fun z : G => z + -(innerRight - innerLeft))
          (neg_sub innerBottom innerTop)
      _ = (innerTop - innerBottom) + (innerLeft - innerRight) := by
        exact congrArg
          (fun z : G => (innerTop - innerBottom) + z)
          (neg_sub innerRight innerLeft)
      _ =
          ((-innerBottom) - (-innerTop)) +
            ((-innerRight) - (-innerLeft)) := by
        have hbottom :
            innerTop - innerBottom = (-innerBottom) - (-innerTop) := by
          calc
            innerTop - innerBottom = innerTop + -innerBottom := by
              exact sub_eq_add_neg innerTop innerBottom
            _ = -innerBottom + innerTop := by
              exact add_comm innerTop (-innerBottom)
            _ = -innerBottom + -(-innerTop) := by
              exact congrArg
                (fun z : G => -innerBottom + z)
                (neg_neg innerTop).symm
            _ = (-innerBottom) - (-innerTop) := by
              exact (sub_eq_add_neg (-innerBottom) (-innerTop)).symm
        have hright :
            innerLeft - innerRight = (-innerRight) - (-innerLeft) := by
          calc
            innerLeft - innerRight = innerLeft + -innerRight := by
              exact sub_eq_add_neg innerLeft innerRight
            _ = -innerRight + innerLeft := by
              exact add_comm innerLeft (-innerRight)
            _ = -innerRight + -(-innerLeft) := by
              exact congrArg
                (fun z : G => -innerRight + z)
                (neg_neg innerLeft).symm
            _ = (-innerRight) - (-innerLeft) := by
              exact (sub_eq_add_neg (-innerRight) (-innerLeft)).symm
        exact congrArg₂ Add.add hbottom hright
  calc
    (outerBottom - outerTop + (outerRight - outerLeft)) -
        (innerBottom - innerTop + (innerRight - innerLeft)) =
        (outerBottom - outerTop + (outerRight - outerLeft)) +
          -(innerBottom - innerTop + (innerRight - innerLeft)) := by
      exact
        sub_eq_add_neg
          (outerBottom - outerTop + (outerRight - outerLeft))
          (innerBottom - innerTop + (innerRight - innerLeft))
    _ =
        (outerBottom - outerTop + (outerRight - outerLeft)) +
          ((-innerBottom) - (-innerTop) +
            ((-innerRight) - (-innerLeft))) := by
      exact congrArg
        (fun z : G =>
          (outerBottom - outerTop + (outerRight - outerLeft)) + z)
        hneg

/-- The negative of an inner four-edge boundary has the orientation that appears
on the exposed boundary of a square-punctured rectangle. -/
theorem zetaExplicitFormulaOnePole_neg_inner_four_edges_exposed
    {G : Type*} [AddCommGroup G]
    (innerBottom innerTop innerRight innerLeft : G) :
    - (innerBottom - innerTop + (innerRight - innerLeft)) =
      -innerBottom + innerTop + (-innerRight + innerLeft) := by
  calc
    - (innerBottom - innerTop + (innerRight - innerLeft)) =
        (-innerBottom) - (-innerTop) +
          ((-innerRight) - (-innerLeft)) := by
      have h :=
        zetaExplicitFormulaOnePole_outer_sub_inner_four_edges
          (0 : G) 0 0 0
          innerBottom innerTop innerRight innerLeft
      have hzero_outer :
          (0 : G) - 0 + (0 - 0) = 0 := by
        calc
          (0 : G) - 0 + (0 - 0) =
              0 + (0 - 0) := by
            exact congrArg (fun z : G => z + (0 - 0)) (sub_zero (0 : G))
          _ = 0 + 0 := by
            exact congrArg (fun z : G => 0 + z) (sub_self (0 : G))
          _ = 0 := by
            exact add_zero (0 : G)
      have hleft :
          (0 : G) -
              (innerBottom - innerTop + (innerRight - innerLeft)) =
            - (innerBottom - innerTop + (innerRight - innerLeft)) := by
        exact zero_sub (innerBottom - innerTop + (innerRight - innerLeft))
      have hright :
          (0 : G) +
              ((-innerBottom) - (-innerTop) +
                ((-innerRight) - (-innerLeft))) =
            (-innerBottom) - (-innerTop) +
              ((-innerRight) - (-innerLeft)) := by
        exact zero_add
          ((-innerBottom) - (-innerTop) +
            ((-innerRight) - (-innerLeft)))
      calc
        - (innerBottom - innerTop + (innerRight - innerLeft)) =
            (0 : G) -
              (innerBottom - innerTop + (innerRight - innerLeft)) := by
          exact hleft.symm
        _ =
            ((0 : G) - 0 + (0 - 0)) +
              ((-innerBottom) - (-innerTop) +
                ((-innerRight) - (-innerLeft))) := by
          exact h
        _ =
            0 +
              ((-innerBottom) - (-innerTop) +
                ((-innerRight) - (-innerLeft))) := by
          exact congrArg
            (fun z : G =>
              z +
                ((-innerBottom) - (-innerTop) +
                  ((-innerRight) - (-innerLeft))))
            hzero_outer
        _ =
            (-innerBottom) - (-innerTop) +
              ((-innerRight) - (-innerLeft)) := by
          exact hright
    _ =
        (-innerBottom + -(-innerTop)) +
          ((-innerRight) + -(-innerLeft)) := by
      exact congrArg₂ Add.add
        (sub_eq_add_neg (-innerBottom) (-innerTop))
        (sub_eq_add_neg (-innerRight) (-innerLeft))
    _ =
        (-innerBottom + innerTop) +
          ((-innerRight) + -(-innerLeft)) := by
      exact congrArg
        (fun z : G => (-innerBottom + z) + ((-innerRight) + -(-innerLeft)))
        (neg_neg innerTop)
    _ =
        (-innerBottom + innerTop) + (-innerRight + innerLeft) := by
      exact congrArg
        (fun z : G => (-innerBottom + innerTop) + (-innerRight + z))
        (neg_neg innerLeft)
    _ = -innerBottom + innerTop + (-innerRight + innerLeft) := by
      rfl

/-- Boundary subtraction algebra in the exact orientation used by the one-pole
punctured rectangle.  The right-hand side groups the exposed outer pieces and
the negatively oriented inner square pieces. -/
theorem zetaExplicitFormulaOnePole_outer_sub_inner_four_edges_grouped
    {G : Type*} [AddCommGroup G]
    (outerBottom outerTop outerRight outerLeft
      innerBottom innerTop innerRight innerLeft : G) :
    (outerBottom - outerTop + (outerRight - outerLeft)) -
        (innerBottom - innerTop + (innerRight - innerLeft)) =
      (outerBottom + -innerBottom) - (outerTop + -innerTop) +
        ((outerRight + -innerRight) - (outerLeft + -innerLeft)) := by
  calc
    (outerBottom - outerTop + (outerRight - outerLeft)) -
        (innerBottom - innerTop + (innerRight - innerLeft)) =
        (outerBottom - outerTop + (outerRight - outerLeft)) +
          ((-innerBottom) - (-innerTop) +
            ((-innerRight) - (-innerLeft))) := by
      exact
        zetaExplicitFormulaOnePole_outer_sub_inner_four_edges
          outerBottom outerTop outerRight outerLeft
          innerBottom innerTop innerRight innerLeft
    _ =
        (outerBottom + -innerBottom) - (outerTop + -innerTop) +
          ((outerRight + -innerRight) - (outerLeft + -innerLeft)) := by
      exact
        zetaExplicitFormulaOnePole_add_four_edge_groups
          outerBottom outerTop outerRight outerLeft
          (-innerBottom) (-innerTop) (-innerRight) (-innerLeft)

/-- A cancellation primitive for moving a negative term next to its positive
mate inside a right-associated sum. -/
theorem zetaExplicitFormulaOnePole_neg_add_cancel_inside_right
    {G : Type*} [AddCommGroup G]
    (a b c : G) :
    a + (-b + (b + c)) = a + c := by
  calc
    a + (-b + (b + c)) =
        a + ((-b + b) + c) := by
      exact congrArg (fun z : G => a + z) (add_assoc (-b) b c).symm
    _ = a + (0 + c) := by
      exact congrArg (fun z : G => a + (z + c)) (neg_add_cancel b)
    _ = a + c := by
      exact congrArg (fun z : G => a + z) (zero_add c)

/-- A cancellation primitive for a positive term followed by its negative inside
a right-associated sum. -/
theorem zetaExplicitFormulaOnePole_add_neg_cancel_inside_right
    {G : Type*} [AddCommGroup G]
    (a b c : G) :
    a + (b + (-b + c)) = a + c := by
  calc
    a + (b + (-b + c)) =
        a + ((b + -b) + c) := by
      exact congrArg (fun z : G => a + z) (add_assoc b (-b) c).symm
    _ = a + (0 + c) := by
      exact congrArg (fun z : G => a + (z + c)) (add_neg_cancel b)
    _ = a + c := by
      exact congrArg (fun z : G => a + z) (zero_add c)

/-- Move the second summand of the left pair next to the first summand of the
right pair and cancel them. -/
theorem zetaExplicitFormulaOnePole_add_pair_neg_left_cancel
    {G : Type*} [AddCommGroup G]
    (a b c : G) :
    (a + b) + (-b + c) = a + c := by
  calc
    (a + b) + (-b + c) =
        a + (b + (-b + c)) := by
      exact add_assoc a b (-b + c)
    _ = a + c := by
      exact zetaExplicitFormulaOnePole_add_neg_cancel_inside_right a b c

/-- Move the negative second summand of the left pair next to the first summand
of the right pair and cancel them. -/
theorem zetaExplicitFormulaOnePole_add_pair_neg_right_cancel
    {G : Type*} [AddCommGroup G]
    (a b c : G) :
    (a + -b) + (b + c) = a + c := by
  calc
    (a + -b) + (b + c) =
        a + (-b + (b + c)) := by
      exact add_assoc a (-b) (b + c)
    _ = a + c := by
      exact zetaExplicitFormulaOnePole_neg_add_cancel_inside_right a b c

/-- Expand a two-term subtraction on the right. -/
theorem zetaExplicitFormulaOnePole_sub_add_pair_eq_sub_sub
    {G : Type*} [AddCommGroup G]
    (a b c : G) :
    a - (b + c) = (a + -b) + -c := by
  calc
    a - (b + c) = a + -(b + c) := by
      exact sub_eq_add_neg a (b + c)
    _ = a + (-b + -c) := by
      exact congrArg (fun z : G => a + z) (neg_add b c)
    _ = (a + -b) + -c := by
      exact (add_assoc a (-b) (-c)).symm

/-- Expand a three-term subtraction on the right, preserving the left-to-right
order of the subtracted terms. -/
theorem zetaExplicitFormulaOnePole_sub_three_eq_sub_sub_sub
    {G : Type*} [AddCommGroup G]
    (a b c d : G) :
    a - ((b + c) + d) = ((a + -b) + -c) + -d := by
  calc
    a - ((b + c) + d) =
        (a + -(b + c)) + -d := by
      exact zetaExplicitFormulaOnePole_sub_add_pair_eq_sub_sub
        a (b + c) d
    _ = (a + (-b + -c)) + -d := by
      exact congrArg (fun z : G => (a + z) + -d) (neg_add b c)
    _ = ((a + -b) + -c) + -d := by
      exact congrArg (fun z : G => z + -d)
        (add_assoc a (-b) (-c)).symm

/-- Expand a three-term sum minus a final term. -/
theorem zetaExplicitFormulaOnePole_three_add_sub_eq_add_add_add_neg
    {G : Type*} [AddCommGroup G]
    (a b c d : G) :
    ((a + b) + c) - d = ((a + b) + c) + -d := by
  exact sub_eq_add_neg ((a + b) + c) d

/-- Swap the last two terms in a left-associated three-term sum. -/
theorem zetaExplicitFormulaOnePole_add_swap_right
    {G : Type*} [AddCommGroup G]
    (a b c : G) :
    (a + b) + c = (a + c) + b := by
  calc
    (a + b) + c = a + (b + c) := by
      exact add_assoc a b c
    _ = a + (c + b) := by
      exact congrArg (fun z : G => a + z) (add_comm b c)
    _ = (a + c) + b := by
      exact (add_assoc a c b).symm

/-- Reorder a four-term sum so that the middle two terms can cancel. -/
theorem zetaExplicitFormulaOnePole_cancel_middle_pair
    {G : Type*} [AddCommGroup G]
    (a b c d : G) :
    ((a + b) + c) + d = (a + d) + (b + c) := by
  calc
    ((a + b) + c) + d = (a + b) + (c + d) := by
      exact add_assoc (a + b) c d
    _ = (a + b) + (d + c) := by
      exact congrArg (fun z : G => (a + b) + z) (add_comm c d)
    _ = ((a + b) + d) + c := by
      exact (add_assoc (a + b) d c).symm
    _ = (a + (b + d)) + c := by
      exact congrArg (fun z : G => z + c) (add_assoc a b d)
    _ = (a + (d + b)) + c := by
      exact congrArg (fun z : G => (a + z) + c) (add_comm b d)
    _ = ((a + d) + b) + c := by
      exact congrArg (fun z : G => z + c) (add_assoc a d b).symm
    _ = (a + d) + (b + c) := by
      exact add_assoc (a + d) b c

/-- Regroup two additive pairs by first and second components. -/
theorem zetaExplicitFormulaOnePole_two_pairs_collect
    {G : Type*} [AddCommGroup G]
    (a b c d : G) :
    (a + b) + (c + d) = (a + c) + (b + d) := by
  exact add_add_add_comm a b c d

/-- Regroup two three-term cells by horizontal, right, and left components. -/
theorem zetaExplicitFormulaOnePole_two_threeTermCells_collect
    {G : Type*} [AddCommGroup G]
    (h₁ r₁ l₁ h₂ r₂ l₂ : G) :
    ((h₁ + r₁) + l₁) + ((h₂ + r₂) + l₂) =
      ((h₁ + h₂) + (r₁ + r₂)) + (l₁ + l₂) := by
  calc
    ((h₁ + r₁) + l₁) + ((h₂ + r₂) + l₂) =
        ((h₁ + r₁) + (h₂ + r₂)) + (l₁ + l₂) := by
      exact add_add_add_comm (h₁ + r₁) l₁ (h₂ + r₂) l₂
    _ = ((h₁ + h₂) + (r₁ + r₂)) + (l₁ + l₂) := by
      exact congrArg
        (fun z : G => z + (l₁ + l₂))
        (zetaExplicitFormulaOnePole_two_pairs_collect h₁ r₁ h₂ r₂)

/-- Cancel a middle positive-negative pair after moving it to the right. -/
theorem zetaExplicitFormulaOnePole_add_add_neg_cancel_middle
    {G : Type*} [AddCommGroup G]
    (a b c : G) :
    ((a + b) + -b) + c = a + c := by
  calc
    ((a + b) + -b) + c = (a + b) + (-b + c) := by
      exact add_assoc (a + b) (-b) c
    _ = a + c := by
      exact zetaExplicitFormulaOnePole_add_pair_neg_left_cancel a b c

/-- Cancel a middle negative-positive pair after moving it to the right. -/
theorem zetaExplicitFormulaOnePole_add_neg_add_cancel_middle
    {G : Type*} [AddCommGroup G]
    (a b c : G) :
    ((a + -b) + b) + c = a + c := by
  calc
    ((a + -b) + b) + c = (a + -b) + (b + c) := by
      exact add_assoc (a + -b) b c
    _ = a + c := by
      exact zetaExplicitFormulaOnePole_add_pair_neg_right_cancel a b c

/-- Cancel a leading split term after first commuting it past the retained
middle term. -/
theorem zetaExplicitFormulaOnePole_add_comm_add_neg_cancel
    {G : Type*} [AddCommGroup G]
    (a b : G) :
    (b + a) + -b = a := by
  calc
    (b + a) + -b = (a + b) + -b := by
      exact congrArg (fun z : G => z + -b) (add_comm b a)
    _ = (a + b) + (-b + 0) := by
      exact congrArg (fun z : G => (a + b) + z) (add_zero (-b)).symm
    _ = a + 0 := by
      exact zetaExplicitFormulaOnePole_add_pair_neg_left_cancel a b 0
    _ = a := by
      exact add_zero a

/-- Fold the exposed horizontal endpoint contribution back into its subtraction
form. -/
theorem zetaExplicitFormulaOnePole_horizontalExposed_add_neg_eq_sub
    {G : Type*} [AddCommGroup G]
    (outerBottom outerTop innerBottom innerTop : G) :
    ((outerBottom + -innerBottom) + -outerTop) + innerTop =
      (outerBottom + -innerBottom) - (outerTop + -innerTop) := by
  calc
    ((outerBottom + -innerBottom) + -outerTop) + innerTop =
        (outerBottom + -innerBottom) + (-outerTop + innerTop) := by
      exact add_assoc (outerBottom + -innerBottom) (-outerTop) innerTop
    _ =
        (outerBottom + -innerBottom) + (-outerTop + -(-innerTop)) := by
      exact congrArg
        (fun z : G => (outerBottom + -innerBottom) + (-outerTop + z))
        (neg_neg innerTop).symm
    _ =
        (outerBottom + -innerBottom) + (-(outerTop + -innerTop)) := by
      exact congrArg
        (fun z : G => (outerBottom + -innerBottom) + z)
        (neg_add outerTop (-innerTop)).symm
    _ = (outerBottom + -innerBottom) - (outerTop + -innerTop) := by
      exact
        (sub_eq_add_neg
          (outerBottom + -innerBottom) (outerTop + -innerTop)).symm

/-- Group the four horizontal split-row terms into the bottom row and the top
row where their duplicated split edges cancel. -/
theorem zetaExplicitFormulaOnePole_horizontalContribution_eq_rowGrouped
    {G : Type*} [AddCommGroup G]
    (bottomRow topRow bottomLeft bottomRight topLeft topRight : G) :
    ((bottomRow + topRow) + (bottomLeft + -topLeft)) +
        (bottomRight + -topRight)
      =
    ((bottomRow + bottomLeft) + bottomRight) +
      ((topRow + -topLeft) + -topRight) := by
  calc
    ((bottomRow + topRow) + (bottomLeft + -topLeft)) +
        (bottomRight + -topRight)
        =
      (bottomRow + topRow) +
        ((bottomLeft + -topLeft) + (bottomRight + -topRight)) := by
      exact add_assoc
        (bottomRow + topRow) (bottomLeft + -topLeft)
        (bottomRight + -topRight)
    _ =
      (bottomRow + topRow) +
        ((bottomLeft + bottomRight) + (-topLeft + -topRight)) := by
      exact congrArg
        (fun z : G => (bottomRow + topRow) + z)
        (add_add_add_comm bottomLeft (-topLeft) bottomRight (-topRight))
    _ =
      (bottomRow + (bottomLeft + bottomRight)) +
        (topRow + (-topLeft + -topRight)) := by
      exact add_add_add_comm
        bottomRow topRow (bottomLeft + bottomRight) (-topLeft + -topRight)
    _ =
      ((bottomRow + bottomLeft) + bottomRight) +
        (topRow + (-topLeft + -topRight)) := by
      exact congrArg
        (fun z : G => z + (topRow + (-topLeft + -topRight)))
        (add_assoc bottomRow bottomLeft bottomRight).symm
    _ =
      ((bottomRow + bottomLeft) + bottomRight) +
        ((topRow + -topLeft) + -topRight) := by
      exact congrArg
        (fun z : G =>
          ((bottomRow + bottomLeft) + bottomRight) + z)
        (add_assoc topRow (-topLeft) (-topRight)).symm

/-- The lower horizontal row cancels its two duplicated split edges and leaves
the exposed bottom-minus-inner contribution. -/
theorem zetaExplicitFormulaOnePole_bottomHorizontalRow_eq_exposed
    {G : Type*} [AddCommGroup G]
    (outerBottom innerBottom bottomLeft bottomRight : G) :
    ((outerBottom - ((bottomLeft + innerBottom) + bottomRight)) +
        bottomLeft) + bottomRight =
      outerBottom + -innerBottom := by
  calc
    ((outerBottom - ((bottomLeft + innerBottom) + bottomRight)) +
        bottomLeft) + bottomRight =
        ((((outerBottom + -bottomLeft) + -innerBottom) + -bottomRight) +
          bottomLeft) + bottomRight := by
      exact congrArg
        (fun z : G => (z + bottomLeft) + bottomRight)
        (zetaExplicitFormulaOnePole_sub_three_eq_sub_sub_sub
          outerBottom bottomLeft innerBottom bottomRight)
    _ =
        (((outerBottom + -bottomLeft) + -innerBottom) + bottomLeft) +
          -bottomRight + bottomRight := by
      exact congrArg
        (fun z : G => z + bottomRight)
        (zetaExplicitFormulaOnePole_add_swap_right
          ((outerBottom + -bottomLeft) + -innerBottom)
          (-bottomRight) bottomLeft)
    _ =
        (((outerBottom + -bottomLeft) + bottomLeft) + -innerBottom) +
          -bottomRight + bottomRight := by
      exact congrArg
        (fun z : G => (z + -bottomRight) + bottomRight)
        (zetaExplicitFormulaOnePole_add_swap_right
          (outerBottom + -bottomLeft) (-innerBottom) bottomLeft)
    _ =
        (outerBottom + -innerBottom) + -bottomRight + bottomRight := by
      exact congrArg
        (fun z : G => z + -bottomRight + bottomRight)
        (zetaExplicitFormulaOnePole_add_neg_add_cancel_middle
          outerBottom bottomLeft (-innerBottom))
    _ =
        outerBottom + -innerBottom := by
      let a : G := outerBottom + -innerBottom
      calc
        (outerBottom + -innerBottom) + -bottomRight + bottomRight =
            ((outerBottom + -innerBottom) + -bottomRight) +
              (bottomRight + 0) := by
          exact congrArg
            (fun z : G => ((outerBottom + -innerBottom) + -bottomRight) + z)
            (add_zero bottomRight).symm
        _ =
            (outerBottom + -innerBottom) +
              (-bottomRight + (bottomRight + 0)) := by
          exact add_assoc
            (outerBottom + -innerBottom) (-bottomRight) (bottomRight + 0)
        _ = (outerBottom + -innerBottom) + 0 := by
          exact zetaExplicitFormulaOnePole_neg_add_cancel_inside_right
            (outerBottom + -innerBottom) bottomRight 0
        _ = outerBottom + -innerBottom := by
          exact add_zero (outerBottom + -innerBottom)

/-- The upper horizontal row cancels its two duplicated split edges and leaves
the exposed top-inner-minus-outer contribution. -/
theorem zetaExplicitFormulaOnePole_topHorizontalRow_eq_exposed
    {G : Type*} [AddCommGroup G]
    (outerTop innerTop topLeft topRight : G) :
    ((((topLeft + innerTop) + topRight) - outerTop) +
        -topLeft) + -topRight =
      -outerTop + innerTop := by
  calc
    ((((topLeft + innerTop) + topRight) - outerTop) +
        -topLeft) + -topRight =
        (((topLeft + innerTop) + topRight) + -outerTop +
          -topLeft) + -topRight := by
      exact congrArg
        (fun z : G => (z + -topLeft) + -topRight)
        (zetaExplicitFormulaOnePole_three_add_sub_eq_add_add_add_neg
          topLeft innerTop topRight outerTop)
    _ =
        ((((topLeft + innerTop) + topRight) + -topLeft) +
          -outerTop) + -topRight := by
      exact congrArg
        (fun z : G => z + -topRight)
        (zetaExplicitFormulaOnePole_add_swap_right
          ((topLeft + innerTop) + topRight) (-outerTop) (-topLeft))
    _ =
        (((topLeft + innerTop) + -topLeft) + topRight +
          -outerTop) + -topRight := by
      exact congrArg
        (fun z : G => (z + -outerTop) + -topRight)
        (zetaExplicitFormulaOnePole_add_swap_right
          (topLeft + innerTop) topRight (-topLeft))
    _ =
        ((innerTop + topRight) + -outerTop) + -topRight := by
      exact congrArg
        (fun z : G => (z + topRight + -outerTop) + -topRight)
        (zetaExplicitFormulaOnePole_add_comm_add_neg_cancel
          innerTop topLeft)
    _ =
        (innerTop + -outerTop) + topRight + -topRight := by
      exact congrArg
        (fun z : G => z + -topRight)
        (zetaExplicitFormulaOnePole_add_swap_right
          innerTop topRight (-outerTop))
    _ =
        innerTop + -outerTop := by
      let a : G := innerTop + -outerTop
      calc
        (innerTop + -outerTop) + topRight + -topRight =
            (innerTop + -outerTop) + (topRight + -topRight) := by
          exact add_assoc (innerTop + -outerTop) topRight (-topRight)
        _ = (innerTop + -outerTop) + 0 := by
          exact congrArg
            (fun z : G => (innerTop + -outerTop) + z)
            (add_neg_cancel topRight)
        _ = innerTop + -outerTop := by
          exact add_zero (innerTop + -outerTop)
    _ = -outerTop + innerTop := by
      exact add_comm innerTop (-outerTop)

/-- Collect the bottom and top horizontal cells into horizontal, right, and
left columns. -/
theorem zetaExplicitFormulaOnePole_upperTwoCells_collect
    {G : Type*} [AddCommGroup G]
    (bottomRow topRow rightBottom rightTop leftBottom leftTop : G) :
    ((bottomRow + rightBottom) + -leftBottom) +
        ((topRow + rightTop) + -leftTop)
      =
    ((bottomRow + topRow) + (rightBottom + rightTop)) +
      (-leftBottom + -leftTop) := by
  exact
    zetaExplicitFormulaOnePole_two_threeTermCells_collect
      bottomRow rightBottom (-leftBottom)
      topRow rightTop (-leftTop)

/-- Collect the middle and right lower cells into horizontal, right, and left
columns. -/
theorem zetaExplicitFormulaOnePole_lowerTwoCells_collect
    {G : Type*} [AddCommGroup G]
    (bottomLeft bottomRight topLeft topRight : G)
    (rightMiddle innerRight leftMiddle innerLeft : G) :
    (((bottomLeft + -topLeft) + innerLeft) + -leftMiddle) +
        (((bottomRight + -topRight) + rightMiddle) + -innerRight)
      =
    (((bottomLeft + -topLeft) + (bottomRight + -topRight)) +
        (innerLeft + rightMiddle)) +
      (-leftMiddle + -innerRight) := by
  exact
    zetaExplicitFormulaOnePole_two_threeTermCells_collect
      (bottomLeft + -topLeft) innerLeft (-leftMiddle)
      (bottomRight + -topRight) rightMiddle (-innerRight)

/-- Merge the upper and lower collected column blocks into horizontal, right,
and left column totals. -/
theorem zetaExplicitFormulaOnePole_collectedUpperLowerBlocks_merge
    {G : Type*} [AddCommGroup G]
    (bottomRow topRow bottomLeft bottomRight topLeft topRight : G)
    (rightBottom rightMiddle rightTop innerRight : G)
    (leftBottom leftMiddle leftTop innerLeft : G) :
    (((bottomRow + topRow) + (rightBottom + rightTop)) +
        (-leftBottom + -leftTop)) +
      ((((bottomLeft + -topLeft) + (bottomRight + -topRight)) +
          (innerLeft + rightMiddle)) +
        (-leftMiddle + -innerRight))
      =
    (((bottomRow + topRow) + (bottomLeft + -topLeft)) +
        (bottomRight + -topRight)) +
      (((rightBottom + rightTop) + rightMiddle) + -innerRight) +
        ((-leftBottom + -leftTop) + (-leftMiddle + innerLeft)) := by
  let horizontal₁ : G := bottomRow + topRow
  let horizontal₂ : G := bottomLeft + -topLeft
  let horizontal₃ : G := bottomRight + -topRight
  let right₁ : G := rightBottom + rightTop
  let right₂ : G := rightMiddle
  let right₃ : G := -innerRight
  let left₁ : G := -leftBottom + -leftTop
  let left₂ : G := -leftMiddle
  let left₃ : G := innerLeft
  change
    ((horizontal₁ + right₁) + left₁) +
      (((horizontal₂ + horizontal₃) + (left₃ + right₂)) + (left₂ + right₃))
      =
    ((horizontal₁ + horizontal₂) + horizontal₃) +
      ((right₁ + right₂) + right₃) +
        (left₁ + (left₂ + left₃))
  have hfirst :
      ((horizontal₁ + right₁) + left₁) +
        (((horizontal₂ + horizontal₃) + (left₃ + right₂)) + (left₂ + right₃))
        =
      ((horizontal₁ + (horizontal₂ + horizontal₃)) +
        (right₁ + (left₃ + right₂))) +
          (left₁ + (left₂ + right₃)) := by
    exact
      zetaExplicitFormulaOnePole_two_threeTermCells_collect
        horizontal₁ right₁ left₁
        (horizontal₂ + horizontal₃) (left₃ + right₂) (left₂ + right₃)
  have hhorizontal :
      horizontal₁ + (horizontal₂ + horizontal₃) =
        (horizontal₁ + horizontal₂) + horizontal₃ := by
    exact (add_assoc horizontal₁ horizontal₂ horizontal₃).symm
  have hright :
      right₁ + (left₃ + right₂) =
        (right₁ + right₂) + left₃ := by
    calc
      right₁ + (left₃ + right₂) =
          right₁ + (right₂ + left₃) := by
        exact congrArg (fun z : G => right₁ + z) (add_comm left₃ right₂)
      _ = (right₁ + right₂) + left₃ := by
        exact (add_assoc right₁ right₂ left₃).symm
  have hleft :
      left₁ + (left₂ + right₃) =
        (left₁ + left₂) + right₃ := by
    exact (add_assoc left₁ left₂ right₃).symm
  have hsecond :
      ((horizontal₁ + (horizontal₂ + horizontal₃)) +
        (right₁ + (left₃ + right₂))) +
          (left₁ + (left₂ + right₃))
        =
      (((horizontal₁ + horizontal₂) + horizontal₃) +
        ((right₁ + right₂) + left₃)) +
          ((left₁ + left₂) + right₃) := by
    exact congrArg₂ Add.add
      (congrArg₂ Add.add hhorizontal hright)
      hleft
  have hthird :
      (((horizontal₁ + horizontal₂) + horizontal₃) +
        ((right₁ + right₂) + left₃)) +
          ((left₁ + left₂) + right₃)
        =
      ((horizontal₁ + horizontal₂) + horizontal₃) +
        ((right₁ + right₂) + right₃) +
          (left₁ + (left₂ + left₃)) := by
    let h : G := (horizontal₁ + horizontal₂) + horizontal₃
    let r : G := right₁ + right₂
    let l : G := left₁ + left₂
    change
      ((h + (r + left₃)) + (l + right₃)) =
        ((h + (r + right₃)) + (left₁ + (left₂ + left₃)))
    have hleft_assoc :
        l + left₃ = left₁ + (left₂ + left₃) := by
      change (left₁ + left₂) + left₃ = left₁ + (left₂ + left₃)
      exact add_assoc left₁ left₂ left₃
    calc
      (h + (r + left₃)) + (l + right₃) =
          h + ((r + left₃) + (l + right₃)) := by
        exact add_assoc h (r + left₃) (l + right₃)
      _ = h + ((r + l) + (left₃ + right₃)) := by
        exact congrArg
          (fun z : G => h + z)
          (add_add_add_comm r left₃ l right₃)
      _ = h + ((r + l) + (right₃ + left₃)) := by
        exact congrArg
          (fun z : G => h + ((r + l) + z))
          (add_comm left₃ right₃)
      _ = h + (((r + l) + right₃) + left₃) := by
        exact congrArg
          (fun z : G => h + z)
          (add_assoc (r + l) right₃ left₃).symm
      _ = h + ((r + (l + right₃)) + left₃) := by
        exact congrArg
          (fun z : G => h + (z + left₃))
          (add_assoc r l right₃)
      _ = h + ((r + (right₃ + l)) + left₃) := by
        exact congrArg
          (fun z : G => h + ((r + z) + left₃))
          (add_comm l right₃)
      _ = h + (((r + right₃) + l) + left₃) := by
        exact congrArg
          (fun z : G => h + (z + left₃))
          (add_assoc r right₃ l).symm
      _ = h + ((r + right₃) + (l + left₃)) := by
        exact congrArg
          (fun z : G => h + z)
          (add_assoc (r + right₃) l left₃)
      _ = h + ((r + right₃) + (left₁ + (left₂ + left₃))) := by
        exact congrArg
          (fun z : G => h + ((r + right₃) + z))
          hleft_assoc
      _ = (h + (r + right₃)) + (left₁ + (left₂ + left₃)) := by
        exact (add_assoc h (r + right₃) (left₁ + (left₂ + left₃))).symm
  Eq.trans hfirst (Eq.trans hsecond hthird)

/-- Expanded four-cell regrouping into horizontal, raw right-side, and raw
left-side contributions.  This is the pure term-collection step before the left
side is folded into the subtraction. -/
theorem zetaExplicitFormulaOnePole_expandedFourCellSplitBoundary_eq_horizontal_right_left_raw
    {G : Type*} [AddCommGroup G]
    (bottomRow topRow : G)
    (bottomLeft bottomRight topLeft topRight : G)
    (rightBottom rightMiddle rightTop innerRight : G)
    (leftBottom leftMiddle leftTop innerLeft : G) :
    (((bottomRow + rightBottom) + -leftBottom) +
        ((topRow + rightTop) + -leftTop)) +
        (((bottomLeft + -topLeft) + innerLeft) + -leftMiddle) +
          (((bottomRight + -topRight) + rightMiddle) + -innerRight)
      =
    (((bottomRow + topRow) + (bottomLeft + -topLeft)) +
        (bottomRight + -topRight)) +
      (((rightBottom + rightTop) + rightMiddle) + -innerRight) +
        ((-leftBottom + -leftTop) + (-leftMiddle + innerLeft)) := by
  have hupper :
      ((bottomRow + rightBottom) + -leftBottom) +
          ((topRow + rightTop) + -leftTop)
        =
      ((bottomRow + topRow) + (rightBottom + rightTop)) +
        (-leftBottom + -leftTop) :=
    zetaExplicitFormulaOnePole_upperTwoCells_collect
      bottomRow topRow rightBottom rightTop leftBottom leftTop
  have hlower :
      (((bottomLeft + -topLeft) + innerLeft) + -leftMiddle) +
          (((bottomRight + -topRight) + rightMiddle) + -innerRight)
        =
      (((bottomLeft + -topLeft) + (bottomRight + -topRight)) +
          (innerLeft + rightMiddle)) +
        (-leftMiddle + -innerRight) :=
    zetaExplicitFormulaOnePole_lowerTwoCells_collect
      bottomLeft bottomRight topLeft topRight
      rightMiddle innerRight leftMiddle innerLeft
  calc
    (((bottomRow + rightBottom) + -leftBottom) +
        ((topRow + rightTop) + -leftTop)) +
        (((bottomLeft + -topLeft) + innerLeft) + -leftMiddle) +
          (((bottomRight + -topRight) + rightMiddle) + -innerRight)
        =
      (((bottomRow + rightBottom) + -leftBottom) +
          ((topRow + rightTop) + -leftTop)) +
        ((((bottomLeft + -topLeft) + innerLeft) + -leftMiddle) +
          (((bottomRight + -topRight) + rightMiddle) + -innerRight)) := by
      exact add_assoc
        (((bottomRow + rightBottom) + -leftBottom) +
          ((topRow + rightTop) + -leftTop))
        (((bottomLeft + -topLeft) + innerLeft) + -leftMiddle)
        (((bottomRight + -topRight) + rightMiddle) + -innerRight)
    _ =
      (((bottomRow + topRow) + (rightBottom + rightTop)) +
          (-leftBottom + -leftTop)) +
        ((((bottomLeft + -topLeft) + (bottomRight + -topRight)) +
            (innerLeft + rightMiddle)) +
          (-leftMiddle + -innerRight)) := by
      exact congrArg₂ Add.add hupper hlower
    _ =
      (((bottomRow + topRow) + (bottomLeft + -topLeft)) +
          (bottomRight + -topRight)) +
        (((rightBottom + rightTop) + rightMiddle) + -innerRight) +
          ((-leftBottom + -leftTop) + (-leftMiddle + innerLeft)) := by
      exact
        zetaExplicitFormulaOnePole_collectedUpperLowerBlocks_merge
          bottomRow topRow bottomLeft bottomRight topLeft topRight
          rightBottom rightMiddle rightTop innerRight
          leftBottom leftMiddle leftTop innerLeft

/-- Fold the raw collected left-side contribution into the negative exposed
left vertical side. -/
theorem zetaExplicitFormulaOnePole_rawLeftContribution_eq_neg_exposed
    {G : Type*} [AddCommGroup G]
    (leftBottom leftMiddle leftTop innerLeft : G) :
    (-leftBottom + -leftTop) + (-leftMiddle + innerLeft) =
      -(((leftBottom + leftTop) + leftMiddle) + -innerLeft) := by
  calc
    (-leftBottom + -leftTop) + (-leftMiddle + innerLeft) =
        (-leftBottom + -leftTop) + (-leftMiddle + -(-innerLeft)) := by
      exact congrArg
        (fun z : G => (-leftBottom + -leftTop) + (-leftMiddle + z))
        (neg_neg innerLeft).symm
    _ =
        (-leftBottom + -leftTop) + (-(leftMiddle + -innerLeft)) := by
      exact congrArg
        (fun z : G => (-leftBottom + -leftTop) + z)
        (neg_add leftMiddle (-innerLeft)).symm
    _ =
        (-(leftBottom + leftTop)) + (-(leftMiddle + -innerLeft)) := by
      exact congrArg
        (fun z : G => z + (-(leftMiddle + -innerLeft)))
        (neg_add leftBottom leftTop).symm
    _ = -((leftBottom + leftTop) + (leftMiddle + -innerLeft)) := by
      exact (neg_add (leftBottom + leftTop) (leftMiddle + -innerLeft)).symm
    _ = -(((leftBottom + leftTop) + leftMiddle) + -innerLeft) := by
      exact congrArg Neg.neg (add_assoc (leftBottom + leftTop) leftMiddle (-innerLeft)).symm

/-- Combine a collected right contribution and the raw negative-left
contribution into the exposed right-minus-left vertical contribution. -/
theorem zetaExplicitFormulaOnePole_rawVerticalContribution_eq_exposedSub
    {G : Type*} [AddCommGroup G]
    (rightBottom rightMiddle rightTop innerRight : G)
    (leftBottom leftMiddle leftTop innerLeft : G) :
    (((rightBottom + rightTop) + rightMiddle) + -innerRight) +
        ((-leftBottom + -leftTop) + (-leftMiddle + innerLeft))
      =
    (((rightBottom + rightTop) + rightMiddle) + -innerRight) -
      (((leftBottom + leftTop) + leftMiddle) + -innerLeft) := by
  calc
    (((rightBottom + rightTop) + rightMiddle) + -innerRight) +
        ((-leftBottom + -leftTop) + (-leftMiddle + innerLeft))
        =
      (((rightBottom + rightTop) + rightMiddle) + -innerRight) +
        -(((leftBottom + leftTop) + leftMiddle) + -innerLeft) := by
      exact congrArg
        (fun z : G =>
          (((rightBottom + rightTop) + rightMiddle) + -innerRight) + z)
        (zetaExplicitFormulaOnePole_rawLeftContribution_eq_neg_exposed
          leftBottom leftMiddle leftTop innerLeft)
    _ =
      (((rightBottom + rightTop) + rightMiddle) + -innerRight) -
        (((leftBottom + leftTop) + leftMiddle) + -innerLeft) := by
      exact
        (sub_eq_add_neg
          (((rightBottom + rightTop) + rightMiddle) + -innerRight)
          (((leftBottom + leftTop) + leftMiddle) + -innerLeft)).symm

/-- Expanded four-cell regrouping: after all cell-side subtractions are written
as additions of negatives, the terms regroup into horizontal and vertical
contributions. -/
theorem zetaExplicitFormulaOnePole_expandedFourCellSplitBoundary_eq_groupedContributions
    {G : Type*} [AddCommGroup G]
    (bottomRow topRow : G)
    (bottomLeft bottomRight topLeft topRight : G)
    (rightBottom rightMiddle rightTop innerRight : G)
    (leftBottom leftMiddle leftTop innerLeft : G) :
    (((bottomRow + rightBottom) + -leftBottom) +
        ((topRow + rightTop) + -leftTop)) +
        (((bottomLeft + -topLeft) + innerLeft) + -leftMiddle) +
          (((bottomRight + -topRight) + rightMiddle) + -innerRight)
      =
    ((bottomRow + topRow) + (bottomLeft + -topLeft) +
          (bottomRight + -topRight)) +
      (((rightBottom + rightTop) + rightMiddle + -innerRight) -
        (((leftBottom + leftTop) + leftMiddle) + -innerLeft)) := by
  have hraw :
      (((bottomRow + rightBottom) + -leftBottom) +
          ((topRow + rightTop) + -leftTop)) +
          (((bottomLeft + -topLeft) + innerLeft) + -leftMiddle) +
            (((bottomRight + -topRight) + rightMiddle) + -innerRight)
        =
      (((bottomRow + topRow) + (bottomLeft + -topLeft)) +
          (bottomRight + -topRight)) +
        (((rightBottom + rightTop) + rightMiddle) + -innerRight) +
          ((-leftBottom + -leftTop) + (-leftMiddle + innerLeft)) :=
    zetaExplicitFormulaOnePole_expandedFourCellSplitBoundary_eq_horizontal_right_left_raw
      bottomRow topRow
      bottomLeft bottomRight topLeft topRight
      rightBottom rightMiddle rightTop innerRight
      leftBottom leftMiddle leftTop innerLeft
  have hvertical :
      (((rightBottom + rightTop) + rightMiddle) + -innerRight) +
          ((-leftBottom + -leftTop) + (-leftMiddle + innerLeft))
        =
      (((rightBottom + rightTop) + rightMiddle) + -innerRight) -
        (((leftBottom + leftTop) + leftMiddle) + -innerLeft) :=
    zetaExplicitFormulaOnePole_rawVerticalContribution_eq_exposedSub
      rightBottom rightMiddle rightTop innerRight
      leftBottom leftMiddle leftTop innerLeft
  calc
    (((bottomRow + rightBottom) + -leftBottom) +
        ((topRow + rightTop) + -leftTop)) +
        (((bottomLeft + -topLeft) + innerLeft) + -leftMiddle) +
          (((bottomRight + -topRight) + rightMiddle) + -innerRight)
        =
      (((bottomRow + topRow) + (bottomLeft + -topLeft)) +
          (bottomRight + -topRight)) +
        (((rightBottom + rightTop) + rightMiddle) + -innerRight) +
          ((-leftBottom + -leftTop) + (-leftMiddle + innerLeft)) := by
      exact hraw
    _ =
      (((bottomRow + topRow) + (bottomLeft + -topLeft)) +
          (bottomRight + -topRight)) +
        ((((rightBottom + rightTop) + rightMiddle) + -innerRight) +
          ((-leftBottom + -leftTop) + (-leftMiddle + innerLeft))) := by
      exact add_assoc
        (((bottomRow + topRow) + (bottomLeft + -topLeft)) +
          (bottomRight + -topRight))
        (((rightBottom + rightTop) + rightMiddle) + -innerRight)
        ((-leftBottom + -leftTop) + (-leftMiddle + innerLeft))
    _ =
      (((bottomRow + topRow) + (bottomLeft + -topLeft)) +
          (bottomRight + -topRight)) +
        ((((rightBottom + rightTop) + rightMiddle) + -innerRight) -
          (((leftBottom + leftTop) + leftMiddle) + -innerLeft)) := by
      exact congrArg
        (fun z : G =>
          (((bottomRow + topRow) + (bottomLeft + -topLeft)) +
            (bottomRight + -topRight)) + z)
        hvertical
    _ =
      ((bottomRow + topRow) + (bottomLeft + -topLeft) +
            (bottomRight + -topRight)) +
        (((rightBottom + rightTop) + rightMiddle + -innerRight) -
          (((leftBottom + leftTop) + leftMiddle) + -innerLeft)) := by
      rfl

/-- The named square-punctured boundary unfolds to the oriented exposed
outer-minus-inner edge grouping.  Each parenthesized sum is one full exposed
side before it is split into the four rectangular cells. -/
theorem zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral_eq_exposedEdges
    (g : ℂ → ℂ) (F : ExplicitFormulaContourFamily) (T R : ℝ) :
    zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral g F T R =
      ((∫ x : ℝ in (1 - F.c)..F.c, g (x + (-T) * Complex.I)) +
          (-(∫ x : ℝ in (1 - R)..(1 + R), g (x + (-R) * Complex.I)))) -
        ((∫ x : ℝ in (1 - F.c)..F.c, g (x + T * Complex.I)) +
          (-(∫ x : ℝ in (1 - R)..(1 + R), g (x + R * Complex.I)))) +
        ((Complex.I • (∫ y : ℝ in -T..T, g (F.c + y * Complex.I))) +
          (-(Complex.I •
              (∫ y : ℝ in -R..R, g ((1 + R) + y * Complex.I))))) -
          ((Complex.I •
              (∫ y : ℝ in -T..T, g ((1 - F.c) + y * Complex.I))) +
            (-(Complex.I •
                (∫ y : ℝ in -R..R, g ((1 - R) + y * Complex.I))))) := by
  let outerBottom : ℂ :=
    ∫ x : ℝ in (1 - F.c)..F.c, g (x + (-T) * Complex.I)
  let outerTop : ℂ :=
    ∫ x : ℝ in (1 - F.c)..F.c, g (x + T * Complex.I)
  let outerRight : ℂ :=
    Complex.I • (∫ y : ℝ in -T..T, g (F.c + y * Complex.I))
  let outerLeft : ℂ :=
    Complex.I • (∫ y : ℝ in -T..T, g ((1 - F.c) + y * Complex.I))
  let innerBottom : ℂ :=
    ∫ x : ℝ in (1 - R)..(1 + R), g (x + (-R) * Complex.I)
  let innerTop : ℂ :=
    ∫ x : ℝ in (1 - R)..(1 + R), g (x + R * Complex.I)
  let innerRight : ℂ :=
    Complex.I • (∫ y : ℝ in -R..R, g ((1 + R) + y * Complex.I))
  let innerLeft : ℂ :=
    Complex.I • (∫ y : ℝ in -R..R, g ((1 - R) + y * Complex.I))
  have houter :
      zetaExplicitFormulaOnePoleOuterStandardBoundaryCoordinateIntegral g F T =
        outerBottom - outerTop + (outerRight - outerLeft) := by
    rfl
  have hinner :
      zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral g R =
        innerBottom - innerTop + (innerRight - innerLeft) := by
    rfl
  have halgebra :
      (outerBottom - outerTop + (outerRight - outerLeft)) -
          (innerBottom - innerTop + (innerRight - innerLeft)) =
        (outerBottom + -innerBottom) - (outerTop + -innerTop) +
          ((outerRight + -innerRight) - (outerLeft + -innerLeft)) :=
    zetaExplicitFormulaOnePole_outer_sub_inner_four_edges_grouped
      outerBottom outerTop outerRight outerLeft
      innerBottom innerTop innerRight innerLeft
  calc
    zetaExplicitFormulaOnePoleSquarePuncturedRectangleBoundaryIntegral g F T R =
        zetaExplicitFormulaOnePoleOuterStandardBoundaryCoordinateIntegral g F T -
          zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral g R := by
      rfl
    _ =
        (outerBottom - outerTop + (outerRight - outerLeft)) -
          zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral g R := by
      exact congrArg
        (fun z : ℂ =>
          z - zetaExplicitFormulaOnePoleInnerSquareBoundaryIntegral g R)
        houter
    _ =
        (outerBottom - outerTop + (outerRight - outerLeft)) -
          (innerBottom - innerTop + (innerRight - innerLeft)) := by
      exact congrArg
        (fun z : ℂ =>
          (outerBottom - outerTop + (outerRight - outerLeft)) - z)
        hinner
    _ =
        (outerBottom + -innerBottom) - (outerTop + -innerTop) +
          ((outerRight + -innerRight) - (outerLeft + -innerLeft)) := by
      exact halgebra
    _ =
      ((∫ x : ℝ in (1 - F.c)..F.c, g (x + (-T) * Complex.I)) +
          (-(∫ x : ℝ in (1 - R)..(1 + R), g (x + (-R) * Complex.I)))) -
        ((∫ x : ℝ in (1 - F.c)..F.c, g (x + T * Complex.I)) +
          (-(∫ x : ℝ in (1 - R)..(1 + R), g (x + R * Complex.I)))) +
        ((Complex.I • (∫ y : ℝ in -T..T, g (F.c + y * Complex.I))) +
          (-(Complex.I •
              (∫ y : ℝ in -R..R, g ((1 + R) + y * Complex.I))))) -
          ((Complex.I •
              (∫ y : ℝ in -T..T, g ((1 - F.c) + y * Complex.I))) +
            (-(Complex.I •
                (∫ y : ℝ in -R..R, g ((1 - R) + y * Complex.I))))) := by
      rfl

/-- The two horizontal cell rows plus the short horizontal puncture edges
collapse to the exposed outer-minus-inner horizontal contribution. -/
theorem zetaExplicitFormulaOnePole_fourCellHorizontalContribution_eq_exposed
    {G : Type*} [AddCommGroup G]
    (outerBottom outerTop innerBottom innerTop : G)
    (bottomLeft bottomRight topLeft topRight : G) :
    (outerBottom - ((bottomLeft + innerBottom) + bottomRight)) +
        (((topLeft + innerTop) + topRight) - outerTop) +
          (bottomLeft - topLeft) +
            (bottomRight - topRight)
      =
    (outerBottom + -innerBottom) - (outerTop + -innerTop) := by
  let bottomRow : G :=
    outerBottom - ((bottomLeft + innerBottom) + bottomRight)
  let topRow : G :=
    ((topLeft + innerTop) + topRight) - outerTop
  have hrow :
      ((bottomRow + topRow) + (bottomLeft + -topLeft)) +
          (bottomRight + -topRight)
        =
      ((bottomRow + bottomLeft) + bottomRight) +
        ((topRow + -topLeft) + -topRight) :=
    zetaExplicitFormulaOnePole_horizontalContribution_eq_rowGrouped
      bottomRow topRow bottomLeft bottomRight topLeft topRight
  have hbottom :
      (bottomRow + bottomLeft) + bottomRight =
        outerBottom + -innerBottom := by
    exact
      zetaExplicitFormulaOnePole_bottomHorizontalRow_eq_exposed
        outerBottom innerBottom bottomLeft bottomRight
  have htop :
      (topRow + -topLeft) + -topRight =
        -outerTop + innerTop := by
    exact
      zetaExplicitFormulaOnePole_topHorizontalRow_eq_exposed
        outerTop innerTop topLeft topRight
  have hfold :
      (outerBottom + -innerBottom) + (-outerTop + innerTop) =
        (outerBottom + -innerBottom) - (outerTop + -innerTop) := by
    calc
      (outerBottom + -innerBottom) + (-outerTop + innerTop) =
          ((outerBottom + -innerBottom) + -outerTop) + innerTop := by
        exact (add_assoc (outerBottom + -innerBottom) (-outerTop) innerTop).symm
      _ = (outerBottom + -innerBottom) - (outerTop + -innerTop) := by
        exact
          zetaExplicitFormulaOnePole_horizontalExposed_add_neg_eq_sub
            outerBottom outerTop innerBottom innerTop
  calc
    (outerBottom - ((bottomLeft + innerBottom) + bottomRight)) +
        (((topLeft + innerTop) + topRight) - outerTop) +
          (bottomLeft - topLeft) +
            (bottomRight - topRight)
        =
      ((bottomRow + topRow) + (bottomLeft + -topLeft)) +
          (bottomRight + -topRight) := by
      exact congrArg₂ Add.add
        (congrArg₂ Add.add rfl (sub_eq_add_neg bottomLeft topLeft))
        (sub_eq_add_neg bottomRight topRight)
    _ =
      ((bottomRow + bottomLeft) + bottomRight) +
        ((topRow + -topLeft) + -topRight) := by
      exact hrow
    _ =
      (outerBottom + -innerBottom) +
        ((topRow + -topLeft) + -topRight) := by
      exact congrArg
        (fun z : G => z + ((topRow + -topLeft) + -topRight))
        hbottom
    _ =
      (outerBottom + -innerBottom) + (-outerTop + innerTop) := by
      exact congrArg
        (fun z : G => (outerBottom + -innerBottom) + z)
        htop
    _ =
      (outerBottom + -innerBottom) - (outerTop + -innerTop) := by
      exact hfold

/-- The three right cell-side pieces and the negative inner right edge collect
to the exposed right vertical side. -/
theorem zetaExplicitFormulaOnePole_fourCellRightContribution_eq_exposed
    {G : Type*} [AddCommGroup G]
    (rightBottom rightMiddle rightTop innerRight : G) :
    rightBottom + rightTop + rightMiddle - innerRight =
      ((rightBottom + rightMiddle) + rightTop) + -innerRight := by
  calc
    rightBottom + rightTop + rightMiddle - innerRight =
        (rightBottom + rightTop + rightMiddle) + -innerRight := by
      exact sub_eq_add_neg
        (rightBottom + rightTop + rightMiddle) innerRight
    _ = ((rightBottom + rightTop) + rightMiddle) + -innerRight := by
      rfl
    _ = (rightBottom + (rightTop + rightMiddle)) + -innerRight := by
      exact congrArg (fun z : G => z + -innerRight)
        (add_assoc rightBottom rightTop rightMiddle)
    _ = (rightBottom + (rightMiddle + rightTop)) + -innerRight := by
      exact congrArg
        (fun z : G => (rightBottom + z) + -innerRight)
        (add_comm rightTop rightMiddle)
    _ = ((rightBottom + rightMiddle) + rightTop) + -innerRight := by
      exact congrArg (fun z : G => z + -innerRight)
        (add_assoc rightBottom rightMiddle rightTop).symm

/-- The three left cell-side pieces and the negative inner left edge collect to
the exposed left vertical side in the orientation used by the subtraction. -/
theorem zetaExplicitFormulaOnePole_fourCellLeftContribution_eq_exposed
    {G : Type*} [AddCommGroup G]
    (leftBottom leftMiddle leftTop innerLeft : G) :
    leftBottom + leftTop + leftMiddle - innerLeft =
      ((leftBottom + leftMiddle) + leftTop) + -innerLeft := by
  calc
    leftBottom + leftTop + leftMiddle - innerLeft =
        (leftBottom + leftTop + leftMiddle) + -innerLeft := by
      exact sub_eq_add_neg
        (leftBottom + leftTop + leftMiddle) innerLeft
    _ = ((leftBottom + leftTop) + leftMiddle) + -innerLeft := by
      rfl
    _ = (leftBottom + (leftTop + leftMiddle)) + -innerLeft := by
      exact congrArg (fun z : G => z + -innerLeft)
        (add_assoc leftBottom leftTop leftMiddle)
    _ = (leftBottom + (leftMiddle + leftTop)) + -innerLeft := by
      exact congrArg
        (fun z : G => (leftBottom + z) + -innerLeft)
        (add_comm leftTop leftMiddle)
    _ = ((leftBottom + leftMiddle) + leftTop) + -innerLeft := by
      exact congrArg (fun z : G => z + -innerLeft)
        (add_assoc leftBottom leftMiddle leftTop).symm

/-- Four-cell split algebra after the four cell sums have first been grouped
into horizontal, right-vertical, and left-vertical contributions. -/
theorem zetaExplicitFormulaOnePole_groupedFourCellContributions_eq_verticalSplitExposed
    {G : Type*} [AddCommGroup G]
    (outerBottom outerTop innerBottom innerTop : G)
    (bottomLeft bottomRight topLeft topRight : G)
    (rightBottom rightMiddle rightTop innerRight : G)
    (leftBottom leftMiddle leftTop innerLeft : G) :
    ((outerBottom - ((bottomLeft + innerBottom) + bottomRight)) +
        (((topLeft + innerTop) + topRight) - outerTop) +
          (bottomLeft - topLeft) +
            (bottomRight - topRight)) +
      ((rightBottom + rightTop + rightMiddle - innerRight) -
        (leftBottom + leftTop + leftMiddle - innerLeft))
      =
    (outerBottom + -innerBottom) - (outerTop + -innerTop) +
      ((((rightBottom + rightMiddle) + rightTop) + -innerRight) -
        ((((leftBottom + leftMiddle) + leftTop) + -innerLeft))) := by
  have hhorizontal :
      (outerBottom - ((bottomLeft + innerBottom) + bottomRight)) +
          (((topLeft + innerTop) + topRight) - outerTop) +
            (bottomLeft - topLeft) +
              (bottomRight - topRight)
        =
      (outerBottom + -innerBottom) - (outerTop + -innerTop) :=
    zetaExplicitFormulaOnePole_fourCellHorizontalContribution_eq_exposed
      outerBottom outerTop innerBottom innerTop
      bottomLeft bottomRight topLeft topRight
  have hright :
      rightBottom + rightTop + rightMiddle - innerRight =
        ((rightBottom + rightMiddle) + rightTop) + -innerRight :=
    zetaExplicitFormulaOnePole_fourCellRightContribution_eq_exposed
      rightBottom rightMiddle rightTop innerRight
  have hleft :
      leftBottom + leftTop + leftMiddle - innerLeft =
        ((leftBottom + leftMiddle) + leftTop) + -innerLeft :=
    zetaExplicitFormulaOnePole_fourCellLeftContribution_eq_exposed
      leftBottom leftMiddle leftTop innerLeft
  calc
    ((outerBottom - ((bottomLeft + innerBottom) + bottomRight)) +
        (((topLeft + innerTop) + topRight) - outerTop) +
          (bottomLeft - topLeft) +
            (bottomRight - topRight)) +
      ((rightBottom + rightTop + rightMiddle - innerRight) -
        (leftBottom + leftTop + leftMiddle - innerLeft))
        =
      ((outerBottom + -innerBottom) - (outerTop + -innerTop)) +
      ((rightBottom + rightTop + rightMiddle - innerRight) -
        (leftBottom + leftTop + leftMiddle - innerLeft)) := by
      exact congrArg
        (fun z : G =>
          z +
            ((rightBottom + rightTop + rightMiddle - innerRight) -
              (leftBottom + leftTop + leftMiddle - innerLeft)))
        hhorizontal
    _ =
      ((outerBottom + -innerBottom) - (outerTop + -innerTop)) +
      ((((rightBottom + rightMiddle) + rightTop) + -innerRight) -
        (leftBottom + leftTop + leftMiddle - innerLeft)) := by
      exact congrArg
        (fun z : G =>
          ((outerBottom + -innerBottom) - (outerTop + -innerTop)) +
            (z - (leftBottom + leftTop + leftMiddle - innerLeft)))
        hright
    _ =
      ((outerBottom + -innerBottom) - (outerTop + -innerTop)) +
      ((((rightBottom + rightMiddle) + rightTop) + -innerRight) -
        ((((leftBottom + leftMiddle) + leftTop) + -innerLeft))) := by
      exact congrArg
        (fun z : G =>
          ((outerBottom + -innerBottom) - (outerTop + -innerTop)) +
            ((((rightBottom + rightMiddle) + rightTop) + -innerRight) - z))
        hleft
    _ =
    (outerBottom + -innerBottom) - (outerTop + -innerTop) +
      ((((rightBottom + rightMiddle) + rightTop) + -innerRight) -
        ((((leftBottom + leftMiddle) + leftTop) + -innerLeft))) := by
      rfl

/-- Rebracket the raw four-cell boundary sum into horizontal, right-vertical,
and left-vertical contributions. -/
theorem zetaExplicitFormulaOnePole_fourCellSplitBoundary_eq_groupedContributions
    {G : Type*} [AddCommGroup G]
    (outerBottom outerTop innerBottom innerTop : G)
    (bottomLeft bottomRight topLeft topRight : G)
    (rightBottom rightMiddle rightTop innerRight : G)
    (leftBottom leftMiddle leftTop innerLeft : G) :
    (outerBottom - ((bottomLeft + innerBottom) + bottomRight) +
        rightBottom - leftBottom) +
      (((topLeft + innerTop) + topRight) - outerTop +
        rightTop - leftTop) +
        (bottomLeft - topLeft + innerLeft - leftMiddle) +
          (bottomRight - topRight + rightMiddle - innerRight)
      =
    ((outerBottom - ((bottomLeft + innerBottom) + bottomRight)) +
        (((topLeft + innerTop) + topRight) - outerTop) +
          (bottomLeft - topLeft) +
            (bottomRight - topRight)) +
      ((rightBottom + rightTop + rightMiddle - innerRight) -
        (leftBottom + leftTop + leftMiddle - innerLeft)) := by
  let bottomRow : G :=
    outerBottom - ((bottomLeft + innerBottom) + bottomRight)
  let topRow : G :=
    ((topLeft + innerTop) + topRight) - outerTop
  have hbottomCell :
      bottomRow + rightBottom - leftBottom =
        (bottomRow + rightBottom) + -leftBottom := by
    exact sub_eq_add_neg (bottomRow + rightBottom) leftBottom
  have htopCell :
      topRow + rightTop - leftTop =
        (topRow + rightTop) + -leftTop := by
    exact sub_eq_add_neg (topRow + rightTop) leftTop
  have hleftCell :
      bottomLeft - topLeft + innerLeft - leftMiddle =
        ((bottomLeft + -topLeft) + innerLeft) + -leftMiddle := by
    calc
      bottomLeft - topLeft + innerLeft - leftMiddle =
          ((bottomLeft - topLeft) + innerLeft) + -leftMiddle := by
        exact sub_eq_add_neg ((bottomLeft - topLeft) + innerLeft) leftMiddle
      _ = ((bottomLeft + -topLeft) + innerLeft) + -leftMiddle := by
        exact congrArg
          (fun z : G => (z + innerLeft) + -leftMiddle)
          (sub_eq_add_neg bottomLeft topLeft)
  have hrightCell :
      bottomRight - topRight + rightMiddle - innerRight =
        ((bottomRight + -topRight) + rightMiddle) + -innerRight := by
    calc
      bottomRight - topRight + rightMiddle - innerRight =
          ((bottomRight - topRight) + rightMiddle) + -innerRight := by
        exact sub_eq_add_neg ((bottomRight - topRight) + rightMiddle) innerRight
      _ = ((bottomRight + -topRight) + rightMiddle) + -innerRight := by
        exact congrArg
          (fun z : G => (z + rightMiddle) + -innerRight)
          (sub_eq_add_neg bottomRight topRight)
  have hrightContribution :
      rightBottom + rightTop + rightMiddle - innerRight =
        ((rightBottom + rightTop) + rightMiddle) + -innerRight := by
    exact sub_eq_add_neg (rightBottom + rightTop + rightMiddle) innerRight
  have hleftContribution :
      leftBottom + leftTop + leftMiddle - innerLeft =
        ((leftBottom + leftTop) + leftMiddle) + -innerLeft := by
    exact sub_eq_add_neg (leftBottom + leftTop + leftMiddle) innerLeft
  have hexpanded :
      (((bottomRow + rightBottom) + -leftBottom) +
          ((topRow + rightTop) + -leftTop)) +
          (((bottomLeft + -topLeft) + innerLeft) + -leftMiddle) +
            (((bottomRight + -topRight) + rightMiddle) + -innerRight)
        =
      ((bottomRow + topRow) + (bottomLeft + -topLeft) +
            (bottomRight + -topRight)) +
        (((rightBottom + rightTop) + rightMiddle + -innerRight) -
          (((leftBottom + leftTop) + leftMiddle) + -innerLeft)) :=
    zetaExplicitFormulaOnePole_expandedFourCellSplitBoundary_eq_groupedContributions
      bottomRow topRow
      bottomLeft bottomRight topLeft topRight
      rightBottom rightMiddle rightTop innerRight
      leftBottom leftMiddle leftTop innerLeft
  calc
    (outerBottom - ((bottomLeft + innerBottom) + bottomRight) +
        rightBottom - leftBottom) +
      (((topLeft + innerTop) + topRight) - outerTop +
        rightTop - leftTop) +
        (bottomLeft - topLeft + innerLeft - leftMiddle) +
          (bottomRight - topRight + rightMiddle - innerRight)
        =
      (((bottomRow + rightBottom) + -leftBottom) +
          ((topRow + rightTop) + -leftTop)) +
          (((bottomLeft + -topLeft) + innerLeft) + -leftMiddle) +
            (((bottomRight + -topRight) + rightMiddle) + -innerRight) := by
      exact congrArg₂ Add.add
        (congrArg₂ Add.add
          (congrArg₂ Add.add hbottomCell htopCell)
          hleftCell)
        hrightCell
    _ =
      ((bottomRow + topRow) + (bottomLeft + -topLeft) +
            (bottomRight + -topRight)) +
        (((rightBottom + rightTop) + rightMiddle + -innerRight) -
          (((leftBottom + leftTop) + leftMiddle) + -innerLeft)) := by
      exact hexpanded
    _ =
      ((outerBottom - ((bottomLeft + innerBottom) + bottomRight)) +
          (((topLeft + innerTop) + topRight) - outerTop) +
            (bottomLeft - topLeft) +
              (bottomRight - topRight)) +
        ((rightBottom + rightTop + rightMiddle - innerRight) -
          (leftBottom + leftTop + leftMiddle - innerLeft)) := by
      exact congrArg₂ Add.add
        (congrArg₂ Add.add
          (congrArg₂ Add.add rfl (sub_eq_add_neg bottomLeft topLeft))
          (sub_eq_add_neg bottomRight topRight))
        (congrArg₂ (fun x y : G => x - y) hrightContribution hleftContribution)

/-- Four-cell split algebra cancels the duplicated puncture-height horizontal
segments and collects the three vertical pieces on each outer side. -/
theorem zetaExplicitFormulaOnePole_fourCellSplitBoundary_eq_verticalSplitExposed_algebra
    {G : Type*} [AddCommGroup G]
    (outerBottom outerTop innerBottom innerTop : G)
    (bottomLeft bottomRight topLeft topRight : G)
    (rightBottom rightMiddle rightTop innerRight : G)
    (leftBottom leftMiddle leftTop innerLeft : G) :
    (outerBottom - ((bottomLeft + innerBottom) + bottomRight) +
        rightBottom - leftBottom) +
      (((topLeft + innerTop) + topRight) - outerTop +
        rightTop - leftTop) +
        (bottomLeft - topLeft + innerLeft - leftMiddle) +
          (bottomRight - topRight + rightMiddle - innerRight)
      =
    (outerBottom + -innerBottom) - (outerTop + -innerTop) +
      ((((rightBottom + rightMiddle) + rightTop) + -innerRight) -
        ((((leftBottom + leftMiddle) + leftTop) + -innerLeft))) := by
  have hgrouped :
      (outerBottom - ((bottomLeft + innerBottom) + bottomRight) +
          rightBottom - leftBottom) +
        (((topLeft + innerTop) + topRight) - outerTop +
          rightTop - leftTop) +
          (bottomLeft - topLeft + innerLeft - leftMiddle) +
            (bottomRight - topRight + rightMiddle - innerRight)
        =
      ((outerBottom - ((bottomLeft + innerBottom) + bottomRight)) +
          (((topLeft + innerTop) + topRight) - outerTop) +
            (bottomLeft - topLeft) +
              (bottomRight - topRight)) +
        ((rightBottom + rightTop + rightMiddle - innerRight) -
          (leftBottom + leftTop + leftMiddle - innerLeft)) :=
    zetaExplicitFormulaOnePole_fourCellSplitBoundary_eq_groupedContributions
      outerBottom outerTop innerBottom innerTop
      bottomLeft bottomRight topLeft topRight
      rightBottom rightMiddle rightTop innerRight
      leftBottom leftMiddle leftTop innerLeft
  have hexposed :
      ((outerBottom - ((bottomLeft + innerBottom) + bottomRight)) +
          (((topLeft + innerTop) + topRight) - outerTop) +
            (bottomLeft - topLeft) +
              (bottomRight - topRight)) +
        ((rightBottom + rightTop + rightMiddle - innerRight) -
          (leftBottom + leftTop + leftMiddle - innerLeft))
        =
      (outerBottom + -innerBottom) - (outerTop + -innerTop) +
        ((((rightBottom + rightMiddle) + rightTop) + -innerRight) -
          ((((leftBottom + leftMiddle) + leftTop) + -innerLeft))) :=
    zetaExplicitFormulaOnePole_groupedFourCellContributions_eq_verticalSplitExposed
      outerBottom outerTop innerBottom innerTop
      bottomLeft bottomRight topLeft topRight
      rightBottom rightMiddle rightTop innerRight
      leftBottom leftMiddle leftTop innerLeft
  Eq.trans hgrouped hexposed

end ZetaAdmissibleFunction

end
end LFunctions
end Boundary
