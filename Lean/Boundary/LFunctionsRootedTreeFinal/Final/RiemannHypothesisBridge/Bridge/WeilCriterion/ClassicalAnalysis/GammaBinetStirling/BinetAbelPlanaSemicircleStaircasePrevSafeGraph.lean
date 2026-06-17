import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleStaircaseWitness

/-!
# Previous safe graph bounds for right semicircle staircase cells

This file owns the graph-dominance facts that compare the current staircase
height with the previous and current safe real coordinates.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology Interval
open Filter MeasureTheory

/-- Bottom endpoint of the staircase height partition. -/
theorem Complex.rightSemicircleStaircaseY_zero
    (ρ : ℝ)
    (m : ℕ) :
    Complex.rightSemicircleStaircaseY ρ m 0 = -ρ := by
  show -ρ + (((0 : ℕ) : ℝ) / (m + 1 : ℝ)) * (2 * ρ) = -ρ
  calc
    -ρ + (((0 : ℕ) : ℝ) / (m + 1 : ℝ)) * (2 * ρ) =
        -ρ + ((0 : ℝ) / (m + 1 : ℝ)) * (2 * ρ) :=
      congrArg
        (fun x : ℝ => -ρ + (x / (m + 1 : ℝ)) * (2 * ρ))
        Nat.cast_zero
    _ =
        -ρ + 0 * (2 * ρ) :=
      congrArg (fun x : ℝ => -ρ + x * (2 * ρ)) (zero_div (m + 1 : ℝ))
    _ = -ρ + 0 :=
      congrArg (fun x : ℝ => -ρ + x) (zero_mul (2 * ρ))
    _ = -ρ :=
      add_zero (-ρ)

/-- At the bottom sample of the staircase, the right semicircle graph has real
coordinate `0`. -/
theorem Complex.rightSemicircleStaircase_currentGraph_zero
    (ρ : ℝ)
    (m : ℕ) :
    Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m 0) = 0 :=
  calc
    Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m 0) =
        Complex.rightSemicircleGraphRe ρ (-ρ) :=
      congrArg (fun y : ℝ => Complex.rightSemicircleGraphRe ρ y)
        (Complex.rightSemicircleStaircaseY_zero ρ m)
    _ = 0 :=
      Complex.rightSemicircleGraphRe_bottom

/-- The previous safe coordinate dominates the bottom graph sample. -/
theorem Complex.rightSemicircleStaircasePrevSafeRe_ge_currentGraph_zero
    (ρ : ℝ)
    (m : ℕ) :
    Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m 0) ≤
      Complex.rightSemicircleStaircasePrevSafeRe ρ m 0 :=
  le_of_eq
    (calc
      Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m 0) = 0 :=
        Complex.rightSemicircleStaircase_currentGraph_zero ρ m
      _ = Complex.rightSemicircleStaircasePrevSafeRe ρ m 0 :=
        Eq.symm
          (Complex.rightSemicircleStaircasePrevSafeRe_zero_owner ρ m))

/-- If `k` is nonzero, the current sample is the right endpoint of the
previous staircase cell. -/
theorem Complex.rightSemicircleStaircaseY_mem_prev_cell_of_ne_zero
    (ρ : ℝ)
    (m k : ℕ)
    (hk0 : k ≠ 0) :
    Complex.rightSemicircleStaircaseY ρ m k ∈
      [[Complex.rightSemicircleStaircaseY ρ m (k - 1),
        Complex.rightSemicircleStaircaseY ρ m ((k - 1) + 1)]] :=
  let hsucc : (k - 1) + 1 = k :=
    Complex.staircase_pred_succ_of_ne_zero hk0
  Eq.mpr
    (congrArg
      (fun j : ℕ =>
        Complex.rightSemicircleStaircaseY ρ m k ∈
          [[Complex.rightSemicircleStaircaseY ρ m (k - 1),
            Complex.rightSemicircleStaircaseY ρ m j]])
      hsucc)
    Set.right_mem_uIcc

/-- Away from the bottom sample, the previous safe coordinate is the previous
cell's safe coordinate and dominates the current graph value. -/
theorem Complex.rightSemicircleStaircasePrevSafeRe_ge_currentGraph_of_ne_zero
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1))
    (hk0 : k ≠ 0) :
    Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m k) ≤
      Complex.rightSemicircleStaircasePrevSafeRe ρ m k :=
  let hkpred_range : k - 1 ∈ Finset.range (m + 1) :=
    Complex.staircase_pred_mem_range_of_ne_zero hk hk0
  let hy_mem :
      Complex.rightSemicircleStaircaseY ρ m k ∈
        [[Complex.rightSemicircleStaircaseY ρ m (k - 1),
          Complex.rightSemicircleStaircaseY ρ m ((k - 1) + 1)]] :=
    Complex.rightSemicircleStaircaseY_mem_prev_cell_of_ne_zero ρ m k hk0
  let hdom :
      Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k) ≤
        Complex.rightSemicircleStaircaseSafeRe ρ m (k - 1) :=
    Complex.rightSemicircleStaircaseSafeRe_ge_graph_on_cell
      hρ m (k - 1) hkpred_range hy_mem
  let hsafe_eq :
      Complex.rightSemicircleStaircaseSafeRe ρ m (k - 1) =
        Complex.rightSemicircleStaircasePrevSafeRe ρ m k :=
    Eq.symm
      (Complex.rightSemicircleStaircasePrevSafeRe_eq_safeRe_pred_of_ne_zero
        ρ m k hk0)
  le_trans hdom (le_of_eq hsafe_eq)

/-- The previous safe real coordinate dominates the graph at the current
bottom sample. -/
theorem Complex.rightSemicircleStaircasePrevSafeRe_ge_currentGraph
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1)) :
    Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m k) ≤
      Complex.rightSemicircleStaircasePrevSafeRe ρ m k :=
  match k with
  | 0 =>
      Complex.rightSemicircleStaircasePrevSafeRe_ge_currentGraph_zero ρ m
  | Nat.succ k' =>
      Complex.rightSemicircleStaircasePrevSafeRe_ge_currentGraph_of_ne_zero
        hρ m (Nat.succ k') hk (Nat.succ_ne_zero k')

/-- The current sample belongs to its own staircase cell. -/
theorem Complex.rightSemicircleStaircaseY_mem_current_cell
    (ρ : ℝ)
    (m k : ℕ) :
    Complex.rightSemicircleStaircaseY ρ m k ∈
      [[Complex.rightSemicircleStaircaseY ρ m k,
        Complex.rightSemicircleStaircaseY ρ m (k + 1)]] :=
  Set.left_mem_uIcc

/-- The current safe real coordinate dominates the graph at the current bottom
sample. -/
theorem Complex.rightSemicircleStaircaseSafeRe_ge_currentGraph
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1)) :
    Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m k) ≤
      Complex.rightSemicircleStaircaseSafeRe ρ m k :=
  Complex.rightSemicircleStaircaseSafeRe_ge_graph_on_cell
    hρ m k hk
    (Complex.rightSemicircleStaircaseY_mem_current_cell ρ m k)

/-- If a horizontal connector coordinate is ordered from previous-safe to
current-safe, then it dominates the current graph value. -/
theorem Complex.rightSemicircleStaircaseHorizontal_re_ge_graph_of_prev_le
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1))
    {x : ℝ}
    (hx :
      Complex.rightSemicircleStaircasePrevSafeRe ρ m k ≤ x ∧
        x ≤ Complex.rightSemicircleStaircaseSafeRe ρ m k) :
    Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m k) ≤ x :=
  let hprev :
      Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k) ≤
        Complex.rightSemicircleStaircasePrevSafeRe ρ m k :=
    Complex.rightSemicircleStaircasePrevSafeRe_ge_currentGraph hρ m k hk
  le_trans hprev hx.1

/-- If a horizontal connector coordinate is ordered from current-safe to
previous-safe, then it dominates the current graph value. -/
theorem Complex.rightSemicircleStaircaseHorizontal_re_ge_graph_of_safe_le
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1))
    {x : ℝ}
    (hx :
      Complex.rightSemicircleStaircaseSafeRe ρ m k ≤ x ∧
        x ≤ Complex.rightSemicircleStaircasePrevSafeRe ρ m k) :
    Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m k) ≤ x :=
  let hsafe :
      Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k) ≤
        Complex.rightSemicircleStaircaseSafeRe ρ m k :=
    Complex.rightSemicircleStaircaseSafeRe_ge_currentGraph hρ m k hk
  le_trans hsafe hx.1

/-- On a horizontal staircase connector, every real coordinate dominates the
circular graph at that height. -/
theorem Complex.rightSemicircleStaircaseHorizontal_re_ge_graph
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1))
    {x : ℝ}
    (hx :
      x ∈
        [[Complex.rightSemicircleStaircasePrevSafeRe ρ m k,
          Complex.rightSemicircleStaircaseSafeRe ρ m k]]) :
    Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m k) ≤ x :=
  match Set.mem_uIcc.mp hx with
  | Or.inl hx_prev =>
      Complex.rightSemicircleStaircaseHorizontal_re_ge_graph_of_prev_le
        hρ m k hk hx_prev
  | Or.inr hx_safe =>
      Complex.rightSemicircleStaircaseHorizontal_re_ge_graph_of_safe_le
        hρ m k hk hx_safe

end

end LFunctions
end Boundary
