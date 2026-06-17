import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleStaircaseCellGraph

/-!
# Witness points for safe right semicircle staircase cells

This file owns the point in each vertical cell where the safe staircase
coordinate is attained as a right-semicircle graph value.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology Interval
open Filter MeasureTheory

/-- The safe staircase real coordinate is the graph value at one point of its
own vertical cell.  In the crossing cell the witness is the midpoint height
`0`; otherwise it is one of the two cell endpoints. -/
theorem Complex.exists_rightSemicircleStaircaseSafeRe_eq_graphRe_of_cell
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m k : ℕ)
    (_hk : k ∈ Finset.range (m + 1)) :
    ∃ yₛ ∈
        [[Complex.rightSemicircleStaircaseY ρ m k,
          Complex.rightSemicircleStaircaseY ρ m (k + 1)]],
      Complex.rightSemicircleStaircaseSafeRe ρ m k =
        Complex.rightSemicircleGraphRe ρ yₛ :=
  let y₀ : ℝ := Complex.rightSemicircleStaircaseY ρ m k
  let y₁ : ℝ := Complex.rightSemicircleStaircaseY ρ m (k + 1)
  match Classical.em (y₀ ≤ 0 ∧ 0 ≤ y₁) with
  | Or.inl hcross =>
      let hmem : (0 : ℝ) ∈ [[y₀, y₁]] :=
        (Set.mem_uIcc).mpr
          (Or.inl (And.intro hcross.1 hcross.2))
      let hgraph_zero : Complex.rightSemicircleGraphRe ρ 0 = ρ :=
        Complex.rightSemicircleGraphRe_zero hρ.le
      let hvalue :
          Complex.rightSemicircleStaircaseSafeRe ρ m k =
            Complex.rightSemicircleGraphRe ρ 0 :=
        calc
          Complex.rightSemicircleStaircaseSafeRe ρ m k = ρ :=
            Complex.rightSemicircleStaircaseSafeRe_eq_radius_of_crossing
              ρ m k hcross
          _ = Complex.rightSemicircleGraphRe ρ 0 :=
            Eq.symm hgraph_zero
      Exists.intro 0 (And.intro hmem hvalue)
  | Or.inr hcross =>
      let hsafe_eq :
          Complex.rightSemicircleStaircaseSafeRe ρ m k =
            max
              (Complex.rightSemicircleGraphRe ρ y₀)
              (Complex.rightSemicircleGraphRe ρ y₁) :=
        Complex.rightSemicircleStaircaseSafeRe_eq_endpointMax_of_not_crossing
          ρ m k hcross
      match Classical.em
          (Complex.rightSemicircleGraphRe ρ y₀ ≤
            Complex.rightSemicircleGraphRe ρ y₁) with
      | Or.inl hmax =>
          let hvalue :
              Complex.rightSemicircleStaircaseSafeRe ρ m k =
                Complex.rightSemicircleGraphRe ρ y₁ :=
            calc
              Complex.rightSemicircleStaircaseSafeRe ρ m k =
                  max
                    (Complex.rightSemicircleGraphRe ρ y₀)
                    (Complex.rightSemicircleGraphRe ρ y₁) :=
                hsafe_eq
              _ = Complex.rightSemicircleGraphRe ρ y₁ :=
                max_eq_right hmax
          Exists.intro y₁ (And.intro Set.right_mem_uIcc hvalue)
      | Or.inr hmax =>
          let hvalue :
              Complex.rightSemicircleStaircaseSafeRe ρ m k =
                Complex.rightSemicircleGraphRe ρ y₀ :=
            calc
              Complex.rightSemicircleStaircaseSafeRe ρ m k =
                  max
                    (Complex.rightSemicircleGraphRe ρ y₀)
                    (Complex.rightSemicircleGraphRe ρ y₁) :=
                hsafe_eq
              _ = Complex.rightSemicircleGraphRe ρ y₀ :=
                max_eq_left (le_of_not_ge hmax)
          Exists.intro y₀ (And.intro Set.left_mem_uIcc hvalue)

/-- Points in one staircase height cell are separated by at most the cell
length. -/
theorem Complex.dist_le_rightSemicircleStaircase_cell_length_of_mem
    (ρ : ℝ)
    (m k : ℕ)
    {y y' : ℝ}
    (hy :
      y ∈
        [[Complex.rightSemicircleStaircaseY ρ m k,
          Complex.rightSemicircleStaircaseY ρ m (k + 1)]])
    (hy' :
      y' ∈
        [[Complex.rightSemicircleStaircaseY ρ m k,
          Complex.rightSemicircleStaircaseY ρ m (k + 1)]]) :
    dist y y' ≤
      |Complex.rightSemicircleStaircaseY ρ m (k + 1) -
        Complex.rightSemicircleStaircaseY ρ m k| :=
  dist_le_uIcc_length_of_mem hy hy'

end

end LFunctions
end Boundary
