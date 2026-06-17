import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleStaircaseMonotonicity

/-!
# Safe endpoint dominance for right semicircle staircases

This file owns the first endpoint domination estimate for the safe
right-semicircle staircase coordinate.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology Interval
open Filter MeasureTheory


/-- On a zero-crossing cell, the safe coordinate dominates the graph at the
left endpoint through the radius value. -/
theorem Complex.rightSemicircleStaircaseSafeRe_ge_left_endpoint_graph_of_crossing
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1))
    (hcross :
      Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1)) :
    Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m k) ≤
      Complex.rightSemicircleStaircaseSafeRe ρ m k := by
  have hgraph_radius :
      Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k) ≤ ρ :=
    Complex.rightSemicircleGraphRe_le_radius hρ
      (Complex.rightSemicircleStaircaseY_mem_Icc hρ m k
        (Complex.staircase_lower_sample_mem_range hk))
  have hsafe :
      Complex.rightSemicircleStaircaseSafeRe ρ m k = ρ :=
    Complex.rightSemicircleStaircaseSafeRe_eq_radius_of_crossing ρ m k hcross
  calc
    Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m k) ≤ ρ :=
      hgraph_radius
    _ = Complex.rightSemicircleStaircaseSafeRe ρ m k :=
      Eq.symm hsafe

/-- On a non-crossing cell, the safe coordinate dominates the graph at the
left endpoint through the endpoint maximum. -/
theorem Complex.rightSemicircleStaircaseSafeRe_ge_left_endpoint_graph_of_not_crossing
    (ρ : ℝ)
    (m k : ℕ)
    (hcross :
      ¬ (Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1))) :
    Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m k) ≤
      Complex.rightSemicircleStaircaseSafeRe ρ m k := by
  have hsafe :
      Complex.rightSemicircleStaircaseSafeRe ρ m k =
        max
          (Complex.rightSemicircleGraphRe ρ
            (Complex.rightSemicircleStaircaseY ρ m k))
          (Complex.rightSemicircleGraphRe ρ
            (Complex.rightSemicircleStaircaseY ρ m (k + 1))) :=
    Complex.rightSemicircleStaircaseSafeRe_eq_endpointMax_of_not_crossing ρ m k
      hcross
  calc
    Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m k) ≤
        max
          (Complex.rightSemicircleGraphRe ρ
            (Complex.rightSemicircleStaircaseY ρ m k))
          (Complex.rightSemicircleGraphRe ρ
            (Complex.rightSemicircleStaircaseY ρ m (k + 1))) :=
      le_max_left _ _
    _ = Complex.rightSemicircleStaircaseSafeRe ρ m k :=
      Eq.symm hsafe

/-- The safe coordinate dominates the graph at the left endpoint of its cell. -/
theorem Complex.rightSemicircleStaircaseSafeRe_ge_left_endpoint_graph
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1)) :
    Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m k) ≤
      Complex.rightSemicircleStaircaseSafeRe ρ m k :=
  let hcrossProp :=
      Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1)
  match Classical.em hcrossProp with
  | Or.inl hcross =>
      Complex.rightSemicircleStaircaseSafeRe_ge_left_endpoint_graph_of_crossing
        hρ m k hk hcross
  | Or.inr hcross =>
      Complex.rightSemicircleStaircaseSafeRe_ge_left_endpoint_graph_of_not_crossing
        ρ m k hcross

end

end LFunctions
end Boundary
