import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleStaircaseEndpointGraph

/-!
# Cell graph bounds for right semicircle staircases

This file owns the interval-containment and one-cell graph estimates that bound
the circular graph by the safe staircase coordinate on each vertical cell.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology Interval
open Filter MeasureTheory

/-- A point in an unordered interval between two points of the radius interval
also lies in the radius interval. -/
theorem Real.mem_radius_uIcc_of_endpoint_mem_of_mem
    {ρ y₀ y₁ y : ℝ}
    (hρ : 0 ≤ ρ)
    (hy₀ : y₀ ∈ [[-ρ, ρ]])
    (hy₁ : y₁ ∈ [[-ρ, ρ]])
    (hy : y ∈ [[y₀, y₁]]) :
    y ∈ [[-ρ, ρ]] :=
  let hy₀_bounds : -ρ ≤ y₀ ∧ y₀ ≤ ρ :=
    Real.bounds_of_mem_uIcc
      (Complex.neg_radius_le_radius hρ)
      hy₀
  let hy₁_bounds : -ρ ≤ y₁ ∧ y₁ ≤ ρ :=
    Real.bounds_of_mem_uIcc
      (Complex.neg_radius_le_radius hρ)
      hy₁
  match Set.mem_uIcc.mp hy with
  | Or.inl hy_pair =>
      let hleft : -ρ ≤ y := le_trans hy₀_bounds.1 hy_pair.1
      let hright : y ≤ ρ := le_trans hy_pair.2 hy₁_bounds.2
      Real.mem_uIcc_of_bounds
        (Complex.neg_radius_le_radius hρ)
        (And.intro hleft hright)
  | Or.inr hy_pair =>
      let hleft : -ρ ≤ y := le_trans hy₁_bounds.1 hy_pair.1
      let hright : y ≤ ρ := le_trans hy_pair.2 hy₀_bounds.2
      Real.mem_uIcc_of_bounds
        (Complex.neg_radius_le_radius hρ)
        (And.intro hleft hright)

/-- If an ordered pair of endpoints does not cross zero, then both endpoints
are on one side of zero. -/
theorem same_side_of_not_crossing
    {y₀ y₁ : ℝ}
    (hcross : ¬ (y₀ ≤ 0 ∧ 0 ≤ y₁)) :
    y₁ ≤ 0 ∨ 0 ≤ y₀ :=
  match le_total y₁ 0 with
  | Or.inl hy₁_nonpos => Or.inl hy₁_nonpos
  | Or.inr h0_le_y₁ =>
      match le_total y₀ 0 with
      | Or.inl hy₀_nonpos =>
          False.elim (hcross (And.intro hy₀_nonpos h0_le_y₁))
      | Or.inr h0_le_y₀ => Or.inr h0_le_y₀

/-- On a nonpositive interval, the absolute value at an interior point is at
least the smaller endpoint absolute value. -/
theorem abs_min_le_of_nonpos_mem_uIcc
    {y₀ y₁ y : ℝ}
    (horder : y₀ ≤ y₁)
    (hy_pair : (y₀ ≤ y ∧ y ≤ y₁) ∨ (y₁ ≤ y ∧ y ≤ y₀))
    (hy₁_nonpos : y₁ ≤ 0) :
    min |y₀| |y₁| ≤ |y| :=
  match hy_pair with
  | Or.inl hy_bounds =>
      let hy_nonpos : y ≤ 0 := le_trans hy_bounds.2 hy₁_nonpos
      let hendpoint : |y₁| ≤ |y| :=
        calc
          |y₁| = -y₁ := abs_of_nonpos hy₁_nonpos
          _ ≤ -y := neg_le_neg hy_bounds.2
          _ = |y| := Eq.symm (abs_of_nonpos hy_nonpos)
      le_trans (min_le_right |y₀| |y₁|) hendpoint
  | Or.inr hy_bounds =>
      let hy₀_nonpos : y₀ ≤ 0 := le_trans horder hy₁_nonpos
      let hy_nonpos : y ≤ 0 := le_trans hy_bounds.2 hy₀_nonpos
      let hendpoint : |y₀| ≤ |y| :=
        calc
          |y₀| = -y₀ := abs_of_nonpos hy₀_nonpos
          _ ≤ -y := neg_le_neg hy_bounds.2
          _ = |y| := Eq.symm (abs_of_nonpos hy_nonpos)
      le_trans (min_le_left |y₀| |y₁|) hendpoint

/-- On a nonnegative interval, the absolute value at an interior point is at
least the smaller endpoint absolute value. -/
theorem abs_min_le_of_nonneg_mem_uIcc
    {y₀ y₁ y : ℝ}
    (horder : y₀ ≤ y₁)
    (hy_pair : (y₀ ≤ y ∧ y ≤ y₁) ∨ (y₁ ≤ y ∧ y ≤ y₀))
    (hy₀_nonneg : 0 ≤ y₀) :
    min |y₀| |y₁| ≤ |y| :=
  match hy_pair with
  | Or.inl hy_bounds =>
      let hy_nonneg : 0 ≤ y := le_trans hy₀_nonneg hy_bounds.1
      let hendpoint : |y₀| ≤ |y| :=
        calc
          |y₀| = y₀ := abs_of_nonneg hy₀_nonneg
          _ ≤ y := hy_bounds.1
          _ = |y| := Eq.symm (abs_of_nonneg hy_nonneg)
      le_trans (min_le_left |y₀| |y₁|) hendpoint
  | Or.inr hy_bounds =>
      let hy₁_nonneg : 0 ≤ y₁ := le_trans hy₀_nonneg horder
      let hy_nonneg : 0 ≤ y := le_trans hy₁_nonneg hy_bounds.1
      let hendpoint : |y₁| ≤ |y| :=
        calc
          |y₁| = y₁ := abs_of_nonneg hy₁_nonneg
          _ ≤ y := hy_bounds.1
          _ = |y| := Eq.symm (abs_of_nonneg hy_nonneg)
      le_trans (min_le_right |y₀| |y₁|) hendpoint

/-- Absolute-value endpoint dominance implies the squared-distance dominance
used by the endpoint graph bound. -/
theorem min_endpoint_sq_le_sq_of_abs_min_le
    {y₀ y₁ y : ℝ}
    [Decidable (|y₀| ≤ |y₁|)]
    (habs : min |y₀| |y₁| ≤ |y|) :
    min (y₀ ^ 2) (y₁ ^ 2) ≤ y ^ 2 :=
  let hmin_abs_nonneg : 0 ≤ min |y₀| |y₁| :=
    le_min (abs_nonneg y₀) (abs_nonneg y₁)
  let habs_sq : min |y₀| |y₁| ^ 2 ≤ |y| ^ 2 :=
    pow_le_pow_left₀ hmin_abs_nonneg habs 2
  let hmin_sq : min (y₀ ^ 2) (y₁ ^ 2) = min |y₀| |y₁| ^ 2 :=
    min_sq_eq_min_abs_sq y₀ y₁
  let hy_sq_abs : y ^ 2 = |y| ^ 2 :=
    Eq.symm (sq_abs y)
  calc
    min (y₀ ^ 2) (y₁ ^ 2) = min |y₀| |y₁| ^ 2 := hmin_sq
    _ ≤ |y| ^ 2 := habs_sq
    _ = y ^ 2 := Eq.symm hy_sq_abs

/-- Crossing cells are bounded by the radius branch of the safe coordinate. -/
theorem Complex.rightSemicircleGraphRe_le_safeRe_of_mem_cell_crossing
    {ρ y₀ y₁ y : ℝ}
    [hcross_dec : Decidable (y₀ ≤ 0 ∧ 0 ≤ y₁)]
    (hρ : 0 ≤ ρ)
    (hy₀ : y₀ ∈ [[-ρ, ρ]])
    (hy₁ : y₁ ∈ [[-ρ, ρ]])
    (hy : y ∈ [[y₀, y₁]])
    (hcross : y₀ ≤ 0 ∧ 0 ≤ y₁) :
    Complex.rightSemicircleGraphRe ρ y ≤
      @ite ℝ (y₀ ≤ 0 ∧ 0 ≤ y₁) hcross_dec
      ρ
      (
        max (Complex.rightSemicircleGraphRe ρ y₀)
          (Complex.rightSemicircleGraphRe ρ y₁)) :=
  let hif :
      @ite ℝ (y₀ ≤ 0 ∧ 0 ≤ y₁) hcross_dec
        ρ
        (
          max (Complex.rightSemicircleGraphRe ρ y₀)
            (Complex.rightSemicircleGraphRe ρ y₁)) = ρ :=
    if_pos hcross
  let hy_bounds : y ∈ [[-ρ, ρ]] :=
    Real.mem_radius_uIcc_of_endpoint_mem_of_mem hρ hy₀ hy₁ hy
  let hgraph_le : Complex.rightSemicircleGraphRe ρ y ≤ ρ :=
    Complex.rightSemicircleGraphRe_le_radius hρ hy_bounds
  calc
    Complex.rightSemicircleGraphRe ρ y ≤ ρ := hgraph_le
    _ = @ite ℝ (y₀ ≤ 0 ∧ 0 ≤ y₁) hcross_dec
        ρ
        (
          max (Complex.rightSemicircleGraphRe ρ y₀)
            (Complex.rightSemicircleGraphRe ρ y₁)) := Eq.symm hif

/-- Noncrossing cells are bounded by the endpoint graph maximum branch of the
safe coordinate. -/
theorem Complex.rightSemicircleGraphRe_le_safeRe_of_mem_cell_not_crossing
    {ρ y₀ y₁ y : ℝ}
    [hcross_dec : Decidable (y₀ ≤ 0 ∧ 0 ≤ y₁)]
    [Decidable (|y₀| ≤ |y₁|)]
    [Decidable (y₀ ^ 2 ≤ y₁ ^ 2)]
    [Decidable (ρ ^ 2 - y₀ ^ 2 ≤ ρ ^ 2 - y₁ ^ 2)]
    (horder : y₀ ≤ y₁)
    (hcross : ¬ (y₀ ≤ 0 ∧ 0 ≤ y₁))
    (hy : y ∈ [[y₀, y₁]]) :
    Complex.rightSemicircleGraphRe ρ y ≤
      @ite ℝ (y₀ ≤ 0 ∧ 0 ≤ y₁) hcross_dec
      ρ
      (
        max (Complex.rightSemicircleGraphRe ρ y₀)
          (Complex.rightSemicircleGraphRe ρ y₁)) :=
  let hif :
      @ite ℝ (y₀ ≤ 0 ∧ 0 ≤ y₁) hcross_dec
        ρ
        (
          max (Complex.rightSemicircleGraphRe ρ y₀)
            (Complex.rightSemicircleGraphRe ρ y₁)) =
        max (Complex.rightSemicircleGraphRe ρ y₀)
          (Complex.rightSemicircleGraphRe ρ y₁) :=
    if_neg hcross
  let hy_pair : (y₀ ≤ y ∧ y ≤ y₁) ∨ (y₁ ≤ y ∧ y ≤ y₀) :=
    Set.mem_uIcc.mp hy
  let hsame_side : y₁ ≤ 0 ∨ 0 ≤ y₀ :=
    same_side_of_not_crossing hcross
  let h_abs_le_endpoint : min |y₀| |y₁| ≤ |y| :=
    match hsame_side with
    | Or.inl hnonpos =>
        abs_min_le_of_nonpos_mem_uIcc horder hy_pair hnonpos
    | Or.inr hnonneg =>
        abs_min_le_of_nonneg_mem_uIcc horder hy_pair hnonneg
  let hsq_ge : min (y₀ ^ 2) (y₁ ^ 2) ≤ y ^ 2 :=
    min_endpoint_sq_le_sq_of_abs_min_le h_abs_le_endpoint
  let hgraph :
      Complex.rightSemicircleGraphRe ρ y ≤
        max (Complex.rightSemicircleGraphRe ρ y₀)
          (Complex.rightSemicircleGraphRe ρ y₁) :=
    Complex.rightSemicircleGraphRe_le_endpointMax_of_min_sq_le
      ρ y₀ y₁ y hsq_ge
  calc
    Complex.rightSemicircleGraphRe ρ y ≤
        max (Complex.rightSemicircleGraphRe ρ y₀)
          (Complex.rightSemicircleGraphRe ρ y₁) := hgraph
    _ = @ite ℝ (y₀ ≤ 0 ∧ 0 ≤ y₁) hcross_dec
        ρ
        (
          max (Complex.rightSemicircleGraphRe ρ y₀)
            (Complex.rightSemicircleGraphRe ρ y₁)) := Eq.symm hif

/-- The safe staircase real coordinate dominates the circular graph on its
vertical cell. -/
theorem Complex.rightSemicircleStaircaseSafeRe_ge_graph_on_cell
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1))
    [hcross_dec : Decidable
      (Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1))]
    [Decidable
      (|Complex.rightSemicircleStaircaseY ρ m k| ≤
        |Complex.rightSemicircleStaircaseY ρ m (k + 1)|)]
    [Decidable
      (Complex.rightSemicircleStaircaseY ρ m k ^ 2 ≤
        Complex.rightSemicircleStaircaseY ρ m (k + 1) ^ 2)]
    [Decidable
      (ρ ^ 2 - Complex.rightSemicircleStaircaseY ρ m k ^ 2 ≤
        ρ ^ 2 - Complex.rightSemicircleStaircaseY ρ m (k + 1) ^ 2)]
    {y : ℝ}
    (hy :
      y ∈
        [[Complex.rightSemicircleStaircaseY ρ m k,
          Complex.rightSemicircleStaircaseY ρ m (k + 1)]]) :
    Complex.rightSemicircleGraphRe ρ y ≤
      Complex.rightSemicircleStaircaseSafeRe ρ m k :=
  let y₀ : ℝ := Complex.rightSemicircleStaircaseY ρ m k
  let y₁ : ℝ := Complex.rightSemicircleStaircaseY ρ m (k + 1)
  let hk0 : k ∈ Finset.range (m + 2) :=
    Complex.staircase_lower_sample_mem_range hk
  let hk1 : k + 1 ∈ Finset.range (m + 2) :=
    Complex.staircase_upper_sample_mem_range hk
  let hy0 : y₀ ∈ [[-ρ, ρ]] :=
    Complex.rightSemicircleStaircaseY_mem_Icc hρ m k hk0
  let hy1 : y₁ ∈ [[-ρ, ρ]] :=
    Complex.rightSemicircleStaircaseY_mem_Icc hρ m (k + 1) hk1
  let horder : y₀ ≤ y₁ :=
    Complex.rightSemicircleStaircaseY_le_succ hρ m k
  match hcross_dec with
  | isTrue hcross =>
      have hgraph :
          Complex.rightSemicircleGraphRe ρ y ≤ ρ :=
        let hy_bounds : y ∈ [[-ρ, ρ]] :=
          Real.mem_radius_uIcc_of_endpoint_mem_of_mem hρ hy0 hy1 hy
        Complex.rightSemicircleGraphRe_le_radius hρ hy_bounds
      have hsafe :
          Complex.rightSemicircleStaircaseSafeRe ρ m k = ρ :=
        Complex.rightSemicircleStaircaseSafeRe_eq_radius_of_crossing
          ρ m k hcross
      Eq.subst
        (motive := fun r : ℝ => Complex.rightSemicircleGraphRe ρ y ≤ r)
        hsafe.symm
        hgraph
  | isFalse hcross =>
      have hgraph :
          Complex.rightSemicircleGraphRe ρ y ≤
            max (Complex.rightSemicircleGraphRe ρ y₀)
              (Complex.rightSemicircleGraphRe ρ y₁) :=
        let hy_pair : (y₀ ≤ y ∧ y ≤ y₁) ∨ (y₁ ≤ y ∧ y ≤ y₀) :=
          Set.mem_uIcc.mp hy
        let hsame_side : y₁ ≤ 0 ∨ 0 ≤ y₀ :=
          same_side_of_not_crossing hcross
        let h_abs_le_endpoint : min |y₀| |y₁| ≤ |y| :=
          match hsame_side with
          | Or.inl hnonpos =>
              abs_min_le_of_nonpos_mem_uIcc horder hy_pair hnonpos
          | Or.inr hnonneg =>
              abs_min_le_of_nonneg_mem_uIcc horder hy_pair hnonneg
        let hsq_ge : min (y₀ ^ 2) (y₁ ^ 2) ≤ y ^ 2 :=
          min_endpoint_sq_le_sq_of_abs_min_le h_abs_le_endpoint
        Complex.rightSemicircleGraphRe_le_endpointMax_of_min_sq_le
          ρ y₀ y₁ y hsq_ge
      have hsafe :
          Complex.rightSemicircleStaircaseSafeRe ρ m k =
            max (Complex.rightSemicircleGraphRe ρ y₀)
              (Complex.rightSemicircleGraphRe ρ y₁) :=
        Complex.rightSemicircleStaircaseSafeRe_eq_endpointMax_of_not_crossing
          ρ m k hcross
      Eq.subst
        (motive := fun r : ℝ => Complex.rightSemicircleGraphRe ρ y ≤ r)
        hsafe.symm
        hgraph

end

end LFunctions
end Boundary
