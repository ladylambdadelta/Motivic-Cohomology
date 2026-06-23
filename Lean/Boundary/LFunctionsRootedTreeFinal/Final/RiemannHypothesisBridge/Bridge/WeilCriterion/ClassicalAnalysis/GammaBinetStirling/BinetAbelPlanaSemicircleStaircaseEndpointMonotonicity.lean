import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleStaircaseEndpointDominance

/-!
# Endpoint equalities and monotonicity for right semicircle staircases

This file owns the safe-coordinate endpoint identities and midpoint
monotonicity estimates for the right semicircle staircase.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology Interval
open Filter MeasureTheory


/-- On a crossing cell whose upper height is nonpositive, the upper endpoint
height is zero. -/
theorem Complex.rightSemicircleStaircase_upper_zero_of_crossing_of_upper_nonpos
    {ρ : ℝ}
    {m k : ℕ}
    (hupper :
      Complex.rightSemicircleStaircaseY ρ m (k + 1) ≤ 0)
    (hcross :
      Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1)) :
    Complex.rightSemicircleStaircaseY ρ m (k + 1) = 0 :=
  le_antisymm hupper hcross.2

/-- On a crossing cell whose lower height is nonnegative, the lower endpoint
height is zero. -/
theorem Complex.rightSemicircleStaircase_lower_zero_of_crossing_of_lower_nonneg
    {ρ : ℝ}
    {m k : ℕ}
    (hlower :
      0 ≤ Complex.rightSemicircleStaircaseY ρ m k)
    (hcross :
      Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1)) :
    Complex.rightSemicircleStaircaseY ρ m k = 0 :=
  le_antisymm hcross.1 hlower

/-- The right endpoint graph value is the radius when the crossing cell's
upper endpoint is forced to height zero. -/
theorem Complex.rightSemicircleStaircaseGraphRe_upper_eq_radius_of_crossing_of_upper_nonpos
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    {m k : ℕ}
    (hupper :
      Complex.rightSemicircleStaircaseY ρ m (k + 1) ≤ 0)
    (hcross :
      Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1)) :
    Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m (k + 1)) = ρ := by
  have hy1_zero :
      Complex.rightSemicircleStaircaseY ρ m (k + 1) = 0 :=
    Complex.rightSemicircleStaircase_upper_zero_of_crossing_of_upper_nonpos
      hupper hcross
  calc
    Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m (k + 1)) =
        Complex.rightSemicircleGraphRe ρ 0 :=
      congrArg (fun y : ℝ => Complex.rightSemicircleGraphRe ρ y) hy1_zero
    _ = ρ :=
      Complex.rightSemicircleGraphRe_zero hρ

/-- The left endpoint graph value is the radius when the crossing cell's lower
endpoint is forced to height zero. -/
theorem Complex.rightSemicircleStaircaseGraphRe_lower_eq_radius_of_crossing_of_lower_nonneg
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    {m k : ℕ}
    (hlower :
      0 ≤ Complex.rightSemicircleStaircaseY ρ m k)
    (hcross :
      Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1)) :
    Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m k) = ρ := by
  have hy0_zero :
      Complex.rightSemicircleStaircaseY ρ m k = 0 :=
    Complex.rightSemicircleStaircase_lower_zero_of_crossing_of_lower_nonneg
      hlower hcross
  calc
    Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m k) =
        Complex.rightSemicircleGraphRe ρ 0 :=
      congrArg (fun y : ℝ => Complex.rightSemicircleGraphRe ρ y) hy0_zero
    _ = ρ :=
      Complex.rightSemicircleGraphRe_zero hρ

/-- Crossing branch for the upper-nonpositive endpoint equality. -/
theorem Complex.rightSemicircleStaircaseSafeRe_eq_right_endpoint_of_upper_nonpos_of_crossing
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
    (hupper :
      Complex.rightSemicircleStaircaseY ρ m (k + 1) ≤ 0)
    (hcross :
      Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1)) :
    Complex.rightSemicircleStaircaseSafeRe ρ m k =
      Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m (k + 1)) := by
  have hsafe :
      Complex.rightSemicircleStaircaseSafeRe ρ m k = ρ :=
    Complex.rightSemicircleStaircaseSafeRe_eq_radius_of_crossing ρ m k hcross
  have hgraph :
      Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m (k + 1)) = ρ :=
    Complex.rightSemicircleStaircaseGraphRe_upper_eq_radius_of_crossing_of_upper_nonpos
      hρ hupper hcross
  calc
    Complex.rightSemicircleStaircaseSafeRe ρ m k = ρ := hsafe
    _ =
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m (k + 1)) :=
      Eq.symm hgraph

/-- Noncrossing branch for the upper-nonpositive endpoint equality. -/
theorem Complex.rightSemicircleStaircaseSafeRe_eq_right_endpoint_of_upper_nonpos_of_not_crossing
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
    (hupper :
      Complex.rightSemicircleStaircaseY ρ m (k + 1) ≤ 0)
    (hcross :
      ¬ (Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1))) :
    Complex.rightSemicircleStaircaseSafeRe ρ m k =
      Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m (k + 1)) := by
  have hy_le :
      Complex.rightSemicircleStaircaseY ρ m k ≤
        Complex.rightSemicircleStaircaseY ρ m (k + 1) :=
    Complex.rightSemicircleStaircaseY_le_succ hρ m k
  have hgraph_le :
      Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k) ≤
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m (k + 1)) :=
    Complex.rightSemicircleGraphRe_mono_nonpos ρ hy_le hupper
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
    Complex.rightSemicircleStaircaseSafeRe ρ m k =
        max
          (Complex.rightSemicircleGraphRe ρ
            (Complex.rightSemicircleStaircaseY ρ m k))
          (Complex.rightSemicircleGraphRe ρ
            (Complex.rightSemicircleStaircaseY ρ m (k + 1))) := hsafe
    _ =
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m (k + 1)) :=
      max_eq_right hgraph_le

/-- On a cell whose upper height is nonpositive, the safe coordinate is the
right endpoint graph value. -/
theorem Complex.rightSemicircleStaircaseSafeRe_eq_right_endpoint_of_upper_nonpos
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
    [Decidable
      (Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1))]
    (hupper :
      Complex.rightSemicircleStaircaseY ρ m (k + 1) ≤ 0) :
    Complex.rightSemicircleStaircaseSafeRe ρ m k =
      Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m (k + 1)) :=
  let hcrossProp :=
      Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1)
  match (inferInstance : Decidable hcrossProp) with
  | isTrue hcross =>
      Complex.rightSemicircleStaircaseSafeRe_eq_right_endpoint_of_upper_nonpos_of_crossing
        hρ m k hupper hcross
  | isFalse hcross =>
      Complex.rightSemicircleStaircaseSafeRe_eq_right_endpoint_of_upper_nonpos_of_not_crossing
        hρ m k hupper hcross

/-- Crossing branch for the lower-nonnegative endpoint equality. -/
theorem Complex.rightSemicircleStaircaseSafeRe_eq_left_endpoint_of_lower_nonneg_of_crossing
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
    (hlower :
      0 ≤ Complex.rightSemicircleStaircaseY ρ m k)
    (hcross :
      Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1)) :
    Complex.rightSemicircleStaircaseSafeRe ρ m k =
      Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m k) := by
  have hsafe :
      Complex.rightSemicircleStaircaseSafeRe ρ m k = ρ :=
    Complex.rightSemicircleStaircaseSafeRe_eq_radius_of_crossing ρ m k hcross
  have hgraph :
      Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k) = ρ :=
    Complex.rightSemicircleStaircaseGraphRe_lower_eq_radius_of_crossing_of_lower_nonneg
      hρ hlower hcross
  calc
    Complex.rightSemicircleStaircaseSafeRe ρ m k = ρ := hsafe
    _ =
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k) :=
      Eq.symm hgraph

/-- Noncrossing branch for the lower-nonnegative endpoint equality. -/
theorem Complex.rightSemicircleStaircaseSafeRe_eq_left_endpoint_of_lower_nonneg_of_not_crossing
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
    (hlower :
      0 ≤ Complex.rightSemicircleStaircaseY ρ m k)
    (hcross :
      ¬ (Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1))) :
    Complex.rightSemicircleStaircaseSafeRe ρ m k =
      Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m k) := by
  have hy_le :
      Complex.rightSemicircleStaircaseY ρ m k ≤
        Complex.rightSemicircleStaircaseY ρ m (k + 1) :=
    Complex.rightSemicircleStaircaseY_le_succ hρ m k
  have hgraph_le :
      Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m (k + 1)) ≤
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k) :=
    Complex.rightSemicircleGraphRe_antitone_nonneg ρ hlower hy_le
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
    Complex.rightSemicircleStaircaseSafeRe ρ m k =
        max
          (Complex.rightSemicircleGraphRe ρ
            (Complex.rightSemicircleStaircaseY ρ m k))
          (Complex.rightSemicircleGraphRe ρ
            (Complex.rightSemicircleStaircaseY ρ m (k + 1))) := hsafe
    _ =
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k) :=
      max_eq_left hgraph_le

/-- On a cell whose lower height is nonnegative, the safe coordinate is the
left endpoint graph value. -/
theorem Complex.rightSemicircleStaircaseSafeRe_eq_left_endpoint_of_lower_nonneg
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
    [Decidable
      (Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1))]
    (hlower :
      0 ≤ Complex.rightSemicircleStaircaseY ρ m k) :
    Complex.rightSemicircleStaircaseSafeRe ρ m k =
      Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m k) :=
  let hcrossProp :=
      Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1)
  match (inferInstance : Decidable hcrossProp) with
  | isTrue hcross =>
      Complex.rightSemicircleStaircaseSafeRe_eq_left_endpoint_of_lower_nonneg_of_crossing
        hρ m k hlower hcross
  | isFalse hcross =>
      Complex.rightSemicircleStaircaseSafeRe_eq_left_endpoint_of_lower_nonneg_of_not_crossing
        hρ m k hlower hcross

/-- The safe right-semicircle staircase real coordinates increase up to the
height cell containing the midpoint height `0`. -/
theorem Complex.rightSemicircleStaircaseSafeRe_monotone_prefix_midpoint
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m : ℕ)
    [∀ k : ℕ, Decidable
      (Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1))] :
    ∀ k : ℕ, k < (m + 1) / 2 →
      Complex.rightSemicircleStaircaseSafeRe ρ m k ≤
        Complex.rightSemicircleStaircaseSafeRe ρ m (k + 1) := by
  intro k hk
  have hk_succ_le_mid : k + 1 ≤ (m + 1) / 2 :=
    Nat.succ_le_of_lt hk
  have hy_succ_nonpos :
      Complex.rightSemicircleStaircaseY ρ m (k + 1) ≤ 0 :=
    Complex.rightSemicircleStaircaseY_nonpos_of_le_midpoint
      hρ hk_succ_le_mid
  have hsafe_left :
      Complex.rightSemicircleStaircaseSafeRe ρ m k =
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m (k + 1)) :=
    Complex.rightSemicircleStaircaseSafeRe_eq_right_endpoint_of_upper_nonpos
      hρ m k hy_succ_nonpos
  have hk1_range : k + 1 ∈ Finset.range (m + 1) := by
    have hhalf_lt : (m + 1) / 2 < m + 1 :=
      Nat.div_lt_self (Nat.succ_pos m) Nat.one_lt_two
    exact Finset.mem_range.mpr (lt_of_le_of_lt hk_succ_le_mid hhalf_lt)
  have hsafe_right :
      Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m (k + 1)) ≤
        Complex.rightSemicircleStaircaseSafeRe ρ m (k + 1) :=
    Complex.rightSemicircleStaircaseSafeRe_ge_left_endpoint_graph
      hρ m (k + 1) hk1_range
  exact
    Eq.mp
      (congrArg
        (fun x : ℝ => x ≤ Complex.rightSemicircleStaircaseSafeRe ρ m (k + 1))
        (Eq.symm hsafe_left))
      hsafe_right

/-- If the upper endpoint is nonnegative and a cell is not a crossing cell,
then the lower endpoint is nonnegative. -/
theorem Complex.rightSemicircleStaircaseY_nonneg_of_not_crossing_of_succ_nonneg
    {ρ : ℝ}
    {m k : ℕ}
    [Decidable (Complex.rightSemicircleStaircaseY ρ m k ≤ 0)]
    (hy_succ_nonneg :
      0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1))
    (hcross :
      ¬ (Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1))) :
    0 ≤ Complex.rightSemicircleStaircaseY ρ m k :=
  match (inferInstance : Decidable (Complex.rightSemicircleStaircaseY ρ m k ≤ 0)) with
  | isTrue hy_nonpos =>
      False.elim (hcross (And.intro hy_nonpos hy_succ_nonneg))
  | isFalse hy_not_nonpos =>
      le_of_not_ge hy_not_nonpos

/-- Crossing branch for the antitone suffix of the safe staircase coordinate. -/
theorem Complex.rightSemicircleStaircaseSafeRe_antitone_suffix_midpoint_of_crossing
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    {m k : ℕ}
    (hkm : k < m)
    (hcross :
      Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1)) :
    Complex.rightSemicircleStaircaseSafeRe ρ m (k + 1) ≤
      Complex.rightSemicircleStaircaseSafeRe ρ m k := by
  have hk1_range : k + 1 ∈ Finset.range (m + 1) :=
    Finset.mem_range.mpr (Nat.succ_lt_succ hkm)
  have hright_le :
      Complex.rightSemicircleStaircaseSafeRe ρ m (k + 1) ≤ ρ :=
    Complex.rightSemicircleStaircaseSafeRe_le_radius hρ hk1_range
  have hleft :
      Complex.rightSemicircleStaircaseSafeRe ρ m k = ρ :=
    Complex.rightSemicircleStaircaseSafeRe_eq_radius_of_crossing ρ m k hcross
  calc
    Complex.rightSemicircleStaircaseSafeRe ρ m (k + 1) ≤ ρ := hright_le
    _ = Complex.rightSemicircleStaircaseSafeRe ρ m k := Eq.symm hleft

/-- Noncrossing branch for the antitone suffix of the safe staircase
coordinate. -/
theorem Complex.rightSemicircleStaircaseSafeRe_antitone_suffix_midpoint_of_not_crossing
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
    [Decidable (Complex.rightSemicircleStaircaseY ρ m k ≤ 0)]
    [Decidable
      (Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1))]
    [Decidable
      (Complex.rightSemicircleStaircaseY ρ m (k + 1) ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 2))]
    (hy_succ_nonneg :
      0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1))
    (hcross :
      ¬ (Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1))) :
    Complex.rightSemicircleStaircaseSafeRe ρ m (k + 1) ≤
      Complex.rightSemicircleStaircaseSafeRe ρ m k := by
  have hy_nonneg :
      0 ≤ Complex.rightSemicircleStaircaseY ρ m k :=
    Complex.rightSemicircleStaircaseY_nonneg_of_not_crossing_of_succ_nonneg
      hy_succ_nonneg hcross
  have hsafe_left :
      Complex.rightSemicircleStaircaseSafeRe ρ m k =
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k) :=
    Complex.rightSemicircleStaircaseSafeRe_eq_left_endpoint_of_lower_nonneg
      hρ m k hy_nonneg
  have hsafe_right :
      Complex.rightSemicircleStaircaseSafeRe ρ m (k + 1) =
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m (k + 1)) :=
    Complex.rightSemicircleStaircaseSafeRe_eq_left_endpoint_of_lower_nonneg
      hρ m (k + 1) hy_succ_nonneg
  have hy_le :
      Complex.rightSemicircleStaircaseY ρ m k ≤
        Complex.rightSemicircleStaircaseY ρ m (k + 1) :=
    Complex.rightSemicircleStaircaseY_le_succ hρ m k
  have hgraph :
      Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m (k + 1)) ≤
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k) :=
    Complex.rightSemicircleGraphRe_antitone_nonneg ρ hy_nonneg hy_le
  have hright_transport :
      Complex.rightSemicircleStaircaseSafeRe ρ m (k + 1) ≤
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k) :=
    Eq.mp
      (congrArg
        (fun x : ℝ =>
          x ≤
            Complex.rightSemicircleGraphRe ρ
              (Complex.rightSemicircleStaircaseY ρ m k))
        (Eq.symm hsafe_right))
      hgraph
  exact
    Eq.mp
      (congrArg
        (fun x : ℝ =>
          Complex.rightSemicircleStaircaseSafeRe ρ m (k + 1) ≤ x)
        (Eq.symm hsafe_left))
      hright_transport

/-- The safe right-semicircle staircase real coordinates decrease after the
height cell containing the midpoint height `0`. -/
theorem Complex.rightSemicircleStaircaseSafeRe_antitone_suffix_midpoint
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m : ℕ)
    [∀ k : ℕ, Decidable
      (Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1))]
    [∀ k : ℕ, Decidable (Complex.rightSemicircleStaircaseY ρ m k ≤ 0)] :
    ∀ k : ℕ, (m + 1) / 2 ≤ k → k < m →
      Complex.rightSemicircleStaircaseSafeRe ρ m (k + 1) ≤
        Complex.rightSemicircleStaircaseSafeRe ρ m k :=
  fun k hmid_le_k hkm =>
  let hy_succ_nonneg :
      0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1) :=
    Complex.rightSemicircleStaircaseY_succ_nonneg_of_midpoint_le
      hρ hmid_le_k
  let hcrossProp :=
      Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1)
  match (inferInstance : Decidable hcrossProp) with
  | isTrue hcross =>
      Complex.rightSemicircleStaircaseSafeRe_antitone_suffix_midpoint_of_crossing
        hρ hkm hcross
  | isFalse hcross =>
      Complex.rightSemicircleStaircaseSafeRe_antitone_suffix_midpoint_of_not_crossing
        hρ m k hy_succ_nonneg hcross

end

end LFunctions
end Boundary
