import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleStaircaseGraphBounds

/-!
# Safe-coordinate bounds for right semicircle staircases

This file owns the radius bounds for the safe staircase real coordinate and its
predecessor coordinate.  These bounds are the next dependency layer after the
vertical sample and graph endpoint estimates.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology Interval
open Filter MeasureTheory

/-- On a zero-crossing cell, the safe coordinate is nonnegative. -/
theorem Complex.rightSemicircleStaircaseSafeRe_nonneg_of_crossing
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
    (hcross :
      Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1)) :
    0 ≤ Complex.rightSemicircleStaircaseSafeRe ρ m k := by
  have hsafe :
      Complex.rightSemicircleStaircaseSafeRe ρ m k = ρ :=
    Complex.rightSemicircleStaircaseSafeRe_eq_radius_of_crossing ρ m k hcross
  calc
    0 ≤ ρ := hρ
    _ = Complex.rightSemicircleStaircaseSafeRe ρ m k := Eq.symm hsafe

/-- On a non-crossing cell, graph nonnegativity makes the safe coordinate
nonnegative. -/
theorem Complex.rightSemicircleStaircaseSafeRe_nonneg_of_not_crossing
    (ρ : ℝ)
    (m k : ℕ)
    (hcross :
      ¬ (Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1))) :
    0 ≤ Complex.rightSemicircleStaircaseSafeRe ρ m k := by
  have hlower :
      0 ≤
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k) :=
    Complex.rightSemicircleStaircaseGraphRe_lower_nonneg ρ m k
  have hmax :
      0 ≤
        max
          (Complex.rightSemicircleGraphRe ρ
            (Complex.rightSemicircleStaircaseY ρ m k))
          (Complex.rightSemicircleGraphRe ρ
            (Complex.rightSemicircleStaircaseY ρ m (k + 1))) :=
    le_max_of_le_left hlower
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
    0 ≤
        max
          (Complex.rightSemicircleGraphRe ρ
            (Complex.rightSemicircleStaircaseY ρ m k))
          (Complex.rightSemicircleGraphRe ρ
            (Complex.rightSemicircleStaircaseY ρ m (k + 1))) := hmax
    _ = Complex.rightSemicircleStaircaseSafeRe ρ m k := Eq.symm hsafe

/-- The safe staircase real coordinate is nonnegative. -/
theorem Complex.rightSemicircleStaircaseSafeRe_nonneg
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
    [Decidable
      (Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1))] :
    0 ≤ Complex.rightSemicircleStaircaseSafeRe ρ m k :=
  let hcrossProp :=
    Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
      0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1)
  match (inferInstance : Decidable hcrossProp) with
  | isTrue hcross =>
      Complex.rightSemicircleStaircaseSafeRe_nonneg_of_crossing hρ m k hcross
  | isFalse hcross =>
      Complex.rightSemicircleStaircaseSafeRe_nonneg_of_not_crossing ρ m k hcross

/-- On a zero-crossing cell, the safe coordinate is radius-bounded. -/
theorem Complex.rightSemicircleStaircaseSafeRe_le_radius_of_crossing
    (ρ : ℝ)
    (m k : ℕ)
    (hcross :
      Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1)) :
    Complex.rightSemicircleStaircaseSafeRe ρ m k ≤ ρ := by
  have hsafe :
      Complex.rightSemicircleStaircaseSafeRe ρ m k = ρ :=
    Complex.rightSemicircleStaircaseSafeRe_eq_radius_of_crossing ρ m k hcross
  calc
    Complex.rightSemicircleStaircaseSafeRe ρ m k = ρ := hsafe
    _ ≤ ρ := le_rfl

/-- On a non-crossing valid cell, endpoint graph bounds make the safe
coordinate radius-bounded. -/
theorem Complex.rightSemicircleStaircaseSafeRe_le_radius_of_not_crossing
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    {m k : ℕ}
    (hk : k ∈ Finset.range (m + 1))
    (hcross :
      ¬ (Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1))) :
    Complex.rightSemicircleStaircaseSafeRe ρ m k ≤ ρ := by
  have hlower :
      Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k) ≤ ρ :=
    Complex.rightSemicircleStaircaseGraphRe_lower_le_radius hρ hk
  have hupper :
      Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m (k + 1)) ≤ ρ :=
    Complex.rightSemicircleStaircaseGraphRe_upper_le_radius hρ hk
  have hmax :
      max
        (Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k))
        (Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m (k + 1))) ≤ ρ :=
    max_le hlower hupper
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
    _ ≤ ρ := hmax

/-- The safe staircase real coordinate in a valid cell is bounded by the
radius. -/
theorem Complex.rightSemicircleStaircaseSafeRe_le_radius
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    {m k : ℕ}
    [Decidable
      (Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1))]
    (hk : k ∈ Finset.range (m + 1)) :
    Complex.rightSemicircleStaircaseSafeRe ρ m k ≤ ρ :=
  let hcrossProp :=
    Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
      0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1)
  match (inferInstance : Decidable hcrossProp) with
  | isTrue hcross =>
      Complex.rightSemicircleStaircaseSafeRe_le_radius_of_crossing ρ m k hcross
  | isFalse hcross =>
      Complex.rightSemicircleStaircaseSafeRe_le_radius_of_not_crossing hρ hk
        hcross

/-- The safe staircase real coordinate lies in `[0,ρ]`. -/
theorem Complex.rightSemicircleStaircaseSafeRe_mem_Icc
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
    [Decidable
      (Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1))]
    (hk : k ∈ Finset.range (m + 1)) :
    Complex.rightSemicircleStaircaseSafeRe ρ m k ∈ [[(0 : ℝ), ρ]] := by
  have hleft :
      0 ≤ Complex.rightSemicircleStaircaseSafeRe ρ m k :=
    Complex.rightSemicircleStaircaseSafeRe_nonneg hρ m k
  have hright :
      Complex.rightSemicircleStaircaseSafeRe ρ m k ≤ ρ :=
    Complex.rightSemicircleStaircaseSafeRe_le_radius hρ hk
  have hIcc :
      Complex.rightSemicircleStaircaseSafeRe ρ m k ∈ Set.Icc (0 : ℝ) ρ :=
    And.intro hleft hright
  have huIcc :
      [[(0 : ℝ), ρ]] = Set.Icc (0 : ℝ) ρ :=
    Set.uIcc_of_le hρ
  exact huIcc.symm ▸ hIcc

/-- At the first cell, the predecessor safe coordinate is nonnegative. -/
theorem Complex.rightSemicircleStaircasePrevSafeRe_nonneg_of_zero
    (ρ : ℝ)
    (m : ℕ) :
    0 ≤ Complex.rightSemicircleStaircasePrevSafeRe ρ m 0 := by
  have hprev :
      Complex.rightSemicircleStaircasePrevSafeRe ρ m 0 = 0 :=
    Complex.rightSemicircleStaircasePrevSafeRe_zero_owner ρ m
  calc
    0 ≤ (0 : ℝ) := le_rfl
    _ = Complex.rightSemicircleStaircasePrevSafeRe ρ m 0 := Eq.symm hprev

/-- At a nonzero valid cell, predecessor nonnegativity follows from the
preceding safe coordinate. -/
theorem Complex.rightSemicircleStaircasePrevSafeRe_nonneg_of_ne_zero
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    {m k : ℕ}
    [Decidable
      (Complex.rightSemicircleStaircaseY ρ m (k - 1) ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m ((k - 1) + 1))]
    (hk0 : k ≠ 0) :
    0 ≤ Complex.rightSemicircleStaircasePrevSafeRe ρ m k := by
  have hsafe :
      0 ≤ Complex.rightSemicircleStaircaseSafeRe ρ m (k - 1) :=
    Complex.rightSemicircleStaircaseSafeRe_nonneg hρ m (k - 1)
  have hprev :
      Complex.rightSemicircleStaircasePrevSafeRe ρ m k =
        Complex.rightSemicircleStaircaseSafeRe ρ m (k - 1) :=
    Complex.rightSemicircleStaircasePrevSafeRe_eq_safeRe_pred_of_ne_zero ρ m k
      hk0
  calc
    0 ≤ Complex.rightSemicircleStaircaseSafeRe ρ m (k - 1) := hsafe
    _ = Complex.rightSemicircleStaircasePrevSafeRe ρ m k := Eq.symm hprev

/-- The predecessor safe coordinate is nonnegative in a valid cell. -/
theorem Complex.rightSemicircleStaircasePrevSafeRe_nonneg
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    {m k : ℕ}
    [Decidable (k = 0)]
    [Decidable
      (Complex.rightSemicircleStaircaseY ρ m (k - 1) ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m ((k - 1) + 1))]
    (_hk : k ∈ Finset.range (m + 1)) :
    0 ≤ Complex.rightSemicircleStaircasePrevSafeRe ρ m k :=
  match (inferInstance : Decidable (k = 0)) with
  | isTrue hk0 =>
      Eq.ndrec
        (motive := fun j : ℕ =>
          0 ≤ Complex.rightSemicircleStaircasePrevSafeRe ρ m j)
        (Complex.rightSemicircleStaircasePrevSafeRe_nonneg_of_zero ρ m)
        (Eq.symm hk0)
  | isFalse hk0 =>
      Complex.rightSemicircleStaircasePrevSafeRe_nonneg_of_ne_zero hρ hk0

/-- At the first cell, the predecessor safe coordinate is radius-bounded. -/
theorem Complex.rightSemicircleStaircasePrevSafeRe_le_radius_of_zero
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m : ℕ) :
    Complex.rightSemicircleStaircasePrevSafeRe ρ m 0 ≤ ρ := by
  have hprev :
      Complex.rightSemicircleStaircasePrevSafeRe ρ m 0 = 0 :=
    Complex.rightSemicircleStaircasePrevSafeRe_zero_owner ρ m
  calc
    Complex.rightSemicircleStaircasePrevSafeRe ρ m 0 = 0 := hprev
    _ ≤ ρ := hρ

/-- At a nonzero valid cell, predecessor radius-boundedness follows from the
preceding safe coordinate. -/
theorem Complex.rightSemicircleStaircasePrevSafeRe_le_radius_of_ne_zero
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    {m k : ℕ}
    [Decidable
      (Complex.rightSemicircleStaircaseY ρ m (k - 1) ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m ((k - 1) + 1))]
    (hk : k ∈ Finset.range (m + 1))
    (hk0 : k ≠ 0) :
    Complex.rightSemicircleStaircasePrevSafeRe ρ m k ≤ ρ := by
  have hk_pred : k - 1 ∈ Finset.range (m + 1) :=
    Complex.staircase_pred_mem_range_of_ne_zero hk hk0
  have hsafe :
      Complex.rightSemicircleStaircaseSafeRe ρ m (k - 1) ≤ ρ :=
    Complex.rightSemicircleStaircaseSafeRe_le_radius hρ hk_pred
  have hprev :
      Complex.rightSemicircleStaircasePrevSafeRe ρ m k =
        Complex.rightSemicircleStaircaseSafeRe ρ m (k - 1) :=
    Complex.rightSemicircleStaircasePrevSafeRe_eq_safeRe_pred_of_ne_zero ρ m k
      hk0
  calc
    Complex.rightSemicircleStaircasePrevSafeRe ρ m k =
        Complex.rightSemicircleStaircaseSafeRe ρ m (k - 1) := hprev
    _ ≤ ρ := hsafe

/-- The predecessor safe coordinate is radius-bounded in a valid cell. -/
theorem Complex.rightSemicircleStaircasePrevSafeRe_le_radius
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    {m k : ℕ}
    [Decidable (k = 0)]
    [Decidable
      (Complex.rightSemicircleStaircaseY ρ m (k - 1) ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m ((k - 1) + 1))]
    (hk : k ∈ Finset.range (m + 1)) :
    Complex.rightSemicircleStaircasePrevSafeRe ρ m k ≤ ρ :=
  match (inferInstance : Decidable (k = 0)) with
  | isTrue hk0 =>
      Eq.ndrec
        (motive := fun j : ℕ =>
          Complex.rightSemicircleStaircasePrevSafeRe ρ m j ≤ ρ)
        (Complex.rightSemicircleStaircasePrevSafeRe_le_radius_of_zero hρ m)
        (Eq.symm hk0)
  | isFalse hk0 =>
      Complex.rightSemicircleStaircasePrevSafeRe_le_radius_of_ne_zero hρ hk
        hk0

/-- The previous safe staircase real coordinate lies in `[0,ρ]`. -/
theorem Complex.rightSemicircleStaircasePrevSafeRe_mem_Icc
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
    [Decidable (k = 0)]
    [Decidable
      (Complex.rightSemicircleStaircaseY ρ m (k - 1) ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m ((k - 1) + 1))]
    (hk : k ∈ Finset.range (m + 1)) :
    Complex.rightSemicircleStaircasePrevSafeRe ρ m k ∈ [[(0 : ℝ), ρ]] := by
  have hleft :
      0 ≤ Complex.rightSemicircleStaircasePrevSafeRe ρ m k :=
    Complex.rightSemicircleStaircasePrevSafeRe_nonneg hρ hk
  have hright :
      Complex.rightSemicircleStaircasePrevSafeRe ρ m k ≤ ρ :=
    Complex.rightSemicircleStaircasePrevSafeRe_le_radius hρ hk
  have hIcc :
      Complex.rightSemicircleStaircasePrevSafeRe ρ m k ∈ Set.Icc (0 : ℝ) ρ :=
    And.intro hleft hright
  have huIcc :
      [[(0 : ℝ), ρ]] = Set.Icc (0 : ℝ) ρ :=
    Set.uIcc_of_le hρ
  exact huIcc.symm ▸ hIcc

/-- The last staircase cell index is valid for `Finset.range (m + 1)`. -/
theorem Complex.rightSemicircleStaircase_last_mem_range
    (m : ℕ) :
    m ∈ Finset.range (m + 1) := by
  exact Finset.mem_range.mpr (Nat.lt_succ_self m)

/-- The last safe staircase real coordinate lies in `[0,ρ]`. -/
theorem Complex.rightSemicircleStaircaseSafeRe_last_mem_Icc
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m : ℕ)
    [Decidable
      (Complex.rightSemicircleStaircaseY ρ m m ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (m + 1))] :
    Complex.rightSemicircleStaircaseSafeRe ρ m m ∈ [[(0 : ℝ), ρ]] :=
  Complex.rightSemicircleStaircaseSafeRe_mem_Icc hρ m m
    (Complex.rightSemicircleStaircase_last_mem_range m)

/-- The last safe staircase real coordinate is nonnegative. -/
theorem Complex.rightSemicircleStaircaseSafeRe_last_nonneg
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m : ℕ)
    [Decidable
      (Complex.rightSemicircleStaircaseY ρ m m ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (m + 1))] :
    0 ≤ Complex.rightSemicircleStaircaseSafeRe ρ m m :=
  Complex.rightSemicircleStaircaseSafeRe_nonneg hρ m m

/-- The last safe staircase real coordinate is bounded by the radius. -/
theorem Complex.rightSemicircleStaircaseSafeRe_last_le_radius
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m : ℕ)
    [Decidable
      (Complex.rightSemicircleStaircaseY ρ m m ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (m + 1))] :
    Complex.rightSemicircleStaircaseSafeRe ρ m m ≤ ρ :=
  Complex.rightSemicircleStaircaseSafeRe_le_radius hρ
    (Complex.rightSemicircleStaircase_last_mem_range m)

/-- The final top horizontal staircase connector has length at most the
radius. -/
theorem Complex.abs_top_sub_rightSemicircleStaircaseSafeRe_le_radius
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m : ℕ)
    [Decidable
      (Complex.rightSemicircleStaircaseY ρ m m ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (m + 1))] :
    |(0 : ℝ) - Complex.rightSemicircleStaircaseSafeRe ρ m m| ≤ ρ := by
  have hnonneg :
      0 ≤ Complex.rightSemicircleStaircaseSafeRe ρ m m :=
    Complex.rightSemicircleStaircaseSafeRe_last_nonneg hρ m
  have hle :
      Complex.rightSemicircleStaircaseSafeRe ρ m m ≤ ρ :=
    Complex.rightSemicircleStaircaseSafeRe_last_le_radius hρ m
  have hnorm :
      |(0 : ℝ) - Complex.rightSemicircleStaircaseSafeRe ρ m m| =
        Complex.rightSemicircleStaircaseSafeRe ρ m m := by
    calc
      |(0 : ℝ) - Complex.rightSemicircleStaircaseSafeRe ρ m m| =
          |-(Complex.rightSemicircleStaircaseSafeRe ρ m m)| := by
        exact congrArg abs (zero_sub (Complex.rightSemicircleStaircaseSafeRe ρ m m))
      _ = |Complex.rightSemicircleStaircaseSafeRe ρ m m| :=
        abs_neg (Complex.rightSemicircleStaircaseSafeRe ρ m m)
      _ = Complex.rightSemicircleStaircaseSafeRe ρ m m :=
        abs_of_nonneg hnonneg
  calc
    |(0 : ℝ) - Complex.rightSemicircleStaircaseSafeRe ρ m m| =
        Complex.rightSemicircleStaircaseSafeRe ρ m m := hnorm
    _ ≤ ρ := hle

/-- Adding a term bounded by `ρ` to a term bounded by `2ρ` is bounded by
`3ρ`. -/
theorem add_le_three_mul_of_le_two_mul_of_le
    {ρ a b : ℝ}
    (ha : a ≤ 2 * ρ)
    (hb : b ≤ ρ) :
    a + b ≤ 3 * ρ := by
  calc
    a + b ≤ 2 * ρ + ρ := add_le_add ha hb
    _ = 3 * ρ := Real.two_mul_add_self_eq_three_mul ρ

/-- Adding the final top connector to a radius-controlled horizontal jump
variation costs at most one more radius. -/
theorem Complex.rightSemicircleStaircaseSafeRe_totalHorizontalVariation_le_three_radius_of_core
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m : ℕ)
    (hcore :
      (∑ k in Finset.range (m + 1),
        |Complex.rightSemicircleStaircaseSafeRe ρ m k -
          Complex.rightSemicircleStaircasePrevSafeRe ρ m k|) ≤ 2 * ρ) :
    (∑ k in Finset.range (m + 1),
        |Complex.rightSemicircleStaircaseSafeRe ρ m k -
          Complex.rightSemicircleStaircasePrevSafeRe ρ m k|) +
      |(0 : ℝ) - Complex.rightSemicircleStaircaseSafeRe ρ m m| ≤ 3 * ρ := by
  have htop :
      |(0 : ℝ) - Complex.rightSemicircleStaircaseSafeRe ρ m m| ≤ ρ :=
    Complex.abs_top_sub_rightSemicircleStaircaseSafeRe_le_radius hρ m
  exact add_le_three_mul_of_le_two_mul_of_le hcore htop

end

end LFunctions
end Boundary
