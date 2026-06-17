import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleStaircaseIntervals

/-!
# Graph and sample bounds for right semicircle staircases

This file owns the vertical sample bounds, circular graph endpoint bounds, and
basic staircase index-range transport used by the right semicircle staircase.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology Interval
open Filter MeasureTheory

/-- The square of zero over the reals is zero. -/
theorem Real.zero_sq_eq_zero :
    (0 : ℝ) ^ 2 = 0 := by
  calc
    (0 : ℝ) ^ 2 = (0 : ℝ) * 0 := sq (0 : ℝ)
    _ = 0 := zero_mul 0

/-- A nonnegative real is equal to its absolute value. -/
theorem Real.eq_abs_of_nonneg
    {x : ℝ}
    (hx : 0 ≤ x) :
    x = |x| :=
  Eq.symm (abs_of_nonneg hx)

/-- The square root of the square of a nonnegative real is that real. -/
theorem Real.sqrt_sq_of_nonneg_explicit
    {x : ℝ}
    (hx : 0 ≤ x) :
    Real.sqrt (x ^ 2) = x := by
  calc
    Real.sqrt (x ^ 2) = Real.sqrt (x * x) := by
      exact congrArg Real.sqrt (sq x)
    _ = x := Real.sqrt_mul_self hx

/-- The real ratio attached to a staircase sample is nonnegative. -/
theorem Complex.rightSemicircleStaircaseY_ratio_nonneg
    (m k : ℕ) :
    0 ≤ (k : ℝ) / (m + 1 : ℝ) := by
  have hden_pos : 0 < (m + 1 : ℝ) :=
    Real.rightSemicircleStaircase_denominator_pos m
  exact div_nonneg (Nat.cast_nonneg k) hden_pos.le

/-- The real ratio attached to an in-range staircase sample is at most one. -/
theorem Complex.rightSemicircleStaircaseY_ratio_le_one
    {m k : ℕ}
    (hk : k ∈ Finset.range (m + 2)) :
    (k : ℝ) / (m + 1 : ℝ) ≤ 1 := by
  have hk_lt : k < m + 2 := by
    exact Finset.mem_range.mp hk
  have hk_nat : k ≤ m + 1 := Nat.lt_succ_iff.mp hk_lt
  have hk_real_cast : (k : ℝ) ≤ ((m + 1 : ℕ) : ℝ) := by
    exact Nat.cast_le.mpr hk_nat
  have hden_cast : ((m + 1 : ℕ) : ℝ) = (m + 1 : ℝ) :=
    Real.natCast_add_one_eq_real_add_one m
  have hk_real : (k : ℝ) ≤ (m + 1 : ℝ) :=
    hden_cast ▸ hk_real_cast
  have hden_pos : 0 < (m + 1 : ℝ) :=
    Real.rightSemicircleStaircase_denominator_pos m
  exact (div_le_one hden_pos).mpr hk_real

/-- The staircase sample is above the lower endpoint of the semicircle. -/
theorem Complex.rightSemicircleStaircaseY_lower_bound
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ) :
    -ρ ≤ Complex.rightSemicircleStaircaseY ρ m k := by
  have hratio_nonneg :
      0 ≤ (k : ℝ) / (m + 1 : ℝ) :=
    Complex.rightSemicircleStaircaseY_ratio_nonneg m k
  have hstep_nonneg :
      0 ≤ ((k : ℝ) / (m + 1 : ℝ)) * (2 * ρ) :=
    mul_nonneg hratio_nonneg
      (mul_nonneg Real.rightSemicircleStaircase_two_nonneg hρ)
  show -ρ ≤ -ρ + ((k : ℝ) / (m + 1 : ℝ)) * (2 * ρ)
  exact le_add_of_nonneg_right hstep_nonneg

/-- The staircase sample is below the upper endpoint of the semicircle. -/
theorem Complex.rightSemicircleStaircaseY_upper_bound
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    {m k : ℕ}
    (hk : k ∈ Finset.range (m + 2)) :
    Complex.rightSemicircleStaircaseY ρ m k ≤ ρ := by
  have hratio_le :
      (k : ℝ) / (m + 1 : ℝ) ≤ 1 :=
    Complex.rightSemicircleStaircaseY_ratio_le_one hk
  have hstep_le :
      ((k : ℝ) / (m + 1 : ℝ)) * (2 * ρ) ≤ 1 * (2 * ρ) :=
    mul_le_mul_of_nonneg_right hratio_le
      (mul_nonneg Real.rightSemicircleStaircase_two_nonneg hρ)
  have htranslated :
      -ρ + ((k : ℝ) / (m + 1 : ℝ)) * (2 * ρ) ≤ -ρ + 1 * (2 * ρ) :=
    add_le_add_left hstep_le (-ρ)
  have hright :
      -ρ + 1 * (2 * ρ) = ρ :=
    Real.rightSemicircleStaircase_top_translate ρ
  show -ρ + ((k : ℝ) / (m + 1 : ℝ)) * (2 * ρ) ≤ ρ
  exact le_trans htranslated (le_of_eq hright)

/-- Staircase vertical samples lie in the semicircle height interval. -/
theorem Complex.rightSemicircleStaircaseY_mem_Icc
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 2)) :
    Complex.rightSemicircleStaircaseY ρ m k ∈ [[-ρ, ρ]] := by
  have hleft :
      -ρ ≤ Complex.rightSemicircleStaircaseY ρ m k :=
    Complex.rightSemicircleStaircaseY_lower_bound hρ m k
  have hright :
      Complex.rightSemicircleStaircaseY ρ m k ≤ ρ :=
    Complex.rightSemicircleStaircaseY_upper_bound hρ hk
  have hIcc :
      Complex.rightSemicircleStaircaseY ρ m k ∈ Set.Icc (-ρ) ρ :=
    And.intro hleft hright
  have huIcc :
      [[-ρ, ρ]] = Set.Icc (-ρ) ρ :=
    Set.uIcc_of_le (Complex.neg_radius_le_radius hρ)
  exact huIcc.symm ▸ hIcc

/-- The circular graph coordinate is nonnegative on the height interval. -/
theorem Complex.rightSemicircleGraphRe_nonneg
    (ρ y : ℝ) :
    0 ≤ Complex.rightSemicircleGraphRe ρ y := by
  exact Real.sqrt_nonneg _

/-- The circular graph coordinate is bounded by the radius on the height
interval. -/
theorem Complex.rightSemicircleGraphRe_le_radius
    {ρ y : ℝ}
    (hρ : 0 ≤ ρ)
    (hy : y ∈ [[-ρ, ρ]]) :
    Complex.rightSemicircleGraphRe ρ y ≤ ρ := by
  have hy_bounds : -ρ ≤ y ∧ y ≤ ρ := by
    exact Complex.mem_semicircle_height_Icc_of_mem_uIcc hρ hy
  have hy_abs : |y| ≤ ρ := by
    exact abs_le.mpr hy_bounds
  have hy_abs_radius : |y| ≤ |ρ| :=
    (Real.eq_abs_of_nonneg hρ) ▸ hy_abs
  have hy_sq : y ^ 2 ≤ ρ ^ 2 := by
    exact sq_le_sq.mpr hy_abs_radius
  have hrad_le : ρ ^ 2 - y ^ 2 ≤ ρ ^ 2 :=
    sub_le_self (ρ ^ 2) (sq_nonneg y)
  have hsqrt_le : Real.sqrt (ρ ^ 2 - y ^ 2) ≤ Real.sqrt (ρ ^ 2) :=
    Real.sqrt_le_sqrt hrad_le
  have hsqrt_radius : Real.sqrt (ρ ^ 2) = ρ :=
    Real.sqrt_sq_of_nonneg_explicit hρ
  show Real.sqrt (ρ ^ 2 - y ^ 2) ≤ ρ
  exact le_trans hsqrt_le (le_of_eq hsqrt_radius)

/-- The graph real-coordinate over the height interval lies in `[0,ρ]`. -/
theorem Complex.rightSemicircleGraphRe_mem_radius_uIcc_of_height_mem
    {ρ y : ℝ}
    (hρ : 0 ≤ ρ)
    (hy : y ∈ [[-ρ, ρ]]) :
    Complex.rightSemicircleGraphRe ρ y ∈ [[(0 : ℝ), ρ]] := by
  have hleft : 0 ≤ Complex.rightSemicircleGraphRe ρ y :=
    Complex.rightSemicircleGraphRe_nonneg ρ y
  have hright : Complex.rightSemicircleGraphRe ρ y ≤ ρ :=
    Complex.rightSemicircleGraphRe_le_radius hρ hy
  have hIcc :
      Complex.rightSemicircleGraphRe ρ y ∈ Set.Icc (0 : ℝ) ρ :=
    And.intro hleft hright
  exact (Set.uIcc_of_le hρ).symm ▸ hIcc

/-- The graph real-coordinate at the horizontal radius point is the radius. -/
theorem Complex.rightSemicircleGraphRe_zero
    {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    Complex.rightSemicircleGraphRe ρ 0 = ρ := by
  show Real.sqrt (ρ ^ 2 - (0 : ℝ) ^ 2) = ρ
  calc
    Real.sqrt (ρ ^ 2 - (0 : ℝ) ^ 2) =
        Real.sqrt (ρ ^ 2 - 0) := by
      exact congrArg (fun x : ℝ => Real.sqrt (ρ ^ 2 - x)) Real.zero_sq_eq_zero
    _ = Real.sqrt (ρ ^ 2) := by
      exact congrArg Real.sqrt (sub_zero (ρ ^ 2))
    _ = Real.sqrt (ρ * ρ) := by
      exact congrArg Real.sqrt (sq ρ)
    _ = ρ :=
      Real.sqrt_mul_self hρ

/-- The graph real-coordinate at the top tangent point is zero. -/
theorem Complex.rightSemicircleGraphRe_top
    {ρ : ℝ} :
    Complex.rightSemicircleGraphRe ρ ρ = 0 := by
  show Real.sqrt (ρ ^ 2 - ρ ^ 2) = 0
  calc
    Real.sqrt (ρ ^ 2 - ρ ^ 2) = Real.sqrt 0 := by
      exact congrArg Real.sqrt (sub_self (ρ ^ 2))
    _ = 0 := Real.sqrt_zero

/-- The graph real-coordinate at the bottom tangent point is zero. -/
theorem Complex.rightSemicircleGraphRe_bottom
    {ρ : ℝ} :
    Complex.rightSemicircleGraphRe ρ (-ρ) = 0 := by
  show Real.sqrt (ρ ^ 2 - (-ρ) ^ 2) = 0
  calc
    Real.sqrt (ρ ^ 2 - (-ρ) ^ 2) = Real.sqrt (ρ ^ 2 - ρ ^ 2) := by
      exact congrArg (fun x : ℝ => Real.sqrt (ρ ^ 2 - x)) (neg_sq ρ)
    _ = Real.sqrt 0 := by
      exact congrArg Real.sqrt (sub_self (ρ ^ 2))
    _ = 0 := Real.sqrt_zero

/-- Membership in the cell-index range is the strict cell-index bound. -/
theorem Complex.staircase_cell_index_lt
    {m k : ℕ}
    (hk : k ∈ Finset.range (m + 1)) :
    k < m + 1 := by
  exact Finset.mem_range.mp hk

/-- A staircase cell index is also valid as a lower sample index. -/
theorem Complex.staircase_lower_sample_mem_range
    {m k : ℕ}
    (hk : k ∈ Finset.range (m + 1)) :
    k ∈ Finset.range (m + 2) := by
  have hklt : k < m + 1 := Complex.staircase_cell_index_lt hk
  have hlt : k < m + 2 := Nat.lt_trans hklt (Nat.lt_succ_self (m + 1))
  exact Finset.mem_range.mpr hlt

/-- A staircase cell index has a valid upper sample index. -/
theorem Complex.staircase_upper_sample_mem_range
    {m k : ℕ}
    (hk : k ∈ Finset.range (m + 1)) :
    k + 1 ∈ Finset.range (m + 2) := by
  have hklt : k < m + 1 := Complex.staircase_cell_index_lt hk
  have hlt : k + 1 < m + 2 := Nat.succ_lt_succ hklt
  exact Finset.mem_range.mpr hlt

/-- A nonzero valid cell index has a valid predecessor cell index. -/
theorem Complex.staircase_pred_mem_range_of_ne_zero
    {m k : ℕ}
    (hk : k ∈ Finset.range (m + 1))
    (_hk0 : k ≠ 0) :
    k - 1 ∈ Finset.range (m + 1) := by
  have hklt : k < m + 1 := Complex.staircase_cell_index_lt hk
  have hpred_lt : k - 1 < m + 1 :=
    lt_of_le_of_lt (Nat.sub_le k 1) hklt
  exact Finset.mem_range.mpr hpred_lt

/-- A nonzero natural number is recovered from its predecessor. -/
theorem Complex.staircase_pred_succ_of_ne_zero
    {k : ℕ}
    (hk0 : k ≠ 0) :
    (k - 1) + 1 = k :=
  Nat.sub_add_cancel (Nat.pos_of_ne_zero hk0)

/-- The lower endpoint graph value in a staircase cell is nonnegative. -/
theorem Complex.rightSemicircleStaircaseGraphRe_lower_nonneg
    (ρ : ℝ)
    (m k : ℕ) :
    0 ≤
      Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m k) :=
  Complex.rightSemicircleGraphRe_nonneg ρ
    (Complex.rightSemicircleStaircaseY ρ m k)

/-- The upper endpoint graph value in a staircase cell is nonnegative. -/
theorem Complex.rightSemicircleStaircaseGraphRe_upper_nonneg
    (ρ : ℝ)
    (m k : ℕ) :
    0 ≤
      Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m (k + 1)) :=
  Complex.rightSemicircleGraphRe_nonneg ρ
    (Complex.rightSemicircleStaircaseY ρ m (k + 1))

/-- The lower endpoint graph value in a valid staircase cell is bounded by the
radius. -/
theorem Complex.rightSemicircleStaircaseGraphRe_lower_le_radius
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    {m k : ℕ}
    (hk : k ∈ Finset.range (m + 1)) :
    Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m k) ≤ ρ :=
  Complex.rightSemicircleGraphRe_le_radius hρ
    (Complex.rightSemicircleStaircaseY_mem_Icc hρ m k
      (Complex.staircase_lower_sample_mem_range hk))

/-- The upper endpoint graph value in a valid staircase cell is bounded by the
radius. -/
theorem Complex.rightSemicircleStaircaseGraphRe_upper_le_radius
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    {m k : ℕ}
    (hk : k ∈ Finset.range (m + 1)) :
    Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m (k + 1)) ≤ ρ :=
  Complex.rightSemicircleGraphRe_le_radius hρ
    (Complex.rightSemicircleStaircaseY_mem_Icc hρ m (k + 1)
      (Complex.staircase_upper_sample_mem_range hk))

end

end LFunctions
end Boundary
