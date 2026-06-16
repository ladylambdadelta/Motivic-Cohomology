import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaRectangularCollars

/-!
# Semicircle staircase geometry for finite-height Abel-Plana collars

This file owns the polygonal staircase approximation to the right semicircle and
its finite Cauchy-Goursat boundary cancellation.  Later contour files consume
this geometry to prove convergence to the curvilinear semicircle boundary.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Uniform vertical sample for the right circular graph. -/
noncomputable def Complex.rightSemicircleStaircaseY
    (ρ : ℝ)
    (m k : ℕ) : ℝ :=
  -ρ + ((k : ℝ) / (m + 1 : ℝ)) * (2 * ρ)

/-- Right circular graph coordinate at vertical coordinate `y`. -/
noncomputable def Complex.rightSemicircleGraphRe
    (ρ y : ℝ) : ℝ :=
  Real.sqrt (ρ ^ 2 - y ^ 2)

/-- Safe vertical coordinate for one staircase cell: the larger of the two
endpoint graph values, hence at least the graph on monotone half-intervals. -/
noncomputable def Complex.rightSemicircleStaircaseSafeRe
    (ρ : ℝ)
    (m k : ℕ) : ℝ :=
  if Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
      0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1) then
    ρ
  else
    max
      (Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m k))
      (Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m (k + 1)))

/-- Previous safe real coordinate used by the horizontal connector at the
bottom of the `k`th staircase cell. -/
noncomputable def Complex.rightSemicircleStaircasePrevSafeRe
    (ρ : ℝ)
    (m k : ℕ) : ℝ :=
  if k = 0 then
    0
  else
    Complex.rightSemicircleStaircaseSafeRe ρ m (k - 1)

/-- Horizontal connector at the bottom of a staircase cell. -/
noncomputable def Complex.rightSemicircleStaircaseHorizontalIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) : ℂ :=
  ∫ x : ℝ in
    Complex.rightSemicircleStaircasePrevSafeRe ρ m k..
      Complex.rightSemicircleStaircaseSafeRe ρ m k,
    f (((c.re + x : ℝ) : ℂ) +
      Complex.I * (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))

/-- Vertical side of a staircase cell. -/
noncomputable def Complex.rightSemicircleStaircaseVerticalIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) : ℂ :=
  Complex.I *
    ∫ y : ℝ in
      Complex.rightSemicircleStaircaseY ρ m k..
        Complex.rightSemicircleStaircaseY ρ m (k + 1),
      f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
        Complex.I * (((c.im + y : ℝ) : ℂ)))

/-- Final horizontal connector from the last safe staircase coordinate to the
top tangent point. -/
noncomputable def Complex.rightSemicircleStaircaseTopConnectorIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) : ℂ :=
  ∫ x : ℝ in
    Complex.rightSemicircleStaircaseSafeRe ρ m m..0,
    f (((c.re + x : ℝ) : ℂ) +
      Complex.I * (((c.im + ρ : ℝ) : ℂ)))

/-- A nonnegative radius has its negative endpoint below its positive endpoint. -/
theorem Complex.neg_radius_le_radius
    {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    -ρ ≤ ρ := by
  have hneg_nonpos : -ρ ≤ 0 := neg_nonpos.mpr hρ
  exact le_trans hneg_nonpos hρ

/-- A closed interval is convex with respect to the unordered interval between
two of its points. -/
theorem mem_uIcc_of_mem_uIcc_endpoints
    {a b u v x : ℝ}
    (hab : a ≤ b)
    (hu : u ∈ [[a, b]])
    (hv : v ∈ [[a, b]])
    (hx : x ∈ [[u, v]]) :
    x ∈ [[a, b]] := by
  have hu_eq : [[a, b]] = Set.Icc a b := Set.uIcc_of_le hab
  have huIcc : u ∈ Set.Icc a b := hu_eq ▸ hu
  have hvIcc : v ∈ Set.Icc a b := hu_eq ▸ hv
  have hx_pair : (u ≤ x ∧ x ≤ v) ∨ (v ≤ x ∧ x ≤ u) := by
    exact Set.mem_uIcc.mp hx
  have hxIcc : x ∈ Set.Icc a b := by
    rcases hx_pair with hx_pair | hx_pair
    · exact
        And.intro
          (le_trans huIcc.1 hx_pair.1)
          (le_trans hx_pair.2 hvIcc.2)
    · exact
        And.intro
          (le_trans hvIcc.1 hx_pair.1)
          (le_trans hx_pair.2 huIcc.2)
  exact hu_eq.symm ▸ hxIcc

/-- Two points in an unordered real interval are separated by at most the
interval length. -/
theorem dist_le_uIcc_length_of_mem
    {a b y y' : ℝ}
    (hy : y ∈ [[a, b]])
    (hy' : y' ∈ [[a, b]]) :
    dist y y' ≤ |b - a| := by
  have hy_pair : (a ≤ y ∧ y ≤ b) ∨ (b ≤ y ∧ y ≤ a) := by
    exact Set.mem_uIcc.mp hy
  have hy'_pair : (a ≤ y' ∧ y' ≤ b) ∨ (b ≤ y' ∧ y' ≤ a) := by
    exact Set.mem_uIcc.mp hy'
  rcases le_total a b with hab | hba
  · have hyIcc : y ∈ Set.Icc a b := by
      rcases hy_pair with h | h
      · exact h
      · exact
          And.intro
            (le_trans hab h.1)
            (le_trans h.2 hab)
    have hy'Icc : y' ∈ Set.Icc a b := by
      rcases hy'_pair with h | h
      · exact h
      · exact
          And.intro
            (le_trans hab h.1)
            (le_trans h.2 hab)
    have hleft_raw : a - b ≤ y - y' := sub_le_sub hyIcc.1 hy'Icc.2
    have hleft_eq : -(b - a) = a - b := neg_sub b a
    have hleft : -(b - a) ≤ y - y' := hleft_eq ▸ hleft_raw
    have hright : y - y' ≤ b - a := sub_le_sub hyIcc.2 hy'Icc.1
    have habs_dist : |y - y'| ≤ b - a :=
      abs_le.mpr (And.intro hleft hright)
    have habs_length : |b - a| = b - a :=
      abs_of_nonneg (sub_nonneg.mpr hab)
    have hdist_eq : dist y y' = |y - y'| := Real.dist_eq y y'
    exact hdist_eq.trans_le (habs_length ▸ habs_dist)
  · have hyIcc : y ∈ Set.Icc b a := by
      rcases hy_pair with h | h
      · exact
          And.intro
            (le_trans hba h.1)
            (le_trans h.2 hba)
      · exact h
    have hy'Icc : y' ∈ Set.Icc b a := by
      rcases hy'_pair with h | h
      · exact
          And.intro
            (le_trans hba h.1)
            (le_trans h.2 hba)
      · exact h
    have hleft_raw : b - a ≤ y - y' := sub_le_sub hyIcc.1 hy'Icc.2
    have hleft_eq : -(a - b) = b - a := neg_sub a b
    have hleft : -(a - b) ≤ y - y' := hleft_eq ▸ hleft_raw
    have hright : y - y' ≤ a - b := sub_le_sub hyIcc.2 hy'Icc.1
    have habs_dist : |y - y'| ≤ a - b :=
      abs_le.mpr (And.intro hleft hright)
    have habs_length : |b - a| = a - b := by
      have hnonpos : b - a ≤ 0 := sub_nonpos.mpr hba
      calc
        |b - a| = -(b - a) := abs_of_nonpos hnonpos
        _ = a - b := neg_sub b a
    have hdist_eq : dist y y' = |y - y'| := Real.dist_eq y y'
    exact hdist_eq.trans_le (habs_length ▸ habs_dist)

/-- If two endpoints lie in `[g - δ, g + δ]`, then every point in the
unordered interval between them has distance at most `δ` from `g`. -/
theorem abs_sub_le_of_mem_uIcc_of_endpoint_abs_sub_le
    {u v x g δ : ℝ}
    (hx : x ∈ [[u, v]])
    (hu : |u - g| ≤ δ)
    (hv : |v - g| ≤ δ) :
    |x - g| ≤ δ := by
  have hu_bounds : g - δ ≤ u ∧ u ≤ g + δ :=
    abs_sub_le_iff.mp hu
  have hv_bounds : g - δ ≤ v ∧ v ≤ g + δ :=
    abs_sub_le_iff.mp hv
  have hx_pair : (u ≤ x ∧ x ≤ v) ∨ (v ≤ x ∧ x ≤ u) := by
    exact Set.mem_uIcc.mp hx
  have hx_bounds : g - δ ≤ x ∧ x ≤ g + δ := by
    rcases hx_pair with hx_pair | hx_pair
    · exact
        And.intro
          (le_trans hu_bounds.1 hx_pair.1)
          (le_trans hx_pair.2 hv_bounds.2)
    · exact
        And.intro
          (le_trans hv_bounds.1 hx_pair.1)
          (le_trans hx_pair.2 hu_bounds.2)
  exact abs_sub_le_iff.mpr hx_bounds

/-- Two points in `[0,ρ]` differ by at most `ρ`. -/
theorem abs_sub_le_radius_of_mem_radius_uIcc
    {ρ a b : ℝ}
    (hρ : 0 ≤ ρ)
    (ha : a ∈ [[(0 : ℝ), ρ]])
    (hb : b ∈ [[(0 : ℝ), ρ]]) :
    |a - b| ≤ ρ := by
  have haIcc : a ∈ Set.Icc (0 : ℝ) ρ := by
    exact (Set.uIcc_of_le hρ) ▸ ha
  have hbIcc : b ∈ Set.Icc (0 : ℝ) ρ := by
    exact (Set.uIcc_of_le hρ) ▸ hb
  have hleft : -ρ ≤ a - b := by
    have hraw : 0 - ρ ≤ a - b := sub_le_sub haIcc.1 hbIcc.2
    simpa [zero_sub] using hraw
  have hright : a - b ≤ ρ := by
    have hraw : a - b ≤ ρ - 0 := sub_le_sub haIcc.2 hbIcc.1
    simpa [sub_zero] using hraw
  exact abs_le.mpr (And.intro hleft hright)

/-- The lower endpoint belongs to an ordered unordered interval. -/
theorem left_endpoint_mem_uIcc_of_le
    {a b : ℝ}
    (hab : a ≤ b) :
    a ∈ [[a, b]] := by
  have hIcc : a ∈ Set.Icc a b := And.intro le_rfl hab
  have huIcc : [[a, b]] = Set.Icc a b := Set.uIcc_of_le hab
  exact huIcc.symm ▸ hIcc

/-- The upper endpoint belongs to an ordered unordered interval. -/
theorem right_endpoint_mem_uIcc_of_le
    {a b : ℝ}
    (hab : a ≤ b) :
    b ∈ [[a, b]] := by
  have hIcc : b ∈ Set.Icc a b := And.intro hab le_rfl
  have huIcc : [[a, b]] = Set.Icc a b := Set.uIcc_of_le hab
  exact huIcc.symm ▸ hIcc

/-- The top radius endpoint belongs to the semicircle height interval. -/
theorem Complex.radius_mem_semicircle_height_uIcc
    {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    ρ ∈ [[-ρ, ρ]] :=
  right_endpoint_mem_uIcc_of_le (Complex.neg_radius_le_radius hρ)

/-- The zero endpoint belongs to `[0,ρ]` when the radius is nonnegative. -/
theorem Complex.zero_mem_radius_uIcc
    {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    (0 : ℝ) ∈ [[(0 : ℝ), ρ]] :=
  left_endpoint_mem_uIcc_of_le hρ

/-- The real ratio attached to a staircase sample is nonnegative. -/
theorem Complex.rightSemicircleStaircaseY_ratio_nonneg
    (m k : ℕ) :
    0 ≤ (k : ℝ) / (m + 1 : ℝ) := by
  have hden_pos : 0 < (m + 1 : ℝ) := by positivity
  exact div_nonneg (Nat.cast_nonneg k) hden_pos.le

/-- The real ratio attached to an in-range staircase sample is at most one. -/
theorem Complex.rightSemicircleStaircaseY_ratio_le_one
    {m k : ℕ}
    (hk : k ∈ Finset.range (m + 2)) :
    (k : ℝ) / (m + 1 : ℝ) ≤ 1 := by
  have hk_lt : k < m + 2 := by
    simpa [Finset.mem_range] using hk
  have hk_nat : k ≤ m + 1 := Nat.lt_succ_iff.mp hk_lt
  have hk_real : (k : ℝ) ≤ (m + 1 : ℝ) := by
    exact_mod_cast hk_nat
  have hden_pos : 0 < (m + 1 : ℝ) := by positivity
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
    mul_nonneg hratio_nonneg (mul_nonneg (by norm_num) hρ)
  dsimp [Complex.rightSemicircleStaircaseY]
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
    mul_le_mul_of_nonneg_right hratio_le (mul_nonneg (by norm_num) hρ)
  have htranslated :
      -ρ + ((k : ℝ) / (m + 1 : ℝ)) * (2 * ρ) ≤ -ρ + 1 * (2 * ρ) :=
    add_le_add_left hstep_le (-ρ)
  have hright :
      -ρ + 1 * (2 * ρ) = ρ := by
    ring
  dsimp [Complex.rightSemicircleStaircaseY]
  exact hright ▸ htranslated

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
    simpa [Set.uIcc_of_le (by linarith : -ρ ≤ ρ)] using hy
  have hy_abs : |y| ≤ ρ := by
    exact abs_le.mpr hy_bounds
  have hy_sq : y ^ 2 ≤ ρ ^ 2 := by
    exact sq_le_sq.mpr hy_abs
  have hrad_le : ρ ^ 2 - y ^ 2 ≤ ρ ^ 2 :=
    sub_le_self (ρ ^ 2) (sq_nonneg y)
  have hsqrt_le : Real.sqrt (ρ ^ 2 - y ^ 2) ≤ Real.sqrt (ρ ^ 2) :=
    Real.sqrt_le_sqrt hrad_le
  have hsqrt_radius : Real.sqrt (ρ ^ 2) = ρ := by
    rw [sq, Real.sqrt_mul_self hρ]
  dsimp [Complex.rightSemicircleGraphRe]
  exact hsqrt_radius ▸ hsqrt_le

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

/-- The graph real-coordinate at the top tangent point is zero. -/
theorem Complex.rightSemicircleGraphRe_top
    {ρ : ℝ} :
    Complex.rightSemicircleGraphRe ρ ρ = 0 := by
  dsimp [Complex.rightSemicircleGraphRe]
  rw [sub_self, Real.sqrt_zero]

/-- The graph real-coordinate at the bottom tangent point is zero. -/
theorem Complex.rightSemicircleGraphRe_bottom
    {ρ : ℝ} :
    Complex.rightSemicircleGraphRe ρ (-ρ) = 0 := by
  dsimp [Complex.rightSemicircleGraphRe]
  rw [neg_sq, sub_self, Real.sqrt_zero]

/-- Membership in the cell-index range is the strict cell-index bound. -/
theorem Complex.staircase_cell_index_lt
    {m k : ℕ}
    (hk : k ∈ Finset.range (m + 1)) :
    k < m + 1 := by
  simpa [Finset.mem_range] using hk

/-- A staircase cell index is also valid as a lower sample index. -/
theorem Complex.staircase_lower_sample_mem_range
    {m k : ℕ}
    (hk : k ∈ Finset.range (m + 1)) :
    k ∈ Finset.range (m + 2) := by
  have hklt : k < m + 1 := Complex.staircase_cell_index_lt hk
  have hlt : k < m + 2 := Nat.lt_trans hklt (Nat.lt_succ_self (m + 1))
  simpa [Finset.mem_range] using hlt

/-- A staircase cell index has a valid upper sample index. -/
theorem Complex.staircase_upper_sample_mem_range
    {m k : ℕ}
    (hk : k ∈ Finset.range (m + 1)) :
    k + 1 ∈ Finset.range (m + 2) := by
  have hklt : k < m + 1 := Complex.staircase_cell_index_lt hk
  have hlt : k + 1 < m + 2 := Nat.succ_lt_succ hklt
  simpa [Finset.mem_range] using hlt

/-- A nonzero valid cell index has a valid predecessor cell index. -/
theorem Complex.staircase_pred_mem_range_of_ne_zero
    {m k : ℕ}
    (hk : k ∈ Finset.range (m + 1))
    (hk0 : k ≠ 0) :
    k - 1 ∈ Finset.range (m + 1) := by
  have hklt : k < m + 1 := Complex.staircase_cell_index_lt hk
  have hpred_lt : k - 1 < m + 1 :=
    lt_of_le_of_lt (Nat.sub_le k 1) hklt
  simpa [Finset.mem_range] using hpred_lt

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

/-- The safe staircase real coordinate is nonnegative. -/
theorem Complex.rightSemicircleStaircaseSafeRe_nonneg
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ) :
    0 ≤ Complex.rightSemicircleStaircaseSafeRe ρ m k := by
  have hlower :
      0 ≤
        Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k) :=
    Complex.rightSemicircleStaircaseGraphRe_lower_nonneg ρ m k
  dsimp [Complex.rightSemicircleStaircaseSafeRe]
  by_cases hcross :
      Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1)
  · rw [if_pos hcross]
    exact hρ
  · rw [if_neg hcross]
    exact le_max_of_le_left hlower

/-- The safe staircase real coordinate in a valid cell is bounded by the
radius. -/
theorem Complex.rightSemicircleStaircaseSafeRe_le_radius
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    {m k : ℕ}
    (hk : k ∈ Finset.range (m + 1)) :
    Complex.rightSemicircleStaircaseSafeRe ρ m k ≤ ρ := by
  have hlower :
      Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k) ≤ ρ :=
    Complex.rightSemicircleStaircaseGraphRe_lower_le_radius hρ hk
  have hupper :
      Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m (k + 1)) ≤ ρ :=
    Complex.rightSemicircleStaircaseGraphRe_upper_le_radius hρ hk
  dsimp [Complex.rightSemicircleStaircaseSafeRe]
  by_cases hcross :
      Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1)
  · rw [if_pos hcross]
  · rw [if_neg hcross]
    exact max_le hlower hupper

/-- The safe staircase real coordinate lies in `[0,ρ]`. -/
theorem Complex.rightSemicircleStaircaseSafeRe_mem_Icc
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
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

/-- The predecessor safe coordinate is nonnegative in a valid cell. -/
theorem Complex.rightSemicircleStaircasePrevSafeRe_nonneg
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    {m k : ℕ}
    (hk : k ∈ Finset.range (m + 1)) :
    0 ≤ Complex.rightSemicircleStaircasePrevSafeRe ρ m k := by
  by_cases hk0 : k = 0
  · subst k
    dsimp [Complex.rightSemicircleStaircasePrevSafeRe]
  · have hk_pred : k - 1 ∈ Finset.range (m + 1) := by
      exact Complex.staircase_pred_mem_range_of_ne_zero hk hk0
    have hsafe :
        0 ≤ Complex.rightSemicircleStaircaseSafeRe ρ m (k - 1) :=
      Complex.rightSemicircleStaircaseSafeRe_nonneg hρ m (k - 1)
    simpa [Complex.rightSemicircleStaircasePrevSafeRe, hk0] using hsafe

/-- The predecessor safe coordinate is radius-bounded in a valid cell. -/
theorem Complex.rightSemicircleStaircasePrevSafeRe_le_radius
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    {m k : ℕ}
    (hk : k ∈ Finset.range (m + 1)) :
    Complex.rightSemicircleStaircasePrevSafeRe ρ m k ≤ ρ := by
  by_cases hk0 : k = 0
  · subst k
    dsimp [Complex.rightSemicircleStaircasePrevSafeRe]
    exact hρ
  · have hk_pred : k - 1 ∈ Finset.range (m + 1) := by
      exact Complex.staircase_pred_mem_range_of_ne_zero hk hk0
    have hsafe :
        Complex.rightSemicircleStaircaseSafeRe ρ m (k - 1) ≤ ρ :=
      Complex.rightSemicircleStaircaseSafeRe_le_radius hρ hk_pred
    simpa [Complex.rightSemicircleStaircasePrevSafeRe, hk0] using hsafe

/-- The previous safe staircase real coordinate lies in `[0,ρ]`. -/
theorem Complex.rightSemicircleStaircasePrevSafeRe_mem_Icc
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
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
  simpa [Finset.mem_range] using Nat.lt_succ_self m

/-- The last safe staircase real coordinate lies in `[0,ρ]`. -/
theorem Complex.rightSemicircleStaircaseSafeRe_last_mem_Icc
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m : ℕ) :
    Complex.rightSemicircleStaircaseSafeRe ρ m m ∈ [[(0 : ℝ), ρ]] :=
  Complex.rightSemicircleStaircaseSafeRe_mem_Icc hρ m m
    (Complex.rightSemicircleStaircase_last_mem_range m)

/-- The last safe staircase real coordinate is nonnegative. -/
theorem Complex.rightSemicircleStaircaseSafeRe_last_nonneg
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m : ℕ) :
    0 ≤ Complex.rightSemicircleStaircaseSafeRe ρ m m :=
  Complex.rightSemicircleStaircaseSafeRe_nonneg hρ m m

/-- The last safe staircase real coordinate is bounded by the radius. -/
theorem Complex.rightSemicircleStaircaseSafeRe_last_le_radius
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m : ℕ) :
    Complex.rightSemicircleStaircaseSafeRe ρ m m ≤ ρ :=
  Complex.rightSemicircleStaircaseSafeRe_le_radius hρ
    (Complex.rightSemicircleStaircase_last_mem_range m)

/-- The final top horizontal staircase connector has length at most the
radius. -/
theorem Complex.abs_top_sub_rightSemicircleStaircaseSafeRe_le_radius
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m : ℕ) :
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
    rw [zero_sub, abs_neg]
    exact abs_of_nonneg hnonneg
  exact hnorm ▸ hle

/-- Adding a term bounded by `ρ` to a term bounded by `2ρ` is bounded by
`3ρ`. -/
theorem add_le_three_mul_of_le_two_mul_of_le
    {ρ a b : ℝ}
    (ha : a ≤ 2 * ρ)
    (hb : b ≤ ρ) :
    a + b ≤ 3 * ρ := by
  calc
    a + b ≤ 2 * ρ + ρ := add_le_add ha hb
    _ = 3 * ρ := by ring

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

/-- Adjacent absolute differences telescope on a monotone finite prefix. -/
theorem sum_abs_adjacent_of_monotone_prefix
    (s : ℕ → ℝ)
    (j : ℕ)
    (hmono : ∀ k : ℕ, k < j → s k ≤ s (k + 1)) :
    (∑ k in Finset.range j, |s (k + 1) - s k|) = s j - s 0 := by
  induction j with
  | zero =>
      simp
  | succ j ih =>
      have hmono_prefix : ∀ k : ℕ, k < j → s k ≤ s (k + 1) := by
        intro k hk
        exact hmono k (Nat.lt_trans hk (Nat.lt_succ_self j))
      have hlast_nonneg : 0 ≤ s (j + 1) - s j :=
        sub_nonneg.mpr (hmono j (Nat.lt_succ_self j))
      rw [Finset.sum_range_succ, ih hmono_prefix, abs_of_nonneg hlast_nonneg]
      ring

/-- Adjacent absolute differences telescope on an antitone finite suffix. -/
theorem sum_abs_adjacent_of_antitone_suffix
    (s : ℕ → ℝ)
    (j n : ℕ)
    (hanti :
      ∀ k : ℕ, k < n → s ((j + k) + 1) ≤ s (j + k)) :
    (∑ k in Finset.range n, |s ((j + k) + 1) - s (j + k)|) =
      s j - s (j + n) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hanti_prefix :
          ∀ k : ℕ, k < n → s ((j + k) + 1) ≤ s (j + k) := by
        intro k hk
        exact hanti k (Nat.lt_trans hk (Nat.lt_succ_self n))
      have hlast_nonneg : 0 ≤ s (j + n) - s ((j + n) + 1) :=
        sub_nonneg.mpr (hanti n (Nat.lt_succ_self n))
      rw [Finset.sum_range_succ, ih hanti_prefix,
        abs_of_nonneg hlast_nonneg]
      ring

/-- Pulling off the initial zero rewrites the `prev`-style variation as the
ordinary adjacent-difference variation. -/
theorem sum_abs_sub_prev_eq_sum_abs_adjacent
    (s : ℕ → ℝ)
    (m : ℕ)
    (h0 : s 0 = 0) :
    (∑ k in Finset.range (m + 1),
      |s k - if k = 0 then (0 : ℝ) else s (k - 1)|) =
      ∑ k in Finset.range m, |s (k + 1) - s k| := by
  rw [Finset.sum_range_succ']
  simp [h0]

/-- The `prev`-style variation is the first jump from zero together with the
ordinary adjacent-difference variation. -/
theorem sum_abs_sub_prev_eq_abs_first_add_sum_abs_adjacent
    (s : ℕ → ℝ)
    (m : ℕ) :
    (∑ k in Finset.range (m + 1),
      |s k - if k = 0 then (0 : ℝ) else s (k - 1)|) =
      |s 0| + ∑ k in Finset.range m, |s (k + 1) - s k| := by
  rw [Finset.sum_range_succ']
  simp [add_comm]

/-- Scalar algebra behind the unimodal variation estimate when the sequence
starts at zero. -/
theorem unimodal_variation_zero_start_scalar_le
    {ρ s₀ sⱼ sₘ : ℝ}
    (hs₀ : s₀ = 0)
    (hsⱼ : sⱼ ≤ ρ) :
    ((sⱼ - s₀) + (sⱼ - sₘ)) + sₘ ≤ 2 * ρ := by
  calc
    ((sⱼ - s₀) + (sⱼ - sₘ)) + sₘ = 2 * sⱼ := by
      rw [hs₀]
      ring
    _ ≤ 2 * ρ := by
      exact mul_le_mul_of_nonneg_left hsⱼ (by norm_num)

/-- Scalar algebra behind the bounded unimodal variation estimate. -/
theorem unimodal_variation_bounded_scalar_le
    {ρ s₀ sⱼ sₘ : ℝ}
    (hsⱼ : sⱼ ≤ ρ) :
    s₀ + ((sⱼ - s₀) + (sⱼ - sₘ)) + sₘ ≤ 2 * ρ := by
  calc
    s₀ + ((sⱼ - s₀) + (sⱼ - sₘ)) + sₘ = 2 * sⱼ := by
      ring
    _ ≤ 2 * ρ := by
      exact mul_le_mul_of_nonneg_left hsⱼ (by norm_num)

/-- A finite real sequence starting at zero, staying in `[0,ρ]`, increasing up
to a peak index and decreasing after it has total horizontal variation,
including the return from the final value to zero, bounded by `2ρ`. -/
theorem sum_abs_sub_prev_add_top_le_two_mul_of_unimodal
    {ρ : ℝ}
    (s : ℕ → ℝ)
    (m j : ℕ)
    (hjm : j ≤ m)
    (h0 : s 0 = 0)
    (hbounds : ∀ k : ℕ, k ≤ m → 0 ≤ s k ∧ s k ≤ ρ)
    (hmono : ∀ k : ℕ, k < j → s k ≤ s (k + 1))
    (hanti : ∀ k : ℕ, j ≤ k → k < m → s (k + 1) ≤ s k) :
    (∑ k in Finset.range (m + 1),
        |s k - if k = 0 then (0 : ℝ) else s (k - 1)|) +
      |(0 : ℝ) - s m| ≤ 2 * ρ := by
  have hprev :
      (∑ k in Finset.range (m + 1),
        |s k - if k = 0 then (0 : ℝ) else s (k - 1)|) =
        ∑ k in Finset.range m, |s (k + 1) - s k| :=
    sum_abs_sub_prev_eq_sum_abs_adjacent s m h0
  have hm_decomp : j + (m - j) = m :=
    Nat.add_sub_of_le hjm
  have hsplit :
      (∑ k in Finset.range m, |s (k + 1) - s k|) =
        (∑ k in Finset.range j, |s (k + 1) - s k|) +
          ∑ k in Finset.range (m - j),
            |s ((j + k) + 1) - s (j + k)| := by
    calc
      (∑ k in Finset.range m, |s (k + 1) - s k|)
          =
        ∑ k in Finset.range (j + (m - j)), |s (k + 1) - s k| := by
          rw [hm_decomp]
      _ =
        (∑ k in Finset.range j, |s (k + 1) - s k|) +
          ∑ k in Finset.range (m - j), |s ((j + k) + 1) - s (j + k)| := by
          rw [Finset.sum_range_add]
  have hprefix :
      (∑ k in Finset.range j, |s (k + 1) - s k|) = s j - s 0 :=
    sum_abs_adjacent_of_monotone_prefix s j hmono
  have hsuffix :
      (∑ k in Finset.range (m - j),
        |s ((j + k) + 1) - s (j + k)|) = s j - s m := by
    have hanti_shift :
        ∀ k : ℕ, k < m - j → s ((j + k) + 1) ≤ s (j + k) := by
      intro k hk
      exact hanti (j + k) (Nat.le_add_right j k)
        (Nat.lt_sub_iff_add_lt'.mp hk)
    have htel :=
      sum_abs_adjacent_of_antitone_suffix s j (m - j) hanti_shift
    simpa [hm_decomp] using htel
  have htop : |(0 : ℝ) - s m| = s m := by
    have hsm_nonneg : 0 ≤ s m := (hbounds m le_rfl).1
    rw [zero_sub, abs_neg, abs_of_nonneg hsm_nonneg]
  have hsj_le : s j ≤ ρ := (hbounds j hjm).2
  calc
    (∑ k in Finset.range (m + 1),
        |s k - if k = 0 then (0 : ℝ) else s (k - 1)|) +
      |(0 : ℝ) - s m|
        =
      ((s j - s 0) + (s j - s m)) + s m := by
        rw [hprev, hsplit, hprefix, hsuffix, htop]
    _ ≤ 2 * ρ :=
        unimodal_variation_zero_start_scalar_le h0 hsj_le

/-- A finite real sequence staying in `[0,ρ]`, increasing up to a peak index
and decreasing after it has total horizontal variation from the left endpoint
`0` through the sequence and back to `0` bounded by `2ρ`. -/
theorem sum_abs_sub_prev_add_top_le_two_mul_of_bounded_unimodal
    {ρ : ℝ}
    (s : ℕ → ℝ)
    (m j : ℕ)
    (hjm : j ≤ m)
    (hbounds : ∀ k : ℕ, k ≤ m → 0 ≤ s k ∧ s k ≤ ρ)
    (hmono : ∀ k : ℕ, k < j → s k ≤ s (k + 1))
    (hanti : ∀ k : ℕ, j ≤ k → k < m → s (k + 1) ≤ s k) :
    (∑ k in Finset.range (m + 1),
        |s k - if k = 0 then (0 : ℝ) else s (k - 1)|) +
      |(0 : ℝ) - s m| ≤ 2 * ρ := by
  have hprev :
      (∑ k in Finset.range (m + 1),
        |s k - if k = 0 then (0 : ℝ) else s (k - 1)|) =
        |s 0| + ∑ k in Finset.range m, |s (k + 1) - s k| :=
    sum_abs_sub_prev_eq_abs_first_add_sum_abs_adjacent s m
  have hm_decomp : j + (m - j) = m :=
    Nat.add_sub_of_le hjm
  have hsplit :
      (∑ k in Finset.range m, |s (k + 1) - s k|) =
        (∑ k in Finset.range j, |s (k + 1) - s k|) +
          ∑ k in Finset.range (m - j),
            |s ((j + k) + 1) - s (j + k)| := by
    calc
      (∑ k in Finset.range m, |s (k + 1) - s k|)
          =
        ∑ k in Finset.range (j + (m - j)), |s (k + 1) - s k| := by
          rw [hm_decomp]
      _ =
        (∑ k in Finset.range j, |s (k + 1) - s k|) +
          ∑ k in Finset.range (m - j), |s ((j + k) + 1) - s (j + k)| := by
          rw [Finset.sum_range_add]
  have hprefix :
      (∑ k in Finset.range j, |s (k + 1) - s k|) = s j - s 0 :=
    sum_abs_adjacent_of_monotone_prefix s j hmono
  have hsuffix :
      (∑ k in Finset.range (m - j),
        |s ((j + k) + 1) - s (j + k)|) = s j - s m := by
    have hanti_shift :
        ∀ k : ℕ, k < m - j → s ((j + k) + 1) ≤ s (j + k) := by
      intro k hk
      exact hanti (j + k) (Nat.le_add_right j k)
        (Nat.lt_sub_iff_add_lt'.mp hk)
    have htel :=
      sum_abs_adjacent_of_antitone_suffix s j (m - j) hanti_shift
    simpa [hm_decomp] using htel
  have hfirst : |s 0| = s 0 := by
    exact abs_of_nonneg ((hbounds 0 (Nat.zero_le m)).1)
  have htop : |(0 : ℝ) - s m| = s m := by
    have hsm_nonneg : 0 ≤ s m := (hbounds m le_rfl).1
    rw [zero_sub, abs_neg, abs_of_nonneg hsm_nonneg]
  have hsj_le : s j ≤ ρ := (hbounds j hjm).2
  calc
    (∑ k in Finset.range (m + 1),
        |s k - if k = 0 then (0 : ℝ) else s (k - 1)|) +
      |(0 : ℝ) - s m|
        =
      s 0 + ((s j - s 0) + (s j - s m)) + s m := by
        rw [hprev, hsplit, hprefix, hsuffix, hfirst, htop]
    _ ≤ 2 * ρ :=
        unimodal_variation_bounded_scalar_le hsj_le

/-- If the safe staircase real coordinates are unimodal, then their full
horizontal variation from the lower tangent point back to the upper tangent
point is bounded by `2ρ`. -/
theorem Complex.rightSemicircleStaircaseSafeRe_totalHorizontalVariation_le_two_radius_of_unimodal
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m j : ℕ)
    (hjm : j ≤ m)
    (hmono :
      ∀ k : ℕ, k < j →
        Complex.rightSemicircleStaircaseSafeRe ρ m k ≤
          Complex.rightSemicircleStaircaseSafeRe ρ m (k + 1))
    (hanti :
      ∀ k : ℕ, j ≤ k → k < m →
        Complex.rightSemicircleStaircaseSafeRe ρ m (k + 1) ≤
      Complex.rightSemicircleStaircaseSafeRe ρ m k) :
    (∑ k in Finset.range (m + 1),
        |Complex.rightSemicircleStaircaseSafeRe ρ m k -
          Complex.rightSemicircleStaircasePrevSafeRe ρ m k|) +
      |(0 : ℝ) - Complex.rightSemicircleStaircaseSafeRe ρ m m| ≤ 2 * ρ := by
  let s : ℕ → ℝ := fun k =>
    Complex.rightSemicircleStaircaseSafeRe ρ m k
  have hbounds : ∀ k : ℕ, k ≤ m → 0 ≤ s k ∧ s k ≤ ρ := by
    intro k hk
    have hcell : k ∈ Finset.range (m + 1) := by
      simpa [Finset.mem_range] using Nat.lt_succ_iff.mpr hk
    have hleft :
        0 ≤ Complex.rightSemicircleStaircaseSafeRe ρ m k :=
      Complex.rightSemicircleStaircaseSafeRe_nonneg hρ m k
    have hright :
        Complex.rightSemicircleStaircaseSafeRe ρ m k ≤ ρ :=
      Complex.rightSemicircleStaircaseSafeRe_le_radius hρ hcell
    exact And.intro hleft hright
  have hgeneric :
      (∑ k in Finset.range (m + 1),
          |s k - if k = 0 then (0 : ℝ) else s (k - 1)|) +
        |(0 : ℝ) - s m| ≤ 2 * ρ :=
    sum_abs_sub_prev_add_top_le_two_mul_of_bounded_unimodal
      s m j hjm hbounds
      (by
        intro k hk
        exact hmono k hk)
      (by
        intro k hjk hkm
        exact hanti k hjk hkm)
  simpa [s, Complex.rightSemicircleStaircasePrevSafeRe] using hgeneric

/-- One step of the uniform staircase height grid. -/
theorem Complex.rightSemicircleStaircaseY_succ_sub
    (ρ : ℝ)
    (m k : ℕ) :
    Complex.rightSemicircleStaircaseY ρ m (k + 1) -
      Complex.rightSemicircleStaircaseY ρ m k =
        (2 * ρ) / (m + 1 : ℝ) := by
  dsimp [Complex.rightSemicircleStaircaseY]
  have hden : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hden]
  ring

/-- The staircase height grid is increasing. -/
theorem Complex.rightSemicircleStaircaseY_le_succ
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ) :
    Complex.rightSemicircleStaircaseY ρ m k ≤
      Complex.rightSemicircleStaircaseY ρ m (k + 1) := by
  have hstep :
      0 ≤
        Complex.rightSemicircleStaircaseY ρ m (k + 1) -
          Complex.rightSemicircleStaircaseY ρ m k := by
    rw [Complex.rightSemicircleStaircaseY_succ_sub]
    exact div_nonneg (mul_nonneg (by norm_num) hρ) (by positivity)
  exact sub_nonneg.mp hstep

/-- Grid points up to the midpoint have nonpositive height. -/
theorem Complex.rightSemicircleStaircaseY_nonpos_of_le_midpoint
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    {m k : ℕ}
    (hk : k ≤ (m + 1) / 2) :
    Complex.rightSemicircleStaircaseY ρ m k ≤ 0 := by
  have hmul_nat : k * 2 ≤ m + 1 :=
    Nat.mul_le_of_le_div 2 k (m + 1) hk
  have hmul_real : 2 * (k : ℝ) ≤ (m + 1 : ℝ) := by
    exact_mod_cast (by simpa [mul_comm] using hmul_nat)
  have hden_pos : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
  have hratio_div : (2 * (k : ℝ)) / (m + 1 : ℝ) ≤ 1 :=
    (div_le_one hden_pos).mpr hmul_real
  have hratio : ((k : ℝ) / (m + 1 : ℝ)) * 2 ≤ 1 := by
    calc
      ((k : ℝ) / (m + 1 : ℝ)) * 2 =
          (2 * (k : ℝ)) / (m + 1 : ℝ) := by ring
      _ ≤ 1 := hratio_div
  have hmul :
      ((k : ℝ) / (m + 1 : ℝ)) * (2 * ρ) ≤ ρ := by
    calc
      ((k : ℝ) / (m + 1 : ℝ)) * (2 * ρ) =
          (((k : ℝ) / (m + 1 : ℝ)) * 2) * ρ := by ring
      _ ≤ 1 * ρ := mul_le_mul_of_nonneg_right hratio hρ
      _ = ρ := by ring
  dsimp [Complex.rightSemicircleStaircaseY]
  linarith

/-- The upper endpoint of every cell at or after the midpoint has
nonnegative height. -/
theorem Complex.rightSemicircleStaircaseY_succ_nonneg_of_midpoint_le
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    {m k : ℕ}
    (hk : (m + 1) / 2 ≤ k) :
    0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1) := by
  have hle_pred : m + 1 ≤ 2 * k + 1 := by
    exact (Nat.div_le_iff_le_mul_add_pred Nat.two_pos).mp hk
  have hle_nat : m + 1 ≤ 2 * (k + 1) := by
    omega
  have hle_real : (m + 1 : ℝ) ≤ 2 * ((k + 1 : ℕ) : ℝ) := by
    exact_mod_cast hle_nat
  have hden_pos : 0 < ((m + 1 : ℕ) : ℝ) := by positivity
  have hratio_div : 1 ≤ (2 * ((k + 1 : ℕ) : ℝ)) / (m + 1 : ℝ) := by
    rw [one_le_div hden_pos]
    exact hle_real
  have hratio :
      1 ≤ (((k + 1 : ℕ) : ℝ) / (m + 1 : ℝ)) * 2 := by
    calc
      1 ≤ (2 * ((k + 1 : ℕ) : ℝ)) / (m + 1 : ℝ) := hratio_div
      _ = (((k + 1 : ℕ) : ℝ) / (m + 1 : ℝ)) * 2 := by ring
  have hmul :
      ρ ≤ (((k + 1 : ℕ) : ℝ) / (m + 1 : ℝ)) * (2 * ρ) := by
    calc
      ρ = 1 * ρ := by ring
      _ ≤ ((((k + 1 : ℕ) : ℝ) / (m + 1 : ℝ)) * 2) * ρ :=
          mul_le_mul_of_nonneg_right hratio hρ
      _ = (((k + 1 : ℕ) : ℝ) / (m + 1 : ℝ)) * (2 * ρ) := by ring
  dsimp [Complex.rightSemicircleStaircaseY]
  linarith

/-- On the nonpositive half of the vertical diameter, the right semicircle
graph real coordinate is monotone increasing. -/
theorem Complex.rightSemicircleGraphRe_mono_nonpos
    (ρ : ℝ)
    {a b : ℝ}
    (hab : a ≤ b)
    (hb : b ≤ 0) :
    Complex.rightSemicircleGraphRe ρ a ≤
      Complex.rightSemicircleGraphRe ρ b := by
  have ha : a ≤ 0 := le_trans hab hb
  have habs : |b| ≤ |a| := by
    rw [abs_of_nonpos hb, abs_of_nonpos ha]
    linarith
  have hsq : b ^ 2 ≤ a ^ 2 := by
    simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg b) habs 2
  have hrad : ρ ^ 2 - a ^ 2 ≤ ρ ^ 2 - b ^ 2 := by
    linarith
  dsimp [Complex.rightSemicircleGraphRe]
  exact Real.sqrt_le_sqrt hrad

/-- On the nonnegative half of the vertical diameter, the right semicircle
graph real coordinate is monotone decreasing. -/
theorem Complex.rightSemicircleGraphRe_antitone_nonneg
    (ρ : ℝ)
    {a b : ℝ}
    (ha : 0 ≤ a)
    (hab : a ≤ b) :
    Complex.rightSemicircleGraphRe ρ b ≤
      Complex.rightSemicircleGraphRe ρ a := by
  have hb : 0 ≤ b := le_trans ha hab
  have habs : |a| ≤ |b| := by
    rw [abs_of_nonneg ha, abs_of_nonneg hb]
    exact hab
  have hsq : a ^ 2 ≤ b ^ 2 := by
    simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg a) habs 2
  have hrad : ρ ^ 2 - b ^ 2 ≤ ρ ^ 2 - a ^ 2 := by
    linarith
  dsimp [Complex.rightSemicircleGraphRe]
  exact Real.sqrt_le_sqrt hrad

/-- The safe coordinate dominates the graph at the left endpoint of its cell. -/
theorem Complex.rightSemicircleStaircaseSafeRe_ge_left_endpoint_graph
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1)) :
    Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m k) ≤
      Complex.rightSemicircleStaircaseSafeRe ρ m k := by
  dsimp [Complex.rightSemicircleStaircaseSafeRe]
  by_cases hcross :
      Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1)
  · rw [if_pos hcross]
    have hk0 : k ∈ Finset.range (m + 2) := by
      exact Complex.staircase_lower_sample_mem_range hk
    exact Complex.rightSemicircleGraphRe_le_radius hρ
      (Complex.rightSemicircleStaircaseY_mem_Icc hρ m k hk0)
  · rw [if_neg hcross]
    exact le_max_left _ _

/-- On a cell whose upper height is nonpositive, the safe coordinate is the
right endpoint graph value. -/
theorem Complex.rightSemicircleStaircaseSafeRe_eq_right_endpoint_of_upper_nonpos
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
    (hupper :
      Complex.rightSemicircleStaircaseY ρ m (k + 1) ≤ 0) :
    Complex.rightSemicircleStaircaseSafeRe ρ m k =
      Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m (k + 1)) := by
  let y₀ : ℝ := Complex.rightSemicircleStaircaseY ρ m k
  let y₁ : ℝ := Complex.rightSemicircleStaircaseY ρ m (k + 1)
  dsimp [Complex.rightSemicircleStaircaseSafeRe]
  by_cases hcross : y₀ ≤ 0 ∧ 0 ≤ y₁
  · have hy₁_zero : y₁ = 0 := le_antisymm hupper hcross.2
    have hgraph_zero : Complex.rightSemicircleGraphRe ρ y₁ = ρ := by
      rw [hy₁_zero]
      dsimp [Complex.rightSemicircleGraphRe]
      rw [zero_sq, sub_zero, sq, Real.sqrt_mul_self hρ]
    rw [if_pos hcross, hgraph_zero]
  · rw [if_neg hcross]
    have hy₀_le_y₁ : y₀ ≤ y₁ := by
      exact Complex.rightSemicircleStaircaseY_le_succ hρ m k
    have hgraph_le :
        Complex.rightSemicircleGraphRe ρ y₀ ≤
          Complex.rightSemicircleGraphRe ρ y₁ :=
      Complex.rightSemicircleGraphRe_mono_nonpos ρ hy₀_le_y₁ hupper
    exact max_eq_right hgraph_le

/-- On a cell whose lower height is nonnegative, the safe coordinate is the
left endpoint graph value. -/
theorem Complex.rightSemicircleStaircaseSafeRe_eq_left_endpoint_of_lower_nonneg
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
    (hlower :
      0 ≤ Complex.rightSemicircleStaircaseY ρ m k) :
    Complex.rightSemicircleStaircaseSafeRe ρ m k =
      Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m k) := by
  let y₀ : ℝ := Complex.rightSemicircleStaircaseY ρ m k
  let y₁ : ℝ := Complex.rightSemicircleStaircaseY ρ m (k + 1)
  dsimp [Complex.rightSemicircleStaircaseSafeRe]
  by_cases hcross : y₀ ≤ 0 ∧ 0 ≤ y₁
  · have hy₀_zero : y₀ = 0 := le_antisymm hcross.1 hlower
    have hgraph_zero : Complex.rightSemicircleGraphRe ρ y₀ = ρ := by
      rw [hy₀_zero]
      dsimp [Complex.rightSemicircleGraphRe]
      rw [zero_sq, sub_zero, sq, Real.sqrt_mul_self hρ]
    rw [if_pos hcross, hgraph_zero]
  · rw [if_neg hcross]
    have hy₀_le_y₁ : y₀ ≤ y₁ := by
      exact Complex.rightSemicircleStaircaseY_le_succ hρ m k
    have hgraph_le :
        Complex.rightSemicircleGraphRe ρ y₁ ≤
          Complex.rightSemicircleGraphRe ρ y₀ :=
      Complex.rightSemicircleGraphRe_antitone_nonneg ρ hlower hy₀_le_y₁
    exact max_eq_left hgraph_le

/-- The safe right-semicircle staircase real coordinates increase up to the
height cell containing the midpoint height `0`. -/
theorem Complex.rightSemicircleStaircaseSafeRe_monotone_prefix_midpoint
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m : ℕ) :
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
      Nat.div_lt_self (Nat.succ_pos m) (by norm_num : 1 < 2)
    exact Finset.mem_range.mpr (lt_of_le_of_lt hk_succ_le_mid hhalf_lt)
  have hsafe_right :
      Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m (k + 1)) ≤
        Complex.rightSemicircleStaircaseSafeRe ρ m (k + 1) :=
    Complex.rightSemicircleStaircaseSafeRe_ge_left_endpoint_graph
      hρ m (k + 1) hk1_range
  rw [hsafe_left]
  exact hsafe_right

/-- The safe right-semicircle staircase real coordinates decrease after the
height cell containing the midpoint height `0`. -/
theorem Complex.rightSemicircleStaircaseSafeRe_antitone_suffix_midpoint
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m : ℕ) :
    ∀ k : ℕ, (m + 1) / 2 ≤ k → k < m →
      Complex.rightSemicircleStaircaseSafeRe ρ m (k + 1) ≤
        Complex.rightSemicircleStaircaseSafeRe ρ m k := by
  intro k hmid_le_k hkm
  have hy_succ_nonneg :
      0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1) :=
    Complex.rightSemicircleStaircaseY_succ_nonneg_of_midpoint_le
      hρ hmid_le_k
  by_cases hcross :
      Complex.rightSemicircleStaircaseY ρ m k ≤ 0 ∧
        0 ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1)
  · have hsafe_left :
        Complex.rightSemicircleStaircaseSafeRe ρ m k = ρ := by
      dsimp [Complex.rightSemicircleStaircaseSafeRe]
      rw [if_pos hcross]
    have hk1_range : k + 1 ∈ Finset.range (m + 1) := by
      exact Finset.mem_range.mpr (Nat.succ_lt_succ hkm)
    have hsafe_right_mem :
        Complex.rightSemicircleStaircaseSafeRe ρ m (k + 1) ∈ [[(0 : ℝ), ρ]] :=
      Complex.rightSemicircleStaircaseSafeRe_mem_Icc hρ m (k + 1) hk1_range
    have hsafe_right_le :
        Complex.rightSemicircleStaircaseSafeRe ρ m (k + 1) ≤ ρ := by
      have hpair :
          0 ≤ Complex.rightSemicircleStaircaseSafeRe ρ m (k + 1) ∧
            Complex.rightSemicircleStaircaseSafeRe ρ m (k + 1) ≤ ρ := by
        simpa [Set.uIcc_of_le hρ] using hsafe_right_mem
      exact hpair.2
    rw [hsafe_left]
    exact hsafe_right_le
  · have hy_nonneg :
        0 ≤ Complex.rightSemicircleStaircaseY ρ m k := by
      by_cases hy_nonpos : Complex.rightSemicircleStaircaseY ρ m k ≤ 0
      · exact False.elim (hcross ⟨hy_nonpos, hy_succ_nonneg⟩)
      · exact le_of_not_ge hy_nonpos
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
    rw [hsafe_left, hsafe_right]
    exact hgraph

/-- Squaring preserves the minimum of two nonnegative real numbers. -/
theorem min_sq_sq {a b : ℝ}
    (ha : 0 ≤ a)
    (hb : 0 ≤ b) :
    (min a b) ^ 2 = min (a ^ 2) (b ^ 2) := by
  apply le_antisymm
  · exact le_min
      (pow_le_pow_left₀ ha (min_le_left a b) 2)
      (pow_le_pow_left₀ hb (min_le_right a b) 2)
  · by_cases hab : a ≤ b
    · have hmin : min a b = a := min_eq_left hab
      have hminsq : min (a ^ 2) (b ^ 2) = a ^ 2 := by
        exact min_eq_left (pow_le_pow_left₀ ha hab 2)
      rw [hmin, hminsq]
    · have hba : b ≤ a := le_of_not_ge hab
      have hmin : min a b = b := min_eq_right hba
      have hminsq : min (a ^ 2) (b ^ 2) = b ^ 2 := by
        exact min_eq_right (pow_le_pow_left₀ hb hba 2)
      rw [hmin, hminsq]

/-- Subtracting from a fixed real number turns endpoint minimum into endpoint
maximum. -/
theorem max_sub_sub_left_eq_sub_min
    (a b c : ℝ) :
    max (a - b) (a - c) = a - min b c := by
  by_cases hbc : b ≤ c
  · have hmin : min b c = b := min_eq_left hbc
    have hmax : max (a - b) (a - c) = a - b := by
      exact max_eq_left (sub_le_sub_left hbc a)
    rw [hmin, hmax]
  · have hcb : c ≤ b := le_of_not_ge hbc
    have hmin : min b c = c := min_eq_right hcb
    have hmax : max (a - b) (a - c) = a - c := by
      exact max_eq_right (sub_le_sub_left hcb a)
    rw [hmin, hmax]

namespace Real

/-- Square-root distributes over binary maximum. -/
theorem sqrt_max (a b : ℝ) :
    Real.sqrt (max a b) = max (Real.sqrt a) (Real.sqrt b) := by
  by_cases hab : a ≤ b
  · have hmax : max a b = b := max_eq_right hab
    have hmaxsqrt : max (Real.sqrt a) (Real.sqrt b) = Real.sqrt b := by
      exact max_eq_right (Real.sqrt_le_sqrt hab)
    rw [hmax, hmaxsqrt]
  · have hba : b ≤ a := le_of_not_ge hab
    have hmax : max a b = a := max_eq_left hba
    have hmaxsqrt : max (Real.sqrt a) (Real.sqrt b) = Real.sqrt a := by
      exact max_eq_left (Real.sqrt_le_sqrt hba)
    rw [hmax, hmaxsqrt]

end Real

/-- The right semicircle graph on a vertical interval is bounded by the safe
endpoint/crossing value. -/
theorem Complex.rightSemicircleGraphRe_le_safeRe_of_mem_cell
    {ρ y₀ y₁ y : ℝ}
    (hρ : 0 ≤ ρ)
    (hy₀ : y₀ ∈ [[-ρ, ρ]])
    (hy₁ : y₁ ∈ [[-ρ, ρ]])
    (hy : y ∈ [[y₀, y₁]]) :
    Complex.rightSemicircleGraphRe ρ y ≤
      if y₀ ≤ 0 ∧ 0 ≤ y₁ then
        ρ
      else
        max (Complex.rightSemicircleGraphRe ρ y₀)
          (Complex.rightSemicircleGraphRe ρ y₁) := by
  by_cases hcross : y₀ ≤ 0 ∧ 0 ≤ y₁
  · rw [if_pos hcross]
    have hy_bounds : y ∈ [[-ρ, ρ]] := by
      have hy₀_bounds : -ρ ≤ y₀ ∧ y₀ ≤ ρ := by
        simpa [Set.uIcc_of_le (by linarith : -ρ ≤ ρ)] using hy₀
      have hy₁_bounds : -ρ ≤ y₁ ∧ y₁ ≤ ρ := by
        simpa [Set.uIcc_of_le (by linarith : -ρ ≤ ρ)] using hy₁
      have hy_pair :
          (y₀ ≤ y ∧ y ≤ y₁) ∨ (y₁ ≤ y ∧ y ≤ y₀) := by
        simpa [Set.mem_uIcc] using hy
      rcases hy_pair with hy_pair | hy_pair
      · have hleft : -ρ ≤ y := le_trans hy₀_bounds.1 hy_pair.1
        have hright : y ≤ ρ := le_trans hy_pair.2 hy₁_bounds.2
        simpa [Set.uIcc_of_le (by linarith : -ρ ≤ ρ)] using And.intro hleft hright
      · have hleft : -ρ ≤ y := le_trans hy₁_bounds.1 hy_pair.1
        have hright : y ≤ ρ := le_trans hy_pair.2 hy₀_bounds.2
        simpa [Set.uIcc_of_le (by linarith : -ρ ≤ ρ)] using And.intro hleft hright
    exact Complex.rightSemicircleGraphRe_le_radius hρ hy_bounds
  · rw [if_neg hcross]
    have hy_pair :
        (y₀ ≤ y ∧ y ≤ y₁) ∨ (y₁ ≤ y ∧ y ≤ y₀) := by
      simpa [Set.mem_uIcc] using hy
    have hsame_side : y₁ ≤ 0 ∨ 0 ≤ y₀ := by
      have hle_or : y₀ ≤ y₁ ∨ y₁ ≤ y₀ := le_total y₀ y₁
      rcases hle_or with hle | hle
      · have hnot : ¬ (y₀ ≤ 0 ∧ 0 ≤ y₁) := hcross
        exact Or.elim (le_total y₁ 0)
          (fun hy₁_nonpos => Or.inl hy₁_nonpos)
          (fun h0_le_y₁ =>
            Or.inr
              (by
                by_contra hy₀_not
                exact hnot ⟨le_of_not_ge hy₀_not, h0_le_y₁⟩))
      · have hnot : ¬ (y₁ ≤ 0 ∧ 0 ≤ y₀) := by
          intro h
          exact hcross ⟨le_trans hle h.1, le_trans h.2 hle⟩
        exact Or.elim (le_total y₀ 0)
          (fun hy₀_nonpos =>
            Or.inl (le_trans hle hy₀_nonpos))
          (fun h0_le_y₀ => Or.inr h0_le_y₀)
    rcases hsame_side with hnonpos | hnonneg
    · have h_abs_le_endpoint :
          |y| ≥ min |y₀| |y₁| := by
        have hy_nonpos : y ≤ 0 := by
          rcases hy_pair with hy_pair | hy_pair
          · exact le_trans hy_pair.2 hnonpos
          · exact le_trans hy_pair.1 hnonpos
        have hy₀_nonpos : y₀ ≤ 0 := by
          rcases hy_pair with hy_pair | hy_pair
          · exact le_trans hy_pair.1 (le_trans hy_pair.2 hnonpos)
          · exact hnonpos
        have hy₁_nonpos : y₁ ≤ 0 := hnonpos
        rcases hy_pair with hy_pair | hy_pair
        · have h0 : |y₁| ≤ |y| := by
            rw [abs_of_nonpos hy₁_nonpos, abs_of_nonpos hy_nonpos]
            linarith
          exact le_trans (min_le_right |y₀| |y₁|) h0
        · have h0 : |y₀| ≤ |y| := by
            rw [abs_of_nonpos hy₀_nonpos, abs_of_nonpos hy_nonpos]
            linarith
          exact le_trans (min_le_left |y₀| |y₁|) h0
      have hsq_ge : min (y₀ ^ 2) (y₁ ^ 2) ≤ y ^ 2 := by
        have habs_sq : min |y₀| |y₁| ^ 2 ≤ |y| ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg y) h_abs_le_endpoint 2
        have hmin_sq : min (y₀ ^ 2) (y₁ ^ 2) = min |y₀| |y₁| ^ 2 := by
          rw [sq_abs y₀, sq_abs y₁]
          exact (min_sq_sq (abs_nonneg y₀) (abs_nonneg y₁)).symm
        simpa [sq_abs y] using hmin_sq ▸ habs_sq
      have hrad_le_endpoint :
          ρ ^ 2 - y ^ 2 ≤ max (ρ ^ 2 - y₀ ^ 2) (ρ ^ 2 - y₁ ^ 2) := by
        have hmax_sub :
            max (ρ ^ 2 - y₀ ^ 2) (ρ ^ 2 - y₁ ^ 2) =
              ρ ^ 2 - min (y₀ ^ 2) (y₁ ^ 2) := by
          exact max_sub_sub_left_eq_sub_min (ρ ^ 2) (y₀ ^ 2) (y₁ ^ 2)
        rw [hmax_sub]
        exact sub_le_sub_left hsq_ge (ρ ^ 2)
      have hsqrt :
          Complex.rightSemicircleGraphRe ρ y ≤
            max (Complex.rightSemicircleGraphRe ρ y₀)
              (Complex.rightSemicircleGraphRe ρ y₁) := by
        dsimp [Complex.rightSemicircleGraphRe]
        rw [Real.sqrt_max]
        exact Real.sqrt_le_sqrt hrad_le_endpoint
      exact hsqrt
    · have h_abs_le_endpoint :
          |y| ≥ min |y₀| |y₁| := by
        have hy_nonneg : 0 ≤ y := by
          rcases hy_pair with hy_pair | hy_pair
          · exact le_trans hnonneg hy_pair.1
          · exact le_trans hnonneg hy_pair.2
        have hy₀_nonneg : 0 ≤ y₀ := hnonneg
        have hy₁_nonneg : 0 ≤ y₁ := by
          rcases hy_pair with hy_pair | hy_pair
          · exact le_trans hnonneg hy_pair.1
          · exact le_trans hnonneg hy_pair.2
        rcases hy_pair with hy_pair | hy_pair
        · have h0 : |y₀| ≤ |y| := by
            rw [abs_of_nonneg hy₀_nonneg, abs_of_nonneg hy_nonneg]
            linarith
          exact le_trans (min_le_left |y₀| |y₁|) h0
        · have h0 : |y₁| ≤ |y| := by
            rw [abs_of_nonneg hy₁_nonneg, abs_of_nonneg hy_nonneg]
            linarith
          exact le_trans (min_le_right |y₀| |y₁|) h0
      have hsq_ge : min (y₀ ^ 2) (y₁ ^ 2) ≤ y ^ 2 := by
        have habs_sq : min |y₀| |y₁| ^ 2 ≤ |y| ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg y) h_abs_le_endpoint 2
        have hmin_sq : min (y₀ ^ 2) (y₁ ^ 2) = min |y₀| |y₁| ^ 2 := by
          rw [sq_abs y₀, sq_abs y₁]
          exact (min_sq_sq (abs_nonneg y₀) (abs_nonneg y₁)).symm
        simpa [sq_abs y] using hmin_sq ▸ habs_sq
      have hrad_le_endpoint :
          ρ ^ 2 - y ^ 2 ≤ max (ρ ^ 2 - y₀ ^ 2) (ρ ^ 2 - y₁ ^ 2) := by
        have hmax_sub :
            max (ρ ^ 2 - y₀ ^ 2) (ρ ^ 2 - y₁ ^ 2) =
              ρ ^ 2 - min (y₀ ^ 2) (y₁ ^ 2) := by
          exact max_sub_sub_left_eq_sub_min (ρ ^ 2) (y₀ ^ 2) (y₁ ^ 2)
        rw [hmax_sub]
        exact sub_le_sub_left hsq_ge (ρ ^ 2)
      have hsqrt :
          Complex.rightSemicircleGraphRe ρ y ≤
            max (Complex.rightSemicircleGraphRe ρ y₀)
              (Complex.rightSemicircleGraphRe ρ y₁) := by
        dsimp [Complex.rightSemicircleGraphRe]
        rw [Real.sqrt_max]
        exact Real.sqrt_le_sqrt hrad_le_endpoint
      exact hsqrt

/-- The safe staircase real coordinate dominates the circular graph on its
vertical cell. -/
theorem Complex.rightSemicircleStaircaseSafeRe_ge_graph_on_cell
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1))
    {y : ℝ}
    (hy :
      y ∈
        [[Complex.rightSemicircleStaircaseY ρ m k,
          Complex.rightSemicircleStaircaseY ρ m (k + 1)]]) :
    Complex.rightSemicircleGraphRe ρ y ≤
      Complex.rightSemicircleStaircaseSafeRe ρ m k := by
  have hk0 : k ∈ Finset.range (m + 2) := by
    exact Complex.staircase_lower_sample_mem_range hk
  have hk1 : k + 1 ∈ Finset.range (m + 2) := by
    exact Complex.staircase_upper_sample_mem_range hk
  have hy0 :
      Complex.rightSemicircleStaircaseY ρ m k ∈ [[-ρ, ρ]] :=
    Complex.rightSemicircleStaircaseY_mem_Icc hρ m k hk0
  have hy1 :
      Complex.rightSemicircleStaircaseY ρ m (k + 1) ∈ [[-ρ, ρ]] :=
    Complex.rightSemicircleStaircaseY_mem_Icc hρ m (k + 1) hk1
  exact
    Complex.rightSemicircleGraphRe_le_safeRe_of_mem_cell
      hρ hy0 hy1 hy

/-- The safe staircase real coordinate is the graph value at one point of its
own vertical cell.  In the crossing cell the witness is the midpoint height
`0`; otherwise it is one of the two cell endpoints. -/
theorem Complex.exists_rightSemicircleStaircaseSafeRe_eq_graphRe_of_cell
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1)) :
    ∃ yₛ ∈
        [[Complex.rightSemicircleStaircaseY ρ m k,
          Complex.rightSemicircleStaircaseY ρ m (k + 1)]],
      Complex.rightSemicircleStaircaseSafeRe ρ m k =
        Complex.rightSemicircleGraphRe ρ yₛ := by
  let y₀ : ℝ := Complex.rightSemicircleStaircaseY ρ m k
  let y₁ : ℝ := Complex.rightSemicircleStaircaseY ρ m (k + 1)
  by_cases hcross : y₀ ≤ 0 ∧ 0 ≤ y₁
  · refine ⟨0, ?_, ?_⟩
    · exact
        (Set.mem_uIcc).mpr
          (Or.inl ⟨hcross.1, hcross.2⟩)
    · have hgraph_zero :
          Complex.rightSemicircleGraphRe ρ 0 = ρ := by
        dsimp [Complex.rightSemicircleGraphRe]
        rw [zero_sq, sub_zero, sq, Real.sqrt_mul_self hρ.le]
      dsimp [Complex.rightSemicircleStaircaseSafeRe, y₀, y₁] at hcross ⊢
      rw [if_pos hcross, hgraph_zero]
  · dsimp [Complex.rightSemicircleStaircaseSafeRe]
    rw [if_neg hcross]
    by_cases hmax :
        Complex.rightSemicircleGraphRe ρ y₀ ≤
          Complex.rightSemicircleGraphRe ρ y₁
    · refine ⟨y₁, right_mem_uIcc, ?_⟩
      exact max_eq_right hmax
    · refine ⟨y₀, left_mem_uIcc, ?_⟩
      exact max_eq_left (le_of_not_ge hmax)

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
        Complex.rightSemicircleStaircaseY ρ m k| := by
  exact dist_le_uIcc_length_of_mem hy hy'

/-- The previous safe real coordinate dominates the graph at the current
bottom sample. -/
theorem Complex.rightSemicircleStaircasePrevSafeRe_ge_currentGraph
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1)) :
    Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m k) ≤
      Complex.rightSemicircleStaircasePrevSafeRe ρ m k := by
  by_cases hk0 : k = 0
  · subst k
    have hgraph_zero :
        Complex.rightSemicircleGraphRe ρ
            (Complex.rightSemicircleStaircaseY ρ m 0) = 0 := by
      rw [Complex.rightSemicircleStaircaseY_zero]
      exact Complex.rightSemicircleGraphRe_bottom
    rw [hgraph_zero]
    dsimp [Complex.rightSemicircleStaircasePrevSafeRe]
    exact le_rfl
  ·
    have hkpred_range : k - 1 ∈ Finset.range (m + 1) := by
      exact Complex.staircase_pred_mem_range_of_ne_zero hk hk0
    have hy_mem :
        Complex.rightSemicircleStaircaseY ρ m k ∈
          [[Complex.rightSemicircleStaircaseY ρ m (k - 1),
            Complex.rightSemicircleStaircaseY ρ m ((k - 1) + 1)]] := by
      have hsucc : (k - 1) + 1 = k :=
        Complex.staircase_pred_succ_of_ne_zero hk0
      rw [hsucc]
      exact right_mem_uIcc
    have hdom :
        Complex.rightSemicircleGraphRe ρ
            (Complex.rightSemicircleStaircaseY ρ m k) ≤
          Complex.rightSemicircleStaircaseSafeRe ρ m (k - 1) :=
      Complex.rightSemicircleStaircaseSafeRe_ge_graph_on_cell
        hρ m (k - 1) hkpred_range hy_mem
    simpa [Complex.rightSemicircleStaircasePrevSafeRe, hk0] using hdom

/-- The current safe real coordinate dominates the graph at the current bottom
sample. -/
theorem Complex.rightSemicircleStaircaseSafeRe_ge_currentGraph
    {ρ : ℝ}
    (hρ : 0 ≤ ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1)) :
    Complex.rightSemicircleGraphRe ρ
        (Complex.rightSemicircleStaircaseY ρ m k) ≤
      Complex.rightSemicircleStaircaseSafeRe ρ m k := by
  have hy_mem :
      Complex.rightSemicircleStaircaseY ρ m k ∈
        [[Complex.rightSemicircleStaircaseY ρ m k,
          Complex.rightSemicircleStaircaseY ρ m (k + 1)]] :=
    left_mem_uIcc
  exact
    Complex.rightSemicircleStaircaseSafeRe_ge_graph_on_cell
      hρ m k hk hy_mem

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
        (Complex.rightSemicircleStaircaseY ρ m k) ≤ x := by
  have hprev :
      Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k) ≤
        Complex.rightSemicircleStaircasePrevSafeRe ρ m k :=
    Complex.rightSemicircleStaircasePrevSafeRe_ge_currentGraph hρ m k hk
  have hsafe :
      Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k) ≤
        Complex.rightSemicircleStaircaseSafeRe ρ m k :=
    Complex.rightSemicircleStaircaseSafeRe_ge_currentGraph hρ m k hk
  have hx_pair :
      (Complex.rightSemicircleStaircasePrevSafeRe ρ m k ≤ x ∧
          x ≤ Complex.rightSemicircleStaircaseSafeRe ρ m k) ∨
        (Complex.rightSemicircleStaircaseSafeRe ρ m k ≤ x ∧
          x ≤ Complex.rightSemicircleStaircasePrevSafeRe ρ m k) := by
    simpa [Set.mem_uIcc] using hx
  rcases hx_pair with hx_pair | hx_pair
  · exact le_trans hprev hx_pair.1
  · exact le_trans hsafe hx_pair.1

/-- Graph-side criterion for membership in the deleted right half-collar. -/
theorem Complex.rightSemicircleGraphPoint_mem_core
    (c : ℂ)
    {ρ x y : ℝ}
    (hρ : 0 < ρ)
    (hx : x ∈ [[(0 : ℝ), ρ]])
    (hy : y ∈ [[-ρ, ρ]])
    (hgraph : Complex.rightSemicircleGraphRe ρ y ≤ x) :
    (((c.re + x : ℝ) : ℂ) + Complex.I * (((c.im + y : ℝ) : ℂ))) ∈
      Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
  let z : ℂ :=
    (((c.re + x : ℝ) : ℂ) + Complex.I * (((c.im + y : ℝ) : ℂ)))
  have hx_bounds : 0 ≤ x ∧ x ≤ ρ := by
    simpa [Set.uIcc_of_le hρ.le] using hx
  have hy_bounds : -ρ ≤ y ∧ y ≤ ρ := by
    simpa [Set.uIcc_of_le (by linarith [hρ.le] : -ρ ≤ ρ)] using hy
  have hz_re : z.re = c.re + x := by
    dsimp [z]
    simp
  have hz_im : z.im = c.im + y := by
    dsimp [z]
    simp
  have hre_mem : z.re ∈ [[c.re, c.re + ρ]] := by
    rw [hz_re]
    have hleft : c.re ≤ c.re + x := by
      linarith
    have hright : c.re + x ≤ c.re + ρ := by
      linarith
    simpa [Set.uIcc_of_le (by linarith [hρ.le] : c.re ≤ c.re + ρ)] using
      And.intro hleft hright
  have him_mem : z.im ∈ [[c.im - ρ, c.im + ρ]] := by
    rw [hz_im]
    have hleft : c.im - ρ ≤ c.im + y := by
      linarith
    have hright : c.im + y ≤ c.im + ρ := by
      linarith
    simpa [Set.uIcc_of_le (by linarith [hρ.le] : c.im - ρ ≤ c.im + ρ)] using
      And.intro hleft hright
  have hx_shift : z.re - c.re ∈ [[(0 : ℝ), ρ]] := by
    rw [hz_re]
    simpa [Set.uIcc_of_le hρ.le] using hx_bounds
  have hy_shift : z.im - c.im ∈ [[-ρ, ρ]] := by
    rw [hz_im]
    simpa [Set.uIcc_of_le (by linarith [hρ.le] : -ρ ≤ ρ)] using hy_bounds
  have hgraph_shift :
      Real.sqrt (ρ ^ 2 - (z.im - c.im) ^ 2) ≤ z.re - c.re := by
    rw [hz_re, hz_im]
    dsimp [Complex.rightSemicircleGraphRe] at hgraph
    simpa using hgraph
  have hcircle :
      ρ ≤ Real.sqrt ((z.re - c.re) ^ 2 + (z.im - c.im) ^ 2) :=
    (Real.tangentBox_outside_circle_iff_graph_right
      hρ hx_shift hy_shift).mpr hgraph_shift
  have hnot_ball : z ∉ Metric.ball c ρ := by
    intro hball
    have hdist_lt : dist z c < ρ := by
      simpa [Metric.mem_ball] using hball
    have hdist_ge : ρ ≤ dist z c := by
      simpa [Complex.dist_eq_re_im] using hcircle
    exact not_lt_of_ge hdist_ge hdist_lt
  exact ⟨⟨hre_mem, him_mem⟩, hnot_ball⟩

/-- Exterior staircase approximation to the inner right semicircle, oriented
from the bottom tangent point to the top tangent point.

The staircase uses horizontal connectors and vertical graph-majorant sides
inside the tangent box.  Every path segment stays in the deleted collar, unlike
the chord chain through the disk and unlike the tangent polygon outside the
fixed box. -/
noncomputable def Complex.rightSemicirclePolygonalArcIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) : ℂ :=
  (∑ k in Finset.range (m + 1),
      Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k +
        Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k) +
    Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m

/-- A horizontal staircase connector lies in the deleted right-half-collar. -/
theorem Complex.rightSemicircleStaircaseHorizontal_subset_core
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1))
    {x : ℝ}
    (hx :
      x ∈
        [[Complex.rightSemicircleStaircasePrevSafeRe ρ m k,
          Complex.rightSemicircleStaircaseSafeRe ρ m k]]) :
    (((c.re + x : ℝ) : ℂ) +
      Complex.I * (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))) ∈
      Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
  have hxprev :
      Complex.rightSemicircleStaircasePrevSafeRe ρ m k ∈ [[(0 : ℝ), ρ]] :=
    Complex.rightSemicircleStaircasePrevSafeRe_mem_Icc hρ.le m k hk
  have hxsafe :
      Complex.rightSemicircleStaircaseSafeRe ρ m k ∈ [[(0 : ℝ), ρ]] :=
    Complex.rightSemicircleStaircaseSafeRe_mem_Icc hρ.le m k hk
  have hx_bounds : x ∈ [[(0 : ℝ), ρ]] := by
    exact
      mem_uIcc_of_mem_uIcc_endpoints
        hρ.le hxprev hxsafe hx
  have hy_bounds :
      Complex.rightSemicircleStaircaseY ρ m k ∈ [[-ρ, ρ]] :=
    Complex.rightSemicircleStaircaseY_mem_Icc hρ.le m k
      (Complex.staircase_lower_sample_mem_range hk)
  have hgraph :
      Complex.rightSemicircleGraphRe ρ
          (Complex.rightSemicircleStaircaseY ρ m k) ≤ x :=
    Complex.rightSemicircleStaircaseHorizontal_re_ge_graph hρ.le m k hk hx
  exact
    Complex.rightSemicircleGraphPoint_mem_core
      c hρ hx_bounds hy_bounds hgraph

/-- A vertical staircase side lies in the deleted right-half-collar. -/
theorem Complex.rightSemicircleStaircaseVertical_subset_core
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1))
    {y : ℝ}
    (hy :
      y ∈
        [[Complex.rightSemicircleStaircaseY ρ m k,
          Complex.rightSemicircleStaircaseY ρ m (k + 1)]]) :
    (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
      Complex.I * (((c.im + y : ℝ) : ℂ))) ∈
      Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
  have hx_bounds :
      Complex.rightSemicircleStaircaseSafeRe ρ m k ∈ [[(0 : ℝ), ρ]] :=
    Complex.rightSemicircleStaircaseSafeRe_mem_Icc hρ.le m k hk
  have hy0 :
      Complex.rightSemicircleStaircaseY ρ m k ∈ [[-ρ, ρ]] :=
    Complex.rightSemicircleStaircaseY_mem_Icc hρ.le m k
      (Complex.staircase_lower_sample_mem_range hk)
  have hy1 :
      Complex.rightSemicircleStaircaseY ρ m (k + 1) ∈ [[-ρ, ρ]] :=
    Complex.rightSemicircleStaircaseY_mem_Icc hρ.le m (k + 1)
      (Complex.staircase_upper_sample_mem_range hk)
  have hy_bounds : y ∈ [[-ρ, ρ]] := by
    exact
      mem_uIcc_of_mem_uIcc_endpoints
        (Complex.neg_radius_le_radius hρ.le) hy0 hy1 hy
  have hgraph :
      Complex.rightSemicircleGraphRe ρ y ≤
        Complex.rightSemicircleStaircaseSafeRe ρ m k :=
    Complex.rightSemicircleStaircaseSafeRe_ge_graph_on_cell hρ.le m k hk hy
  exact
    Complex.rightSemicircleGraphPoint_mem_core
      c hρ hx_bounds hy_bounds hgraph

/-- The top staircase connector lies in the deleted right-half-collar. -/
theorem Complex.rightSemicircleStaircaseTopConnector_subset_core
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m : ℕ)
    {x : ℝ}
    (hx : x ∈ [[Complex.rightSemicircleStaircaseSafeRe ρ m m, 0]]) :
    (((c.re + x : ℝ) : ℂ) +
      Complex.I * (((c.im + ρ : ℝ) : ℂ))) ∈
      Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
  have hx_safe :
      Complex.rightSemicircleStaircaseSafeRe ρ m m ∈ [[(0 : ℝ), ρ]] :=
    Complex.rightSemicircleStaircaseSafeRe_last_mem_Icc hρ.le m
  have hx_bounds : x ∈ [[(0 : ℝ), ρ]] := by
    have hzero : (0 : ℝ) ∈ [[(0 : ℝ), ρ]] :=
      Complex.zero_mem_radius_uIcc hρ.le
    exact
      mem_uIcc_of_mem_uIcc_endpoints
        hρ.le hx_safe hzero hx
  have hy_bounds : ρ ∈ [[-ρ, ρ]] := by
    exact Complex.radius_mem_semicircle_height_uIcc hρ.le
  have hgraph : Complex.rightSemicircleGraphRe ρ ρ ≤ x := by
    have hgraph_zero : Complex.rightSemicircleGraphRe ρ ρ = 0 := by
      dsimp [Complex.rightSemicircleGraphRe]
      rw [sub_self, Real.sqrt_zero]
    have hx_nonneg : 0 ≤ x := by
      have hxbounds : 0 ≤ x ∧ x ≤ ρ := by
        simpa [Set.uIcc_of_le hρ.le] using hx_bounds
      exact hxbounds.1
    rw [hgraph_zero]
    exact hx_nonneg
  exact
    Complex.rightSemicircleGraphPoint_mem_core
      c hρ hx_bounds hy_bounds hgraph

/-- Polygonal half-collar boundary with the fixed outer sides and a safe
exterior staircase approximation to the circular side.

The sign of the inner polygonal chain matches the deleted-boundary convention:
the positive semicircle is traversed bottom-to-top, and the punctured-domain
boundary subtracts it. -/
noncomputable def Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundaryIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) : ℂ :=
  (∫ x : ℝ in c.re..(c.re + ρ),
      f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) -
    (∫ x : ℝ in c.re..(c.re + ρ),
      f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) +
      Complex.I *
        (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
              f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
        Complex.rightSemicirclePolygonalArcIntegral f c ρ m

/-- Boundary integral of one rectangular strip in the staircase exhaustion. -/
noncomputable def Complex.rightSemicircleStaircaseCellBoundaryIntegral
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) : ℂ :=
  (∫ x : ℝ in
      (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k)..
        (c.re + ρ),
      f ((x : ℂ) +
        Complex.I * (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))) -
    (∫ x : ℝ in
      (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k)..
        (c.re + ρ),
      f ((x : ℂ) +
        Complex.I *
          (((c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) : ℝ) : ℂ)))) +
      Complex.I *
        (∫ y : ℝ in
          (c.im + Complex.rightSemicircleStaircaseY ρ m k)..
            (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)),
          f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
        Complex.I *
          (∫ y : ℝ in
            (c.im + Complex.rightSemicircleStaircaseY ρ m k)..
              (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)),
            f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
              Complex.I * (y : ℂ)))

/-- The closed rectangle of one staircase strip lies in the deleted
right-half-collar. -/
theorem Complex.rightSemicircleStaircaseCellRectangle_subset_core
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1)) :
    ([[c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k, c.re + ρ]] ×ℂ
        [[c.im + Complex.rightSemicircleStaircaseY ρ m k,
          c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)]]) ⊆
      Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
  intro z hz
  have hzdata := Complex.mem_reProdIm.mp hz
  let x : ℝ := z.re - c.re
  let y : ℝ := z.im - c.im
  have hz_eq :
      z = (((c.re + x : ℝ) : ℂ) + Complex.I * (((c.im + y : ℝ) : ℂ))) := by
    dsimp [x, y]
    ext <;> simp
  have hsafe_bounds :
      Complex.rightSemicircleStaircaseSafeRe ρ m k ∈ [[(0 : ℝ), ρ]] :=
    Complex.rightSemicircleStaircaseSafeRe_mem_Icc hρ.le m k hk
  have hx_pair :
      (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k ≤ z.re ∧
          z.re ≤ c.re + ρ) ∨
        (c.re + ρ ≤ z.re ∧
          z.re ≤ c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k) := by
    simpa [Set.mem_uIcc] using hzdata.1
  have hx_bounds : x ∈ [[(0 : ℝ), ρ]] := by
    have hsafe_pair : 0 ≤ Complex.rightSemicircleStaircaseSafeRe ρ m k ∧
        Complex.rightSemicircleStaircaseSafeRe ρ m k ≤ ρ := by
      simpa [Set.uIcc_of_le hρ.le] using hsafe_bounds
    rcases hx_pair with hx_pair | hx_pair
    · have hleft : 0 ≤ x := by
        dsimp [x]
        linarith
      have hright : x ≤ ρ := by
        dsimp [x]
        linarith
      simpa [Set.uIcc_of_le hρ.le] using And.intro hleft hright
    · have hleft : 0 ≤ x := by
        dsimp [x]
        linarith
      have hright : x ≤ ρ := by
        dsimp [x]
        linarith
      simpa [Set.uIcc_of_le hρ.le] using And.intro hleft hright
  have hy_pair :
      (c.im + Complex.rightSemicircleStaircaseY ρ m k ≤ z.im ∧
          z.im ≤ c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)) ∨
        (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) ≤ z.im ∧
          z.im ≤ c.im + Complex.rightSemicircleStaircaseY ρ m k) := by
    simpa [Set.mem_uIcc] using hzdata.2
  have hy_cell :
      y ∈ [[Complex.rightSemicircleStaircaseY ρ m k,
        Complex.rightSemicircleStaircaseY ρ m (k + 1)]] := by
    rcases hy_pair with hy_pair | hy_pair
    · have hleft : Complex.rightSemicircleStaircaseY ρ m k ≤ y := by
        dsimp [y]
        linarith
      have hright : y ≤ Complex.rightSemicircleStaircaseY ρ m (k + 1) := by
        dsimp [y]
        linarith
      exact Or.inl ⟨hleft, hright⟩
    · have hleft : Complex.rightSemicircleStaircaseY ρ m (k + 1) ≤ y := by
        dsimp [y]
        linarith
      have hright : y ≤ Complex.rightSemicircleStaircaseY ρ m k := by
        dsimp [y]
        linarith
      exact Or.inr ⟨hleft, hright⟩
  have hy_bounds : y ∈ [[-ρ, ρ]] := by
    have hk0 : k ∈ Finset.range (m + 2) := by
      exact Complex.staircase_lower_sample_mem_range hk
    have hk1 : k + 1 ∈ Finset.range (m + 2) := by
      exact Complex.staircase_upper_sample_mem_range hk
    have hy0 :=
      Complex.rightSemicircleStaircaseY_mem_Icc hρ.le m k hk0
    have hy1 :=
      Complex.rightSemicircleStaircaseY_mem_Icc hρ.le m (k + 1) hk1
    exact
      mem_uIcc_of_mem_uIcc_endpoints
        (Complex.neg_radius_le_radius hρ.le) hy0 hy1 hy_cell
  have hgraph_safe :
      Complex.rightSemicircleGraphRe ρ y ≤
        Complex.rightSemicircleStaircaseSafeRe ρ m k :=
    Complex.rightSemicircleStaircaseSafeRe_ge_graph_on_cell
      hρ.le m k hk hy_cell
  have hx_safe : Complex.rightSemicircleStaircaseSafeRe ρ m k ≤ x := by
    rcases hx_pair with hx_pair | hx_pair
    · dsimp [x]
      linarith
    · dsimp [x]
      have hsafe_pair : 0 ≤ Complex.rightSemicircleStaircaseSafeRe ρ m k ∧
          Complex.rightSemicircleStaircaseSafeRe ρ m k ≤ ρ := by
        simpa [Set.uIcc_of_le hρ.le] using hsafe_bounds
      linarith
  have hgraph : Complex.rightSemicircleGraphRe ρ y ≤ x :=
    le_trans hgraph_safe hx_safe
  rw [hz_eq]
  exact
    Complex.rightSemicircleGraphPoint_mem_core
      c hρ hx_bounds hy_bounds hgraph

/-- Cauchy-Goursat on one rectangular strip of the staircase exhaustion. -/
theorem Complex.rightSemicircleStaircaseCellBoundary_eq_zero
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1))
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Complex.rightSemicircleStaircaseCellBoundaryIntegral f c ρ m k = 0 := by
  let z₀ : ℂ :=
    (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
      Complex.I * (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))
  let z₁ : ℂ :=
    (((c.re + ρ : ℝ) : ℂ) +
      Complex.I * (((c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) : ℝ) : ℂ)))
  have hclosed :
      ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) ⊆
        Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
    dsimp [z₀, z₁]
    simpa using
      Complex.rightSemicircleStaircaseCellRectangle_subset_core
        c hρ m k hk
  have hopen :
      (Set.Ioo (min z₀.re z₁.re) (max z₀.re z₁.re) ×ℂ
          Set.Ioo (min z₀.im z₁.im) (max z₀.im z₁.im)) ⊆
        Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
    intro z hz
    have hclosed_rect :
        z ∈ ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) := by
      have hzdata := Complex.mem_reProdIm.mp hz
      exact
        Complex.mem_reProdIm.mpr
          ⟨Set.Ioo_subset_Icc_self hzdata.1,
            Set.Ioo_subset_Icc_self hzdata.2⟩
    exact hclosed hclosed_rect
  have hcontinuous_closed :
      ContinuousOn f ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) :=
    hcont.mono hclosed
  have hdifferentiable_open :
      DifferentiableOn ℂ f
        (Set.Ioo (min z₀.re z₁.re) (max z₀.re z₁.re) ×ℂ
          Set.Ioo (min z₀.im z₁.im) (max z₀.im z₁.im)) :=
    hdiff.mono hopen
  have hcauchy :
      (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₀.im : ℂ) * Complex.I)) -
          (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₁.im : ℂ) * Complex.I)) +
            Complex.I •
              (∫ y : ℝ in z₀.im..z₁.im, f ((z₁.re : ℂ) + (y : ℂ) * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in z₀.im..z₁.im, f ((z₀.re : ℂ) + (y : ℂ) * Complex.I)) =
        0 :=
    Complex.integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn
      f z₀ z₁ hcontinuous_closed hdifferentiable_open
  simpa [Complex.rightSemicircleStaircaseCellBoundaryIntegral, z₀, z₁,
    Algebra.smul_def, mul_comm, mul_left_comm, mul_assoc] using hcauchy

/-- Bottom endpoint of the staircase height partition. -/
theorem Complex.rightSemicircleStaircaseY_zero
    (ρ : ℝ)
    (m : ℕ) :
    Complex.rightSemicircleStaircaseY ρ m 0 = -ρ := by
  dsimp [Complex.rightSemicircleStaircaseY]
  ring

/-- Top endpoint of the staircase height partition. -/
theorem Complex.rightSemicircleStaircaseY_last
    (ρ : ℝ)
    (m : ℕ) :
    Complex.rightSemicircleStaircaseY ρ m (m + 1) = ρ := by
  dsimp [Complex.rightSemicircleStaircaseY]
  have hden : ((m + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have hratio : ((m + 1 : ℕ) : ℝ) / ((m + 1 : ℕ) : ℝ) = 1 :=
    div_self hden
  rw [hratio]
  ring

/-- The first previous-safe coordinate is the bottom tangent point. -/
theorem Complex.rightSemicircleStaircasePrevSafeRe_zero
    (ρ : ℝ)
    (m : ℕ) :
    Complex.rightSemicircleStaircasePrevSafeRe ρ m 0 = 0 := by
  simp [Complex.rightSemicircleStaircasePrevSafeRe]

/-- Successor previous-safe coordinate is the preceding safe coordinate. -/
theorem Complex.rightSemicircleStaircasePrevSafeRe_succ
    (ρ : ℝ)
    (m k : ℕ) :
    Complex.rightSemicircleStaircasePrevSafeRe ρ m (k + 1) =
      Complex.rightSemicircleStaircaseSafeRe ρ m k := by
  simp [Complex.rightSemicircleStaircasePrevSafeRe]

/-- Bottom endpoint of the translated staircase height partition. -/
theorem Complex.rightSemicircleStaircaseY_zero_add_im
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) :
    c.im + Complex.rightSemicircleStaircaseY ρ m 0 = c.im - ρ := by
  rw [Complex.rightSemicircleStaircaseY_zero]

/-- Top endpoint of the translated staircase height partition. -/
theorem Complex.rightSemicircleStaircaseY_last_add_im
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) :
    c.im + Complex.rightSemicircleStaircaseY ρ m (m + 1) = c.im + ρ := by
  rw [Complex.rightSemicircleStaircaseY_last]

/-- The first cell bottom side begins at the tangent point `c.re`. -/
theorem Complex.rightSemicircleStaircase_firstBottomStart
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) :
    c.re + Complex.rightSemicircleStaircasePrevSafeRe ρ m 0 = c.re := by
  rw [Complex.rightSemicircleStaircasePrevSafeRe_zero]
  exact add_zero c.re

/-- The `k+1`st bottom side starts where the `k`th vertical side sits. -/
theorem Complex.rightSemicircleStaircase_succBottomStart
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) :
    c.re + Complex.rightSemicircleStaircasePrevSafeRe ρ m (k + 1) =
      c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k := by
  rw [Complex.rightSemicircleStaircasePrevSafeRe_succ]

/-- The final top connector ends at the tangent point `c.re`. -/
theorem Complex.rightSemicircleStaircase_topConnectorEnd
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) :
    c.re + (0 : ℝ) = c.re := by
  exact add_zero c.re

/-- Horizontal staircase connectors are interval-integrable under continuity on
the deleted collar. -/
theorem Complex.intervalIntegrable_rightSemicircleStaircaseHorizontal
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1))
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    IntervalIntegrable
      (fun x : ℝ =>
        f (((c.re + x : ℝ) : ℂ) +
          Complex.I *
            (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))))
      volume
      (Complex.rightSemicircleStaircasePrevSafeRe ρ m k)
      (Complex.rightSemicircleStaircaseSafeRe ρ m k) := by
  have hmaps :
      MapsTo
        (fun x : ℝ =>
          (((c.re + x : ℝ) : ℂ) +
            Complex.I *
              (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))))
        [[Complex.rightSemicircleStaircasePrevSafeRe ρ m k,
          Complex.rightSemicircleStaircaseSafeRe ρ m k]]
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ) := by
    intro x hx
    exact
      Complex.rightSemicircleStaircaseHorizontal_subset_core
        c hρ m k hk hx
  have hparam :
      ContinuousOn
        (fun x : ℝ =>
          (((c.re + x : ℝ) : ℂ) +
            Complex.I *
              (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))))
        [[Complex.rightSemicircleStaircasePrevSafeRe ρ m k,
          Complex.rightSemicircleStaircaseSafeRe ρ m k]] := by
    exact
      ((continuous_const.add continuous_ofReal).add
        (continuous_const.mul continuous_const)).continuousOn
  exact (hcont.comp_continuousOn hparam hmaps).intervalIntegrable

/-- Vertical staircase sides are interval-integrable under continuity on the
deleted collar. -/
theorem Complex.intervalIntegrable_rightSemicircleStaircaseVertical
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1))
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    IntervalIntegrable
      (fun y : ℝ =>
        f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
          Complex.I * (((c.im + y : ℝ) : ℂ))))
      volume
      (Complex.rightSemicircleStaircaseY ρ m k)
      (Complex.rightSemicircleStaircaseY ρ m (k + 1)) := by
  have hmaps :
      MapsTo
        (fun y : ℝ =>
          (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
            Complex.I * (((c.im + y : ℝ) : ℂ))))
        [[Complex.rightSemicircleStaircaseY ρ m k,
          Complex.rightSemicircleStaircaseY ρ m (k + 1)]]
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ) := by
    intro y hy
    exact
      Complex.rightSemicircleStaircaseVertical_subset_core
        c hρ m k hk hy
  have hparam :
      ContinuousOn
        (fun y : ℝ =>
          (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
            Complex.I * (((c.im + y : ℝ) : ℂ))))
        [[Complex.rightSemicircleStaircaseY ρ m k,
          Complex.rightSemicircleStaircaseY ρ m (k + 1)]] := by
    exact
      (continuous_const.add
        (continuous_const.mul
          (continuous_const.add continuous_ofReal))).continuousOn
  exact (hcont.comp_continuousOn hparam hmaps).intervalIntegrable

/-- The final top connector is interval-integrable under continuity on the
deleted collar. -/
theorem Complex.intervalIntegrable_rightSemicircleStaircaseTopConnector
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m : ℕ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    IntervalIntegrable
      (fun x : ℝ =>
        f (((c.re + x : ℝ) : ℂ) +
          Complex.I * (((c.im + ρ : ℝ) : ℂ))))
      volume
      (Complex.rightSemicircleStaircaseSafeRe ρ m m)
      0 := by
  have hmaps :
      MapsTo
        (fun x : ℝ =>
          (((c.re + x : ℝ) : ℂ) +
            Complex.I * (((c.im + ρ : ℝ) : ℂ))))
        [[Complex.rightSemicircleStaircaseSafeRe ρ m m, 0]]
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ) := by
    intro x hx
    exact
      Complex.rightSemicircleStaircaseTopConnector_subset_core
        c hρ m hx
  have hparam :
      ContinuousOn
        (fun x : ℝ =>
          (((c.re + x : ℝ) : ℂ) +
            Complex.I * (((c.im + ρ : ℝ) : ℂ))))
        [[Complex.rightSemicircleStaircaseSafeRe ρ m m, 0]] := by
    exact
      ((continuous_const.add continuous_ofReal).add
        (continuous_const.mul continuous_const)).continuousOn
  exact (hcont.comp_continuousOn hparam hmaps).intervalIntegrable

/-- Bottom right-tail side of a staircase cell is interval-integrable. -/
theorem Complex.intervalIntegrable_rightSemicircleStaircaseCellBottomTail
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1))
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    IntervalIntegrable
      (fun x : ℝ =>
        f ((x : ℂ) +
          Complex.I *
            (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))))
      volume
      (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k)
      (c.re + ρ) := by
  let z₀ : ℂ :=
    (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
      Complex.I * (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))
  let z₁ : ℂ :=
    (((c.re + ρ : ℝ) : ℂ) +
      Complex.I * (((c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) : ℝ) : ℂ)))
  have hrect :
      ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) ⊆
        Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
    dsimp [z₀, z₁]
    simpa using
      Complex.rightSemicircleStaircaseCellRectangle_subset_core
        c hρ m k hk
  have hmaps :
      MapsTo
        (fun x : ℝ =>
          ((x : ℂ) +
            Complex.I *
              (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))))
        [[c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k, c.re + ρ]]
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ) := by
    intro x hx
    exact hrect (Complex.mem_reProdIm.mpr ⟨by simpa [z₀, z₁] using hx, by
      dsimp [z₀, z₁]
      exact left_mem_uIcc⟩)
  have hparam :
      ContinuousOn
        (fun x : ℝ =>
          ((x : ℂ) +
            Complex.I *
              (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))))
        [[c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k, c.re + ρ]] := by
    exact (continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn
  exact (hcont.comp_continuousOn hparam hmaps).intervalIntegrable

/-- Top right-tail side of a staircase cell is interval-integrable. -/
theorem Complex.intervalIntegrable_rightSemicircleStaircaseCellTopTail
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1))
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    IntervalIntegrable
      (fun x : ℝ =>
        f ((x : ℂ) +
          Complex.I *
            (((c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) : ℝ) : ℂ))))
      volume
      (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k)
      (c.re + ρ) := by
  let z₀ : ℂ :=
    (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
      Complex.I * (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))
  let z₁ : ℂ :=
    (((c.re + ρ : ℝ) : ℂ) +
      Complex.I * (((c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) : ℝ) : ℂ)))
  have hrect :
      ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) ⊆
        Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
    dsimp [z₀, z₁]
    simpa using
      Complex.rightSemicircleStaircaseCellRectangle_subset_core
        c hρ m k hk
  have hmaps :
      MapsTo
        (fun x : ℝ =>
          ((x : ℂ) +
            Complex.I *
              (((c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) : ℝ) : ℂ))))
        [[c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k, c.re + ρ]]
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ) := by
    intro x hx
    exact hrect (Complex.mem_reProdIm.mpr ⟨by simpa [z₀, z₁] using hx, by
      dsimp [z₀, z₁]
      exact right_mem_uIcc⟩)
  have hparam :
      ContinuousOn
        (fun x : ℝ =>
          ((x : ℂ) +
            Complex.I *
              (((c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) : ℝ) : ℂ))))
        [[c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k, c.re + ρ]] := by
    exact (continuous_ofReal.add (continuous_const.mul continuous_const)).continuousOn
  exact (hcont.comp_continuousOn hparam hmaps).intervalIntegrable

/-- Outer vertical side of a staircase cell is interval-integrable. -/
theorem Complex.intervalIntegrable_rightSemicircleStaircaseCellOuterVertical
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m k : ℕ)
    (hk : k ∈ Finset.range (m + 1))
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    IntervalIntegrable
      (fun y : ℝ =>
        f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
      volume
      (c.im + Complex.rightSemicircleStaircaseY ρ m k)
      (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)) := by
  let z₀ : ℂ :=
    (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
      Complex.I * (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))
  let z₁ : ℂ :=
    (((c.re + ρ : ℝ) : ℂ) +
      Complex.I * (((c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) : ℝ) : ℂ)))
  have hrect :
      ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) ⊆
        Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
    dsimp [z₀, z₁]
    simpa using
      Complex.rightSemicircleStaircaseCellRectangle_subset_core
        c hρ m k hk
  have hmaps :
      MapsTo
        (fun y : ℝ =>
          (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
        [[c.im + Complex.rightSemicircleStaircaseY ρ m k,
          c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)]]
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ) := by
    intro y hy
    exact hrect (Complex.mem_reProdIm.mpr ⟨by
      dsimp [z₀, z₁]
      exact right_mem_uIcc, by
      dsimp [z₀, z₁]
      simpa using hy⟩)
  have hparam :
      ContinuousOn
        (fun y : ℝ =>
          (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
        [[c.im + Complex.rightSemicircleStaircaseY ρ m k,
          c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)]] := by
    exact (continuous_const.add (continuous_const.mul continuous_ofReal)).continuousOn
  exact (hcont.comp_continuousOn hparam hmaps).intervalIntegrable

/-- A finite chain of right-tail differences telescopes to the endpoint tails,
subtracting the intermediate connectors and the final reverse connector.

This is the interval-additivity owner lemma behind the horizontal part of the
staircase collar assembly.  The hypotheses are intentionally explicit:
splitting interval integrals in mathlib requires `IntervalIntegrable`, so the
geometry layer must supply continuity/integrability before using this lemma. -/
theorem Complex.sum_rightTail_integral_sub_successor_eq_endpoint_sub_connectors
    (F : ℕ → ℝ → ℂ)
    (x : ℕ → ℝ)
    (B : ℝ)
    (m : ℕ)
    (hconn :
      ∀ k ∈ Finset.range (m + 1),
        IntervalIntegrable (F k) volume (x k) (x (k + 1)))
    (htail :
      ∀ k ∈ Finset.range (m + 1),
        IntervalIntegrable (F k) volume (x (k + 1)) B)
    (hend_seg :
      IntervalIntegrable (F (m + 1)) volume (x 0) (x (m + 1)))
    (hend_tail :
      IntervalIntegrable (F (m + 1)) volume (x (m + 1)) B) :
    (∑ k in Finset.range (m + 1),
        ((∫ t : ℝ in (x (k + 1))..B, F k t) -
          (∫ t : ℝ in (x (k + 1))..B, F (k + 1) t))) =
      (∫ t : ℝ in (x 0)..B, F 0 t) -
        (∫ t : ℝ in (x 0)..B, F (m + 1) t) -
          (∑ k in Finset.range (m + 1),
            ∫ t : ℝ in (x k)..(x (k + 1)), F k t) -
          (∫ t : ℝ in (x (m + 1))..(x 0), F (m + 1) t) := by
  classical
  let T : ℕ → ℂ := fun k => ∫ t : ℝ in (x k)..B, F k t
  let C : ℕ → ℂ := fun k => ∫ t : ℝ in (x k)..(x (k + 1)), F k t
  have hsplit :
      ∀ k ∈ Finset.range (m + 1),
        (∫ t : ℝ in (x (k + 1))..B, F k t) = T k - C k := by
    intro k hk
    have hadd :
        (∫ t : ℝ in (x k)..(x (k + 1)), F k t) +
            (∫ t : ℝ in (x (k + 1))..B, F k t) =
          ∫ t : ℝ in (x k)..B, F k t :=
      intervalIntegral.integral_add_adjacent_intervals
        (hconn k hk) (htail k hk)
    dsimp [T, C]
    rw [← hadd]
    abel
  have hend :
      T (m + 1) =
        (∫ t : ℝ in (x 0)..B, F (m + 1) t) +
          (∫ t : ℝ in (x (m + 1))..(x 0), F (m + 1) t) := by
    have hadd :
        (∫ t : ℝ in (x 0)..(x (m + 1)), F (m + 1) t) +
            (∫ t : ℝ in (x (m + 1))..B, F (m + 1) t) =
          ∫ t : ℝ in (x 0)..B, F (m + 1) t :=
      intervalIntegral.integral_add_adjacent_intervals hend_seg hend_tail
    dsimp [T]
    rw [← hadd]
    rw [intervalIntegral.integral_symm]
    abel
  have htel :
      (∑ k in Finset.range (m + 1), ((T k - C k) - T (k + 1))) =
        T 0 - T (m + 1) - ∑ k in Finset.range (m + 1), C k := by
    rw [Finset.sum_sub_distrib]
    rw [Finset.sum_sub_distrib]
    have hsumT :
        (∑ k in Finset.range (m + 1), T k) -
            (∑ k in Finset.range (m + 1), T (k + 1)) =
          T 0 - T (m + 1) := by
      simpa using (Finset.sum_range_sub T (m + 1))
    rw [← sub_sub]
    rw [hsumT]
  calc
    (∑ k in Finset.range (m + 1),
        ((∫ t : ℝ in (x (k + 1))..B, F k t) -
          (∫ t : ℝ in (x (k + 1))..B, F (k + 1) t))) =
        ∑ k in Finset.range (m + 1), ((T k - C k) - T (k + 1)) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hsplit k hk]
      dsimp [T]
    _ = T 0 - T (m + 1) - ∑ k in Finset.range (m + 1), C k := htel
    _ =
      (∫ t : ℝ in (x 0)..B, F 0 t) -
        (∫ t : ℝ in (x 0)..B, F (m + 1) t) -
          (∑ k in Finset.range (m + 1),
            ∫ t : ℝ in (x k)..(x (k + 1)), F k t) -
          (∫ t : ℝ in (x (m + 1))..(x 0), F (m + 1) t) := by
      dsimp [T, C] at hend ⊢
      rw [hend]
      abel

/-- Relative and absolute parametrizations of one horizontal staircase
connector agree. -/
theorem Complex.rightSemicircleStaircaseHorizontalIntegral_eq_absolute
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m k : ℕ) :
    Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k =
      ∫ x : ℝ in
        (c.re + Complex.rightSemicircleStaircasePrevSafeRe ρ m k)..
          (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k),
        f ((x : ℂ) +
          Complex.I *
            (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))) := by
  let G : ℝ → ℂ := fun x =>
    f ((x : ℂ) +
      Complex.I *
        (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))
  have htranslate :
      (∫ x : ℝ in
          Complex.rightSemicircleStaircasePrevSafeRe ρ m k..
            Complex.rightSemicircleStaircaseSafeRe ρ m k,
          G (x + c.re)) =
        ∫ x : ℝ in
          (Complex.rightSemicircleStaircasePrevSafeRe ρ m k + c.re)..
            (Complex.rightSemicircleStaircaseSafeRe ρ m k + c.re),
          G x := by
    exact
      intervalIntegral.integral_comp_add_right
        (f := G)
        (a := Complex.rightSemicircleStaircasePrevSafeRe ρ m k)
        (b := Complex.rightSemicircleStaircaseSafeRe ρ m k)
        c.re
  dsimp [Complex.rightSemicircleStaircaseHorizontalIntegral, G]
  rw [htranslate]
  congr 2
  · rw [add_comm]
  · rw [add_comm]

/-- Relative and absolute parametrizations of the top staircase connector
agree. -/
theorem Complex.rightSemicircleStaircaseTopConnectorIntegral_eq_absolute
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) :
    Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m =
      ∫ x : ℝ in
        (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m m)..c.re,
        f ((x : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ)) := by
  let G : ℝ → ℂ := fun x =>
    f ((x : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))
  have htranslate :
      (∫ x : ℝ in
          Complex.rightSemicircleStaircaseSafeRe ρ m m..0,
          G (x + c.re)) =
        ∫ x : ℝ in
          (Complex.rightSemicircleStaircaseSafeRe ρ m m + c.re)..(0 + c.re),
          G x := by
    exact
      intervalIntegral.integral_comp_add_right
        (f := G)
        (a := Complex.rightSemicircleStaircaseSafeRe ρ m m)
        (b := 0)
        c.re
  dsimp [Complex.rightSemicircleStaircaseTopConnectorIntegral, G]
  rw [htranslate]
  congr 2
  · rw [add_comm]
  · rw [zero_add]

/-- Paired horizontal sides of the staircase-cell rectangles telescope to the
outer bottom side minus the outer top side and the staircase horizontal
connectors. -/
theorem Complex.sum_rightSemicircleStaircaseCellHorizontal_eq_outerHorizontal_sub_arcHorizontal
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m : ℕ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    (∑ k in Finset.range (m + 1),
        ((∫ x : ℝ in
            (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k)..(c.re + ρ),
            f ((x : ℂ) +
              Complex.I *
                (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))) -
          (∫ x : ℝ in
            (c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k)..(c.re + ρ),
            f ((x : ℂ) +
              Complex.I *
                (((c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1) : ℝ) : ℂ)))))) =
      (∫ x : ℝ in c.re..(c.re + ρ),
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) -
        (∫ x : ℝ in c.re..(c.re + ρ),
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) -
        (∑ k in Finset.range (m + 1),
          Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k) +
        Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m := by
  let F : ℕ → ℝ → ℂ := fun k x =>
    f ((x : ℂ) +
      Complex.I *
        (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ)))
  let X : ℕ → ℝ := fun k =>
    c.re + Complex.rightSemicircleStaircasePrevSafeRe ρ m k
  let B : ℝ := c.re + ρ
  have hconn :
      ∀ k ∈ Finset.range (m + 1),
        IntervalIntegrable (F k) volume (X k) (X (k + 1)) := by
    intro k hk
    have hrel :
        IntervalIntegrable
          (fun x : ℝ =>
            f (((c.re + x : ℝ) : ℂ) +
              Complex.I *
                (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))))
          volume
          (Complex.rightSemicircleStaircasePrevSafeRe ρ m k)
          (Complex.rightSemicircleStaircaseSafeRe ρ m k) :=
      Complex.intervalIntegrable_rightSemicircleStaircaseHorizontal
        f c hρ m k hk hcont
    have hshift := hrel.comp_add_right (-c.re)
    dsimp [F, X] at hshift ⊢
    rw [Complex.rightSemicircleStaircasePrevSafeRe_succ]
    simpa [sub_neg_eq_add, add_comm, add_left_comm, add_assoc] using hshift
  have htail :
      ∀ k ∈ Finset.range (m + 1),
        IntervalIntegrable (F k) volume (X (k + 1)) B := by
    intro k hk
    dsimp [F, X, B]
    rw [Complex.rightSemicircleStaircasePrevSafeRe_succ]
    exact
      Complex.intervalIntegrable_rightSemicircleStaircaseCellBottomTail
        f c hρ m k hk hcont
  have hend_seg :
      IntervalIntegrable (F (m + 1)) volume (X 0) (X (m + 1)) := by
    have hrel :
        IntervalIntegrable
          (fun x : ℝ =>
            f (((c.re + x : ℝ) : ℂ) +
              Complex.I * (((c.im + ρ : ℝ) : ℂ))))
          volume
          (Complex.rightSemicircleStaircaseSafeRe ρ m m)
          0 :=
      Complex.intervalIntegrable_rightSemicircleStaircaseTopConnector
        f c hρ m hcont
    have hshift := hrel.comp_add_right (-c.re)
    have hsymm := hshift.symm
    dsimp [F, X] at hsymm ⊢
    rw [Complex.rightSemicircleStaircasePrevSafeRe_zero,
      Complex.rightSemicircleStaircasePrevSafeRe_succ,
      Complex.rightSemicircleStaircaseY_last]
    simpa [sub_neg_eq_add, add_comm, add_left_comm, add_assoc] using hsymm
  have hend_tail :
      IntervalIntegrable (F (m + 1)) volume (X (m + 1)) B := by
    have hm : m ∈ Finset.range (m + 1) := by
      simpa [Finset.mem_range] using Nat.lt_succ_self m
    dsimp [F, X, B]
    rw [Complex.rightSemicircleStaircasePrevSafeRe_succ,
      Complex.rightSemicircleStaircaseY_last]
    exact
      Complex.intervalIntegrable_rightSemicircleStaircaseCellTopTail
        f c hρ m m hm hcont
  have htail_tel :=
    Complex.sum_rightTail_integral_sub_successor_eq_endpoint_sub_connectors
      F X B m hconn htail hend_seg hend_tail
  have hconnectors :
      (∑ k in Finset.range (m + 1),
          ∫ t : ℝ in X k..X (k + 1), F k t) =
        ∑ k in Finset.range (m + 1),
          Complex.rightSemicircleStaircaseHorizontalIntegral f c ρ m k := by
    apply Finset.sum_congr rfl
    intro k _hk
    dsimp [F, X]
    rw [Complex.rightSemicircleStaircasePrevSafeRe_succ]
    exact
      (Complex.rightSemicircleStaircaseHorizontalIntegral_eq_absolute
        f c ρ m k).symm
  have htop :
      (∫ t : ℝ in X (m + 1)..X 0, F (m + 1) t) =
        Complex.rightSemicircleStaircaseTopConnectorIntegral f c ρ m := by
    dsimp [F, X]
    rw [Complex.rightSemicircleStaircasePrevSafeRe_succ,
      Complex.rightSemicircleStaircasePrevSafeRe_zero,
      Complex.rightSemicircleStaircaseY_last]
    exact
      (Complex.rightSemicircleStaircaseTopConnectorIntegral_eq_absolute
        f c ρ m).symm
  dsimp [F, X, B] at htail_tel
  rw [Complex.rightSemicircleStaircasePrevSafeRe_succ] at htail_tel
  rw [Complex.rightSemicircleStaircasePrevSafeRe_zero] at htail_tel
  rw [Complex.rightSemicircleStaircaseY_zero] at htail_tel
  rw [Complex.rightSemicircleStaircaseY_last] at htail_tel
  rw [hconnectors, htop] at htail_tel
  exact htail_tel

/-- Outer vertical sides of the staircase-cell rectangles concatenate to the
outer vertical side of the half-collar. -/
theorem Complex.sum_rightSemicircleStaircaseCellOuterVertical_eq_outerVertical
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m : ℕ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    (∑ k in Finset.range (m + 1),
        ∫ y : ℝ in
          (c.im + Complex.rightSemicircleStaircaseY ρ m k)..
            (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)),
          f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) =
      ∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
        f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)) := by
  let F : ℝ → ℂ := fun y =>
    f (((c.re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))
  let a : ℕ → ℝ := fun k =>
    c.im + Complex.rightSemicircleStaircaseY ρ m k
  have hA : a 0 = c.im - ρ := by
    dsimp [a]
    exact Complex.rightSemicircleStaircaseY_zero_add_im c ρ m
  have hB : a (m + 1) = c.im + ρ := by
    dsimp [a]
    exact Complex.rightSemicircleStaircaseY_last_add_im c ρ m
  have hint :
      ∀ k < m + 1, IntervalIntegrable F volume (a k) (a (k + 1)) := by
    intro k hk
    have hkrange : k ∈ Finset.range (m + 1) := by
      simpa [Finset.mem_range] using hk
    dsimp [F, a]
    exact
      Complex.intervalIntegrable_rightSemicircleStaircaseCellOuterVertical
        f c hρ m k hkrange hcont
  exact
    (Complex.integral_eq_sum_adjacent_intervals_of_endpoint_chain
      F a (m + 1) (c.im - ρ) (c.im + ρ) hA hB hint).symm

/-- Inner vertical sides of the staircase-cell rectangles are exactly the
vertical part of the staircase arc integral. -/
theorem Complex.sum_rightSemicircleStaircaseCellInnerVertical_eq_verticalArc
    (f : ℂ → ℂ)
    (c : ℂ)
    (ρ : ℝ)
    (m : ℕ) :
    (∑ k in Finset.range (m + 1),
        Complex.I *
          (∫ y : ℝ in
            (c.im + Complex.rightSemicircleStaircaseY ρ m k)..
              (c.im + Complex.rightSemicircleStaircaseY ρ m (k + 1)),
            f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
              Complex.I * (y : ℂ)))) =
      ∑ k in Finset.range (m + 1),
        Complex.rightSemicircleStaircaseVerticalIntegral f c ρ m k := by
  apply Finset.sum_congr rfl
  intro k _hk
  let G : ℝ → ℂ := fun y =>
    f (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
      Complex.I * (y : ℂ))
  have htranslate :
      (∫ y : ℝ in
          Complex.rightSemicircleStaircaseY ρ m k..
            Complex.rightSemicircleStaircaseY ρ m (k + 1),
          G (y + c.im)) =
        ∫ y : ℝ in
          (Complex.rightSemicircleStaircaseY ρ m k + c.im)..
            (Complex.rightSemicircleStaircaseY ρ m (k + 1) + c.im),
          G y := by
    exact
      intervalIntegral.integral_comp_add_right
        (f := G)
        (a := Complex.rightSemicircleStaircaseY ρ m k)
        (b := Complex.rightSemicircleStaircaseY ρ m (k + 1))
        c.im
  dsimp [Complex.rightSemicircleStaircaseVerticalIntegral, G]
  rw [← htranslate]
  congr 2
  · rw [add_comm]
  · rw [add_comm]

/-- The finite sum of staircase strip boundaries assembles to the polygonal
half-collar boundary. -/
theorem Complex.sum_rightSemicircleStaircaseCellBoundary_eq_polygonalCoreBoundary
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m : ℕ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    (∑ k in Finset.range (m + 1),
        Complex.rightSemicircleStaircaseCellBoundaryIntegral f c ρ m k) =
      Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundaryIntegral f c ρ m := by
  have hhorizontal :=
    Complex.sum_rightSemicircleStaircaseCellHorizontal_eq_outerHorizontal_sub_arcHorizontal
      f c hρ m hcont
  have houter :=
    Complex.sum_rightSemicircleStaircaseCellOuterVertical_eq_outerVertical
      f c hρ m hcont
  have hinner :=
    Complex.sum_rightSemicircleStaircaseCellInnerVertical_eq_verticalArc
      f c ρ m
  dsimp [Complex.rightSemicircleStaircaseCellBoundaryIntegral,
    Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundaryIntegral,
    Complex.rightSemicirclePolygonalArcIntegral]
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_add_distrib]
  rw [Finset.sum_sub_distrib]
  rw [hhorizontal, houter, hinner]
  abel

/-- Finite Cauchy-Goursat for the exterior staircase half-collar,
assuming the staircase sides are known to lie in the collar. -/
theorem Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundary_eq_zero_from_staircaseGeometry
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m : ℕ)
    (hhorizontal :
      ∀ k ∈ Finset.range (m + 1),
        ∀ x ∈
          [[Complex.rightSemicircleStaircasePrevSafeRe ρ m k,
            Complex.rightSemicircleStaircaseSafeRe ρ m k]],
          (((c.re + x : ℝ) : ℂ) +
            Complex.I *
              (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))) ∈
            Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)
    (hvertical :
      ∀ k ∈ Finset.range (m + 1),
        ∀ y ∈
          [[Complex.rightSemicircleStaircaseY ρ m k,
            Complex.rightSemicircleStaircaseY ρ m (k + 1)]],
          (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
            Complex.I * (((c.im + y : ℝ) : ℂ))) ∈
            Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)
    (htop :
      ∀ x ∈ [[Complex.rightSemicircleStaircaseSafeRe ρ m m, 0]],
        (((c.re + x : ℝ) : ℂ) +
          Complex.I * (((c.im + ρ : ℝ) : ℂ))) ∈
          Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundaryIntegral f c ρ m = 0 := by
  have hcell_zero :
      ∀ k ∈ Finset.range (m + 1),
        Complex.rightSemicircleStaircaseCellBoundaryIntegral f c ρ m k = 0 := by
    intro k hk
    exact
      Complex.rightSemicircleStaircaseCellBoundary_eq_zero
        f c hρ m k hk hcont hdiff
  have hsum_zero :
      (∑ k in Finset.range (m + 1),
          Complex.rightSemicircleStaircaseCellBoundaryIntegral f c ρ m k) = 0 := by
    exact Finset.sum_eq_zero hcell_zero
  have hassemble :
      (∑ k in Finset.range (m + 1),
          Complex.rightSemicircleStaircaseCellBoundaryIntegral f c ρ m k) =
        Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundaryIntegral f c ρ m :=
    Complex.sum_rightSemicircleStaircaseCellBoundary_eq_polygonalCoreBoundary
      f c hρ m hcont
  exact Eq.trans hassemble.symm hsum_zero

/-- Generic finite polygonal Cauchy-Goursat theorem for the right half-collar.

This is the finite path-integration owner theorem used by the local collar
argument.  The polygonal boundary is obtained by replacing the inner right
semicircle by its exterior staircase.  Cauchy-Goursat applies on the finite
polygonal subdivision of the half-collar, and internal chord contributions
cancel in pairs. -/
theorem Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundary_eq_zero_owner
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m : ℕ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundaryIntegral f c ρ m = 0 := by
  have hhorizontal :
      ∀ k ∈ Finset.range (m + 1),
        ∀ x ∈
          [[Complex.rightSemicircleStaircasePrevSafeRe ρ m k,
            Complex.rightSemicircleStaircaseSafeRe ρ m k]],
          (((c.re + x : ℝ) : ℂ) +
            Complex.I *
              (((c.im + Complex.rightSemicircleStaircaseY ρ m k : ℝ) : ℂ))) ∈
            Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
    intro k hk x hx
    exact
      Complex.rightSemicircleStaircaseHorizontal_subset_core
        c hρ m k hk hx
  have hvertical :
      ∀ k ∈ Finset.range (m + 1),
        ∀ y ∈
          [[Complex.rightSemicircleStaircaseY ρ m k,
            Complex.rightSemicircleStaircaseY ρ m (k + 1)]],
          (((c.re + Complex.rightSemicircleStaircaseSafeRe ρ m k : ℝ) : ℂ) +
            Complex.I * (((c.im + y : ℝ) : ℂ))) ∈
            Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
    intro k hk y hy
    exact
      Complex.rightSemicircleStaircaseVertical_subset_core
        c hρ m k hk hy
  have htop :
      ∀ x ∈ [[Complex.rightSemicircleStaircaseSafeRe ρ m m, 0]],
        (((c.re + x : ℝ) : ℂ) +
          Complex.I * (((c.im + ρ : ℝ) : ℂ))) ∈
          Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ := by
    intro x hx
    exact
      Complex.rightSemicircleStaircaseTopConnector_subset_core
        c hρ m hx
  exact
    Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundary_eq_zero_from_staircaseGeometry
      f c hρ m hhorizontal hvertical htop hcont hdiff

/-- Finite polygonal Cauchy-Goursat for the full right half-collar.

For each polygonal approximation to the deleted right semicircle, the polygonal
half-collar is decomposed into finitely many ordinary polygonal cells.  Cauchy-
Goursat kills each cell boundary, and all internal edges cancel, leaving the
displayed polygonal core boundary. -/
theorem Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundary_eq_zero
    (f : ℂ → ℂ)
    (c : ℂ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (m : ℕ)
    (hcont :
      ContinuousOn f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.rightHalfRectangleDeletedDiskCoreDomain c ρ ρ)) :
    Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundaryIntegral f c ρ m = 0 := by
  exact
    Complex.rightHalfRectangleDeletedDiskPolygonalCoreBoundary_eq_zero_owner
      f c hρ m hcont hdiff

end

end LFunctions
end Boundary
