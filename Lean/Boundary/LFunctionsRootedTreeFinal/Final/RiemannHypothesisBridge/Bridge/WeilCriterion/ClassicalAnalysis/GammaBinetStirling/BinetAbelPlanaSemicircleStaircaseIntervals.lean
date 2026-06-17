import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaSemicircleStaircaseDefinitions

/-!
# Interval lemmas for right semicircle staircases

This file owns the elementary unordered-interval and semicircle-height
membership facts used by the right staircase geometry.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology Interval
open Filter MeasureTheory

/-- A point in an unordered interval between two points of `[a,b]` belongs to
`[a,b]`. -/
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
  have hx_pair : (u ≤ x ∧ x ≤ v) ∨ (v ≤ x ∧ x ≤ u) :=
    Set.mem_uIcc.mp hx
  have hxIcc : x ∈ Set.Icc a b :=
    match hx_pair with
    | Or.inl hx_left =>
        And.intro
          (le_trans huIcc.1 hx_left.1)
          (le_trans hx_left.2 hvIcc.2)
    | Or.inr hx_right =>
        And.intro
          (le_trans hvIcc.1 hx_right.1)
          (le_trans hx_right.2 huIcc.2)
  exact hu_eq.symm ▸ hxIcc

/-- The left-to-right translated unordered-interval branch transports through
subtraction of the center. -/
theorem sub_center_mem_uIcc_left_branch
    {a b c z : ℝ}
    (h : c + a ≤ z ∧ z ≤ c + b) :
    z - c ∈ [[a, b]] := by
  exact Set.mem_uIcc.mpr
    (Or.inl
      (And.intro
        (by
          calc
            a = (c + a) - c := Eq.symm (add_sub_cancel_left c a)
            _ ≤ z - c := sub_le_sub_right h.1 c)
        (by
          calc
            z - c ≤ (c + b) - c := sub_le_sub_right h.2 c
            _ = b := add_sub_cancel_left c b)))

/-- The right-to-left translated unordered-interval branch transports through
subtraction of the center. -/
theorem sub_center_mem_uIcc_right_branch
    {a b c z : ℝ}
    (h : c + b ≤ z ∧ z ≤ c + a) :
    z - c ∈ [[a, b]] := by
  exact Set.mem_uIcc.mpr
    (Or.inr
      (And.intro
        (by
          calc
            b = (c + b) - c := Eq.symm (add_sub_cancel_left c b)
            _ ≤ z - c := sub_le_sub_right h.1 c)
        (by
          calc
            z - c ≤ (c + a) - c := sub_le_sub_right h.2 c
            _ = a := add_sub_cancel_left c a)))

/-- Subtracting a center transports membership in a translated unordered
interval back to the untranslated interval. -/
theorem sub_center_mem_uIcc_of_mem_translated_uIcc
    {a b c z : ℝ}
    (hz : z ∈ [[c + a, c + b]]) :
    z - c ∈ [[a, b]] := by
  have hpair :
      (c + a ≤ z ∧ z ≤ c + b) ∨ (c + b ≤ z ∧ z ≤ c + a) :=
    Set.mem_uIcc.mp hz
  exact
    match hpair with
    | Or.inl hleft => sub_center_mem_uIcc_left_branch hleft
    | Or.inr hright => sub_center_mem_uIcc_right_branch hright

/-- Subtracting a center transports membership in a translated ordered
interval back to ordered bounds. -/
theorem sub_center_bounds_of_mem_translated_ordered_uIcc
    {a b c z : ℝ}
    (hab : a ≤ b)
    (hz : z ∈ [[c + a, c + b]]) :
    a ≤ z - c ∧ z - c ≤ b :=
  Real.bounds_of_mem_uIcc hab
    (sub_center_mem_uIcc_of_mem_translated_uIcc hz)

/-- A point in the forward unordered branch of `[a,b]` is in the ordered
interval `[a,b]`. -/
theorem mem_Icc_of_uIcc_forward_branch
    {a b y : ℝ}
    (_hab : a ≤ b)
    (h : a ≤ y ∧ y ≤ b) :
    y ∈ Set.Icc a b :=
  h

/-- A point in the reverse unordered branch of `[a,b]` is in the ordered
interval `[a,b]` when `a ≤ b`. -/
theorem mem_Icc_of_uIcc_reverse_branch
    {a b y : ℝ}
    (hab : a ≤ b)
    (h : b ≤ y ∧ y ≤ a) :
    y ∈ Set.Icc a b :=
  And.intro
    (le_trans hab h.1)
    (le_trans h.2 hab)

/-- Membership in an unordered interval becomes ordered membership once the
endpoint order is chosen. -/
theorem mem_Icc_of_mem_uIcc_of_le
    {a b y : ℝ}
    (hab : a ≤ b)
    (hy : y ∈ [[a, b]]) :
    y ∈ Set.Icc a b := by
  have hy_pair : (a ≤ y ∧ y ≤ b) ∨ (b ≤ y ∧ y ≤ a) :=
    Set.mem_uIcc.mp hy
  exact
    match hy_pair with
    | Or.inl hforward => mem_Icc_of_uIcc_forward_branch hab hforward
    | Or.inr hreverse => mem_Icc_of_uIcc_reverse_branch hab hreverse

/-- Two points in an ordered interval are separated by at most the interval
length. -/
theorem dist_le_ordered_Icc_length_of_mem
    {a b y y' : ℝ}
    (hab : a ≤ b)
    (hy : y ∈ Set.Icc a b)
    (hy' : y' ∈ Set.Icc a b) :
    dist y y' ≤ |b - a| := by
  have hleft_raw : a - b ≤ y - y' := sub_le_sub hy.1 hy'.2
  have hleft_eq : -(b - a) = a - b := neg_sub b a
  have hleft : -(b - a) ≤ y - y' := hleft_eq ▸ hleft_raw
  have hright : y - y' ≤ b - a := sub_le_sub hy.2 hy'.1
  have habs_dist : |y - y'| ≤ b - a :=
    abs_le.mpr (And.intro hleft hright)
  have habs_length : b - a = |b - a| :=
    Eq.symm (abs_of_nonneg (sub_nonneg.mpr hab))
  have hdist_eq : dist y y' = |y - y'| := Real.dist_eq y y'
  exact
    hdist_eq.trans_le
      (Eq.mp (congrArg (fun t : ℝ => |y - y'| ≤ t) habs_length) habs_dist)

/-- Two points in an unordered real interval are separated by at most the
interval length. -/
theorem dist_le_uIcc_length_of_mem
    {a b y y' : ℝ}
    (hy : y ∈ [[a, b]])
    (hy' : y' ∈ [[a, b]]) :
    dist y y' ≤ |b - a| := by
  exact
    match le_total a b with
    | Or.inl hab =>
        dist_le_ordered_Icc_length_of_mem hab
          (mem_Icc_of_mem_uIcc_of_le hab hy)
          (mem_Icc_of_mem_uIcc_of_le hab hy')
    | Or.inr hba =>
        have hy_rev : y ∈ [[b, a]] :=
          (Set.uIcc_comm b a).symm ▸ hy
        have hy'_rev : y' ∈ [[b, a]] :=
          (Set.uIcc_comm b a).symm ▸ hy'
        have hdist : dist y y' ≤ |a - b| :=
          dist_le_ordered_Icc_length_of_mem hba
            (mem_Icc_of_mem_uIcc_of_le hba hy_rev)
            (mem_Icc_of_mem_uIcc_of_le hba hy'_rev)
        have hlength : |a - b| = |b - a| := by
          calc
            |a - b| = |-(b - a)| := by
              exact congrArg abs (Eq.symm (neg_sub b a))
            _ = |b - a| := abs_neg (b - a)
        Eq.mp (congrArg (fun t : ℝ => dist y y' ≤ t) hlength) hdist

/-- Difference bounds give membership in the center interval. -/
theorem center_bounds_of_abs_sub_le
    {u g δ : ℝ}
    (hu : |u - g| ≤ δ) :
    g - δ ≤ u ∧ u ≤ g + δ := by
  have hdiff : u - g ≤ δ ∧ g - u ≤ δ :=
    abs_sub_le_iff.mp hu
  have hleft : g - δ ≤ u := by
    exact sub_le_iff_le_add.mpr
      (by
        calc
          g ≤ δ + u := sub_le_iff_le_add.mp hdiff.2
          _ = u + δ := add_comm δ u)
  have hright : u ≤ g + δ := by
    calc
      u ≤ δ + g := sub_le_iff_le_add.mp hdiff.1
      _ = g + δ := add_comm δ g
  exact And.intro hleft hright

/-- Membership in a center interval gives an absolute-value bound. -/
theorem abs_sub_le_of_center_bounds
    {x g δ : ℝ}
    (hx : g - δ ≤ x ∧ x ≤ g + δ) :
    |x - g| ≤ δ := by
  have hright : x - g ≤ δ :=
    sub_le_iff_le_add.mpr
      (by
        calc
          x ≤ g + δ := hx.2
          _ = δ + g := add_comm g δ)
  have hleft : g - x ≤ δ := by
    exact sub_le_iff_le_add.mpr
      (by
        calc
          g ≤ x + δ := sub_le_iff_le_add.mp hx.1
          _ = δ + x := add_comm x δ)
  exact abs_sub_le_iff.mpr (And.intro hright hleft)

/-- If two endpoints lie in `[g - δ, g + δ]`, then every point in the unordered
interval between them has distance at most `δ` from `g`. -/
theorem abs_sub_le_of_mem_uIcc_of_endpoint_abs_sub_le
    {u v x g δ : ℝ}
    (hx : x ∈ [[u, v]])
    (hu : |u - g| ≤ δ)
    (hv : |v - g| ≤ δ) :
    |x - g| ≤ δ := by
  have hu_bounds : g - δ ≤ u ∧ u ≤ g + δ :=
    center_bounds_of_abs_sub_le hu
  have hv_bounds : g - δ ≤ v ∧ v ≤ g + δ :=
    center_bounds_of_abs_sub_le hv
  have hx_pair : (u ≤ x ∧ x ≤ v) ∨ (v ≤ x ∧ x ≤ u) :=
    Set.mem_uIcc.mp hx
  have hx_bounds : g - δ ≤ x ∧ x ≤ g + δ :=
    match hx_pair with
    | Or.inl hleft =>
        And.intro
          (le_trans hu_bounds.1 hleft.1)
          (le_trans hleft.2 hv_bounds.2)
    | Or.inr hright =>
        And.intro
          (le_trans hv_bounds.1 hright.1)
          (le_trans hright.2 hu_bounds.2)
  exact abs_sub_le_of_center_bounds hx_bounds

/-- Two points in `[0,ρ]` differ by at most `ρ`. -/
theorem abs_sub_le_radius_of_mem_radius_uIcc
    {ρ a b : ℝ}
    (hρ : 0 ≤ ρ)
    (ha : a ∈ [[(0 : ℝ), ρ]])
    (hb : b ∈ [[(0 : ℝ), ρ]]) :
    |a - b| ≤ ρ := by
  have haIcc : a ∈ Set.Icc (0 : ℝ) ρ :=
    (Set.uIcc_of_le hρ) ▸ ha
  have hbIcc : b ∈ Set.Icc (0 : ℝ) ρ :=
    (Set.uIcc_of_le hρ) ▸ hb
  have hleft : -ρ ≤ a - b := by
    have hraw : 0 - ρ ≤ a - b := sub_le_sub haIcc.1 hbIcc.2
    calc
      -ρ = 0 - ρ := Eq.symm (zero_sub ρ)
      _ ≤ a - b := hraw
  have hright : a - b ≤ ρ := by
    have hraw : a - b ≤ ρ - 0 := sub_le_sub haIcc.2 hbIcc.1
    calc
      a - b ≤ ρ - 0 := hraw
      _ = ρ := sub_zero ρ
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

/-- Membership in the semicircle height unordered interval is membership in the
ordered interval when the radius is nonnegative. -/
theorem Complex.mem_semicircle_height_Icc_of_mem_uIcc
    {ρ y : ℝ}
    (hρ : 0 ≤ ρ)
    (hy : y ∈ [[-ρ, ρ]]) :
    y ∈ Set.Icc (-ρ) ρ := by
  have huIcc : [[-ρ, ρ]] = Set.Icc (-ρ) ρ :=
    Set.uIcc_of_le (Complex.neg_radius_le_radius hρ)
  exact huIcc ▸ hy

/-- The top radius endpoint belongs to the ordered semicircle height interval. -/
theorem Complex.radius_mem_semicircle_height_Icc
    {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    ρ ∈ Set.Icc (-ρ) ρ :=
  Complex.mem_semicircle_height_Icc_of_mem_uIcc hρ
    (Complex.radius_mem_semicircle_height_uIcc hρ)

/-- The zero endpoint belongs to `[0,ρ]` when the radius is nonnegative. -/
theorem Complex.zero_mem_radius_uIcc
    {ρ : ℝ}
    (hρ : 0 ≤ ρ) :
    (0 : ℝ) ∈ [[(0 : ℝ), ρ]] :=
  left_endpoint_mem_uIcc_of_le hρ

end

end LFunctions
end Boundary
