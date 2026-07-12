import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.OscillatorySums.PhaseCutoff
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Geometry.Euclidean.Basic

/-!
# Canonical smooth cutoffs for finite integer blocks

The cutoff center is the midpoint of the two integer endpoints.  Its reference
radius is the larger endpoint distance.  The inner and outer radii add `1/3`
and `2/3`, respectively; hence every block integer lies in the closed inner
ball while the two neighboring integers lie outside the outer ball.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped ContDiff
open Set

/-- Ordered form of distance on the real line. -/
theorem Real.dist_eq_sub_of_le_explicit
    {x y : ℝ}
    (hxy : x ≤ y) :
    dist x y = y - x :=
  (Real.dist_eq x y).trans
    ((abs_of_nonpos (sub_nonpos.mpr hxy)).trans
      (neg_sub x y))

/-- Midpoint of an integer block, regarded as a real point. -/
def Real.integerBlockCutoffCenter
    (a b : ℤ) : ℝ :=
  midpoint ℝ (a : ℝ) (b : ℝ)

/-- Maximum distance from the midpoint to either endpoint. -/
def Real.integerBlockCutoffEndpointRadius
    (a b : ℤ) : ℝ :=
  max
    (dist (a : ℝ) (Real.integerBlockCutoffCenter a b))
    (dist (b : ℝ) (Real.integerBlockCutoffCenter a b))

/-- Inner radius of the canonical integer-block cutoff. -/
def Real.integerBlockCutoffInnerRadius
    (a b : ℤ) : ℝ :=
  Real.integerBlockCutoffEndpointRadius a b + 1 / 3

/-- Outer radius of the canonical integer-block cutoff. -/
def Real.integerBlockCutoffOuterRadius
    (a b : ℤ) : ℝ :=
  Real.integerBlockCutoffEndpointRadius a b + 2 / 3

/-- The endpoint reference radius is nonnegative. -/
theorem Real.integerBlockCutoffEndpointRadius_nonneg
    (a b : ℤ) :
    0 ≤ Real.integerBlockCutoffEndpointRadius a b :=
  le_trans
    dist_nonneg
    (le_max_left
      (dist (a : ℝ) (Real.integerBlockCutoffCenter a b))
      (dist (b : ℝ) (Real.integerBlockCutoffCenter a b)))

/-- The midpoint is equidistant from the two endpoints. -/
theorem Real.dist_left_integerBlockCutoffCenter_eq_right
    (a b : ℤ) :
    dist (a : ℝ) (Real.integerBlockCutoffCenter a b) =
      dist (b : ℝ) (Real.integerBlockCutoffCenter a b) :=
  EuclideanGeometry.dist_left_midpoint_eq_dist_right_midpoint
    (a : ℝ) (b : ℝ)

/-- The reference radius equals the distance from the left endpoint. -/
theorem Real.integerBlockCutoffEndpointRadius_eq_left
    (a b : ℤ) :
    Real.integerBlockCutoffEndpointRadius a b =
      dist (a : ℝ) (Real.integerBlockCutoffCenter a b) :=
  max_eq_left
    (le_of_eq
      (Real.dist_left_integerBlockCutoffCenter_eq_right a b).symm)

/-- The reference radius equals the distance from the right endpoint. -/
theorem Real.integerBlockCutoffEndpointRadius_eq_right
    (a b : ℤ) :
    Real.integerBlockCutoffEndpointRadius a b =
      dist (b : ℝ) (Real.integerBlockCutoffCenter a b) :=
  (Real.integerBlockCutoffEndpointRadius_eq_left a b).trans
    (Real.dist_left_integerBlockCutoffCenter_eq_right a b)

/-- For ordered endpoints, their midpoint belongs to the closed interval. -/
theorem Real.integerBlockCutoffCenter_mem_Icc
    {a b : ℤ}
    (hab : a ≤ b) :
    Real.integerBlockCutoffCenter a b ∈ Icc (a : ℝ) (b : ℝ) := by
  have habReal : (a : ℝ) ≤ (b : ℝ) :=
    Int.cast_le.mpr hab
  have hmidpoint :
      midpoint ℝ (a : ℝ) (b : ℝ) ∈
        segment ℝ (a : ℝ) (b : ℝ) :=
    midpoint_mem_segment (a : ℝ) (b : ℝ)
  have hsegment :
      segment ℝ (a : ℝ) (b : ℝ) =
        Icc (a : ℝ) (b : ℝ) :=
    segment_eq_Icc habReal
  exact
    Eq.subst
      (motive := fun carrier : Set ℝ =>
        Real.integerBlockCutoffCenter a b ∈ carrier)
      hsegment
      hmidpoint

/-- Distance is additive from a point left of the block through the left
endpoint to the block midpoint. -/
theorem Real.dist_add_dist_leftEndpoint_eq_dist_center
    {a b n : ℤ}
    (hab : a ≤ b)
    (hna : n ≤ a) :
    dist (n : ℝ) (a : ℝ) +
        dist (a : ℝ) (Real.integerBlockCutoffCenter a b) =
      dist (n : ℝ) (Real.integerBlockCutoffCenter a b) := by
  have hcenter := Real.integerBlockCutoffCenter_mem_Icc hab
  have hnReal : (n : ℝ) ≤ (a : ℝ) := Int.cast_le.mpr hna
  have hnc : (n : ℝ) ≤ Real.integerBlockCutoffCenter a b :=
    le_trans hnReal hcenter.1
  calc
    dist (n : ℝ) (a : ℝ) +
        dist (a : ℝ) (Real.integerBlockCutoffCenter a b) =
      ((a : ℝ) - (n : ℝ)) +
        (Real.integerBlockCutoffCenter a b - (a : ℝ)) :=
      congrArg₂ (fun u v : ℝ => u + v)
        (Real.dist_eq_sub_of_le_explicit hnReal)
        (Real.dist_eq_sub_of_le_explicit hcenter.1)
    _ = (Real.integerBlockCutoffCenter a b - (a : ℝ)) +
        ((a : ℝ) - (n : ℝ)) :=
      add_comm ((a : ℝ) - (n : ℝ))
        (Real.integerBlockCutoffCenter a b - (a : ℝ))
    _ = Real.integerBlockCutoffCenter a b - (n : ℝ) :=
      sub_add_sub_cancel
        (Real.integerBlockCutoffCenter a b) (a : ℝ) (n : ℝ)
    _ = dist (n : ℝ) (Real.integerBlockCutoffCenter a b) :=
      (Real.dist_eq_sub_of_le_explicit hnc).symm

/-- Real-point form of additivity through the left endpoint of an ordered
integer block. -/
theorem Real.dist_add_dist_leftEndpoint_eq_dist_center_real
    {a b : ℤ}
    {x : ℝ}
    (hab : a ≤ b)
    (hxa : x ≤ (a : ℝ)) :
    dist x (a : ℝ) +
        dist (a : ℝ) (Real.integerBlockCutoffCenter a b) =
      dist x (Real.integerBlockCutoffCenter a b) := by
  have hcenter := Real.integerBlockCutoffCenter_mem_Icc hab
  have hxc : x ≤ Real.integerBlockCutoffCenter a b :=
    le_trans hxa hcenter.1
  calc
    dist x (a : ℝ) +
        dist (a : ℝ) (Real.integerBlockCutoffCenter a b) =
      ((a : ℝ) - x) +
        (Real.integerBlockCutoffCenter a b - (a : ℝ)) :=
      congrArg₂ (fun left right : ℝ => left + right)
        (Real.dist_eq_sub_of_le_explicit hxa)
        (Real.dist_eq_sub_of_le_explicit hcenter.1)
    _ = (Real.integerBlockCutoffCenter a b - (a : ℝ)) +
        ((a : ℝ) - x) :=
      add_comm ((a : ℝ) - x)
        (Real.integerBlockCutoffCenter a b - (a : ℝ))
    _ = Real.integerBlockCutoffCenter a b - x :=
      sub_add_sub_cancel
        (Real.integerBlockCutoffCenter a b) (a : ℝ) x
    _ = dist x (Real.integerBlockCutoffCenter a b) :=
      (Real.dist_eq_sub_of_le_explicit hxc).symm

/-- Distance is additive from the block midpoint through the right endpoint
to a point right of the block. -/
theorem Real.dist_add_dist_rightEndpoint_eq_dist_center
    {a b n : ℤ}
    (hab : a ≤ b)
    (hbn : b ≤ n) :
    dist (b : ℝ) (n : ℝ) +
        dist (b : ℝ) (Real.integerBlockCutoffCenter a b) =
      dist (n : ℝ) (Real.integerBlockCutoffCenter a b) := by
  have hcenter := Real.integerBlockCutoffCenter_mem_Icc hab
  have hbnReal : (b : ℝ) ≤ (n : ℝ) := Int.cast_le.mpr hbn
  have hcn : Real.integerBlockCutoffCenter a b ≤ (n : ℝ) :=
    le_trans hcenter.2 hbnReal
  have hrightEndpoint :
      dist (b : ℝ) (Real.integerBlockCutoffCenter a b) =
        (b : ℝ) - Real.integerBlockCutoffCenter a b :=
    (dist_comm (b : ℝ) (Real.integerBlockCutoffCenter a b)).trans
      (Real.dist_eq_sub_of_le_explicit hcenter.2)
  calc
    dist (b : ℝ) (n : ℝ) +
        dist (b : ℝ) (Real.integerBlockCutoffCenter a b) =
      ((n : ℝ) - (b : ℝ)) +
        ((b : ℝ) - Real.integerBlockCutoffCenter a b) :=
      congrArg₂ (fun u v : ℝ => u + v)
        (Real.dist_eq_sub_of_le_explicit hbnReal)
        hrightEndpoint
    _ = (n : ℝ) - Real.integerBlockCutoffCenter a b :=
      sub_add_sub_cancel
        (n : ℝ) (b : ℝ) (Real.integerBlockCutoffCenter a b)
    _ = dist (n : ℝ) (Real.integerBlockCutoffCenter a b) :=
      ((dist_comm (n : ℝ) (Real.integerBlockCutoffCenter a b)).trans
        (Real.dist_eq_sub_of_le_explicit hcn)).symm

/-- Real-point form of additivity through the right endpoint of an ordered
integer block. -/
theorem Real.dist_add_dist_rightEndpoint_eq_dist_center_real
    {a b : ℤ}
    {x : ℝ}
    (hab : a ≤ b)
    (hbx : (b : ℝ) ≤ x) :
    dist (b : ℝ) x +
        dist (b : ℝ) (Real.integerBlockCutoffCenter a b) =
      dist x (Real.integerBlockCutoffCenter a b) := by
  have hcenter := Real.integerBlockCutoffCenter_mem_Icc hab
  have hcx : Real.integerBlockCutoffCenter a b ≤ x :=
    le_trans hcenter.2 hbx
  have hrightEndpoint :
      dist (b : ℝ) (Real.integerBlockCutoffCenter a b) =
        (b : ℝ) - Real.integerBlockCutoffCenter a b :=
    (dist_comm (b : ℝ) (Real.integerBlockCutoffCenter a b)).trans
      (Real.dist_eq_sub_of_le_explicit hcenter.2)
  calc
    dist (b : ℝ) x +
        dist (b : ℝ) (Real.integerBlockCutoffCenter a b) =
      (x - (b : ℝ)) +
        ((b : ℝ) - Real.integerBlockCutoffCenter a b) :=
      congrArg₂ (fun left right : ℝ => left + right)
        (Real.dist_eq_sub_of_le_explicit hbx)
        hrightEndpoint
    _ = x - Real.integerBlockCutoffCenter a b :=
      sub_add_sub_cancel x (b : ℝ)
        (Real.integerBlockCutoffCenter a b)
    _ = dist x (Real.integerBlockCutoffCenter a b) :=
      ((dist_comm x (Real.integerBlockCutoffCenter a b)).trans
        (Real.dist_eq_sub_of_le_explicit hcx)).symm

/-- The fixed inner-radius increment is positive. -/
theorem Real.one_div_three_pos :
    (0 : ℝ) < 1 / 3 :=
  div_pos zero_lt_one zero_lt_three

/-- The fixed inner increment is strictly smaller than the outer increment. -/
theorem Real.one_div_three_lt_two_div_three :
    (1 / 3 : ℝ) < 2 / 3 :=
  (div_lt_div_iff_of_pos_right zero_lt_three).mpr one_lt_two

/-- The outer-radius increment is at most one integer spacing. -/
theorem Real.two_lt_three_explicit :
    (2 : ℝ) < 3 :=
  calc
    (2 : ℝ) = 1 + 1 := one_add_one_eq_two.symm
    _ < 2 + 1 := add_lt_add_right one_lt_two 1
    _ = 3 := two_add_one_eq_three

/-- The outer-radius increment is at most one integer spacing. -/
theorem Real.two_div_three_le_one :
    (2 / 3 : ℝ) ≤ 1 :=
  (div_le_one zero_lt_three).mpr
    (le_of_lt Real.two_lt_three_explicit)

/-- The two canonical fractional cutoff margins sum to one. -/
theorem Real.two_div_three_add_one_div_three_eq_one :
    (2 / 3 : ℝ) + 1 / 3 = 1 := by
  calc
    (2 / 3 : ℝ) + 1 / 3 = (2 + 1) / 3 :=
      (add_div (2 : ℝ) 1 3).symm
    _ = 3 / 3 :=
      congrArg (fun numerator : ℝ => numerator / 3)
        two_add_one_eq_three
    _ = 1 := div_self (ne_of_gt zero_lt_three)

/-- The two cutoff-transition widths have total length `4/3`. -/
theorem Real.two_div_three_add_two_div_three_eq_four_div_three :
    (2 / 3 : ℝ) + 2 / 3 = 4 / 3 := by
  calc
    (2 / 3 : ℝ) + 2 / 3 = (2 + 2) / 3 :=
      (add_div (2 : ℝ) 2 3).symm
    _ = 4 / 3 :=
      congrArg (fun numerator : ℝ => numerator / 3)
        (two_add_two_eq_four : (2 : ℝ) + 2 = 4)

/-- A point at most `1/3` lies at least `2/3` to the left of every integer
endpoint at least one. -/
theorem Real.two_div_three_le_dist_leftEndpoint_of_le_one_div_three
    {a : ℤ}
    {x : ℝ}
    (ha : 1 ≤ a)
    (hx : x ≤ 1 / 3) :
    (2 / 3 : ℝ) ≤ dist x (a : ℝ) := by
  have ha_real : (1 : ℝ) ≤ (a : ℝ) :=
    Eq.subst
      (motive := fun value : ℝ => value ≤ (a : ℝ))
      Int.cast_one
      (Int.cast_le.mpr ha)
  have hsum : (2 / 3 : ℝ) + x ≤ (a : ℝ) :=
    le_trans
      (add_le_add_left hx (2 / 3 : ℝ))
      (Eq.subst
        (motive := fun value : ℝ => value ≤ (a : ℝ))
        Real.two_div_three_add_one_div_three_eq_one.symm
        ha_real)
  have hxa : x ≤ (a : ℝ) :=
    le_trans hx
      (le_trans
        (le_of_lt Real.one_div_three_lt_two_div_three)
        (le_trans Real.two_div_three_le_one ha_real))
  exact
    le_trans
      (le_sub_iff_add_le.mpr hsum)
      (le_of_eq (Real.dist_eq_sub_of_le_explicit hxa).symm)

/-- A strictly earlier integer is at least unit distance from the left
endpoint. -/
theorem Real.one_le_dist_leftEndpoint_of_lt
    {a n : ℤ}
    (hna : n < a) :
    1 ≤ dist (n : ℝ) (a : ℝ) := by
  have hgapInt : n + 1 ≤ a := Int.add_one_le_iff.mpr hna
  have hgapCast : ((n + 1 : ℤ) : ℝ) ≤ (a : ℝ) :=
    Int.cast_le.mpr hgapInt
  have hcastAdd : ((n + 1 : ℤ) : ℝ) = (n : ℝ) + 1 :=
    (Int.cast_add n 1).trans
      (congrArg (fun value : ℝ => (n : ℝ) + value)
        (Int.cast_one : ((1 : ℤ) : ℝ) = 1))
  have hgapReal : (n : ℝ) + 1 ≤ (a : ℝ) :=
    Eq.subst
      (motive := fun left : ℝ => left ≤ (a : ℝ))
      hcastAdd
      hgapCast
  have honeSub : (1 : ℝ) ≤ (a : ℝ) - (n : ℝ) :=
    le_sub_iff_add_le.mpr
      (Eq.subst
        (motive := fun left : ℝ => left ≤ (a : ℝ))
        (add_comm (n : ℝ) (1 : ℝ))
        hgapReal)
  have hnaReal : (n : ℝ) ≤ (a : ℝ) :=
    Int.cast_le.mpr (le_of_lt hna)
  exact
    le_trans honeSub
      (le_of_eq (Real.dist_eq_sub_of_le_explicit hnaReal).symm)

/-- A strictly later integer is at least unit distance from the right
endpoint. -/
theorem Real.one_le_dist_rightEndpoint_of_lt
    {b n : ℤ}
    (hbn : b < n) :
    1 ≤ dist (b : ℝ) (n : ℝ) := by
  have hgapInt : b + 1 ≤ n := Int.add_one_le_iff.mpr hbn
  have hgapCast : ((b + 1 : ℤ) : ℝ) ≤ (n : ℝ) :=
    Int.cast_le.mpr hgapInt
  have hcastAdd : ((b + 1 : ℤ) : ℝ) = (b : ℝ) + 1 :=
    (Int.cast_add b 1).trans
      (congrArg (fun value : ℝ => (b : ℝ) + value)
        (Int.cast_one : ((1 : ℤ) : ℝ) = 1))
  have hgapReal : (b : ℝ) + 1 ≤ (n : ℝ) :=
    Eq.subst
      (motive := fun left : ℝ => left ≤ (n : ℝ))
      hcastAdd
      hgapCast
  have honeSub : (1 : ℝ) ≤ (n : ℝ) - (b : ℝ) :=
    le_sub_iff_add_le.mpr
      (Eq.subst
        (motive := fun left : ℝ => left ≤ (n : ℝ))
        (add_comm (b : ℝ) (1 : ℝ))
        hgapReal)
  have hbnReal : (b : ℝ) ≤ (n : ℝ) :=
    Int.cast_le.mpr (le_of_lt hbn)
  exact
    le_trans honeSub
      (le_of_eq (Real.dist_eq_sub_of_le_explicit hbnReal).symm)

/-- Every integer strictly left of an ordered block lies outside the outer
cutoff ball. -/
theorem Real.integerBlockCutoffOuterRadius_le_dist_of_lt_left
    {a b n : ℤ}
    (hab : a ≤ b)
    (hna : n < a) :
    Real.integerBlockCutoffOuterRadius a b ≤
      dist (n : ℝ) (Real.integerBlockCutoffCenter a b) := by
  have hgap : (2 / 3 : ℝ) ≤ dist (n : ℝ) (a : ℝ) :=
    le_trans Real.two_div_three_le_one
      (Real.one_le_dist_leftEndpoint_of_lt hna)
  have hadditive :=
    Real.dist_add_dist_leftEndpoint_eq_dist_center hab (le_of_lt hna)
  calc
    Real.integerBlockCutoffOuterRadius a b =
        Real.integerBlockCutoffEndpointRadius a b + 2 / 3 := rfl
    _ ≤ Real.integerBlockCutoffEndpointRadius a b +
        dist (n : ℝ) (a : ℝ) :=
      add_le_add_left hgap (Real.integerBlockCutoffEndpointRadius a b)
    _ = dist (n : ℝ) (a : ℝ) +
        Real.integerBlockCutoffEndpointRadius a b :=
      add_comm
        (Real.integerBlockCutoffEndpointRadius a b)
        (dist (n : ℝ) (a : ℝ))
    _ = dist (n : ℝ) (a : ℝ) +
        dist (a : ℝ) (Real.integerBlockCutoffCenter a b) :=
      congrArg
        (fun value : ℝ => dist (n : ℝ) (a : ℝ) + value)
        (Real.integerBlockCutoffEndpointRadius_eq_left a b)
    _ = dist (n : ℝ) (Real.integerBlockCutoffCenter a b) :=
      hadditive

/-- Every real point separated from the left endpoint by the outer margin lies
outside the canonical cutoff ball. -/
theorem Real.integerBlockCutoffOuterRadius_le_dist_of_left_margin
    {a b : ℤ}
    {x : ℝ}
    (hab : a ≤ b)
    (hxa : x ≤ (a : ℝ))
    (hgap : (2 / 3 : ℝ) ≤ dist x (a : ℝ)) :
    Real.integerBlockCutoffOuterRadius a b ≤
      dist x (Real.integerBlockCutoffCenter a b) := by
  have hadditive :=
    Real.dist_add_dist_leftEndpoint_eq_dist_center_real hab hxa
  calc
    Real.integerBlockCutoffOuterRadius a b =
        Real.integerBlockCutoffEndpointRadius a b + 2 / 3 := rfl
    _ ≤ Real.integerBlockCutoffEndpointRadius a b + dist x (a : ℝ) :=
      add_le_add_left hgap
        (Real.integerBlockCutoffEndpointRadius a b)
    _ = dist x (a : ℝ) +
        Real.integerBlockCutoffEndpointRadius a b :=
      add_comm
        (Real.integerBlockCutoffEndpointRadius a b)
        (dist x (a : ℝ))
    _ = dist x (a : ℝ) +
        dist (a : ℝ) (Real.integerBlockCutoffCenter a b) :=
      congrArg
        (fun value : ℝ => dist x (a : ℝ) + value)
        (Real.integerBlockCutoffEndpointRadius_eq_left a b)
    _ = dist x (Real.integerBlockCutoffCenter a b) :=
      hadditive

/-- Every integer strictly right of an ordered block lies outside the outer
cutoff ball. -/
theorem Real.integerBlockCutoffOuterRadius_le_dist_of_lt_right
    {a b n : ℤ}
    (hab : a ≤ b)
    (hbn : b < n) :
    Real.integerBlockCutoffOuterRadius a b ≤
      dist (n : ℝ) (Real.integerBlockCutoffCenter a b) := by
  have hgap : (2 / 3 : ℝ) ≤ dist (b : ℝ) (n : ℝ) :=
    le_trans Real.two_div_three_le_one
      (Real.one_le_dist_rightEndpoint_of_lt hbn)
  have hadditive :=
    Real.dist_add_dist_rightEndpoint_eq_dist_center hab (le_of_lt hbn)
  calc
    Real.integerBlockCutoffOuterRadius a b =
        Real.integerBlockCutoffEndpointRadius a b + 2 / 3 := rfl
    _ ≤ Real.integerBlockCutoffEndpointRadius a b +
        dist (b : ℝ) (n : ℝ) :=
      add_le_add_left hgap (Real.integerBlockCutoffEndpointRadius a b)
    _ = dist (b : ℝ) (n : ℝ) +
        Real.integerBlockCutoffEndpointRadius a b :=
      add_comm
        (Real.integerBlockCutoffEndpointRadius a b)
        (dist (b : ℝ) (n : ℝ))
    _ = dist (b : ℝ) (n : ℝ) +
        dist (b : ℝ) (Real.integerBlockCutoffCenter a b) :=
      congrArg
        (fun value : ℝ => dist (b : ℝ) (n : ℝ) + value)
        (Real.integerBlockCutoffEndpointRadius_eq_right a b)
    _ = dist (n : ℝ) (Real.integerBlockCutoffCenter a b) :=
      hadditive

/-- Every real point separated from the right endpoint by the outer margin
lies outside the canonical cutoff ball. -/
theorem Real.integerBlockCutoffOuterRadius_le_dist_of_right_margin
    {a b : ℤ}
    {x : ℝ}
    (hab : a ≤ b)
    (hbx : (b : ℝ) ≤ x)
    (hgap : (2 / 3 : ℝ) ≤ dist (b : ℝ) x) :
    Real.integerBlockCutoffOuterRadius a b ≤
      dist x (Real.integerBlockCutoffCenter a b) := by
  have hadditive :=
    Real.dist_add_dist_rightEndpoint_eq_dist_center_real hab hbx
  calc
    Real.integerBlockCutoffOuterRadius a b =
        Real.integerBlockCutoffEndpointRadius a b + 2 / 3 := rfl
    _ ≤ Real.integerBlockCutoffEndpointRadius a b + dist (b : ℝ) x :=
      add_le_add_left hgap
        (Real.integerBlockCutoffEndpointRadius a b)
    _ = dist (b : ℝ) x +
        Real.integerBlockCutoffEndpointRadius a b :=
      add_comm
        (Real.integerBlockCutoffEndpointRadius a b)
        (dist (b : ℝ) x)
    _ = dist (b : ℝ) x +
        dist (b : ℝ) (Real.integerBlockCutoffCenter a b) :=
      congrArg
        (fun value : ℝ => dist (b : ℝ) x + value)
        (Real.integerBlockCutoffEndpointRadius_eq_right a b)
    _ = dist x (Real.integerBlockCutoffCenter a b) :=
      hadditive

/-- Positivity of the canonical inner radius. -/
theorem Real.integerBlockCutoffInnerRadius_pos
    (a b : ℤ) :
    0 < Real.integerBlockCutoffInnerRadius a b :=
  add_pos_of_nonneg_of_pos
    (Real.integerBlockCutoffEndpointRadius_nonneg a b)
    Real.one_div_three_pos

/-- Strict separation of the canonical inner and outer radii. -/
theorem Real.integerBlockCutoffInnerRadius_lt_outerRadius
    (a b : ℤ) :
    Real.integerBlockCutoffInnerRadius a b <
      Real.integerBlockCutoffOuterRadius a b :=
  add_lt_add_left
    Real.one_div_three_lt_two_div_three
    (Real.integerBlockCutoffEndpointRadius a b)

/-- Canonical smooth bump attached to an integer block. -/
def Real.integerBlockContDiffBump
    (a b : ℤ) :
    ContDiffBump (Real.integerBlockCutoffCenter a b) where
  rIn := Real.integerBlockCutoffInnerRadius a b
  rOut := Real.integerBlockCutoffOuterRadius a b
  rIn_pos := Real.integerBlockCutoffInnerRadius_pos a b
  rIn_lt_rOut := Real.integerBlockCutoffInnerRadius_lt_outerRadius a b

/-- The real-valued canonical cutoff function for an integer block. -/
def Real.integerBlockCutoff
    (a b : ℤ) : ℝ → ℝ :=
  Real.integerBlockContDiffBump a b

/-- The canonical integer-block cutoff is smooth. -/
theorem Real.contDiff_integerBlockCutoff
    (a b : ℤ) :
    ContDiff ℝ ∞ (Real.integerBlockCutoff a b) :=
  (Real.integerBlockContDiffBump a b).contDiff

/-- The canonical integer-block cutoff has compact support. -/
theorem Real.hasCompactSupport_integerBlockCutoff
    (a b : ℤ) :
    HasCompactSupport (Real.integerBlockCutoff a b) :=
  (Real.integerBlockContDiffBump a b).hasCompactSupport

/-- Pointwise nonnegativity of the canonical integer-block cutoff. -/
theorem Real.integerBlockCutoff_nonneg
    (a b : ℤ)
    (x : ℝ) :
    0 ≤ Real.integerBlockCutoff a b x :=
  (Real.integerBlockContDiffBump a b).nonneg

/-- Pointwise unit upper bound for the canonical integer-block cutoff. -/
theorem Real.integerBlockCutoff_le_one
    (a b : ℤ)
    (x : ℝ) :
    Real.integerBlockCutoff a b x ≤ 1 :=
  (Real.integerBlockContDiffBump a b).le_one

/-- Exact zero value at every integer strictly left of an ordered block. -/
theorem Real.integerBlockCutoff_eq_zero_of_lt_left
    {a b n : ℤ}
    (hab : a ≤ b)
    (hna : n < a) :
    Real.integerBlockCutoff a b (n : ℝ) = 0 :=
  (Real.integerBlockContDiffBump a b).zero_of_le_dist
    (Real.integerBlockCutoffOuterRadius_le_dist_of_lt_left hab hna)

/-- The cutoff vanishes at every real point at least `2/3` before the left
integer endpoint. -/
theorem Real.integerBlockCutoff_eq_zero_of_left_margin
    {a b : ℤ}
    (hab : a ≤ b)
    {x : ℝ}
    (hx : x ≤ (a : ℝ) - 2 / 3) :
    Real.integerBlockCutoff a b x = 0 := by
  have hmargin_nonneg : (0 : ℝ) ≤ 2 / 3 :=
    le_of_lt
      (lt_trans Real.one_div_three_pos
        Real.one_div_three_lt_two_div_three)
  have hxa : x ≤ (a : ℝ) :=
    le_trans hx (sub_le_self (a : ℝ) hmargin_nonneg)
  have hadd : x + 2 / 3 ≤ (a : ℝ) :=
    (le_sub_iff_add_le).mp hx
  have hsub : (2 / 3 : ℝ) ≤ (a : ℝ) - x :=
    le_sub_iff_add_le.mpr
      ((add_comm x (2 / 3 : ℝ)).symm ▸ hadd)
  have hgap : (2 / 3 : ℝ) ≤ dist x (a : ℝ) :=
    le_trans hsub
      (le_of_eq (Real.dist_eq_sub_of_le_explicit hxa).symm)
  exact
    (Real.integerBlockContDiffBump a b).zero_of_le_dist
      (Real.integerBlockCutoffOuterRadius_le_dist_of_left_margin
        hab hxa hgap)

/-- A positive-block cutoff vanishes throughout the fixed left neighborhood
`(-∞, 1/3]`, in particular on a neighborhood of the logarithmic singularity. -/
theorem Real.integerBlockCutoff_eq_zero_of_le_one_div_three
    {a b : ℤ}
    (hab : a ≤ b)
    (ha : 1 ≤ a)
    {x : ℝ}
    (hx : x ≤ 1 / 3) :
    Real.integerBlockCutoff a b x = 0 := by
  have ha_real : (1 : ℝ) ≤ (a : ℝ) :=
    Eq.subst
      (motive := fun value : ℝ => value ≤ (a : ℝ))
      Int.cast_one
      (Int.cast_le.mpr ha)
  have hxa : x ≤ (a : ℝ) :=
    le_trans hx
      (le_trans
        (le_of_lt Real.one_div_three_lt_two_div_three)
        (le_trans Real.two_div_three_le_one ha_real))
  have hgap : (2 / 3 : ℝ) ≤ dist x (a : ℝ) :=
    Real.two_div_three_le_dist_leftEndpoint_of_le_one_div_three ha hx
  exact
    (Real.integerBlockContDiffBump a b).zero_of_le_dist
      (Real.integerBlockCutoffOuterRadius_le_dist_of_left_margin
        hab hxa hgap)

/-- Exact zero value at every integer strictly right of an ordered block. -/
theorem Real.integerBlockCutoff_eq_zero_of_lt_right
    {a b n : ℤ}
    (hab : a ≤ b)
    (hbn : b < n) :
    Real.integerBlockCutoff a b (n : ℝ) = 0 :=
  (Real.integerBlockContDiffBump a b).zero_of_le_dist
    (Real.integerBlockCutoffOuterRadius_le_dist_of_lt_right hab hbn)

/-- The cutoff vanishes at every real point at least `2/3` beyond the right
integer endpoint. -/
theorem Real.integerBlockCutoff_eq_zero_of_right_margin
    {a b : ℤ}
    (hab : a ≤ b)
    {x : ℝ}
    (hx : (b : ℝ) + 2 / 3 ≤ x) :
    Real.integerBlockCutoff a b x = 0 := by
  have hbx : (b : ℝ) ≤ x :=
    le_trans
      (le_add_of_nonneg_right
        (le_of_lt
          (lt_trans Real.one_div_three_pos
            Real.one_div_three_lt_two_div_three)))
      hx
  have hsub : (2 / 3 : ℝ) ≤ x - (b : ℝ) :=
    le_sub_iff_add_le.mpr
      (Eq.subst
        (motive := fun left : ℝ => left ≤ x)
        (add_comm (2 / 3 : ℝ) (b : ℝ)).symm
        hx)
  have hgap : (2 / 3 : ℝ) ≤ dist (b : ℝ) x :=
    le_trans hsub
      (le_of_eq (Real.dist_eq_sub_of_le_explicit hbx).symm)
  exact
    (Real.integerBlockContDiffBump a b).zero_of_le_dist
      (Real.integerBlockCutoffOuterRadius_le_dist_of_right_margin
        hab hbx hgap)

/-- Exact zero value at every integer outside an ordered block. -/
theorem Real.integerBlockCutoff_eq_zero_of_not_mem_Icc
    {a b n : ℤ}
    (hab : a ≤ b)
    (hn : n ∉ Finset.Icc a b) :
    Real.integerBlockCutoff a b (n : ℝ) = 0 := by
  have hnotBounds : ¬ (a ≤ n ∧ n ≤ b) :=
    fun hbounds => hn (Finset.mem_Icc.mpr hbounds)
  exact
    Or.elim
      (not_and_or.mp hnotBounds)
      (fun hleft =>
        Real.integerBlockCutoff_eq_zero_of_lt_left
          hab (lt_of_not_ge hleft))
      (fun hright =>
        Real.integerBlockCutoff_eq_zero_of_lt_right
          hab (lt_of_not_ge hright))

/-- A real point between the integer endpoints lies no farther from the
midpoint than the larger endpoint distance. -/
theorem Real.dist_integerBlockCutoffCenter_le_endpointRadius
    {a b n : ℤ}
    (han : a ≤ n)
    (hnb : n ≤ b) :
    dist (n : ℝ) (Real.integerBlockCutoffCenter a b) ≤
      Real.integerBlockCutoffEndpointRadius a b := by
  let center : ℝ := Real.integerBlockCutoffCenter a b
  have hleft : (a : ℝ) - center ≤ (n : ℝ) - center :=
    sub_le_sub_right (Int.cast_le.mpr han) center
  have hright : (n : ℝ) - center ≤ (b : ℝ) - center :=
    sub_le_sub_right (Int.cast_le.mpr hnb) center
  have habsolute :
      |(n : ℝ) - center| ≤
        max |(a : ℝ) - center| |(b : ℝ) - center| :=
    abs_le_max_abs_abs hleft hright
  calc
    dist (n : ℝ) (Real.integerBlockCutoffCenter a b) =
        |(n : ℝ) - center| :=
      Real.dist_eq (n : ℝ) center
    _ ≤ max |(a : ℝ) - center| |(b : ℝ) - center| :=
      habsolute
    _ = Real.integerBlockCutoffEndpointRadius a b := by
      exact
        congrArg₂ max
          (Real.dist_eq (a : ℝ) center).symm
          (Real.dist_eq (b : ℝ) center).symm

/-- Real-point form of the endpoint-radius bound on the closed block. -/
theorem Real.dist_integerBlockCutoffCenter_le_endpointRadius_real
    {a b : ℤ}
    {x : ℝ}
    (hax : (a : ℝ) ≤ x)
    (hxb : x ≤ (b : ℝ)) :
    dist x (Real.integerBlockCutoffCenter a b) ≤
      Real.integerBlockCutoffEndpointRadius a b := by
  let center : ℝ := Real.integerBlockCutoffCenter a b
  have hleft : (a : ℝ) - center ≤ x - center :=
    sub_le_sub_right hax center
  have hright : x - center ≤ (b : ℝ) - center :=
    sub_le_sub_right hxb center
  have habsolute :
      |x - center| ≤
        max |(a : ℝ) - center| |(b : ℝ) - center| :=
    abs_le_max_abs_abs hleft hright
  calc
    dist x (Real.integerBlockCutoffCenter a b) = |x - center| :=
      Real.dist_eq x center
    _ ≤ max |(a : ℝ) - center| |(b : ℝ) - center| :=
      habsolute
    _ = Real.integerBlockCutoffEndpointRadius a b :=
      congrArg₂ max
        (Real.dist_eq (a : ℝ) center).symm
        (Real.dist_eq (b : ℝ) center).symm

/-- Every real point in the closed block lies in the closed inner cutoff
ball. -/
theorem Real.mem_closedBall_integerBlockContDiffBump_of_mem_Icc
    {a b : ℤ}
    {x : ℝ}
    (hx : x ∈ Icc (a : ℝ) (b : ℝ)) :
    x ∈
      Metric.closedBall
        (Real.integerBlockCutoffCenter a b)
        (Real.integerBlockContDiffBump a b).rIn := by
  have hreference :
      dist x (Real.integerBlockCutoffCenter a b) ≤
        Real.integerBlockCutoffEndpointRadius a b :=
    Real.dist_integerBlockCutoffCenter_le_endpointRadius_real hx.1 hx.2
  have hinner :
      dist x (Real.integerBlockCutoffCenter a b) ≤
        Real.integerBlockCutoffInnerRadius a b :=
    le_trans hreference
      (le_add_of_nonneg_right (le_of_lt Real.one_div_three_pos))
  exact Metric.mem_closedBall.mpr hinner

/-- The canonical cutoff is identically one throughout the real block, not
only at its integer samples. -/
theorem Real.integerBlockCutoff_eq_one_of_mem_real_Icc
    {a b : ℤ}
    {x : ℝ}
    (hx : x ∈ Icc (a : ℝ) (b : ℝ)) :
    Real.integerBlockCutoff a b x = 1 :=
  (Real.integerBlockContDiffBump a b).one_of_mem_closedBall
    (Real.mem_closedBall_integerBlockContDiffBump_of_mem_Icc hx)

/-- Every integer sample in the block lies in the closed inner ball. -/
theorem Real.integer_mem_closedBall_integerBlockContDiffBump
    {a b n : ℤ}
    (han : a ≤ n)
    (hnb : n ≤ b) :
    (n : ℝ) ∈
      Metric.closedBall
        (Real.integerBlockCutoffCenter a b)
        (Real.integerBlockContDiffBump a b).rIn := by
  have hreference :
      dist (n : ℝ) (Real.integerBlockCutoffCenter a b) ≤
        Real.integerBlockCutoffEndpointRadius a b :=
    Real.dist_integerBlockCutoffCenter_le_endpointRadius han hnb
  have hincrement_nonneg : (0 : ℝ) ≤ 1 / 3 :=
    le_of_lt Real.one_div_three_pos
  have hinner :
      dist (n : ℝ) (Real.integerBlockCutoffCenter a b) ≤
        Real.integerBlockCutoffInnerRadius a b :=
    le_trans hreference
      (le_add_of_nonneg_right hincrement_nonneg)
  exact Metric.mem_closedBall.mpr hinner

/-- Exact value one at every integer sample inside the block. -/
theorem Real.integerBlockCutoff_eq_one_of_mem
    {a b n : ℤ}
    (han : a ≤ n)
    (hnb : n ≤ b) :
    Real.integerBlockCutoff a b (n : ℝ) = 1 :=
  (Real.integerBlockContDiffBump a b).one_of_mem_closedBall
    (Real.integer_mem_closedBall_integerBlockContDiffBump han hnb)

/-- Finset-membership form of the exact interior sampling law. -/
theorem Real.integerBlockCutoff_eq_one_of_mem_Icc
    (a b n : ℤ)
    (hn : n ∈ Finset.Icc a b) :
    Real.integerBlockCutoff a b (n : ℝ) = 1 :=
  Real.integerBlockCutoff_eq_one_of_mem
    (Finset.mem_Icc.mp hn).1
    (Finset.mem_Icc.mp hn).2

/-- Canonical exact Poisson reconstruction for a finite ordered integer block.
All cutoff hypotheses have been discharged by the integer-block construction. -/
theorem Complex.integerBlock_poisson_reconstruction
    (phase : ℝ → ℝ)
    (hphase : ContDiff ℝ ∞ phase)
    (a b : ℤ)
    (hab : a ≤ b) :
    (∑ n ∈ Finset.Icc a b,
        Complex.exp (Complex.I * (phase (n : ℝ) : ℂ))) =
      ∑' m : ℤ,
        SchwartzMap.fourierTransformCLM ℝ
          (Complex.phaseCutoffSchwartz
            phase
            (Real.integerBlockCutoff a b)
            hphase
            (Real.contDiff_integerBlockCutoff a b)
            (Real.hasCompactSupport_integerBlockCutoff a b))
          (m : ℝ) :=
  Complex.finite_realPhase_poisson_reconstruction
    phase
    (Real.integerBlockCutoff a b)
    hphase
    (Real.contDiff_integerBlockCutoff a b)
    (Real.hasCompactSupport_integerBlockCutoff a b)
    (Finset.Icc a b)
    (fun n hn => Real.integerBlockCutoff_eq_one_of_mem_Icc a b n hn)
    (fun n hn =>
      Real.integerBlockCutoff_eq_zero_of_not_mem_Icc (n := n) hab hn)

end

end LFunctions
end Boundary
