import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# A quantitative lower bound for the logistic odd ratio

For nonnegative `z`, the elementary estimate `1+z ≤ exp z` and monotonicity
of `(y-1)/(y+1)` give

`z/(z+2) ≤ (exp z - 1)/(exp z + 1)`.

This is the transcendental input in the convexity proof for the normalized
flat transition.
-/

namespace Boundary
namespace LFunctions

noncomputable section

def Real.logisticOddRatio (y : ℝ) : ℝ :=
  (y - 1) / (y + 1)

def Real.exponentialOddRatio (z : ℝ) : ℝ :=
  (Real.exp z - 1) / (Real.exp z + 1)

def Real.rationalOddLower (z : ℝ) : ℝ :=
  z / (z + 2)

theorem Real.logisticOddRatio_eq
    (y : ℝ) :
    Real.logisticOddRatio y = (y - 1) / (y + 1) := by
  rfl

theorem Real.exponentialOddRatio_eq_logistic
    (z : ℝ) :
    Real.exponentialOddRatio z =
      Real.logisticOddRatio (Real.exp z) := by
  rfl

theorem Real.rationalOddLower_eq_logistic_add_one
    (z : ℝ) :
    Real.rationalOddLower z =
      Real.logisticOddRatio (1 + z) := by
  unfold Real.rationalOddLower
  unfold Real.logisticOddRatio
  have hnumerator : (1 + z) - 1 = z := by
    calc
      (1 + z) - 1 = (1 - 1) + z :=
        add_sub_right_comm 1 z 1
      _ = 0 + z :=
        congrArg (fun value : ℝ => value + z) (sub_self 1)
      _ = z := zero_add _
  have hdenominator : (1 + z) + 1 = z + 2 := by
    calc
      (1 + z) + 1 = z + (1 + 1) := by
        exact (add_assoc 1 z 1).trans (add_left_comm 1 z 1)
      _ = z + 2 :=
        congrArg (fun value : ℝ => z + value)
          one_add_one_eq_two
  exact congrArg₂ (fun numerator denominator : ℝ => numerator / denominator)
    hnumerator.symm hdenominator.symm

theorem Real.logisticOddRatio_denominator_pos
    {y : ℝ}
    (hy : -1 < y) :
    0 < y + 1 := by
  have htranslated := add_lt_add_right hy 1
  have hzero : (-1 : ℝ) + 1 = 0 := neg_add_cancel 1
  exact Eq.subst (motive := fun z : ℝ => z < y + 1) hzero htranslated

theorem Real.logisticOddRatio_difference_identity
    (u v : ℝ) :
    (v - 1) * (u + 1) - (u - 1) * (v + 1) =
      2 * (v - u) := by
  calc
    (v - 1) * (u + 1) - (u - 1) * (v + 1) =
      (v * u + v * 1 - (1 * u + 1 * 1)) -
        (u * v + u * 1 - (1 * v + 1 * 1)) := by
      exact congrArg₂ (fun first second : ℝ => first - second)
        ((sub_mul v 1 (u + 1)).trans
          (congrArg₂ (fun first second : ℝ => first - second)
            (mul_add v u 1)
            (mul_add 1 u 1)))
        ((sub_mul u 1 (v + 1)).trans
          (congrArg₂ (fun first second : ℝ => first - second)
            (mul_add u v 1)
            (mul_add 1 v 1)))
    _ = (v * u + v - (u + 1)) -
        (u * v + u - (v + 1)) := by
      exact congrArg₂ (fun first second : ℝ => first - second)
        (congrArg₂ (fun first second : ℝ => first - second)
          (congrArg₂ (fun first second : ℝ => first + second)
            rfl (mul_one v))
          (congrArg₂ (fun first second : ℝ => first + second)
            (one_mul u) (one_mul 1)))
        (congrArg₂ (fun first second : ℝ => first - second)
          (congrArg₂ (fun first second : ℝ => first + second)
            rfl (mul_one u))
          (congrArg₂ (fun first second : ℝ => first + second)
            (one_mul v) (one_mul 1)))
    _ = 2 * (v - u) := by
      have hcomm : v * u = u * v := mul_comm v u
      let common := u * v
      calc
        (v * u + v - (u + 1)) - (u * v + u - (v + 1)) =
          (common + v - (u + 1)) - (common + u - (v + 1)) :=
            congrArg₂ (fun first second : ℝ => first - second)
              (congrArg (fun value : ℝ => value + v - (u + 1)) hcomm)
              rfl
        _ = (v - u - 1) - (u - v - 1) := by
          have hcancelFirst : common + v - (u + 1) =
              common + (v - u - 1) := by
            calc
              common + v - (u + 1) = common + (v - (u + 1)) :=
                add_sub_assoc common v (u + 1)
              _ = common + (v - u - 1) :=
                congrArg (fun value : ℝ => common + value)
                  (sub_sub v u 1).symm
          have hcancelSecond : common + u - (v + 1) =
              common + (u - v - 1) := by
            calc
              common + u - (v + 1) = common + (u - (v + 1)) :=
                add_sub_assoc common u (v + 1)
              _ = common + (u - v - 1) :=
                congrArg (fun value : ℝ => common + value)
                  (sub_sub u v 1).symm
          exact Eq.trans
            (congrArg₂ (fun first second : ℝ => first - second)
              hcancelFirst hcancelSecond)
            (add_sub_add_left_eq_sub (v - u - 1) (u - v - 1) common)
        _ = (v - u) - (u - v) :=
          sub_sub_sub_cancel_right (v - u) (u - v) 1
        _ = (v - u) - (-(v - u)) := by
          congr 1
          exact (neg_sub v u).symm
        _ = (v - u) + (v - u) := by
          exact (sub_eq_add_neg (v - u) (-(v - u))).trans
            (congrArg (fun value : ℝ => (v - u) + value)
              (neg_neg (v - u)))
        _ = 2 * (v - u) := (two_mul (v - u)).symm

theorem Real.logisticOddRatio_mono
    {u v : ℝ}
    (hu : -1 < u)
    (huv : u ≤ v) :
    Real.logisticOddRatio u ≤ Real.logisticOddRatio v := by
  have hv : -1 < v := lt_of_lt_of_le hu huv
  have huDen := Real.logisticOddRatio_denominator_pos hu
  have hvDen := Real.logisticOddRatio_denominator_pos hv
  unfold Real.logisticOddRatio
  have hcross :
      (u - 1) * (v + 1) ≤ (v - 1) * (u + 1) := by
    have hdifference : 0 ≤ 2 * (v - u) :=
      mul_nonneg (Nat.cast_nonneg 2) (sub_nonneg.mpr huv)
    have hidentity := Real.logisticOddRatio_difference_identity u v
    have hnonneg :
        0 ≤ (v - 1) * (u + 1) - (u - 1) * (v + 1) :=
      Eq.subst (motive := fun value : ℝ => 0 ≤ value)
        hidentity.symm hdifference
    exact sub_nonneg.mp hnonneg
  exact (div_le_div_iff₀ huDen hvDen).mpr hcross

theorem Real.one_add_nonnegative_gt_neg_one
    {z : ℝ}
    (hz : 0 ≤ z) :
    (-1 : ℝ) < 1 + z := by
  have hminusOneLtOne : (-1 : ℝ) < 1 := by
    exact neg_lt_self zero_lt_one
  exact lt_of_lt_of_le hminusOneLtOne
    (le_add_of_nonneg_right hz)

theorem Real.one_add_le_exp_of_nonneg
    {z : ℝ}
    (hz : 0 ≤ z) :
    1 + z ≤ Real.exp z := by
  exact Eq.subst (motive := fun w : ℝ => w ≤ Real.exp z)
    (add_comm z 1) (Real.add_one_le_exp z)

theorem Real.rationalOddLower_le_exponentialOddRatio
    {z : ℝ}
    (hz : 0 ≤ z) :
    Real.rationalOddLower z ≤ Real.exponentialOddRatio z := by
  have honeAdd := Real.one_add_nonnegative_gt_neg_one hz
  have horder := Real.one_add_le_exp_of_nonneg hz
  have hmono := Real.logisticOddRatio_mono honeAdd horder
  exact Eq.subst
    (motive := fun left : ℝ =>
      left ≤ Real.exponentialOddRatio z)
    (Real.rationalOddLower_eq_logistic_add_one z).symm
    (Eq.subst
      (motive := fun right : ℝ =>
        Real.logisticOddRatio (1 + z) ≤ right)
      (Real.exponentialOddRatio_eq_logistic z).symm
      hmono)

theorem Real.zero_le_rationalOddLower
    {z : ℝ}
    (hz : 0 ≤ z) :
    0 ≤ Real.rationalOddLower z := by
  unfold Real.rationalOddLower
  have hdenominator : 0 ≤ z + 2 :=
    add_nonneg hz (Nat.cast_nonneg 2)
  exact div_nonneg hz hdenominator

theorem Real.zero_le_exponentialOddRatio
    {z : ℝ}
    (hz : 0 ≤ z) :
    0 ≤ Real.exponentialOddRatio z := by
  exact le_trans
    (Real.zero_le_rationalOddLower hz)
    (Real.rationalOddLower_le_exponentialOddRatio hz)

end
end LFunctions
end Boundary
