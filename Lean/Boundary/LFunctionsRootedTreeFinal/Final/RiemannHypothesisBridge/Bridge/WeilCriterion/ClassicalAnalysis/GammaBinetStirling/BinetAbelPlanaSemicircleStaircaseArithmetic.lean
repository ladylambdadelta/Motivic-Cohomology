import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaRectangularCollars

/-!
# Arithmetic foundations for right semicircle staircases

This file owns the elementary real, natural-number, and complex-algebra
normalizations used by the polygonal staircase approximation to the right
semicircle.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open Filter MeasureTheory

/-- Casting a natural successor written as `m + 1` gives the real grid
denominator `m + 1`. -/
theorem Real.natCast_add_one_eq_real_add_one
    (m : ℕ) :
    ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by
  calc
    ((m + 1 : ℕ) : ℝ) = (m : ℝ) + ((1 : ℕ) : ℝ) :=
      Nat.cast_add m 1
    _ = (m : ℝ) + 1 := by
      exact congrArg (fun x : ℝ => (m : ℝ) + x) (Nat.cast_one)

/-- Uniform vertical sample for the right circular graph. -/
noncomputable def Complex.rightSemicircleStaircaseY
    (ρ : ℝ)
    (m k : ℕ) : ℝ :=
  -ρ + ((k : ℝ) / (m + 1 : ℝ)) * (2 * ρ)

/-- The denominator in the staircase ratio is strictly positive. -/
theorem Real.rightSemicircleStaircase_denominator_pos
    (m : ℕ) :
    0 < (m + 1 : ℝ) := by
  have hnat :
      0 < ((m + 1 : ℕ) : ℝ) :=
    Nat.cast_pos.mpr (Nat.succ_pos m)
  have hcast :
      ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by
    exact Real.natCast_add_one_eq_real_add_one m
  exact Eq.mp (congrArg (fun x : ℝ => 0 < x) hcast) hnat

/-- The denominator in the staircase ratio is nonzero. -/
theorem Real.rightSemicircleStaircase_denominator_ne_zero
    (m : ℕ) :
    ((m + 1 : ℕ) : ℝ) ≠ 0 :=
  ne_of_gt (Nat.cast_pos.mpr (Nat.succ_pos m))

/-- The scalar `2` is nonnegative over the reals. -/
theorem Real.rightSemicircleStaircase_two_nonneg :
    (0 : ℝ) ≤ 2 :=
  zero_le_two

/-- Expanding the endpoint translation at the top of the right semicircle. -/
theorem Real.rightSemicircleStaircase_top_translate
    (ρ : ℝ) :
    -ρ + 1 * (2 * ρ) = ρ := by
  calc
    -ρ + 1 * (2 * ρ) = -ρ + (2 * ρ) := by
      exact congrArg (fun x : ℝ => -ρ + x) (one_mul (2 * ρ))
    _ = -ρ + (ρ + ρ) := by
      exact congrArg (fun x : ℝ => -ρ + x) (two_mul ρ)
    _ = (-ρ + ρ) + ρ := by
      exact Eq.symm (add_assoc (-ρ) ρ ρ)
    _ = 0 + ρ := by
      exact congrArg (fun x : ℝ => x + ρ) (neg_add_cancel ρ)
    _ = ρ := zero_add ρ

/-- The real numeral identity `2 + 1 = 3`. -/
theorem Real.two_add_one_eq_three :
    (2 : ℝ) + 1 = 3 :=
  _root_.two_add_one_eq_three

/-- The scalar normalization `2ρ + ρ = 3ρ`. -/
theorem Real.two_mul_add_self_eq_three_mul
    (ρ : ℝ) :
    2 * ρ + ρ = 3 * ρ := by
  calc
    2 * ρ + ρ = 2 * ρ + 1 * ρ := by
      exact congrArg (fun x : ℝ => 2 * ρ + x) (Eq.symm (one_mul ρ))
    _ = (2 + 1 : ℝ) * ρ := by
      exact Eq.symm (add_mul 2 1 ρ)
    _ = 3 * ρ := by
      exact congrArg (fun x : ℝ => x * ρ) Real.two_add_one_eq_three

/-- The zero-start unimodal variation scalar collapses to twice the peak. -/
theorem Real.unimodal_zero_start_scalar_collapse
    {s0 sj sm : ℝ}
    (hs0 : s0 = 0) :
    ((sj - s0) + (sj - sm)) + sm = 2 * sj := by
  calc
    ((sj - s0) + (sj - sm)) + sm =
        ((sj - 0) + (sj - sm)) + sm := by
      exact congrArg
        (fun x : ℝ => ((sj - x) + (sj - sm)) + sm)
        hs0
    _ = (sj + (sj - sm)) + sm := by
      exact congrArg (fun x : ℝ => (x + (sj - sm)) + sm) (sub_zero sj)
    _ = sj + ((sj - sm) + sm) := by
      exact add_assoc sj (sj - sm) sm
    _ = sj + sj := by
      exact congrArg (fun x : ℝ => sj + x) (sub_add_cancel sj sm)
    _ = 2 * sj := by
      exact Eq.symm (two_mul sj)

/-- The bounded unimodal variation scalar collapses to twice the peak. -/
theorem Real.unimodal_bounded_scalar_collapse
    (s0 sj sm : ℝ) :
    s0 + ((sj - s0) + (sj - sm)) + sm = 2 * sj := by
  calc
    s0 + ((sj - s0) + (sj - sm)) + sm =
        (s0 + (sj - s0)) + (sj - sm) + sm := by
      exact congrArg (fun x : ℝ => x + sm)
        (Eq.symm (add_assoc s0 (sj - s0) (sj - sm)))
    _ = (s0 + (sj - s0)) + ((sj - sm) + sm) := by
      exact add_assoc (s0 + (sj - s0)) (sj - sm) sm
    _ = sj + ((sj - sm) + sm) := by
      exact congrArg (fun x : ℝ => x + ((sj - sm) + sm)) (add_sub_cancel s0 sj)
    _ = sj + sj := by
      exact congrArg (fun x : ℝ => sj + x) (sub_add_cancel sj sm)
    _ = 2 * sj := by
      exact Eq.symm (two_mul sj)

/-- Adjacent difference increments telescope forward. -/
theorem Real.forward_difference_telescope_step
    (a b c : ℝ) :
    (b - a) + (c - b) = c - a := by
  calc
    (b - a) + (c - b) = (c - b) + (b - a) := add_comm (b - a) (c - b)
    _ = c - a := sub_add_sub_cancel c b a

/-- Adjacent difference increments telescope backward. -/
theorem Real.backward_difference_telescope_step
    (a b c : ℝ) :
    (a - b) + (b - c) = a - c :=
  sub_add_sub_cancel a b c

/-- Transport a doubled natural-number inequality to the real grid scale. -/
theorem Real.two_mul_natCast_le_succ_of_nat_mul_le
    {m k : ℕ}
    (h : k * 2 ≤ m + 1) :
    2 * (k : ℝ) ≤ (m + 1 : ℝ) := by
  have hcast : ((k * 2 : ℕ) : ℝ) ≤ ((m + 1 : ℕ) : ℝ) :=
    Nat.cast_le.mpr h
  have hdenom :
      ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 :=
    Real.natCast_add_one_eq_real_add_one m
  calc
    2 * (k : ℝ) = (k : ℝ) * 2 := mul_comm 2 (k : ℝ)
    _ = ((k * 2 : ℕ) : ℝ) := Eq.symm (Nat.cast_mul k 2)
    _ ≤ ((m + 1 : ℕ) : ℝ) := hcast
    _ = (m + 1 : ℝ) := hdenom

/-- Transport a natural upper bound by a doubled successor to the real grid
scale. -/
theorem Real.succ_le_two_mul_succ_natCast_of_nat_le
    {m k : ℕ}
    (h : m + 1 ≤ 2 * (k + 1)) :
    (m + 1 : ℝ) ≤ 2 * ((k + 1 : ℕ) : ℝ) := by
  have hcast : ((m + 1 : ℕ) : ℝ) ≤ ((2 * (k + 1) : ℕ) : ℝ) :=
    Nat.cast_le.mpr h
  have hdenom :
      (m + 1 : ℝ) = ((m + 1 : ℕ) : ℝ) :=
    (Real.natCast_add_one_eq_real_add_one m).symm
  calc
    (m + 1 : ℝ) = ((m + 1 : ℕ) : ℝ) := hdenom
    _ ≤ ((2 * (k + 1) : ℕ) : ℝ) := hcast
    _ = (2 : ℝ) * ((k + 1 : ℕ) : ℝ) := Nat.cast_mul 2 (k + 1)

/-- The natural number `1` is strictly less than `2`. -/
theorem Nat.one_lt_two : 1 < 2 :=
  Nat.lt.base 1

/-- The odd predecessor of a doubled successor is bounded by that doubled
successor. -/
theorem Nat.two_mul_add_one_le_two_mul_succ
    (k : ℕ) :
    2 * k + 1 ≤ 2 * (k + 1) := by
  have hbase :
      2 * k ≤ 2 * k + 1 :=
    Nat.le_add_right (2 * k) 1
  calc
    2 * k + 1 ≤ 2 * k + 2 :=
      Nat.succ_le_succ hbase
    _ = 2 * (k + 1) :=
      Eq.symm (Nat.mul_succ 2 k)

/-- A bound by the midpoint predecessor gives a bound by the doubled successor. -/
theorem Nat.succ_le_two_mul_succ_of_le_two_mul_add_one
    {m k : ℕ}
    (h : m + 1 ≤ 2 * k + 1) :
    m + 1 ≤ 2 * (k + 1) :=
  le_trans h (Nat.two_mul_add_one_le_two_mul_succ k)

/-- Move the factor `2` from the right of a quotient to the numerator. -/
theorem Real.div_mul_two_eq_two_mul_div
    (a d : ℝ) :
    (a / d) * 2 = (2 * a) / d := by
  calc
    (a / d) * 2 = (a * 2) / d := div_mul_eq_mul_div a d 2
    _ = (2 * a) / d := by
      exact congrArg (fun x : ℝ => x / d) (mul_comm a 2)

/-- Reassociate the grid ratio with the radius factor. -/
theorem Real.ratio_mul_two_mul_radius
    (r ρ : ℝ) :
    r * (2 * ρ) = (r * 2) * ρ :=
  (mul_assoc r 2 ρ).symm

/-- If a grid contribution is at most the radius, its centered height is
nonpositive. -/
theorem Real.neg_radius_add_le_zero_of_le_radius
    {ρ a : ℝ}
    (h : a ≤ ρ) :
    -ρ + a ≤ 0 := by
  calc
    -ρ + a ≤ -ρ + ρ := add_le_add_left h (-ρ)
    _ = 0 := neg_add_cancel ρ

/-- If a grid contribution is at least the radius, its centered height is
nonnegative. -/
theorem Real.nonneg_neg_radius_add_of_radius_le
    {ρ a : ℝ}
    (h : ρ ≤ a) :
    0 ≤ -ρ + a := by
  calc
    0 = -ρ + ρ := Eq.symm (neg_add_cancel ρ)
    _ ≤ -ρ + a := add_le_add_left h (-ρ)

/-- Absolute value reverses order on the nonpositive half-line. -/
theorem Real.abs_le_abs_of_nonpos_interval
    {a b : ℝ}
    (hab : a ≤ b)
    (hb : b ≤ 0) :
    |b| ≤ |a| := by
  have ha : a ≤ 0 := le_trans hab hb
  calc
    |b| = -b := abs_of_nonpos hb
    _ ≤ -a := neg_le_neg hab
    _ = |a| := Eq.symm (abs_of_nonpos ha)

/-- Subtracting from a fixed square reverses a square inequality. -/
theorem Real.sub_sq_le_sub_sq_of_sq_le
    {ρ x y : ℝ}
    (h : x ^ 2 ≤ y ^ 2) :
    ρ ^ 2 - y ^ 2 ≤ ρ ^ 2 - x ^ 2 :=
  sub_le_sub_left h (ρ ^ 2)

/-- Reassociate a subtraction across an endpoint-return decomposition. -/
theorem Complex.sub_add_sub_reassociate_endpoint
    (A B C D : ℂ) :
    A - (B + D) - C = A - B - C - D := by
  calc
    A - (B + D) - C = (A - B - D) - C := by
      exact congrArg (fun x : ℂ => x - C) (sub_add_eq_sub_sub A B D)
    _ = A - B - C - D :=
      sub_right_comm (A - B) D C

/-- Two right subtractions may be interchanged. -/
theorem Complex.sub_sub_right_comm
    (A B C : ℂ) :
    (A - B) - C = (A - C) - B :=
  sub_right_comm A B C

/-- Reverse orientation of the finite difference telescope. -/
theorem Complex.sum_range_sub_reverse
    (T : ℕ → ℂ)
    (n : ℕ) :
    (∑ k in Finset.range n, T k) -
        ∑ k in Finset.range n, T (k + 1) =
      T 0 - T n := by
  let A : ℂ := ∑ k in Finset.range n, T k
  let B : ℂ := ∑ k in Finset.range n, T (k + 1)
  have hsplit :
      (∑ k in Finset.range n, (T (k + 1) - T k)) = B - A :=
    Finset.sum_sub_distrib
  have htelescope :
      (∑ k in Finset.range n, (T (k + 1) - T k)) = T n - T 0 :=
    Finset.sum_range_sub T n
  calc
    (∑ k in Finset.range n, T k) -
        ∑ k in Finset.range n, T (k + 1) = A - B := by
      exact rfl
    _ = -(B - A) := by
      exact Eq.symm (neg_sub B A)
    _ = -(∑ k in Finset.range n, (T (k + 1) - T k)) := by
      exact congrArg Neg.neg (Eq.symm hsplit)
    _ = -(T n - T 0) := by
      exact congrArg Neg.neg htelescope
    _ = T 0 - T n := by
      exact neg_sub (T n) (T 0)

/-- A shifted finite sum of differences telescopes against its endpoint terms. -/
theorem Complex.sum_shift_sub_segment_telescope
    (T C : ℕ → ℂ)
    (m : ℕ) :
    (∑ k in Finset.range (m + 1), ((T k - C k) - T (k + 1))) =
      T 0 - T (m + 1) - ∑ k in Finset.range (m + 1), C k := by
  calc
    (∑ k in Finset.range (m + 1), ((T k - C k) - T (k + 1))) =
        (∑ k in Finset.range (m + 1), (T k - C k)) -
          ∑ k in Finset.range (m + 1), T (k + 1) :=
      Finset.sum_sub_distrib
    _ =
        ((∑ k in Finset.range (m + 1), T k) -
            ∑ k in Finset.range (m + 1), C k) -
          ∑ k in Finset.range (m + 1), T (k + 1) :=
      congrArg
        (fun z : ℂ => z - ∑ k in Finset.range (m + 1), T (k + 1))
        Finset.sum_sub_distrib
    _ =
        ((∑ k in Finset.range (m + 1), T k) -
            ∑ k in Finset.range (m + 1), T (k + 1)) -
          ∑ k in Finset.range (m + 1), C k :=
      Complex.sub_sub_right_comm
        (∑ k in Finset.range (m + 1), T k)
        (∑ k in Finset.range (m + 1), C k)
        (∑ k in Finset.range (m + 1), T (k + 1))
    _ = T 0 - T (m + 1) - ∑ k in Finset.range (m + 1), C k :=
      congrArg
        (fun z : ℂ => z - ∑ k in Finset.range (m + 1), C k)
        (Complex.sum_range_sub_reverse T (m + 1))

/-- Collect the horizontal, outer-vertical, and inner-arc contributions in the
right polygonal half-collar boundary. -/
theorem Complex.rightPolygonalHalfCollarBoundary_collect
    (bottom top horizontal topConnector outer inner tangent : ℂ) :
    (bottom - top - horizontal - topConnector) + tangent * outer - inner =
      bottom - top + tangent * outer -
        ((horizontal + inner) + topConnector) := by
  let X : ℂ := bottom - top + tangent * outer
  have hmove_tangent :
      (bottom - top - horizontal - topConnector) + tangent * outer =
        X - horizontal - topConnector := by
    calc
      (bottom - top - horizontal - topConnector) + tangent * outer =
          (bottom - top - horizontal) + tangent * outer - topConnector := by
        exact
          sub_add_eq_add_sub
            (bottom - top - horizontal) topConnector (tangent * outer)
      _ = (bottom - top + tangent * outer - horizontal) - topConnector := by
        exact
          congrArg (fun z : ℂ => z - topConnector)
            (sub_add_eq_add_sub (bottom - top) horizontal (tangent * outer))
      _ = X - horizontal - topConnector := by
        exact rfl
  calc
    (bottom - top - horizontal - topConnector) + tangent * outer - inner =
        (X - horizontal - topConnector) - inner := by
      exact congrArg (fun z : ℂ => z - inner) hmove_tangent
    _ = (X - horizontal - inner) - topConnector := by
      exact sub_right_comm (X - horizontal) topConnector inner
    _ = (X - (horizontal + inner)) - topConnector := by
      exact
        congrArg (fun z : ℂ => z - topConnector)
          (Eq.symm (sub_add_eq_sub_sub X horizontal inner))
    _ = X - ((horizontal + inner) + topConnector) := by
      exact Eq.symm
        (sub_add_eq_sub_sub X (horizontal + inner) topConnector)

end

end LFunctions
end Boundary
