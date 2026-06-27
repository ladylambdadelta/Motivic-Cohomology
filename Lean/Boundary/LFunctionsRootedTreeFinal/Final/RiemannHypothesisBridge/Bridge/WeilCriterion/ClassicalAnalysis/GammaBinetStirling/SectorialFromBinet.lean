import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.Binet
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Integral.SetIntegral
import Mathlib.Order.Interval.Set.Disjoint

/-!
# Sectorial estimates from Binet

This file owns the sectorial remainder estimate extracted from the
Binet-kernel majorant package.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open MeasureTheory
open Set

/-- Trivial real nonnegativity of `2`, named to keep arithmetic side
conditions out of the Binet estimates. -/
theorem Real.zero_le_two_real : (0 : ℝ) ≤ 2 :=
  zero_le_two

/-- The Binet arctangent kernel is measurable for each fixed `w`. -/
theorem Complex.measurable_binetSecondFormula_arctan_kernel
    (w : ℂ) :
    Measurable
      (fun t : ℝ =>
        Complex.arctan ((t : ℂ) / w)) := by
  have hofReal : Measurable fun t : ℝ => (t : ℂ) :=
    Complex.measurable_ofReal
  have hquot : Measurable fun t : ℝ => (t : ℂ) / w :=
    hofReal.div measurable_const
  exact Complex.measurable_arctan.comp hquot

/-- The full Binet second-formula kernel is measurable for each fixed `w`. -/
theorem Complex.measurable_binetSecondFormula_kernel
    (w : ℂ) :
    Measurable
      (fun t : ℝ =>
        Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)) := by
  have harctan : Measurable fun t : ℝ =>
      Complex.arctan ((t : ℂ) / w) :=
    Complex.measurable_binetSecondFormula_arctan_kernel w
  have hlinearReal : Measurable fun t : ℝ =>
      (2 : ℝ) * Real.pi * t :=
    (measurable_const.mul measurable_const).mul measurable_id
  have hlinearComplex : Measurable fun t : ℝ =>
      (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) :=
    Complex.measurable_ofReal.comp hlinearReal
  have hden : Measurable fun t : ℝ =>
      Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1 :=
    hlinearComplex.cexp.sub measurable_const
  exact harctan.div hden

/-- Trivial strict lower bound for `8`, named to keep arithmetic side conditions
out of the Binet estimates. -/
theorem Real.zero_lt_eight_real : (0 : ℝ) < 8 := by
  exact Nat.cast_pos.mpr (Nat.succ_pos 7)

/-- Multiplying twice a number by one half recovers the number. -/
theorem Real.eq_two_mul_mul_half
    (B : ℝ) :
    B = (2 * B) * (1 / 2 : ℝ) := by
  calc
    B = B * 1 := Eq.symm (mul_one B)
    _ = B * ((1 : ℝ) / 2 + (1 : ℝ) / 2) := by
      exact congrArg (fun x : ℝ => B * x) (Eq.symm (add_halves (1 : ℝ)))
    _ = B * ((1 : ℝ) / 2) + B * ((1 : ℝ) / 2) := by
      exact left_distrib B ((1 : ℝ) / 2) ((1 : ℝ) / 2)
    _ = (B + B) * ((1 : ℝ) / 2) := by
      exact Eq.symm (right_distrib B B ((1 : ℝ) / 2))
    _ = (2 * B) * ((1 : ℝ) / 2) := by
      exact congrArg (fun x : ℝ => x * ((1 : ℝ) / 2)) (Eq.symm (two_mul B))

/-- Multiplying by two twice gives the explicit coefficient four. -/
theorem Real.two_mul_two_mul
    (x : ℝ) :
    2 * (2 * x) = 4 * x := by
  calc
    2 * (2 * x) = (2 * x) + (2 * x) := two_mul (2 * x)
    _ = (2 * x + 2 * x) := Eq.refl _
    _ = (2 + 2 : ℝ) * x := by
      exact Eq.symm (right_distrib 2 2 x)
    _ = 4 * x := by
      exact congrArg (fun c : ℝ => c * x) (two_add_two_eq_four)

/-- Multiplying coefficient four by two gives coefficient eight. -/
theorem Real.two_mul_four_mul
    (x : ℝ) :
    2 * (4 * x) = 8 * x := by
  have hcoeff : (2 : ℝ) * 4 = 8 := by
    calc
      (2 : ℝ) * 4 = ((2 * 4 : ℕ) : ℝ) := by
        exact (Nat.cast_mul 2 4).symm
      _ = (8 : ℝ) := by
        exact congrArg (fun n : ℕ => (n : ℝ)) rfl
  calc
    2 * (4 * x) = (2 * 4 : ℝ) * x := by
      exact (mul_assoc 2 4 x).symm
    _ = 8 * x := by
      exact congrArg (fun c : ℝ => c * x) hcoeff

/-- Rewriting the lower split kernel majorant into constant-times-majorant
form. -/
theorem Real.two_mul_div_norm_div_exp_sub_one_eq
    (t : ℝ)
    (r : ℝ) :
    (2 * (t / r)) /
        (Real.exp ((2 : ℝ) * Real.pi * t) - 1) =
      (2 / r) *
        (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  let D : ℝ := Real.exp ((2 : ℝ) * Real.pi * t) - 1
  calc
    (2 * (t / r)) / D = (2 * t / r) / D := by
      exact congrArg (fun x : ℝ => x / D) (mul_div_assoc' 2 t r)
    _ = 2 * t / (r * D) := div_div (2 * t) r D
    _ = (2 / r) * (t / D) := Eq.symm (div_mul_div_comm 2 r t D)

/-- Doubling a constant-times-integral expression gives the Binet split
constant. -/
theorem Real.two_mul_two_div_mul_eq_four_mul_div
    (J r : ℝ) :
    2 * ((2 / r) * J) = 4 * J / r := by
  calc
    2 * ((2 / r) * J) = 2 * (2 * J / r) := by
      exact congrArg (fun x : ℝ => 2 * x) (div_mul_eq_mul_div 2 r J)
    _ = 2 * (2 * J) / r := mul_div_assoc' 2 (2 * J) r
    _ = 4 * J / r := by
      exact congrArg (fun x : ℝ => x / r) (Real.two_mul_two_mul J)

/-- The triangle-assembled split constant is `8`. -/
theorem Real.four_div_add_four_div_eq_eight_div
    (J r : ℝ) :
    4 * J / r + 4 * J / r = 8 * J / r := by
  calc
    4 * J / r + 4 * J / r = (4 * J + 4 * J) / r := by
      exact Eq.symm (add_div (4 * J) (4 * J) r)
    _ = (2 * (4 * J)) / r := by
      exact congrArg (fun x : ℝ => x / r) (Eq.symm (two_mul (4 * J)))
    _ = 8 * J / r := by
      exact congrArg (fun x : ℝ => x / r) (Real.two_mul_four_mul J)

/-- The cutoff conversion arithmetic for turning a bounded tail estimate into
a linear estimate. -/
theorem Real.two_mul_div_mul_half_eq
    {B r : ℝ}
    (hr : r ≠ 0) :
    (2 * B / r) * (r / 2) = B := by
  calc
    (2 * B / r) * (r / 2) =
        ((2 * B / r) * r) / 2 := by
      exact mul_div_assoc' (2 * B / r) r 2
    _ = (2 * B) / 2 := by
      exact congrArg (fun x : ℝ => x / 2) (div_mul_cancel₀ (2 * B) hr)
    _ = (2 * B) * (1 / 2 : ℝ) := by
      exact Eq.trans (div_eq_mul_inv (2 * B) 2)
        (congrArg (fun x : ℝ => (2 * B) * x) (inv_eq_one_div 2))
    _ = B := by
      exact Eq.symm (Real.eq_two_mul_mul_half B)

/-- Twice a real half recovers the original real number. -/
theorem Real.two_mul_div_two
    (x : ℝ) :
    2 * (x / 2) = x := by
  calc
    2 * (x / 2) = x / 2 + x / 2 := two_mul (x / 2)
    _ = x := add_halves x

/-- Exponential tail integral bound for the decay `exp (-(2π)t)`. -/
theorem Real.exp_neg_two_pi_tail_integral_le_exp
    (a : ℝ) :
    ∫ t : ℝ in Set.Ioi a,
        Real.exp (-((2 : ℝ) * Real.pi) * t) ≤
      Real.exp (-((2 : ℝ) * Real.pi) * a) := by
  let k : ℝ := (2 : ℝ) * Real.pi
  have hk_pos : 0 < k :=
    mul_pos two_pos Real.pi_pos
  have hchange :
      ∫ t : ℝ in Set.Ioi a, Real.exp (-((2 : ℝ) * Real.pi) * t) =
        k⁻¹ * ∫ u : ℝ in Set.Ioi (k * a), Real.exp (-u) := by
    calc
      ∫ t : ℝ in Set.Ioi a, Real.exp (-((2 : ℝ) * Real.pi) * t) =
          ∫ t : ℝ in Set.Ioi a, (fun u : ℝ => Real.exp (-u)) (k * t) := by
        exact
          setIntegral_congr_fun measurableSet_Ioi
            (fun t _ht =>
              congrArg Real.exp
                (by
                  exact neg_mul ((2 : ℝ) * Real.pi) t))
      _ =
          k⁻¹ •
            ∫ u : ℝ in Set.Ioi (k * a), Real.exp (-u) :=
        integral_comp_mul_left_Ioi
          (fun u : ℝ => Real.exp (-u)) a hk_pos
      _ =
          k⁻¹ * ∫ u : ℝ in Set.Ioi (k * a), Real.exp (-u) := by
        rfl
  have htail_exact :
      ∫ u : ℝ in Set.Ioi (k * a), Real.exp (-u) =
        Real.exp (-(k * a)) :=
    integral_exp_neg_Ioi (k * a)
  have htail_scaled :
      ∫ t : ℝ in Set.Ioi a,
          Real.exp (-((2 : ℝ) * Real.pi) * t) =
        k⁻¹ * Real.exp (-((2 : ℝ) * Real.pi) * a) := by
    calc
      ∫ t : ℝ in Set.Ioi a, Real.exp (-((2 : ℝ) * Real.pi) * t) =
          k⁻¹ * ∫ u : ℝ in Set.Ioi (k * a), Real.exp (-u) :=
        hchange
      _ = k⁻¹ * Real.exp (-(k * a)) := by
        exact congrArg (fun x : ℝ => k⁻¹ * x) htail_exact
      _ = k⁻¹ * Real.exp (-((2 : ℝ) * Real.pi) * a) := by
        rfl
  have hone_le_k : (1 : ℝ) ≤ k := by
    have hone_le_two : (1 : ℝ) ≤ 2 := one_le_two
    have hone_le_pi : (1 : ℝ) ≤ Real.pi :=
      le_of_lt (lt_trans Real.binetMajorant_one_lt_three Real.pi_gt_three)
    calc
      (1 : ℝ) ≤ 2 := hone_le_two
      _ = 2 * 1 := Eq.symm (mul_one (2 : ℝ))
      _ ≤ 2 * Real.pi :=
        mul_le_mul_of_nonneg_left hone_le_pi zero_le_two
      _ = k := rfl
  have hk_inv_le_one : k⁻¹ ≤ 1 :=
    inv_le_one_of_one_le₀ hone_le_k
  have hexp_nonneg :
      0 ≤ Real.exp (-((2 : ℝ) * Real.pi) * a) :=
    le_of_lt (Real.exp_pos (-((2 : ℝ) * Real.pi) * a))
  exact
    Eq.subst
      (motive := fun x : ℝ =>
        x ≤ Real.exp (-((2 : ℝ) * Real.pi) * a))
      htail_scaled.symm
      (mul_le_of_le_one_left hexp_nonneg hk_inv_le_one)

/-- Reassociate an `ε * (3 * N)` product into `3 * (ε * N)`. -/
theorem Real.mul_three_mul_reassoc
    (ε N : ℝ) :
    ε * (3 * N) = 3 * (ε * N) := by
  calc
    ε * (3 * N) = (3 * N) * ε := by
      exact mul_comm ε (3 * N)
    _ = 3 * (N * ε) := by
      exact mul_assoc 3 N ε
    _ = 3 * (ε * N) := by
      exact congrArg (fun z : ℝ => 3 * z) (mul_comm N ε)

/-- Reassociate a `(3 * N) * ε` product into `3 * (ε * N)`. -/
theorem Real.three_mul_mul_reassoc
    (ε N : ℝ) :
    3 * N * ε = 3 * (ε * N) := by
  calc
    3 * N * ε = 3 * (N * ε) := by
      exact mul_assoc 3 N ε
    _ = 3 * (ε * N) := by
      exact congrArg (fun z : ℝ => 3 * z) (mul_comm N ε)

/-- A number plus twice itself is three times itself. -/
theorem Real.add_two_mul_eq_three_mul
    (x : ℝ) :
    x + 2 * x = 3 * x := by
  have hcoeff : (2 : ℝ) + 1 = 3 := by
    exact two_add_one_eq_three
  calc
    x + 2 * x = x + (x + x) := by
      exact congrArg (fun z : ℝ => x + z) (two_mul x)
    _ = (x + x) + x := by
      exact (add_assoc x x x).symm
    _ = 2 * x + x := by
      exact congrArg (fun z : ℝ => z + x) (two_mul x).symm
    _ = 2 * x + 1 * x := by
      exact congrArg (fun z : ℝ => 2 * x + z) (Eq.symm (one_mul x))
    _ = (2 + 1 : ℝ) * x := by
      exact Eq.symm (right_distrib 2 1 x)
    _ = 3 * x := by
      exact congrArg (fun c : ℝ => c * x) hcoeff

/-- Upper bound for a quotient from an upper numerator bound and a lower
denominator bound. -/
theorem Real.div_le_div_of_le_of_le
    {a A d n : ℝ}
    (ha_pos : 0 < a)
    (hn_nonneg : 0 ≤ n)
    (hnA : n ≤ A)
    (had : a ≤ d) :
    n / d ≤ A / a := by
  have hd_pos : 0 < d := lt_of_lt_of_le ha_pos had
  have hA_nonneg : 0 ≤ A := le_trans hn_nonneg hnA
  have hmul : n * a ≤ A * d :=
    le_trans
      (mul_le_mul_of_nonneg_right hnA (le_of_lt ha_pos))
      (mul_le_mul_of_nonneg_left had hA_nonneg)
  exact (div_le_div_iff₀ hd_pos ha_pos).2 hmul

/-- Lower bound for a quotient from a lower numerator bound and an upper
denominator bound. -/
theorem Real.div_le_div_of_le_of_le'
    {a A d n : ℝ}
    (ha_pos : 0 < a)
    (hA_pos : 0 < A)
    (hd_pos : 0 < d)
    (had : d ≤ A)
    (han : a ≤ n) :
    a / A ≤ n / d := by
  have hmul : a * d ≤ n * A :=
    le_trans
      (mul_le_mul_of_nonneg_left had (le_of_lt ha_pos))
      (mul_le_mul_of_nonneg_right han (le_of_lt hA_pos))
  exact (div_le_div_iff₀ hA_pos hd_pos).2 hmul

/-- The real number `3` is positive. -/
theorem Real.zero_lt_three : (0 : ℝ) < 3 :=
  Nat.cast_pos.mpr (Nat.succ_pos 2)

/-- The real number `3` is nonnegative. -/
theorem Real.zero_le_three : (0 : ℝ) ≤ 3 :=
  le_of_lt Real.zero_lt_three

/-- The real number `1` is at most `3`. -/
theorem Real.one_le_three_real : (1 : ℝ) ≤ (3 : ℝ) :=
  Real.one_le_three

/-- The real number `1/3` is at most `3`. -/
theorem Real.one_div_three_le_three_real : (1 / 3 : ℝ) ≤ 3 := by
  have hthree_pos : (0 : ℝ) < 3 := Real.zero_lt_three
  have hthree_mul : (1 : ℝ) ≤ 3 * 3 := by
    calc
      (1 : ℝ) ≤ (3 : ℝ) := Real.one_le_three_real
      _ ≤ 3 * 3 := by
        exact le_mul_of_one_le_right (le_of_lt hthree_pos) Real.one_le_three_real
  exact (div_le_iff₀ hthree_pos).2 hthree_mul

/-- The real number `4` is nonnegative. -/
theorem Real.zero_le_four : (0 : ℝ) ≤ 4 :=
  Nat.cast_nonneg 4

/-- Reversing a subtraction is the same as negating it. -/
theorem Complex.sub_swap_eq_neg_sub
    (a b : ℂ) :
    b - a = -(a - b) :=
  Eq.symm (neg_sub a b)

/-- Removing a negative summand turns subtraction into addition, then commutes
the two summands. -/
theorem Complex.sub_neg_eq_add_comm
    (a b : ℂ) :
    a - (-b) = b + a := by
  calc
    a - (-b) = a + b := sub_neg_eq_add a b
    _ = b + a := add_comm a b

/-- The real part of `w + t⋅I` is the real part of `w`. -/
theorem Complex.add_im_re (w : ℂ) (t : ℝ) :
    (w + (t : ℂ) * Complex.I).re = w.re := by
  calc
    (w + (t : ℂ) * Complex.I).re = w.re + ((t : ℂ) * Complex.I).re := by
      exact Complex.add_re w ((t : ℂ) * Complex.I)
    _ = w.re := by
      have hI : ((t : ℂ) * Complex.I).re = 0 := by
        calc
          ((t : ℂ) * Complex.I).re = -((t : ℂ).im) := by
            exact Complex.mul_I_re (t : ℂ)
          _ = -0 := by
            exact congrArg Neg.neg (Complex.ofReal_im t)
          _ = 0 := by
            exact neg_zero
      calc
        w.re + ((t : ℂ) * Complex.I).re = w.re + 0 := by
          exact congrArg (fun x : ℝ => w.re + x) hI
        _ = w.re := by
          exact add_zero w.re

/-- The real part of `w - t⋅I` is the real part of `w`. -/
theorem Complex.sub_im_re (w : ℂ) (t : ℝ) :
    (w - (t : ℂ) * Complex.I).re = w.re := by
  calc
    (w - (t : ℂ) * Complex.I).re = w.re - ((t : ℂ) * Complex.I).re := by
      exact Complex.sub_re w ((t : ℂ) * Complex.I)
    _ = w.re := by
      have hI : ((t : ℂ) * Complex.I).re = 0 := by
        calc
          ((t : ℂ) * Complex.I).re = -((t : ℂ).im) := by
            exact Complex.mul_I_re (t : ℂ)
          _ = -0 := by
            exact congrArg Neg.neg (Complex.ofReal_im t)
          _ = 0 := by
            exact neg_zero
      calc
        w.re - ((t : ℂ) * Complex.I).re = w.re - 0 := by
          exact congrArg (fun x : ℝ => w.re - x) hI
        _ = w.re := by
          exact sub_zero w.re

/-- The imaginary part of `w - t⋅I` is the vertical distance coordinate from
the arctangent branch point. -/
theorem Complex.sub_im_im (w : ℂ) (t : ℝ) :
    (w - (t : ℂ) * Complex.I).im = w.im - t := by
  calc
    (w - (t : ℂ) * Complex.I).im =
        w.im - ((t : ℂ) * Complex.I).im := by
      exact Complex.sub_im w ((t : ℂ) * Complex.I)
    _ = w.im - (t : ℂ).re := by
      exact congrArg (fun x : ℝ => w.im - x)
        (Complex.mul_I_im (t : ℂ))
    _ = w.im - t := by
      exact congrArg (fun x : ℝ => w.im - x)
        (Complex.ofReal_re t)

/-- The denominator distance in the Binet arctangent ratio controls the
vertical indentation distance to the branch wall. -/
theorem Complex.binetSecondFormula_arctan_tail_denominator_branchWall_distance_le
    (w : ℂ)
    (t : ℝ) :
    |w.im - t| ≤ ‖w - (t : ℂ) * Complex.I‖ := by
  have him :
      (w - (t : ℂ) * Complex.I).im = w.im - t :=
    Complex.sub_im_im w t
  calc
    |w.im - t| = |(w - (t : ℂ) * Complex.I).im| := by
      exact congrArg abs him.symm
    _ ≤ ‖w - (t : ℂ) * Complex.I‖ := by
      exact Complex.abs_im_le_abs (w - (t : ℂ) * Complex.I)

/-- Multiplying by `1 / 3` cancels a leading factor `3`. -/
theorem Real.one_div_three_mul_three_mul
    (x : ℝ) :
    (1 / 3 : ℝ) * (3 * x) = x := by
  calc
    (1 / 3 : ℝ) * (3 * x)
        = ((1 / 3 : ℝ) * 3) * x :=
            (mul_assoc (1 / 3 : ℝ) 3 x).symm
    _ = 1 * x := by
            exact congrArg (fun y : ℝ => y * x)
              (one_div_mul_cancel (ne_of_gt Real.zero_lt_three))
    _ = x :=
            one_mul x

/-- Distributing the leading Binet factor over a split complex integral. -/
theorem Complex.two_mul_add_eq_add_two_mul
    (a b : ℂ) :
    2 * (a + b) = 2 * a + 2 * b := by
  exact left_distrib (2 : ℂ) a b

/-- Algebraic normalization of the first arctangent branch denominator. -/
theorem Complex.one_sub_real_div_mul_I_eq
    (w : ℂ)
    (hw : w ≠ 0)
    (t : ℝ) :
    1 - ((t : ℂ) / w) * Complex.I =
      (w - (t : ℂ) * Complex.I) / w := by
  exact Complex.arctan_fixed_tail_one_sub_real_div_mul_I_eq w hw t

/-- Algebraic normalization of the second arctangent branch denominator. -/
theorem Complex.one_add_real_div_mul_I_eq
    (w : ℂ)
    (hw : w ≠ 0)
    (t : ℝ) :
    1 + ((t : ℂ) / w) * Complex.I =
      (w + (t : ℂ) * Complex.I) / w := by
  exact Complex.arctan_fixed_tail_one_add_real_div_mul_I_eq w hw t

/-- The norm of a pure imaginary real multiple is the absolute value of the
real coefficient. -/
theorem Complex.norm_real_mul_I (t : ℝ) :
    ‖(t : ℂ) * Complex.I‖ = |t| := by
  calc
    ‖(t : ℂ) * Complex.I‖ = ‖(t : ℂ)‖ * ‖Complex.I‖ := by
      exact norm_mul _ _
    _ = |t| * 1 := by
      exact congrArg₂ HMul.hMul (Complex.norm_real t) Complex.norm_I
    _ = |t| := mul_one |t|

/-- The scalar factor in the arctangent logarithm has norm `1/2`. -/
theorem Complex.norm_neg_I_div_two :
    ‖(-Complex.I / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
  calc
    ‖(-Complex.I / 2 : ℂ)‖ =
        ‖(-Complex.I : ℂ)‖ / ‖(2 : ℂ)‖ := by
      exact norm_div (-Complex.I) (2 : ℂ)
    _ = ‖Complex.I‖ / ‖(2 : ℂ)‖ := by
      exact congrArg (fun x : ℝ => x / ‖(2 : ℂ)‖) (norm_neg Complex.I)
    _ = 1 / ‖(2 : ℂ)‖ := by
      exact congrArg (fun x : ℝ => x / ‖(2 : ℂ)‖) Complex.norm_I
    _ = (1 / 2 : ℝ) := by
      exact congrArg (fun x : ℝ => (1 : ℝ) / x) (Complex.norm_natCast 2)

/-- The half scalar is bounded by one. -/
theorem Real.one_div_two_le_one : (1 / 2 : ℝ) ≤ 1 :=
  le_of_lt one_half_lt_one

/-- If `2n ≤ t`, then `n + t` is bounded by three copies of the tail
`t - n`. -/
theorem Real.add_le_three_mul_sub_of_two_mul_le
    {n t : ℝ}
    (hn : 0 ≤ n)
    (h : 2 * n ≤ t) :
    n + t ≤ 3 * (t - n) := by
  have hsum : n + n ≤ t := by
    exact (two_mul n).symm ▸ h
  have hn_le_t : n ≤ t :=
    le_trans (le_add_of_nonneg_right hn) hsum
  have hn_le_tail : n ≤ t - n :=
    le_sub_iff_add_le'.mpr hsum
  have ht_eq_tail_add_n : t = (t - n) + n :=
    Eq.symm (tsub_add_cancel_of_le hn_le_t)
  have ht_le_two_tail : t ≤ 2 * (t - n) := by
    calc
      t = (t - n) + n := ht_eq_tail_add_n
      _ ≤ (t - n) + (t - n) :=
        add_le_add_left hn_le_tail (t - n)
      _ = 2 * (t - n) := Eq.symm (two_mul (t - n))
  calc
    n + t ≤ (t - n) + t :=
      add_le_add_right hn_le_tail t
    _ ≤ (t - n) + 2 * (t - n) :=
      add_le_add_left ht_le_two_tail (t - n)
    _ = 3 * (t - n) := Real.add_two_mul_eq_three_mul (t - n)

/-- The scalar factor in the arctangent logarithm has norm at most one. -/
theorem Complex.norm_neg_I_div_two_le_one :
    ‖(-Complex.I / 2 : ℂ)‖ ≤ (1 : ℝ) := by
  calc
    ‖(-Complex.I / 2 : ℂ)‖ = (1 / 2 : ℝ) :=
      Complex.norm_neg_I_div_two
    _ ≤ 1 := Real.one_div_two_le_one

/-- The first normalized branch denominator is bounded below by the real part
of the fixed open-half-plane point. -/
theorem Complex.one_sub_real_div_mul_I_norm_lower
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (t : ℝ) :
    w.re / ‖w‖ ≤ ‖1 - ((t : ℂ) / w) * Complex.I‖ := by
  have hw_ne_zero : w ≠ 0 := by
    intro hw_zero
    cases hw_zero
    exact (lt_irrefl (0 : ℝ)) hw_re_pos
  have hw_norm_pos : 0 < ‖w‖ :=
    norm_pos_iff.mpr hw_ne_zero
  have hre_nonneg : 0 ≤ (w - (t : ℂ) * Complex.I).re := by
    have hre : (w - (t : ℂ) * Complex.I).re = w.re :=
      Complex.sub_im_re w t
    exact hre.symm ▸ le_of_lt hw_re_pos
  have hre_abs_eq :
      |(w - (t : ℂ) * Complex.I).re| = w.re := by
    have hre : (w - (t : ℂ) * Complex.I).re = w.re :=
      Complex.sub_im_re w t
    exact Eq.trans (abs_of_nonneg hre_nonneg) hre
  have hre_le_norm :
    w.re ≤ ‖w - (t : ℂ) * Complex.I‖ := by
    calc
      w.re = |(w - (t : ℂ) * Complex.I).re| := hre_abs_eq.symm
      _ ≤ ‖w - (t : ℂ) * Complex.I‖ := by
        exact Complex.abs_re_le_abs (w - (t : ℂ) * Complex.I)
  calc
    w.re / ‖w‖ ≤ ‖w - (t : ℂ) * Complex.I‖ / ‖w‖ :=
      div_le_div_of_nonneg_right hre_le_norm (le_of_lt hw_norm_pos)
    _ = ‖(w - (t : ℂ) * Complex.I) / w‖ := by
      exact (norm_div _ _).symm
    _ = ‖1 - ((t : ℂ) / w) * Complex.I‖ := by
      exact congrArg norm (Complex.one_sub_real_div_mul_I_eq w hw_ne_zero t).symm

/-- The second normalized branch denominator is bounded below by the real part
of the fixed open-half-plane point. -/
theorem Complex.one_add_real_div_mul_I_norm_lower
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (t : ℝ) :
    w.re / ‖w‖ ≤ ‖1 + ((t : ℂ) / w) * Complex.I‖ := by
  have hw_ne_zero : w ≠ 0 := by
    intro hw_zero
    cases hw_zero
    exact (lt_irrefl (0 : ℝ)) hw_re_pos
  have hw_norm_pos : 0 < ‖w‖ :=
    norm_pos_iff.mpr hw_ne_zero
  have hre_nonneg : 0 ≤ (w + (t : ℂ) * Complex.I).re := by
    have hre : (w + (t : ℂ) * Complex.I).re = w.re :=
      Complex.add_im_re w t
    exact hre.symm ▸ le_of_lt hw_re_pos
  have hre_abs_eq :
      |(w + (t : ℂ) * Complex.I).re| = w.re := by
    have hre : (w + (t : ℂ) * Complex.I).re = w.re :=
      Complex.add_im_re w t
    exact Eq.trans (abs_of_nonneg hre_nonneg) hre
  have hre_le_norm :
      w.re ≤ ‖w + (t : ℂ) * Complex.I‖ := by
    calc
      w.re = |(w + (t : ℂ) * Complex.I).re| := hre_abs_eq.symm
      _ ≤ ‖w + (t : ℂ) * Complex.I‖ := by
        exact Complex.abs_re_le_abs (w + (t : ℂ) * Complex.I)
  calc
    w.re / ‖w‖ ≤ ‖w + (t : ℂ) * Complex.I‖ / ‖w‖ :=
      div_le_div_of_nonneg_right hre_le_norm (le_of_lt hw_norm_pos)
    _ = ‖(w + (t : ℂ) * Complex.I) / w‖ := by
      exact (norm_div _ _).symm
    _ = ‖1 + ((t : ℂ) / w) * Complex.I‖ := by
      exact congrArg norm (Complex.one_add_real_div_mul_I_eq w hw_ne_zero t).symm

/-- Along the fixed open-half-plane ray `t / w`, the principal arctangent is
uniformly separated from the arctangent branch singularities on the upper split
interval. -/
theorem Complex.binetSecondFormula_arctan_tail_branch_separation
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ δ : ℝ,
      0 < δ ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          δ ≤ ‖1 - ((t : ℂ) / w) * Complex.I‖ ∧
          δ ≤ ‖1 + ((t : ℂ) / w) * Complex.I‖ := by
  have hw_ne_zero : w ≠ 0 := by
    intro hw_zero
    cases hw_zero
    exact (lt_irrefl (0 : ℝ)) hw_re_pos
  have hw_norm_pos : 0 < ‖w‖ :=
    norm_pos_iff.mpr hw_ne_zero
  refine ⟨w.re / ‖w‖, div_pos hw_re_pos hw_norm_pos, ?_⟩
  intro t ht
  exact
    ⟨Complex.one_sub_real_div_mul_I_norm_lower hw_re_pos t,
      Complex.one_add_real_div_mul_I_norm_lower hw_re_pos t⟩

/-- The principal logarithm is bounded by the absolute logarithm of the norm
plus the universal argument bound. -/
theorem Complex.log_norm_le_abs_log_norm_add_pi
    (z : ℂ) :
    ‖Complex.log z‖ ≤ |Real.log ‖z‖| + Real.pi := by
  calc
    ‖Complex.log z‖ = Complex.abs (Complex.log z) := Complex.norm_eq_abs _
    _ ≤ |(Complex.log z).re| + |(Complex.log z).im| :=
      Complex.abs_le_abs_re_add_abs_im (Complex.log z)
    _ = |Real.log ‖z‖| + |Complex.arg z| := by
      have hlog_re : (Complex.log z).re = Real.log ‖z‖ := Complex.log_re z
      have hlog_im : (Complex.log z).im = Complex.arg z := Complex.log_im z
      calc
        |(Complex.log z).re| + |(Complex.log z).im| =
            |Real.log ‖z‖| + |(Complex.log z).im| := by
          exact congrArg (fun x : ℝ => |x| + |(Complex.log z).im|) hlog_re
        _ = |Real.log ‖z‖| + |Complex.arg z| := by
          exact congrArg (fun x : ℝ => |Real.log ‖z‖| + |x|) hlog_im
    _ ≤ |Real.log ‖z‖| + Real.pi :=
      add_le_add_left (Complex.abs_arg_le_pi z) _

/-- A positive two-sided bound for a real argument gives a finite bound for
the absolute value of its logarithm. -/
theorem Real.abs_log_le_max_abs_log_of_bounds
    {m M x : ℝ}
    (hm_pos : 0 < m)
    (hmM : m ≤ M)
    (hmx : m ≤ x)
    (hxM : x ≤ M) :
    |Real.log x| ≤
      max |Real.log m| |Real.log M| := by
  have hx_pos : 0 < x := lt_of_lt_of_le hm_pos hmx
  have hM_pos : 0 < M := lt_of_lt_of_le hm_pos hmM
  have hlog_lower : Real.log m ≤ Real.log x :=
    Real.log_le_log hm_pos hmx
  have hlog_upper : Real.log x ≤ Real.log M :=
    Real.log_le_log hx_pos hxM
  have hleft :
      -(max |Real.log m| |Real.log M|) ≤ Real.log x := by
    have hneg_abs_m : -|Real.log m| ≤ Real.log m :=
      neg_abs_le (Real.log m)
    have hmax_left : |Real.log m| ≤ max |Real.log m| |Real.log M| :=
      le_max_left _ _
    exact
      le_trans (neg_le_neg hmax_left)
        (le_trans hneg_abs_m hlog_lower)
  have hright :
      Real.log x ≤ max |Real.log m| |Real.log M| := by
    have hlogM_le_abs : Real.log M ≤ |Real.log M| :=
      le_abs_self (Real.log M)
    have hmax_right : |Real.log M| ≤ max |Real.log m| |Real.log M| :=
      le_max_right _ _
    exact le_trans hlog_upper (le_trans hlogM_le_abs hmax_right)
  exact abs_le.mpr ⟨hleft, hright⟩

/-- A nonzero complex number whose norm has positive two-sided real bounds
has bounded principal logarithm. -/
theorem Complex.log_norm_le_of_norm_bounds
    {m M : ℝ}
    (hm_pos : 0 < m)
    (hmM : m ≤ M)
    {z : ℂ}
    (hmz : m ≤ ‖z‖)
    (hzM : ‖z‖ ≤ M) :
    ‖Complex.log z‖ ≤
      max |Real.log m| |Real.log M| + Real.pi := by
  have hlog :
      |Real.log ‖z‖| ≤ max |Real.log m| |Real.log M| :=
    Real.abs_log_le_max_abs_log_of_bounds
      hm_pos hmM hmz hzM
  calc
    ‖Complex.log z‖ ≤ |Real.log ‖z‖| + Real.pi :=
      Complex.log_norm_le_abs_log_norm_add_pi z
    _ ≤ max |Real.log m| |Real.log M| + Real.pi :=
      add_le_add_right hlog _

/-- The upper-tail ratio can be rewritten without the common factor `w`.

This is the algebraic normalization used by all subsequent real estimates. -/
theorem Complex.binetSecondFormula_arctan_tail_ratio_eq
    (w : ℂ)
    (hw : w ≠ 0)
    (t : ℝ) :
    ((1 + ((t : ℂ) / w) * Complex.I) /
        (1 - ((t : ℂ) / w) * Complex.I)) =
      (w + (t : ℂ) * Complex.I) /
        (w - (t : ℂ) * Complex.I) := by
  exact Complex.arctan_fixed_tail_ratio_eq w hw t

/-- The arctangent ratio can be rewritten in cleared-denominator form. -/
theorem Complex.binetSecondFormula_arctan_tail_ratio_eq_norm
    (w : ℂ)
    (hw : w ≠ 0)
    (t : ℝ) :
    ‖(1 + ((t : ℂ) / w) * Complex.I) /
        (1 - ((t : ℂ) / w) * Complex.I)‖ =
      ‖(w + (t : ℂ) * Complex.I) /
        (w - (t : ℂ) * Complex.I)‖ := by
  exact congrArg norm (Complex.binetSecondFormula_arctan_tail_ratio_eq w hw t)

/-- The arctangent expression is the scaled logarithm of the ratio. -/
theorem Complex.binetSecondFormula_arctan_tail_expr_eq
  (w : ℂ)
  (t : ℝ) :
    Complex.arctan ((t : ℂ) / w) =
      (-Complex.I / 2 : ℂ) *
        Complex.log
          ((1 + ((t : ℂ) / w) * Complex.I) /
            (1 - ((t : ℂ) / w) * Complex.I)) := by
  rfl

/-- The positive-tail exponential denominator norm is explicit. -/
theorem Complex.exp_tail_denominator_norm_eq
    (t : ℝ)
    (ht_pos : 0 < t) :
    ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ =
      Real.exp ((2 : ℝ) * Real.pi * t) - 1 := by
  calc
    ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ =
        ‖Real.exp ((2 : ℝ) * Real.pi * t) - 1‖ :=
      Complex.binetSecondFormula_exp_denominator_norm_eq t
    _ = Real.exp ((2 : ℝ) * Real.pi * t) - 1 :=
      Real.binetSecondFormula_exp_denominator_norm_eq ht_pos

/-- A positive real part gives a positive norm. -/
theorem Complex.norm_pos_of_re_pos
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    0 < ‖w‖ :=
  norm_pos_iff.mpr
    (fun hw_zero => by
      cases hw_zero
      exact (lt_irrefl (0 : ℝ)) hw_re_pos)

/-- The separation hypothesis implies the lower real-part product bound. -/
theorem Complex.sep_mul_le_re
    {ε : ℝ} {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hw_sep : ε ≤ w.re / ‖w‖) :
    ε * ‖w‖ ≤ w.re := by
  have hw_norm_pos : 0 < ‖w‖ :=
    Complex.norm_pos_of_re_pos hw_re_pos
  have hmul : ε * ‖w‖ ≤ w.re := by
    have h := hw_sep
    exact (le_div_iff₀ hw_norm_pos).mp h
  exact hmul

/-- The norm cutoff implies the `1/2` tail lower bound. -/
theorem Complex.half_le_tail
    {w : ℂ}
    (hw_large : 1 ≤ ‖w‖)
    {t : ℝ}
    (ht_tail : t ∈ Set.Ioi (‖w‖ / 2)) :
    (1 / 2 : ℝ) ≤ t := by
  calc
    (1 / 2 : ℝ) ≤ ‖w‖ / 2 :=
      div_le_div_of_nonneg_right hw_large Real.zero_le_two_real
    _ ≤ t := le_of_lt ht_tail

/-- The numerator in the arctangent ratio has norm bounded below by the fixed
positive real part. -/
theorem Complex.binetSecondFormula_arctan_tail_ratio_numerator_lower
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (t : ℝ) :
    w.re ≤ ‖w + (t : ℂ) * Complex.I‖ := by
  have hre_nonneg : 0 ≤ (w + (t : ℂ) * Complex.I).re := by
    have hre : (w + (t : ℂ) * Complex.I).re = w.re := by
      calc
        (w + (t : ℂ) * Complex.I).re = w.re + ((t : ℂ) * Complex.I).re := by
          exact Complex.add_re w ((t : ℂ) * Complex.I)
        _ = w.re + 0 := by
          have hI : ((t : ℂ) * Complex.I).re = 0 := by
            calc
              ((t : ℂ) * Complex.I).re = -((t : ℂ).im) := by
                exact Complex.mul_I_re (t : ℂ)
              _ = -0 := by
                exact congrArg Neg.neg (Complex.ofReal_im t)
              _ = 0 := by
                exact neg_zero
          exact congrArg (fun x : ℝ => w.re + x) hI
        _ = w.re := by
          exact add_zero w.re
    exact hre.symm ▸ le_of_lt hw_re_pos
  have hre_abs_eq :
      |(w + (t : ℂ) * Complex.I).re| = w.re := by
    calc
      |(w + (t : ℂ) * Complex.I).re| = |w.re| := by
        congr 1
        calc
          (w + (t : ℂ) * Complex.I).re = w.re + ((t : ℂ) * Complex.I).re := by
            exact Complex.add_re w ((t : ℂ) * Complex.I)
          _ = w.re := by
            have hI : ((t : ℂ) * Complex.I).re = 0 := by
              calc
                ((t : ℂ) * Complex.I).re = -((t : ℂ).im) := by
                  exact Complex.mul_I_re (t : ℂ)
                _ = -0 := by
                  exact congrArg Neg.neg (Complex.ofReal_im t)
                _ = 0 := by
                  exact neg_zero
            calc
              w.re + ((t : ℂ) * Complex.I).re = w.re + 0 := by
                exact congrArg (fun x : ℝ => w.re + x) hI
              _ = w.re := by
                exact add_zero w.re
      _ = w.re := abs_of_nonneg (le_of_lt hw_re_pos)
  calc
    w.re = |(w + (t : ℂ) * Complex.I).re| := hre_abs_eq.symm
    _ ≤ ‖w + (t : ℂ) * Complex.I‖ := by
      exact Complex.abs_re_le_abs (w + (t : ℂ) * Complex.I)

/-- The denominator in the arctangent ratio has norm bounded below by the fixed
positive real part. -/
theorem Complex.binetSecondFormula_arctan_tail_ratio_denominator_lower
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (t : ℝ) :
    w.re ≤ ‖w - (t : ℂ) * Complex.I‖ := by
  have hre_nonneg : 0 ≤ (w - (t : ℂ) * Complex.I).re := by
    have hre : (w - (t : ℂ) * Complex.I).re = w.re :=
      Complex.sub_im_re w t
    exact hre.symm ▸ le_of_lt hw_re_pos
  have hre_abs_eq :
      |(w - (t : ℂ) * Complex.I).re| = w.re := by
    calc
      |(w - (t : ℂ) * Complex.I).re| = |w.re| := by
        congr 1
        calc
          (w - (t : ℂ) * Complex.I).re = w.re - ((t : ℂ) * Complex.I).re := by
            exact Complex.sub_re w ((t : ℂ) * Complex.I)
          _ = w.re := by
            have hI : ((t : ℂ) * Complex.I).re = 0 := by
              calc
                ((t : ℂ) * Complex.I).re = -((t : ℂ).im) := by
                  exact Complex.mul_I_re (t : ℂ)
                _ = -0 := by
                  exact congrArg Neg.neg (Complex.ofReal_im t)
                _ = 0 := by
                  exact neg_zero
            calc
              w.re - ((t : ℂ) * Complex.I).re = w.re - 0 := by
                exact congrArg (fun x : ℝ => w.re - x) hI
              _ = w.re := by
                exact sub_zero w.re
      _ = w.re := abs_of_nonneg (le_of_lt hw_re_pos)
  calc
    w.re = |(w - (t : ℂ) * Complex.I).re| := hre_abs_eq.symm
    _ ≤ ‖w - (t : ℂ) * Complex.I‖ := by
      exact Complex.abs_re_le_abs (w - (t : ℂ) * Complex.I)

/-- The denominator distance in the Binet arctangent ratio simultaneously
controls the right-half-plane indentation radius and the vertical branch-wall
distance. -/
theorem Complex.binetSecondFormula_arctan_tail_denominator_max_branchWall_distance_le
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (t : ℝ) :
    max w.re |w.im - t| ≤ ‖w - (t : ℂ) * Complex.I‖ := by
  exact
    max_le
      (Complex.binetSecondFormula_arctan_tail_ratio_denominator_lower
        hw_re_pos t)
      (Complex.binetSecondFormula_arctan_tail_denominator_branchWall_distance_le
        w t)

/-- On the bounded part of the tail, the unnormalized numerator is bounded by
`3 * ‖w‖`. -/
theorem Complex.binetSecondFormula_arctan_tail_numerator_le_three_norm
    {w : ℂ}
    {t : ℝ}
    (ht_nonneg : 0 ≤ t)
    (ht_le : t ≤ 2 * ‖w‖) :
    ‖w + (t : ℂ) * Complex.I‖ ≤ 3 * ‖w‖ := by
  have htI_norm : ‖(t : ℂ) * Complex.I‖ = t := by
    calc
      ‖(t : ℂ) * Complex.I‖ = |t| := Complex.norm_real_mul_I t
      _ = t := abs_of_nonneg ht_nonneg
  calc
    ‖w + (t : ℂ) * Complex.I‖ ≤ ‖w‖ + ‖(t : ℂ) * Complex.I‖ :=
      norm_add_le _ _
    _ = ‖w‖ + t := by exact congrArg (fun x : ℝ => ‖w‖ + x) htI_norm
    _ ≤ ‖w‖ + 2 * ‖w‖ := add_le_add_left ht_le _
    _ = 3 * ‖w‖ := by
      exact Real.add_two_mul_eq_three_mul ‖w‖

/-- On the bounded part of the tail, the cleared arctangent ratio is bounded
by the branch-wall indentation denominator.

This is the pointwise local-indentation majorant: the numerator is at most
`3‖w‖`, while the denominator controls both the right-half-plane indentation
radius and the vertical distance to the branch wall. -/
theorem Complex.binetSecondFormula_arctan_tail_cleared_ratio_norm_le_three_norm_div_branchWall_distance
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    {t : ℝ}
    (ht_nonneg : 0 ≤ t)
    (ht_le : t ≤ 2 * ‖w‖) :
    ‖(w + (t : ℂ) * Complex.I) /
        (w - (t : ℂ) * Complex.I)‖ ≤
      (3 * ‖w‖) / max w.re |w.im - t| := by
  have hnum_upper :
      ‖w + (t : ℂ) * Complex.I‖ ≤ 3 * ‖w‖ :=
    Complex.binetSecondFormula_arctan_tail_numerator_le_three_norm
      ht_nonneg ht_le
  have hden_lower :
      max w.re |w.im - t| ≤ ‖w - (t : ℂ) * Complex.I‖ :=
    Complex.binetSecondFormula_arctan_tail_denominator_max_branchWall_distance_le
      hw_re_pos t
  have hmax_pos : 0 < max w.re |w.im - t| :=
    lt_of_lt_of_le hw_re_pos (le_max_left w.re |w.im - t|)
  calc
    ‖(w + (t : ℂ) * Complex.I) /
        (w - (t : ℂ) * Complex.I)‖ =
        ‖w + (t : ℂ) * Complex.I‖ /
          ‖w - (t : ℂ) * Complex.I‖ := by
      exact norm_div _ _
    _ ≤ (3 * ‖w‖) / max w.re |w.im - t| := by
      exact
        Real.div_le_div_of_le_of_le
          hmax_pos
          (norm_nonneg (w + (t : ℂ) * Complex.I))
          hnum_upper
          hden_lower

/-- Normalized arctangent-ratio version of the branch-wall indentation
majorant on the bounded part of the tail. -/
theorem Complex.binetSecondFormula_arctan_tail_ratio_norm_le_three_norm_div_branchWall_distance
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    {t : ℝ}
    (ht_nonneg : 0 ≤ t)
    (ht_le : t ≤ 2 * ‖w‖) :
    ‖(1 + ((t : ℂ) / w) * Complex.I) /
        (1 - ((t : ℂ) / w) * Complex.I)‖ ≤
      (3 * ‖w‖) / max w.re |w.im - t| := by
  have hw_ne_zero : w ≠ 0 := by
    intro hw_zero
    cases hw_zero
    exact (lt_irrefl (0 : ℝ)) hw_re_pos
  calc
    ‖(1 + ((t : ℂ) / w) * Complex.I) /
        (1 - ((t : ℂ) / w) * Complex.I)‖ =
        ‖(w + (t : ℂ) * Complex.I) /
          (w - (t : ℂ) * Complex.I)‖ := by
      exact Complex.binetSecondFormula_arctan_tail_ratio_eq_norm
        w hw_ne_zero t
    _ ≤ (3 * ‖w‖) / max w.re |w.im - t| :=
      Complex.binetSecondFormula_arctan_tail_cleared_ratio_norm_le_three_norm_div_branchWall_distance
        hw_re_pos ht_nonneg ht_le

/-- The branch-wall distance package is bounded below by the real part. -/
theorem Complex.binetSecondFormula_branchWall_distance_re_le
    (w : ℂ)
    (t : ℝ) :
    w.re ≤ max w.re |w.im - t| := by
  exact le_max_left w.re |w.im - t|

/-- The branch-wall distance package is positive in the open right half-plane. -/
theorem Complex.binetSecondFormula_branchWall_distance_pos
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (t : ℝ) :
    0 < max w.re |w.im - t| := by
  exact
    lt_of_lt_of_le
      hw_re_pos
      (Complex.binetSecondFormula_branchWall_distance_re_le w t)

/-- Increasing the branch-wall distance lowers the normalized arctangent
ratio majorant. -/
theorem Complex.binetSecondFormula_branchWall_ratio_le_realPart_ratio
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (t : ℝ) :
    (3 * ‖w‖) / max w.re |w.im - t| ≤
      (3 * ‖w‖) / w.re := by
  have hnum_nonneg : 0 ≤ 3 * ‖w‖ :=
    mul_nonneg Real.zero_le_three (norm_nonneg w)
  have hden_le :
      w.re ≤ max w.re |w.im - t| :=
    Complex.binetSecondFormula_branchWall_distance_re_le w t
  exact
    div_le_div_of_nonneg_left
      hnum_nonneg
      hw_re_pos
      hden_le

/-- On the bounded branch-wall window the moving logarithmic ratio lies between
`1` and the real-part ratio. -/
theorem Complex.binetSecondFormula_branchWall_moving_ratio_bounds
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    {t : ℝ}
    (ht_nonneg : 0 ≤ t)
    (ht_le : t ≤ 2 * ‖w‖) :
    (1 : ℝ) ≤ (3 * ‖w‖) / max w.re |w.im - t| ∧
      (3 * ‖w‖) / max w.re |w.im - t| ≤
        (3 * ‖w‖) / w.re := by
  have hdist_pos :
      0 < max w.re |w.im - t| :=
    Complex.binetSecondFormula_branchWall_distance_pos hw_re_pos t
  have hdist_le :
      max w.re |w.im - t| ≤ 3 * ‖w‖ :=
    Complex.binetSecondFormula_arctan_tail_denominator_max_branchWall_distance_le
      (w := w) (t := t) ht_nonneg ht_le
  have hlower :
      (1 : ℝ) ≤ (3 * ‖w‖) / max w.re |w.im - t| := by
    exact
      (le_div_iff₀ hdist_pos).mpr
        (Eq.subst
          (motive := fun x : ℝ => x ≤ 3 * ‖w‖)
          (one_mul (max w.re |w.im - t|)).symm
          hdist_le)
  have hupper :
      (3 * ‖w‖) / max w.re |w.im - t| ≤
        (3 * ‖w‖) / w.re :=
    Complex.binetSecondFormula_branchWall_ratio_le_realPart_ratio
      hw_re_pos t
  exact And.intro hlower hupper

/-- The moving branch-wall logarithm is bounded by the fixed real-part
logarithmic window on the bounded tail interval. -/
theorem Complex.binetSecondFormula_branchWall_moving_ratio_abs_log_le_realPart_window
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    {t : ℝ}
    (ht_nonneg : 0 ≤ t)
    (ht_le : t ≤ 2 * ‖w‖) :
    |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| ≤
      max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| := by
  let A : ℝ := (3 * ‖w‖) / max w.re |w.im - t|
  let U : ℝ := (3 * ‖w‖) / w.re
  have hw_norm_pos : 0 < ‖w‖ :=
    Complex.norm_pos_of_re_pos hw_re_pos
  have hre_le_norm : w.re ≤ ‖w‖ := by
    calc
      w.re = |w.re| := Eq.symm (abs_of_pos hw_re_pos)
      _ ≤ ‖w‖ := Complex.abs_re_le_abs w
  have hre_le_three_norm : w.re ≤ 3 * ‖w‖ := by
    calc
      w.re ≤ ‖w‖ := hre_le_norm
      _ ≤ 3 * ‖w‖ :=
        le_mul_of_one_le_left
          (le_of_lt hw_norm_pos)
          Real.one_le_three_real
  have hU_ge_one : (1 : ℝ) ≤ U := by
    exact
      (le_div_iff₀ hw_re_pos).mpr
        (Eq.subst
          (motive := fun x : ℝ => x ≤ 3 * ‖w‖)
          (one_mul w.re).symm
          hre_le_three_norm)
  have hbounds :
      (1 : ℝ) ≤ A ∧ A ≤ U :=
    Complex.binetSecondFormula_branchWall_moving_ratio_bounds
      hw_re_pos ht_nonneg ht_le
  exact
    Real.abs_log_le_max_abs_log_of_bounds
      zero_lt_one
      hU_ge_one
      hbounds.1
      hbounds.2

/-- The moving branch-wall logarithmic numerator is bounded by the fixed
real-part logarithmic numerator on the bounded tail interval. -/
theorem Complex.binetSecondFormula_branchWall_moving_logNumerator_le_realPart_window
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    {t : ℝ}
    (ht_nonneg : 0 ≤ t)
    (ht_le : t ≤ 2 * ‖w‖) :
    |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi ≤
      max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| +
        Real.pi := by
  exact
    add_le_add_right
      (Complex.binetSecondFormula_branchWall_moving_ratio_abs_log_le_realPart_window
        hw_re_pos ht_nonneg ht_le)
      Real.pi

/-- On the bounded tail window, the exponential denominator is no smaller than
the denominator at the lower split scale `‖w‖ / 2`. -/
theorem Complex.binetSecondFormula_branchWall_exp_denominator_lower
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    {t : ℝ}
    (ht_lower : ‖w‖ / 2 ≤ t) :
    Real.exp (Real.pi * ‖w‖) - 1 ≤
      Real.exp ((2 : ℝ) * Real.pi * t) - 1 := by
  have hpi_le : Real.pi * ‖w‖ ≤ (2 : ℝ) * Real.pi * t := by
    have hmul_lower :
        Real.pi * (‖w‖ / 2) ≤ Real.pi * t :=
      mul_le_mul_of_nonneg_left ht_lower (le_of_lt Real.pi_pos)
    calc
      Real.pi * ‖w‖ =
          (2 : ℝ) * (Real.pi * (‖w‖ / 2)) := by
        exact Eq.symm <| by
          calc
            (2 : ℝ) * (Real.pi * (‖w‖ / 2)) =
                ((2 : ℝ) * Real.pi) * (‖w‖ / 2) := by
              exact (mul_assoc (2 : ℝ) Real.pi (‖w‖ / 2)).symm
            _ = (Real.pi * 2) * (‖w‖ / 2) := by
              exact congrArg (fun x : ℝ => x * (‖w‖ / 2))
                (mul_comm (2 : ℝ) Real.pi)
            _ = Real.pi * (2 * (‖w‖ / 2)) := by
              exact mul_assoc Real.pi 2 (‖w‖ / 2)
            _ = Real.pi * ‖w‖ := by
              exact congrArg (fun x : ℝ => Real.pi * x)
                (Real.two_mul_div_two ‖w‖)
      _ ≤ (2 : ℝ) * (Real.pi * t) :=
        mul_le_mul_of_nonneg_left hmul_lower Real.zero_le_two_real
      _ = (2 : ℝ) * Real.pi * t :=
        (mul_assoc (2 : ℝ) Real.pi t).symm
  exact sub_le_sub_right (Real.exp_le_exp.mpr hpi_le) 1

/-- The lower split-scale Binet denominator is positive in the open right
half-plane. -/
theorem Complex.binetSecondFormula_branchWall_split_exp_denominator_pos
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    0 < Real.exp (Real.pi * ‖w‖) - 1 := by
  have hw_norm_pos : 0 < ‖w‖ :=
    Complex.norm_pos_of_re_pos hw_re_pos
  have hpi_norm_pos : 0 < Real.pi * ‖w‖ :=
    mul_pos Real.pi_pos hw_norm_pos
  exact sub_pos.mpr
    (calc
      (1 : ℝ) = Real.exp 0 := Eq.symm Real.exp_zero
      _ < Real.exp (Real.pi * ‖w‖) :=
        Real.exp_lt_exp.mpr hpi_norm_pos)

/-- The branch-wall logarithmic spike produced by the local arctangent-ratio
majorant is integrable on the bounded tail window against the Binet
exponential denominator. -/
theorem Complex.binetSecondFormula_branchWall_logSpike_integrableOn_boundedTailWindow
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    IntegrableOn
      (fun t : ℝ =>
        (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi) /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (Set.Icc (‖w‖ / 2) (2 * ‖w‖)) := by
  let S : Set ℝ := Set.Icc (‖w‖ / 2) (2 * ‖w‖)
  let D : ℝ → ℝ := fun t : ℝ => max w.re |w.im - t|
  let A : ℝ → ℝ := fun t : ℝ => (3 * ‖w‖) / D t
  let E : ℝ → ℝ := fun t : ℝ =>
    Real.exp ((2 : ℝ) * Real.pi * t) - 1
  have hw_norm_pos : 0 < ‖w‖ :=
    Complex.norm_pos_of_re_pos hw_re_pos
  have hD_pos : ∀ t : ℝ, 0 < D t := by
    intro t
    exact lt_of_lt_of_le hw_re_pos (le_max_left w.re |w.im - t|)
  have hA_pos : ∀ t : ℝ, 0 < A t := by
    intro t
    exact div_pos (mul_pos Real.zero_lt_three hw_norm_pos) (hD_pos t)
  have hS_lower : ∀ t : ℝ, t ∈ S → ‖w‖ / 2 ≤ t := by
    intro t ht
    exact ht.1
  have hhalf_pos : 0 < ‖w‖ / 2 :=
    div_pos hw_norm_pos zero_lt_two
  have ht_pos : ∀ t : ℝ, t ∈ S → 0 < t := by
    intro t ht
    exact lt_of_lt_of_le hhalf_pos (hS_lower t ht)
  have hE_ne : ∀ t : ℝ, t ∈ S → E t ≠ 0 := by
    intro t ht
    exact (Real.binetSecondFormula_exp_denominator_pos (ht_pos t ht)).ne'
  have hD_cont : Continuous D := by
    have hdist_cont : Continuous fun t : ℝ => |w.im - t| :=
      (continuous_const.sub continuous_id).abs
    exact continuous_const.max hdist_cont
  have hA_cont : Continuous A := by
    exact continuous_const.div hD_cont (fun t => (hD_pos t).ne')
  have hlog_contOn : ContinuousOn (fun t : ℝ => Real.log (A t)) S :=
    (hA_cont.continuousOn).log (fun t ht => (hA_pos t).ne')
  have hnum_contOn :
      ContinuousOn (fun t : ℝ => |Real.log (A t)| + Real.pi) S :=
    hlog_contOn.abs.add continuousOn_const
  have hlinear_cont : Continuous fun t : ℝ => (2 : ℝ) * Real.pi * t :=
    (continuous_const.mul continuous_const).mul continuous_id
  have hE_cont : Continuous E := by
    exact (Real.continuous_exp.comp hlinear_cont).sub continuous_const
  have hquot_contOn :
      ContinuousOn
        (fun t : ℝ => (|Real.log (A t)| + Real.pi) / E t) S :=
    hnum_contOn.div hE_cont.continuousOn hE_ne
  exact hquot_contOn.integrableOn_Icc

/-- The branch-wall logarithmic spike is integrable on the half-open bounded
tail window used by the exact Binet tail split. -/
theorem Complex.binetSecondFormula_branchWall_logSpike_integrableOn_boundedTailWindow_Ioc
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    IntegrableOn
      (fun t : ℝ =>
        (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi) /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (Set.Ioc (‖w‖ / 2) (2 * ‖w‖)) := by
  have hIcc :
      IntegrableOn
        (fun t : ℝ =>
          (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi) /
            (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
        (Set.Icc (‖w‖ / 2) (2 * ‖w‖)) :=
    Complex.binetSecondFormula_branchWall_logSpike_integrableOn_boundedTailWindow
      hw_re_pos
  have hsubset :
      Set.Ioc (‖w‖ / 2) (2 * ‖w‖) ⊆
        Set.Icc (‖w‖ / 2) (2 * ‖w‖) := by
    intro t ht
    exact ⟨le_of_lt ht.1, ht.2⟩
  exact hIcc.mono_set hsubset

/-- The unweighted branch-wall logarithmic spike is integrable on the
half-open bounded tail window used by the Binet split.

This is the real-variable core that should be used before any fixed
real-part envelope is introduced: the singularity is the moving logarithmic
one, and it is locally integrable on the exact split interval. -/
theorem Complex.binetSecondFormula_branchWall_unweightedLogSpike_integrableOn_boundedTailWindow_Ioc
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    IntegrableOn
      (fun t : ℝ =>
        |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi)
      (Set.Ioc (‖w‖ / 2) (2 * ‖w‖)) := by
  let Scc : Set ℝ := Set.Icc (‖w‖ / 2) (2 * ‖w‖)
  let D : ℝ → ℝ := fun t : ℝ => max w.re |w.im - t|
  let A : ℝ → ℝ := fun t : ℝ => (3 * ‖w‖) / D t
  have hw_norm_pos : 0 < ‖w‖ :=
    Complex.norm_pos_of_re_pos hw_re_pos
  have hD_pos : ∀ t : ℝ, 0 < D t := by
    intro t
    exact lt_of_lt_of_le hw_re_pos (le_max_left w.re |w.im - t|)
  have hA_pos : ∀ t : ℝ, 0 < A t := by
    intro t
    exact div_pos (mul_pos Real.zero_lt_three hw_norm_pos) (hD_pos t)
  have hdist_cont : Continuous fun t : ℝ => |w.im - t| :=
    (continuous_const.sub continuous_id).abs
  have hD_cont : Continuous D :=
    continuous_const.max hdist_cont
  have hA_cont : Continuous A :=
    continuous_const.div hD_cont (fun t => (hD_pos t).ne')
  have hlog_contOn : ContinuousOn (fun t : ℝ => Real.log (A t)) Scc :=
    (hA_cont.continuousOn).log (fun t _ht => (hA_pos t).ne')
  have hnum_contOn :
      ContinuousOn (fun t : ℝ => |Real.log (A t)| + Real.pi) Scc :=
    hlog_contOn.abs.add continuousOn_const
  have hIcc :
      IntegrableOn
        (fun t : ℝ =>
          |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi)
        Scc :=
    hnum_contOn.integrableOn_Icc
  have hsubset :
      Set.Ioc (‖w‖ / 2) (2 * ‖w‖) ⊆
        Set.Icc (‖w‖ / 2) (2 * ‖w‖) := by
    intro t ht
    exact ⟨le_of_lt ht.1, ht.2⟩
  exact hIcc.mono_set hsubset

/-- Pointwise bounded-window control of the branch-wall logarithmic spike
against the Binet exponential denominator. -/
theorem Complex.binetSecondFormula_branchWall_logSpike_pointwise_le_boundedTailWindow
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    {t : ℝ}
    (ht_mem : t ∈ Set.Icc (‖w‖ / 2) (2 * ‖w‖)) :
    (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi) /
        (Real.exp ((2 : ℝ) * Real.pi * t) - 1) ≤
      (max |Real.log (1 : ℝ)|
          |Real.log ((3 * ‖w‖) / w.re)| + Real.pi) /
        (Real.exp (Real.pi * ‖w‖) - 1) := by
  let D : ℝ := max w.re |w.im - t|
  let A : ℝ := (3 * ‖w‖) / D
  let U : ℝ := (3 * ‖w‖) / w.re
  let E : ℝ := Real.exp ((2 : ℝ) * Real.pi * t) - 1
  let E₀ : ℝ := Real.exp (Real.pi * ‖w‖) - 1
  have hw_norm_pos : 0 < ‖w‖ :=
    Complex.norm_pos_of_re_pos hw_re_pos
  have ht_lower : ‖w‖ / 2 ≤ t :=
    ht_mem.1
  have ht_upper : t ≤ 2 * ‖w‖ :=
    ht_mem.2
  have hhalf_pos : 0 < ‖w‖ / 2 :=
    div_pos hw_norm_pos zero_lt_two
  have ht_pos : 0 < t :=
    lt_of_lt_of_le hhalf_pos ht_lower
  have ht_nonneg : 0 ≤ t :=
    le_of_lt ht_pos
  have hD_pos : 0 < D :=
    lt_of_lt_of_le hw_re_pos (le_max_left w.re |w.im - t|)
  have hD_lower : w.re ≤ D :=
    le_max_left w.re |w.im - t|
  have hnum_pos : 0 < 3 * ‖w‖ :=
    mul_pos Real.zero_lt_three hw_norm_pos
  have hU_pos : 0 < U :=
    div_pos hnum_pos hw_re_pos
  have hre_le_norm : w.re ≤ ‖w‖ := by
    calc
      w.re = |w.re| := Eq.symm (abs_of_pos hw_re_pos)
      _ ≤ ‖w‖ := Complex.abs_re_le_abs w
  have hre_le_three : w.re ≤ 3 * ‖w‖ := by
    calc
      w.re ≤ ‖w‖ := hre_le_norm
      _ ≤ 3 * ‖w‖ :=
        le_mul_of_one_le_left (le_of_lt hw_norm_pos) Real.one_le_three_real
  have hU_ge_one : (1 : ℝ) ≤ U := by
    exact (le_div_iff₀ hw_re_pos).2
      (calc
        (1 : ℝ) * w.re = w.re := one_mul w.re
        _ ≤ 3 * ‖w‖ := hre_le_three)
  have hD_upper : D ≤ 3 * ‖w‖ := by
    have him_le_three : |w.im - t| ≤ 3 * ‖w‖ := by
      calc
        |w.im - t| ≤ ‖w - (t : ℂ) * Complex.I‖ :=
          Complex.binetSecondFormula_arctan_tail_denominator_branchWall_distance_le
            w t
        _ ≤ ‖w‖ + ‖(t : ℂ) * Complex.I‖ := by
          calc
            ‖w - (t : ℂ) * Complex.I‖ =
                ‖w + -((t : ℂ) * Complex.I)‖ := by
              exact congrArg norm (sub_eq_add_neg w ((t : ℂ) * Complex.I))
            _ ≤ ‖w‖ + ‖-((t : ℂ) * Complex.I)‖ :=
              norm_add_le w (-((t : ℂ) * Complex.I))
            _ = ‖w‖ + ‖(t : ℂ) * Complex.I‖ := by
              exact congrArg (fun x : ℝ => ‖w‖ + x)
                (norm_neg ((t : ℂ) * Complex.I))
        _ = ‖w‖ + t := by
          have htI_norm : ‖(t : ℂ) * Complex.I‖ = t := by
            calc
              ‖(t : ℂ) * Complex.I‖ = |t| :=
                Complex.norm_real_mul_I t
              _ = t := abs_of_nonneg ht_nonneg
          exact congrArg (fun x : ℝ => ‖w‖ + x) htI_norm
        _ ≤ ‖w‖ + 2 * ‖w‖ :=
          add_le_add_left ht_upper ‖w‖
        _ = 3 * ‖w‖ :=
          Real.add_two_mul_eq_three_mul ‖w‖
    exact max_le hre_le_three him_le_three
  have hA_lower : (1 : ℝ) ≤ A := by
    exact (le_div_iff₀ hD_pos).2
      (calc
        (1 : ℝ) * D = D := one_mul D
        _ ≤ 3 * ‖w‖ := hD_upper)
  have hA_upper : A ≤ U := by
    exact div_le_div_of_nonneg_left (le_of_lt hnum_pos) hw_re_pos hD_lower
  have hlog_bound :
      |Real.log A| ≤
        max |Real.log (1 : ℝ)| |Real.log U| :=
    Complex.binetSecondFormula_branchWall_moving_ratio_abs_log_le_realPart_window
      hw_re_pos ht_nonneg ht_upper
  have hnum_bound :
      |Real.log A| + Real.pi ≤
        max |Real.log (1 : ℝ)| |Real.log U| + Real.pi :=
    Complex.binetSecondFormula_branchWall_moving_logNumerator_le_realPart_window
      hw_re_pos ht_nonneg ht_upper
  have hE0_pos : 0 < E₀ := by
    exact
      Complex.binetSecondFormula_branchWall_split_exp_denominator_pos
        hw_re_pos
  have hE_lower : E₀ ≤ E := by
    exact
      Complex.binetSecondFormula_branchWall_exp_denominator_lower
        hw_re_pos ht_lower
  have hnum_nonneg : 0 ≤ |Real.log A| + Real.pi :=
    add_nonneg (abs_nonneg (Real.log A)) Real.pi_nonneg
  exact
    Real.div_le_div_of_le_of_le
      hE0_pos hnum_nonneg hnum_bound hE_lower

/-- Quantitative bounded-window integral estimate for the branch-wall
logarithmic spike produced by the local-indentation majorant. -/
theorem Complex.binetSecondFormula_branchWall_logSpike_integral_le_boundedTailWindow
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∫ t : ℝ in Set.Icc (‖w‖ / 2) (2 * ‖w‖),
        (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi) /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) ≤
      ((max |Real.log (1 : ℝ)|
          |Real.log ((3 * ‖w‖) / w.re)| + Real.pi) /
        (Real.exp (Real.pi * ‖w‖) - 1)) *
        (volume (Set.Icc (‖w‖ / 2) (2 * ‖w‖))).toReal := by
  let S : Set ℝ := Set.Icc (‖w‖ / 2) (2 * ‖w‖)
  let F : ℝ → ℝ := fun t : ℝ =>
    (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi) /
      (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  let C : ℝ :=
    (max |Real.log (1 : ℝ)|
        |Real.log ((3 * ‖w‖) / w.re)| + Real.pi) /
      (Real.exp (Real.pi * ‖w‖) - 1)
  have hF_bound : ∀ t : ℝ, t ∈ S → ‖F t‖ ≤ C := by
    intro t ht
    have hle :
        F t ≤ C :=
      Complex.binetSecondFormula_branchWall_logSpike_pointwise_le_boundedTailWindow
        hw_re_pos ht
    have hw_norm_pos : 0 < ‖w‖ :=
      Complex.norm_pos_of_re_pos hw_re_pos
    have ht_lower : ‖w‖ / 2 ≤ t :=
      ht.1
    have hhalf_pos : 0 < ‖w‖ / 2 :=
      div_pos hw_norm_pos zero_lt_two
    have ht_pos : 0 < t :=
      lt_of_lt_of_le hhalf_pos ht_lower
    have hden_pos :
        0 < Real.exp ((2 : ℝ) * Real.pi * t) - 1 :=
      Real.binetSecondFormula_exp_denominator_pos ht_pos
    have hF_nonneg : 0 ≤ F t :=
      div_nonneg
        (add_nonneg
          (abs_nonneg
            (Real.log ((3 * ‖w‖) / max w.re |w.im - t|)))
          Real.pi_nonneg)
        (le_of_lt hden_pos)
    calc
      ‖F t‖ = |F t| := Real.norm_eq_abs (F t)
      _ = F t := abs_of_nonneg hF_nonneg
      _ ≤ C := hle
  have hnorm_integral :
      ‖∫ t : ℝ in S, F t‖ ≤ C * (volume S).toReal :=
    norm_setIntegral_le_of_norm_le_const'
      measure_Icc_lt_top measurableSet_Icc hF_bound
  calc
    ∫ t : ℝ in S, F t ≤ |∫ t : ℝ in S, F t| :=
      le_abs_self (∫ t : ℝ in S, F t)
    _ = ‖∫ t : ℝ in S, F t‖ :=
      Eq.symm (Real.norm_eq_abs (∫ t : ℝ in S, F t))
    _ ≤ C * (volume S).toReal :=
      hnorm_integral

/-- Any nonnegative numerator over the positive Binet tail denominator is
controlled by twice the same numerator over the pure exponential. -/
theorem Real.binetSecondFormula_nonneg_div_exp_denominator_le_two_mul_div_exp
    {N t : ℝ}
    (hN_nonneg : 0 ≤ N)
    (ht : t ∈ Set.Ioi (1 : ℝ)) :
    N / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) ≤
      (2 * N) / Real.exp ((2 : ℝ) * Real.pi * t) := by
  let E : ℝ := Real.exp ((2 : ℝ) * Real.pi * t)
  let D : ℝ := Real.exp ((2 : ℝ) * Real.pi * t) - 1
  have hE_pos : 0 < E :=
    Real.exp_pos ((2 : ℝ) * Real.pi * t)
  have hE_half_pos : 0 < E / 2 :=
    div_pos hE_pos two_pos
  have hD_lower : E / 2 ≤ D :=
    Real.binetSecondFormula_kernel_majorant_tail_denominator_lower ht
  have hdiv :
      N / D ≤ N / (E / 2) :=
    div_le_div_of_nonneg_left hN_nonneg hE_half_pos hD_lower
  have hrewrite :
      N / (E / 2) = (2 * N) / E := by
    calc
      N / (E / 2) = N * 2 / E := by
        exact div_div_eq_mul_div N E 2
      _ = (N * 2) / E := rfl
      _ = (2 * N) / E := by
        exact congrArg (fun x : ℝ => x / E) (mul_comm N 2)
  exact le_trans hdiv (le_of_eq hrewrite)

/-- On the C5 bounded branch-wall window, the exponential Binet denominator
turns the logarithmic spike into an explicitly exponentially weighted spike.

This is the first real-variable reduction needed for the local-indentation
absorption: it replaces the Binet denominator by a pure exponential weight. -/
theorem Complex.binetSecondFormula_branchWall_logSpike_denominator_le_expWeighted_on_boundedTailWindow
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hw_large : 2 ≤ ‖w‖)
    {t : ℝ}
    (ht_mem : t ∈ Set.Ioc (‖w‖ / 2) (2 * ‖w‖)) :
    (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi) /
        (Real.exp ((2 : ℝ) * Real.pi * t) - 1) ≤
      (2 *
        (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi)) /
        Real.exp ((2 : ℝ) * Real.pi * t) := by
  let N : ℝ :=
    |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi
  have hhalf_ge_one : (1 : ℝ) ≤ ‖w‖ / 2 := by
    exact (le_div_iff₀ zero_lt_two).2
      (calc
        (1 : ℝ) * 2 = 2 := one_mul 2
        _ ≤ ‖w‖ := hw_large)
  have ht_gt_one : t ∈ Set.Ioi (1 : ℝ) :=
    lt_of_le_of_lt hhalf_ge_one ht_mem.1
  have hN_nonneg : 0 ≤ N :=
    add_nonneg
      (abs_nonneg
        (Real.log ((3 * ‖w‖) / max w.re |w.im - t|)))
      Real.pi_nonneg
  exact
    Real.binetSecondFormula_nonneg_div_exp_denominator_le_two_mul_div_exp
      hN_nonneg ht_gt_one

/-- Pointwise replacement of the moving branch-wall logarithmic numerator by
the fixed real-part logarithmic numerator under the same exponential weight. -/
theorem Complex.binetSecondFormula_branchWall_expWeighted_moving_le_realPart_window
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    {t : ℝ}
    (ht_mem : t ∈ Set.Ioc (‖w‖ / 2) (2 * ‖w‖)) :
    (2 *
        (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi)) /
        Real.exp ((2 : ℝ) * Real.pi * t) ≤
      (2 *
        (max |Real.log (1 : ℝ)|
          |Real.log ((3 * ‖w‖) / w.re)| + Real.pi)) /
        Real.exp ((2 : ℝ) * Real.pi * t) := by
  have ht_nonneg : 0 ≤ t := by
    have hcut_nonneg : 0 ≤ ‖w‖ / 2 :=
      div_nonneg (norm_nonneg w) Real.zero_le_two_real
    exact le_trans hcut_nonneg (le_of_lt ht_mem.1)
  have hnum :
      |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi ≤
        max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| +
          Real.pi :=
    Complex.binetSecondFormula_branchWall_moving_logNumerator_le_realPart_window
      hw_re_pos ht_nonneg ht_mem.2
  have htwo_num :
      2 *
          (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi) ≤
        2 *
          (max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| +
            Real.pi) :=
    mul_le_mul_of_nonneg_left hnum Real.zero_le_two_real
  exact
    div_le_div_of_nonneg_right
      htwo_num
      (le_of_lt (Real.exp_pos ((2 : ℝ) * Real.pi * t)))

/-- On the bounded branch-wall window, the pure exponential weight can be
pulled down to the left endpoint scale while keeping the moving logarithmic
spike intact.

This is the pointwise step that avoids replacing the moving singularity by
the fixed real-part envelope. -/
theorem Complex.binetSecondFormula_branchWall_expWeighted_moving_le_cutoffExp
    {w : ℂ}
    {t : ℝ}
    (ht_mem : t ∈ Set.Ioc (‖w‖ / 2) (2 * ‖w‖)) :
    (2 *
        (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi)) /
        Real.exp ((2 : ℝ) * Real.pi * t) ≤
      (2 *
        (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi)) *
        Real.exp (-Real.pi * ‖w‖) := by
  let L : ℝ :=
    |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi
  let K : ℝ := (2 : ℝ) * L
  have hL_nonneg : 0 ≤ L :=
    add_nonneg
      (abs_nonneg
        (Real.log ((3 * ‖w‖) / max w.re |w.im - t|)))
      Real.pi_nonneg
  have hK_nonneg : 0 ≤ K :=
    mul_nonneg Real.zero_le_two hL_nonneg
  have ht_lower : ‖w‖ / 2 ≤ t :=
    le_of_lt ht_mem.1
  have hcoeff_nonneg : 0 ≤ (2 : ℝ) * Real.pi :=
    mul_nonneg Real.zero_le_two Real.pi_nonneg
  have hmul_le :
      ((2 : ℝ) * Real.pi) * (‖w‖ / 2) ≤
        ((2 : ℝ) * Real.pi) * t :=
    mul_le_mul_of_nonneg_left ht_lower hcoeff_nonneg
  have hleft_scale :
      ((2 : ℝ) * Real.pi) * (‖w‖ / 2) = Real.pi * ‖w‖ := by
    calc
      ((2 : ℝ) * Real.pi) * (‖w‖ / 2) =
          (((2 : ℝ) * Real.pi) * ‖w‖) / 2 := by
        exact mul_div_assoc ((2 : ℝ) * Real.pi) ‖w‖ 2
      _ = ((Real.pi * ‖w‖) * 2) / 2 := by
        exact
          congrArg (fun x : ℝ => x / 2)
            (calc
              ((2 : ℝ) * Real.pi) * ‖w‖ =
                  2 * (Real.pi * ‖w‖) := by
                exact mul_assoc 2 Real.pi ‖w‖
              _ = (Real.pi * ‖w‖) * 2 := by
                exact mul_comm 2 (Real.pi * ‖w‖))
      _ = Real.pi * ‖w‖ := by
        exact mul_div_cancel_right₀ (Real.pi * ‖w‖) two_ne_zero
  have hneg_le :
      -(((2 : ℝ) * Real.pi) * t) ≤ -Real.pi * ‖w‖ := by
    have hscale_le :
        Real.pi * ‖w‖ ≤ ((2 : ℝ) * Real.pi) * t :=
      Eq.subst
        (motive := fun x : ℝ => x ≤ ((2 : ℝ) * Real.pi) * t)
        hleft_scale
        hmul_le
    have hneg :
        -(((2 : ℝ) * Real.pi) * t) ≤ -(Real.pi * ‖w‖) :=
      neg_le_neg hscale_le
    exact
      Eq.subst
        (motive := fun x : ℝ => -(((2 : ℝ) * Real.pi) * t) ≤ x)
        (neg_mul Real.pi ‖w‖)
        hneg
  have hexp_le :
      Real.exp (-(((2 : ℝ) * Real.pi) * t)) ≤
        Real.exp (-Real.pi * ‖w‖) :=
    Real.exp_le_exp.mpr hneg_le
  have hweighted_le :
      K * Real.exp (-(((2 : ℝ) * Real.pi) * t)) ≤
        K * Real.exp (-Real.pi * ‖w‖) :=
    mul_le_mul_of_nonneg_left hexp_le hK_nonneg
  have hleft_eq :
      (2 * L) / Real.exp ((2 : ℝ) * Real.pi * t) =
        K * Real.exp (-(((2 : ℝ) * Real.pi) * t)) := by
    calc
      (2 * L) / Real.exp ((2 : ℝ) * Real.pi * t) =
          K * (Real.exp ((2 : ℝ) * Real.pi * t))⁻¹ := by
        rfl
      _ = K * Real.exp (-(((2 : ℝ) * Real.pi) * t)) := by
        exact congrArg (fun x : ℝ => K * x)
          (Real.exp_neg (((2 : ℝ) * Real.pi) * t)).symm
  exact
    Eq.subst
      (motive := fun x : ℝ =>
        x ≤
          (2 *
            (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi)) *
            Real.exp (-Real.pi * ‖w‖))
      hleft_eq.symm
      hweighted_le

/-- Integrated cutoff-exponential extraction for the moving branch-wall
logarithmic spike.

This keeps the logarithmic singularity in its moving, locally integrable form
and extracts only the uniform exponential scale from the bounded tail window. -/
theorem Complex.binetSecondFormula_branchWall_expWeighted_integral_le_cutoffExp_integral_Ioc
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (2 *
          (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi)) /
          Real.exp ((2 : ℝ) * Real.pi * t) ≤
      ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (2 *
          (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi)) *
          Real.exp (-Real.pi * ‖w‖) := by
  let S : Set ℝ := Set.Ioc (‖w‖ / 2) (2 * ‖w‖)
  let G : ℝ → ℝ := fun t : ℝ =>
    (2 *
      (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi)) /
      Real.exp ((2 : ℝ) * Real.pi * t)
  let H : ℝ → ℝ := fun t : ℝ =>
    (2 *
      (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi)) *
      Real.exp (-Real.pi * ‖w‖)
  have hG_integrable : IntegrableOn G S := by
    let Scc : Set ℝ := Set.Icc (‖w‖ / 2) (2 * ‖w‖)
    let B : ℝ → ℝ := fun t : ℝ => max w.re |w.im - t|
    let A : ℝ → ℝ := fun t : ℝ => (3 * ‖w‖) / B t
    let Gcc : ℝ → ℝ := fun t : ℝ =>
      (2 * (|Real.log (A t)| + Real.pi)) /
        Real.exp ((2 : ℝ) * Real.pi * t)
    have hw_norm_pos : 0 < ‖w‖ :=
      Complex.norm_pos_of_re_pos hw_re_pos
    have hB_pos : ∀ t : ℝ, 0 < B t := by
      intro t
      exact lt_of_lt_of_le hw_re_pos (le_max_left w.re |w.im - t|)
    have hA_pos : ∀ t : ℝ, 0 < A t := by
      intro t
      exact div_pos (mul_pos Real.zero_lt_three hw_norm_pos) (hB_pos t)
    have hdist_cont : Continuous fun t : ℝ => |w.im - t| :=
      (continuous_const.sub continuous_id).abs
    have hB_cont : Continuous B :=
      continuous_const.max hdist_cont
    have hA_cont : Continuous A :=
      continuous_const.div hB_cont (fun t => (hB_pos t).ne')
    have hlog_contOn :
        ContinuousOn (fun t : ℝ => Real.log (A t)) Scc :=
      (hA_cont.continuousOn).log (fun t _ht => (hA_pos t).ne')
    have hnum_contOn :
        ContinuousOn (fun t : ℝ => 2 * (|Real.log (A t)| + Real.pi)) Scc :=
      continuousOn_const.mul (hlog_contOn.abs.add continuousOn_const)
    have hlinear_cont : Continuous fun t : ℝ => (2 : ℝ) * Real.pi * t :=
      (continuous_const.mul continuous_const).mul continuous_id
    have hden_cont : Continuous fun t : ℝ =>
        Real.exp ((2 : ℝ) * Real.pi * t) :=
      Real.continuous_exp.comp hlinear_cont
    have hden_ne : ∀ t : ℝ, t ∈ Scc →
        Real.exp ((2 : ℝ) * Real.pi * t) ≠ 0 := by
      intro t _ht
      exact (Real.exp_pos ((2 : ℝ) * Real.pi * t)).ne'
    have hGcc_contOn : ContinuousOn Gcc Scc :=
      hnum_contOn.div hden_cont.continuousOn hden_ne
    have hGcc_integrable_Icc : IntegrableOn Gcc Scc :=
      hGcc_contOn.integrableOn_Icc
    exact hGcc_integrable_Icc.mono_set Ioc_subset_Icc_self
  have hH_integrable : IntegrableOn H S := by
    let Scc : Set ℝ := Set.Icc (‖w‖ / 2) (2 * ‖w‖)
    let B : ℝ → ℝ := fun t : ℝ => max w.re |w.im - t|
    let A : ℝ → ℝ := fun t : ℝ => (3 * ‖w‖) / B t
    let Hcc : ℝ → ℝ := fun t : ℝ =>
      (2 * (|Real.log (A t)| + Real.pi)) *
        Real.exp (-Real.pi * ‖w‖)
    have hw_norm_pos : 0 < ‖w‖ :=
      Complex.norm_pos_of_re_pos hw_re_pos
    have hB_pos : ∀ t : ℝ, 0 < B t := by
      intro t
      exact lt_of_lt_of_le hw_re_pos (le_max_left w.re |w.im - t|)
    have hA_pos : ∀ t : ℝ, 0 < A t := by
      intro t
      exact div_pos (mul_pos Real.zero_lt_three hw_norm_pos) (hB_pos t)
    have hdist_cont : Continuous fun t : ℝ => |w.im - t| :=
      (continuous_const.sub continuous_id).abs
    have hB_cont : Continuous B :=
      continuous_const.max hdist_cont
    have hA_cont : Continuous A :=
      continuous_const.div hB_cont (fun t => (hB_pos t).ne')
    have hlog_contOn :
        ContinuousOn (fun t : ℝ => Real.log (A t)) Scc :=
      (hA_cont.continuousOn).log (fun t _ht => (hA_pos t).ne')
    have hnum_contOn :
        ContinuousOn (fun t : ℝ => 2 * (|Real.log (A t)| + Real.pi)) Scc :=
      continuousOn_const.mul (hlog_contOn.abs.add continuousOn_const)
    have hHcc_contOn : ContinuousOn Hcc Scc :=
      hnum_contOn.mul continuousOn_const
    have hHcc_integrable_Icc : IntegrableOn Hcc Scc :=
      hHcc_contOn.integrableOn_Icc
    exact hHcc_integrable_Icc.mono_set Ioc_subset_Icc_self
  have hpoint :
      ∀ᵐ t ∂volume.restrict S, G t ≤ H t :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun t ht =>
        Complex.binetSecondFormula_branchWall_expWeighted_moving_le_cutoffExp
          (w := w) ht)
  exact
    setIntegral_mono_ae_restrict hG_integrable hH_integrable hpoint

/-- Integrated denominator replacement for the branch-wall logarithmic spike
on the bounded local-indentation window.

The theorem isolates the exact remaining real-variable absorption problem:
the right hand side is an exponentially weighted logarithmic spike over
`Ioc (‖w‖ / 2) (2‖w‖)`. -/
theorem Complex.binetSecondFormula_branchWall_logSpike_integral_le_expWeighted_boundedTailWindow_Ioc
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hw_large : 2 ≤ ‖w‖) :
    ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi) /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) ≤
      ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (2 *
          (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi)) /
          Real.exp ((2 : ℝ) * Real.pi * t) := by
  let S : Set ℝ := Set.Ioc (‖w‖ / 2) (2 * ‖w‖)
  let F : ℝ → ℝ := fun t : ℝ =>
    (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi) /
      (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  let G : ℝ → ℝ := fun t : ℝ =>
    (2 *
      (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi)) /
      Real.exp ((2 : ℝ) * Real.pi * t)
  have hF_integrable :
      IntegrableOn F S :=
    (Complex.binetSecondFormula_branchWall_logSpike_integrableOn_boundedTailWindow
      (w := w) hw_re_pos).mono_set Ioc_subset_Icc_self
  have hG_integrable : IntegrableOn G S := by
    let Scc : Set ℝ := Set.Icc (‖w‖ / 2) (2 * ‖w‖)
    let B : ℝ → ℝ := fun t : ℝ => max w.re |w.im - t|
    let A : ℝ → ℝ := fun t : ℝ => (3 * ‖w‖) / B t
    let H : ℝ → ℝ := fun t : ℝ =>
      (2 * (|Real.log (A t)| + Real.pi)) /
        Real.exp ((2 : ℝ) * Real.pi * t)
    have hw_norm_pos : 0 < ‖w‖ :=
      Complex.norm_pos_of_re_pos hw_re_pos
    have hB_pos : ∀ t : ℝ, 0 < B t := by
      intro t
      exact lt_of_lt_of_le hw_re_pos (le_max_left w.re |w.im - t|)
    have hA_pos : ∀ t : ℝ, 0 < A t := by
      intro t
      exact div_pos (mul_pos Real.zero_lt_three hw_norm_pos) (hB_pos t)
    have hdist_cont : Continuous fun t : ℝ => |w.im - t| :=
      (continuous_const.sub continuous_id).abs
    have hB_cont : Continuous B :=
      continuous_const.max hdist_cont
    have hA_cont : Continuous A :=
      continuous_const.div hB_cont (fun t => (hB_pos t).ne')
    have hlog_contOn :
        ContinuousOn (fun t : ℝ => Real.log (A t)) Scc :=
      (hA_cont.continuousOn).log (fun t ht => (hA_pos t).ne')
    have hnum_contOn :
        ContinuousOn (fun t : ℝ => 2 * (|Real.log (A t)| + Real.pi)) Scc :=
      continuousOn_const.mul (hlog_contOn.abs.add continuousOn_const)
    have hlinear_cont : Continuous fun t : ℝ => (2 : ℝ) * Real.pi * t :=
      (continuous_const.mul continuous_const).mul continuous_id
    have hden_cont : Continuous fun t : ℝ =>
        Real.exp ((2 : ℝ) * Real.pi * t) :=
      Real.continuous_exp.comp hlinear_cont
    have hden_ne : ∀ t : ℝ, t ∈ Scc →
        Real.exp ((2 : ℝ) * Real.pi * t) ≠ 0 := by
      intro t ht
      exact (Real.exp_pos ((2 : ℝ) * Real.pi * t)).ne'
    have hH_contOn : ContinuousOn H Scc :=
      hnum_contOn.div hden_cont.continuousOn hden_ne
    have hH_integrable_Icc : IntegrableOn H Scc :=
      hH_contOn.integrableOn_Icc
    exact hH_integrable_Icc.mono_set Ioc_subset_Icc_self
  have hpoint :
      ∀ᵐ t ∂volume.restrict S, F t ≤ G t :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun t ht =>
        Complex.binetSecondFormula_branchWall_logSpike_denominator_le_expWeighted_on_boundedTailWindow
          (w := w) hw_re_pos hw_large ht)
  exact
    setIntegral_mono_ae_restrict hF_integrable hG_integrable hpoint

/-- The branch-wall logarithmic spike with the Binet denominator is controlled
by the moving singular integral times the left-endpoint exponential scale.

This combines the denominator replacement with cutoff-exponential extraction
without replacing the moving branch-wall singularity by a fixed real-part
envelope. -/
theorem Complex.binetSecondFormula_branchWall_logSpike_integral_le_cutoffExp_movingIntegral_Ioc
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hw_large : 2 ≤ ‖w‖) :
    ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi) /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) ≤
      ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (2 *
          (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi)) *
          Real.exp (-Real.pi * ‖w‖) := by
  exact
    le_trans
      (Complex.binetSecondFormula_branchWall_logSpike_integral_le_expWeighted_boundedTailWindow_Ioc
        hw_re_pos hw_large)
      (Complex.binetSecondFormula_branchWall_expWeighted_integral_le_cutoffExp_integral_Ioc
        hw_re_pos)

/-- The extracted cutoff exponential is a constant factor in the moving
branch-wall spike integral. -/
theorem Complex.binetSecondFormula_branchWall_cutoffExp_movingIntegral_eq_movingIntegral_mul_exp_Ioc
    (w : ℂ) :
    ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (2 *
          (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi)) *
          Real.exp (-Real.pi * ‖w‖) =
      (∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        2 *
          (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi)) *
          Real.exp (-Real.pi * ‖w‖) := by
  exact
    integral_mul_right
      (Real.exp (-Real.pi * ‖w‖))
      (fun t : ℝ =>
        2 *
          (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi))

/-- The branch-wall logarithmic spike with Binet denominator is bounded by the
unweighted moving-spike integral times the cutoff exponential.

This is the reusable moving-singularity form of the bounded-window estimate;
no fixed `w.re` logarithmic envelope appears. -/
theorem Complex.binetSecondFormula_branchWall_logSpike_integral_le_movingIntegral_mul_exp_Ioc
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hw_large : 2 ≤ ‖w‖) :
    ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi) /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) ≤
      (∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        2 *
          (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi)) *
          Real.exp (-Real.pi * ‖w‖) := by
  have hcutoff :
      ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
          (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi) /
            (Real.exp ((2 : ℝ) * Real.pi * t) - 1) ≤
        ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
          (2 *
            (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi)) *
            Real.exp (-Real.pi * ‖w‖) :=
    Complex.binetSecondFormula_branchWall_logSpike_integral_le_cutoffExp_movingIntegral_Ioc
      hw_re_pos hw_large
  have hfactor :
      ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
          (2 *
            (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi)) *
            Real.exp (-Real.pi * ‖w‖) =
        (∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
          2 *
            (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi)) *
            Real.exp (-Real.pi * ‖w‖) :=
    Complex.binetSecondFormula_branchWall_cutoffExp_movingIntegral_eq_movingIntegral_mul_exp_Ioc
      w
  exact
    Eq.subst
      (motive := fun x : ℝ =>
        ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
            (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi) /
              (Real.exp ((2 : ℝ) * Real.pi * t) - 1) ≤ x)
      hfactor
      hcutoff

/-- Integrated replacement of the moving branch-wall logarithmic numerator by
the fixed real-part logarithmic numerator under the exponential weight. -/
theorem Complex.binetSecondFormula_branchWall_expWeighted_integral_le_realPart_window_Ioc
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (2 *
          (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi)) /
          Real.exp ((2 : ℝ) * Real.pi * t) ≤
      ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (2 *
          (max |Real.log (1 : ℝ)|
            |Real.log ((3 * ‖w‖) / w.re)| + Real.pi)) /
          Real.exp ((2 : ℝ) * Real.pi * t) := by
  let S : Set ℝ := Set.Ioc (‖w‖ / 2) (2 * ‖w‖)
  let G : ℝ → ℝ := fun t : ℝ =>
    (2 *
      (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi)) /
      Real.exp ((2 : ℝ) * Real.pi * t)
  let H : ℝ → ℝ := fun t : ℝ =>
    (2 *
      (max |Real.log (1 : ℝ)|
        |Real.log ((3 * ‖w‖) / w.re)| + Real.pi)) /
      Real.exp ((2 : ℝ) * Real.pi * t)
  have hG_integrable : IntegrableOn G S := by
    let Scc : Set ℝ := Set.Icc (‖w‖ / 2) (2 * ‖w‖)
    let B : ℝ → ℝ := fun t : ℝ => max w.re |w.im - t|
    let A : ℝ → ℝ := fun t : ℝ => (3 * ‖w‖) / B t
    let Gcc : ℝ → ℝ := fun t : ℝ =>
      (2 * (|Real.log (A t)| + Real.pi)) /
        Real.exp ((2 : ℝ) * Real.pi * t)
    have hw_norm_pos : 0 < ‖w‖ :=
      Complex.norm_pos_of_re_pos hw_re_pos
    have hB_pos : ∀ t : ℝ, 0 < B t := by
      intro t
      exact
        lt_of_lt_of_le
          hw_re_pos
          (Complex.binetSecondFormula_branchWall_distance_re_le w t)
    have hA_pos : ∀ t : ℝ, 0 < A t := by
      intro t
      exact div_pos (mul_pos Real.zero_lt_three hw_norm_pos) (hB_pos t)
    have hdist_cont : Continuous fun t : ℝ => |w.im - t| :=
      (continuous_const.sub continuous_id).abs
    have hB_cont : Continuous B :=
      continuous_const.max hdist_cont
    have hA_cont : Continuous A :=
      continuous_const.div hB_cont (fun t => (hB_pos t).ne')
    have hlog_contOn :
        ContinuousOn (fun t : ℝ => Real.log (A t)) Scc :=
      (hA_cont.continuousOn).log (fun t ht => (hA_pos t).ne')
    have hnum_contOn :
        ContinuousOn (fun t : ℝ => 2 * (|Real.log (A t)| + Real.pi)) Scc :=
      continuousOn_const.mul (hlog_contOn.abs.add continuousOn_const)
    have hlinear_cont : Continuous fun t : ℝ => (2 : ℝ) * Real.pi * t :=
      (continuous_const.mul continuous_const).mul continuous_id
    have hden_cont : Continuous fun t : ℝ =>
        Real.exp ((2 : ℝ) * Real.pi * t) :=
      Real.continuous_exp.comp hlinear_cont
    have hden_ne : ∀ t : ℝ, t ∈ Scc →
        Real.exp ((2 : ℝ) * Real.pi * t) ≠ 0 := by
      intro t ht
      exact (Real.exp_pos ((2 : ℝ) * Real.pi * t)).ne'
    have hGcc_contOn : ContinuousOn Gcc Scc :=
      hnum_contOn.div hden_cont.continuousOn hden_ne
    have hGcc_integrable_Icc : IntegrableOn Gcc Scc :=
      hGcc_contOn.integrableOn_Icc
    exact hGcc_integrable_Icc.mono_set Ioc_subset_Icc_self
  have hH_integrable : IntegrableOn H S := by
    let Scc : Set ℝ := Set.Icc (‖w‖ / 2) (2 * ‖w‖)
    let K : ℝ := 2 *
      (max |Real.log (1 : ℝ)|
        |Real.log ((3 * ‖w‖) / w.re)| + Real.pi)
    let Hcc : ℝ → ℝ := fun t : ℝ =>
      K / Real.exp ((2 : ℝ) * Real.pi * t)
    have hlinear_cont : Continuous fun t : ℝ => (2 : ℝ) * Real.pi * t :=
      (continuous_const.mul continuous_const).mul continuous_id
    have hden_cont : Continuous fun t : ℝ =>
        Real.exp ((2 : ℝ) * Real.pi * t) :=
      Real.continuous_exp.comp hlinear_cont
    have hden_ne : ∀ t : ℝ, t ∈ Scc →
        Real.exp ((2 : ℝ) * Real.pi * t) ≠ 0 := by
      intro t ht
      exact (Real.exp_pos ((2 : ℝ) * Real.pi * t)).ne'
    have hHcc_contOn : ContinuousOn Hcc Scc :=
      continuousOn_const.div hden_cont.continuousOn hden_ne
    have hHcc_integrable_Icc : IntegrableOn Hcc Scc :=
      hHcc_contOn.integrableOn_Icc
    exact hHcc_integrable_Icc.mono_set Ioc_subset_Icc_self
  have hpoint :
      ∀ᵐ t ∂volume.restrict S, G t ≤ H t :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun t ht =>
        Complex.binetSecondFormula_branchWall_expWeighted_moving_le_realPart_window
          hw_re_pos ht)
  exact
    setIntegral_mono_ae_restrict hG_integrable hH_integrable hpoint

/-- The bounded branch-wall logarithmic spike is controlled by the fixed
real-part logarithmic numerator under the pure exponential weight. -/
theorem Complex.binetSecondFormula_branchWall_logSpike_integral_le_realPart_expWeighted_Ioc
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hw_large : 2 ≤ ‖w‖) :
    ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi) /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) ≤
      ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (2 *
          (max |Real.log (1 : ℝ)|
            |Real.log ((3 * ‖w‖) / w.re)| + Real.pi)) /
          Real.exp ((2 : ℝ) * Real.pi * t) := by
  exact
    le_trans
      (Complex.binetSecondFormula_branchWall_logSpike_integral_le_expWeighted_boundedTailWindow_Ioc
        hw_re_pos hw_large)
      (Complex.binetSecondFormula_branchWall_expWeighted_integral_le_realPart_window_Ioc
        hw_re_pos)

/-- The fixed-window branch-wall exponential integral has the expected
`exp (-π‖w‖)` scale. -/
theorem Complex.binetSecondFormula_branchWall_realPart_expWeighted_integral_le_expScale_Ioc
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (2 *
          (max |Real.log (1 : ℝ)|
            |Real.log ((3 * ‖w‖) / w.re)| + Real.pi)) /
          Real.exp ((2 : ℝ) * Real.pi * t) ≤
      (2 *
        (max |Real.log (1 : ℝ)|
          |Real.log ((3 * ‖w‖) / w.re)| + Real.pi)) *
        Real.exp (-Real.pi * ‖w‖) := by
  let N : ℝ := ‖w‖
  let K : ℝ :=
    2 *
      (max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| +
        Real.pi)
  let F : ℝ → ℝ := fun t : ℝ =>
    Real.exp (-((2 : ℝ) * Real.pi) * t)
  have hK_nonneg : 0 ≤ K := by
    have hinside_nonneg :
        0 ≤
          max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| +
            Real.pi :=
      add_nonneg
        (le_max_of_le_left (abs_nonneg (Real.log (1 : ℝ))))
        Real.pi_nonneg
    exact mul_nonneg Real.zero_le_two hinside_nonneg
  have htail_integrable :
      IntegrableOn F (Set.Ioi (N / 2)) := by
    have hcoeff_pos : 0 < (2 : ℝ) * Real.pi :=
      mul_pos two_pos Real.pi_pos
    exact exp_neg_integrableOn_Ioi (N / 2) hcoeff_pos
  have htail_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioi (N / 2))] F :=
    Filter.Eventually.of_forall
      (fun t => le_of_lt (Real.exp_pos (-((2 : ℝ) * Real.pi) * t)))
  have hsubset :
      Set.Ioc (N / 2) (2 * N) ≤ᵐ[volume] Set.Ioi (N / 2) :=
    Filter.Eventually.of_forall
      (fun t ht => ht.1)
  have hmono :
      ∫ t : ℝ in Set.Ioc (N / 2) (2 * N), F t ≤
        ∫ t : ℝ in Set.Ioi (N / 2), F t :=
    setIntegral_mono_set htail_integrable htail_nonneg hsubset
  have hscaled_mono :
      K * (∫ t : ℝ in Set.Ioc (N / 2) (2 * N), F t) ≤
        K * (∫ t : ℝ in Set.Ioi (N / 2), F t) :=
    mul_le_mul_of_nonneg_left hmono hK_nonneg
  have htail_bound :
      ∫ t : ℝ in Set.Ioi (N / 2), F t ≤
        Real.exp (-((2 : ℝ) * Real.pi) * (N / 2)) :=
    Real.exp_neg_two_pi_tail_integral_le_exp (N / 2)
  have hexponent :
      -((2 : ℝ) * Real.pi) * (N / 2) = -Real.pi * ‖w‖ := by
    calc
      -((2 : ℝ) * Real.pi) * (N / 2) =
          -(((2 : ℝ) * Real.pi) * (N / 2)) := by
        exact neg_mul ((2 : ℝ) * Real.pi) (N / 2)
      _ = -(Real.pi * ‖w‖) := by
        have hinside :
            ((2 : ℝ) * Real.pi) * (N / 2) =
              Real.pi * ‖w‖ := by
          calc
            ((2 : ℝ) * Real.pi) * (N / 2) =
                ((2 : ℝ) * Real.pi) * (‖w‖ / 2) := by
              rfl
            _ = (((2 : ℝ) * Real.pi) * ‖w‖) / 2 := by
              exact mul_div_assoc ((2 : ℝ) * Real.pi) ‖w‖ 2
            _ = ((Real.pi * ‖w‖) * 2) / 2 := by
              exact
                congrArg (fun x : ℝ => x / 2)
                  (calc
                    ((2 : ℝ) * Real.pi) * ‖w‖ =
                        2 * (Real.pi * ‖w‖) := by
                      exact mul_assoc 2 Real.pi ‖w‖
                    _ = (Real.pi * ‖w‖) * 2 := by
                      exact mul_comm 2 (Real.pi * ‖w‖))
            _ = Real.pi * ‖w‖ := by
              exact mul_div_cancel_right₀ (Real.pi * ‖w‖) two_ne_zero
        exact congrArg Neg.neg hinside
      _ = -Real.pi * ‖w‖ := by
        exact (neg_mul Real.pi ‖w‖).symm
  have htail_scale :
      K * (∫ t : ℝ in Set.Ioi (N / 2), F t) ≤
        K * Real.exp (-Real.pi * ‖w‖) := by
    exact
      mul_le_mul_of_nonneg_left
        (Eq.subst
          (motive := fun x : ℝ =>
            ∫ t : ℝ in Set.Ioi (N / 2), F t ≤ Real.exp x)
          hexponent
          htail_bound)
        hK_nonneg
  have hintegrand_eq :
      ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
          (2 *
            (max |Real.log (1 : ℝ)|
              |Real.log ((3 * ‖w‖) / w.re)| + Real.pi)) /
            Real.exp ((2 : ℝ) * Real.pi * t) =
        K * ∫ t : ℝ in Set.Ioc (N / 2) (2 * N), F t := by
    calc
      ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
          (2 *
            (max |Real.log (1 : ℝ)|
              |Real.log ((3 * ‖w‖) / w.re)| + Real.pi)) /
            Real.exp ((2 : ℝ) * Real.pi * t) =
          ∫ t : ℝ in Set.Ioc (N / 2) (2 * N),
            K * F t := by
        exact
          setIntegral_congr_fun measurableSet_Ioc
            (fun t _ht =>
              calc
                (2 *
                    (max |Real.log (1 : ℝ)|
                      |Real.log ((3 * ‖w‖) / w.re)| + Real.pi)) /
                    Real.exp ((2 : ℝ) * Real.pi * t) =
                    K * (Real.exp ((2 : ℝ) * Real.pi * t))⁻¹ := by
                  rfl
                _ = K * Real.exp (-((2 : ℝ) * Real.pi * t)) := by
                  exact congrArg (fun x : ℝ => K * x)
                    (Real.exp_neg ((2 : ℝ) * Real.pi * t)).symm
                _ = K * F t := by
                  exact congrArg (fun x : ℝ => K * Real.exp x)
                    (neg_mul ((2 : ℝ) * Real.pi) t))
      _ = K * ∫ t : ℝ in Set.Ioc (N / 2) (2 * N), F t := by
        exact integral_mul_left K F
  exact
    Eq.subst
      (motive := fun x : ℝ =>
        x ≤
          (2 *
            (max |Real.log (1 : ℝ)|
              |Real.log ((3 * ‖w‖) / w.re)| + Real.pi)) *
            Real.exp (-Real.pi * ‖w‖))
      hintegrand_eq.symm
      (le_trans hscaled_mono htail_scale)

/-- The bounded branch-wall logarithmic spike has the explicit exponential
scale supplied by the lower split point. -/
theorem Complex.binetSecondFormula_branchWall_logSpike_integral_le_expScale_Ioc
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hw_large : 2 ≤ ‖w‖) :
    ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (|Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi) /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) ≤
      (2 *
        (max |Real.log (1 : ℝ)|
          |Real.log ((3 * ‖w‖) / w.re)| + Real.pi)) *
        Real.exp (-Real.pi * ‖w‖) := by
  exact
    le_trans
      (Complex.binetSecondFormula_branchWall_logSpike_integral_le_realPart_expWeighted_Ioc
        hw_re_pos hw_large)
      (Complex.binetSecondFormula_branchWall_realPart_expWeighted_integral_le_expScale_Ioc
        hw_re_pos)

/-- The full moving branch-wall logarithmic numerator is bounded by the sum of
the two fixed logarithmic windows. -/
theorem Complex.binetSecondFormula_branchWall_fullLogNumerator_le_fixedWindowSum
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    {t : ℝ}
    (ht_nonneg : 0 ≤ t)
    (ht_le : t ≤ 2 * ‖w‖) :
    max |Real.log (w.re / (3 * ‖w‖))|
        |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi ≤
      |Real.log (w.re / (3 * ‖w‖))| +
        max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| +
        Real.pi := by
  have hmoving :
      |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| ≤
        max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| :=
    Complex.binetSecondFormula_branchWall_moving_ratio_abs_log_le_realPart_window
      hw_re_pos ht_nonneg ht_le
  have hmax :
      max |Real.log (w.re / (3 * ‖w‖))|
          |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| ≤
        |Real.log (w.re / (3 * ‖w‖))| +
          max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| := by
    have hfixed_nonneg :
        0 ≤ max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| :=
      le_max_of_le_left (abs_nonneg (Real.log (1 : ℝ)))
    have hleft :
        |Real.log (w.re / (3 * ‖w‖))| ≤
          |Real.log (w.re / (3 * ‖w‖))| +
            max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| :=
      le_add_of_nonneg_right hfixed_nonneg
    have hright :
        |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| ≤
          |Real.log (w.re / (3 * ‖w‖))| +
            max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| :=
      le_trans hmoving
        (le_add_of_nonneg_left (abs_nonneg (Real.log (w.re / (3 * ‖w‖)))))
    exact
      max_le hleft hright
  exact add_le_add_right hmax Real.pi

/-- Pointwise weighted form of the full branch-wall logarithmic numerator
bound. -/
theorem Complex.binetSecondFormula_branchWall_expWeighted_fullLogEnvelope_le_fixedWindowSum
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    {t : ℝ}
    (ht_mem : t ∈ Set.Ioc (‖w‖ / 2) (2 * ‖w‖)) :
    (2 *
      (max |Real.log (w.re / (3 * ‖w‖))|
        |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi)) /
      Real.exp ((2 : ℝ) * Real.pi * t) ≤
    (2 *
      (|Real.log (w.re / (3 * ‖w‖))| +
        max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| +
        Real.pi)) /
      Real.exp ((2 : ℝ) * Real.pi * t) := by
  have ht_nonneg : 0 ≤ t := by
    have hcut_nonneg : 0 ≤ ‖w‖ / 2 :=
      div_nonneg (norm_nonneg w) Real.zero_le_two_real
    exact le_trans hcut_nonneg (le_of_lt ht_mem.1)
  have hnum :
      max |Real.log (w.re / (3 * ‖w‖))|
          |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi ≤
        |Real.log (w.re / (3 * ‖w‖))| +
          max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| +
          Real.pi :=
    Complex.binetSecondFormula_branchWall_fullLogNumerator_le_fixedWindowSum
      hw_re_pos ht_nonneg ht_mem.2
  have htwo_num :
      2 *
        (max |Real.log (w.re / (3 * ‖w‖))|
          |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi) ≤
      2 *
        (|Real.log (w.re / (3 * ‖w‖))| +
          max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| +
          Real.pi) :=
    mul_le_mul_of_nonneg_left hnum Real.zero_le_two_real
  exact
    div_le_div_of_nonneg_right
      htwo_num
      (le_of_lt (Real.exp_pos ((2 : ℝ) * Real.pi * t)))

/-- Integrated weighted full-envelope comparison for the bounded branch-wall
window. -/
theorem Complex.binetSecondFormula_branchWall_expWeighted_fullLogEnvelope_integral_le_fixedWindowSum_Ioc
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (2 *
          (max |Real.log (w.re / (3 * ‖w‖))|
            |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi)) /
          Real.exp ((2 : ℝ) * Real.pi * t) ≤
      ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (2 *
          (|Real.log (w.re / (3 * ‖w‖))| +
            max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| +
            Real.pi)) /
          Real.exp ((2 : ℝ) * Real.pi * t) := by
  let S : Set ℝ := Set.Ioc (‖w‖ / 2) (2 * ‖w‖)
  let G : ℝ → ℝ := fun t : ℝ =>
    (2 *
      (max |Real.log (w.re / (3 * ‖w‖))|
        |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi)) /
      Real.exp ((2 : ℝ) * Real.pi * t)
  let H : ℝ → ℝ := fun t : ℝ =>
    (2 *
      (|Real.log (w.re / (3 * ‖w‖))| +
        max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| +
        Real.pi)) /
      Real.exp ((2 : ℝ) * Real.pi * t)
  have hG_integrable : IntegrableOn G S := by
    let Scc : Set ℝ := Set.Icc (‖w‖ / 2) (2 * ‖w‖)
    let B : ℝ → ℝ := fun t : ℝ => max w.re |w.im - t|
    let A : ℝ → ℝ := fun t : ℝ => (3 * ‖w‖) / B t
    let Gcc : ℝ → ℝ := fun t : ℝ =>
      (2 *
        (max |Real.log (w.re / (3 * ‖w‖))| |Real.log (A t)| +
          Real.pi)) /
        Real.exp ((2 : ℝ) * Real.pi * t)
    have hw_norm_pos : 0 < ‖w‖ :=
      Complex.norm_pos_of_re_pos hw_re_pos
    have hB_pos : ∀ t : ℝ, 0 < B t := by
      intro t
      exact
        lt_of_lt_of_le
          hw_re_pos
          (Complex.binetSecondFormula_branchWall_distance_re_le w t)
    have hA_pos : ∀ t : ℝ, 0 < A t := by
      intro t
      exact div_pos (mul_pos Real.zero_lt_three hw_norm_pos) (hB_pos t)
    have hdist_cont : Continuous fun t : ℝ => |w.im - t| :=
      (continuous_const.sub continuous_id).abs
    have hB_cont : Continuous B :=
      continuous_const.max hdist_cont
    have hA_cont : Continuous A :=
      continuous_const.div hB_cont (fun t => (hB_pos t).ne')
    have hlog_contOn :
        ContinuousOn (fun t : ℝ => Real.log (A t)) Scc :=
      (hA_cont.continuousOn).log (fun t ht => (hA_pos t).ne')
    have hnum_contOn :
        ContinuousOn
          (fun t : ℝ =>
            2 *
              (max |Real.log (w.re / (3 * ‖w‖))| |Real.log (A t)| +
                Real.pi))
          Scc :=
      continuousOn_const.mul
        ((continuousOn_const.max hlog_contOn.abs).add continuousOn_const)
    have hlinear_cont : Continuous fun t : ℝ => (2 : ℝ) * Real.pi * t :=
      (continuous_const.mul continuous_const).mul continuous_id
    have hden_cont : Continuous fun t : ℝ =>
        Real.exp ((2 : ℝ) * Real.pi * t) :=
      Real.continuous_exp.comp hlinear_cont
    have hden_ne : ∀ t : ℝ, t ∈ Scc →
        Real.exp ((2 : ℝ) * Real.pi * t) ≠ 0 := by
      intro t ht
      exact (Real.exp_pos ((2 : ℝ) * Real.pi * t)).ne'
    have hGcc_contOn : ContinuousOn Gcc Scc :=
      hnum_contOn.div hden_cont.continuousOn hden_ne
    have hGcc_integrable_Icc : IntegrableOn Gcc Scc :=
      hGcc_contOn.integrableOn_Icc
    exact hGcc_integrable_Icc.mono_set Ioc_subset_Icc_self
  have hH_integrable : IntegrableOn H S := by
    let Scc : Set ℝ := Set.Icc (‖w‖ / 2) (2 * ‖w‖)
    let K : ℝ := 2 *
      (|Real.log (w.re / (3 * ‖w‖))| +
        max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| +
        Real.pi)
    let Hcc : ℝ → ℝ := fun t : ℝ =>
      K / Real.exp ((2 : ℝ) * Real.pi * t)
    have hlinear_cont : Continuous fun t : ℝ => (2 : ℝ) * Real.pi * t :=
      (continuous_const.mul continuous_const).mul continuous_id
    have hden_cont : Continuous fun t : ℝ =>
        Real.exp ((2 : ℝ) * Real.pi * t) :=
      Real.continuous_exp.comp hlinear_cont
    have hden_ne : ∀ t : ℝ, t ∈ Scc →
        Real.exp ((2 : ℝ) * Real.pi * t) ≠ 0 := by
      intro t ht
      exact (Real.exp_pos ((2 : ℝ) * Real.pi * t)).ne'
    have hHcc_contOn : ContinuousOn Hcc Scc :=
      continuousOn_const.div hden_cont.continuousOn hden_ne
    have hHcc_integrable_Icc : IntegrableOn Hcc Scc :=
      hHcc_contOn.integrableOn_Icc
    exact hHcc_integrable_Icc.mono_set Ioc_subset_Icc_self
  have hpoint :
      ∀ᵐ t ∂volume.restrict S, G t ≤ H t :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun t ht =>
        Complex.binetSecondFormula_branchWall_expWeighted_fullLogEnvelope_le_fixedWindowSum
          hw_re_pos ht)
  exact
    setIntegral_mono_ae_restrict hG_integrable hH_integrable hpoint

/-- The fixed-window-sum full branch-wall envelope has the expected
`exp (-π‖w‖)` scale. -/
theorem Complex.binetSecondFormula_branchWall_fixedWindowSum_expWeighted_integral_le_expScale_Ioc
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (2 *
          (|Real.log (w.re / (3 * ‖w‖))| +
            max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| +
            Real.pi)) /
          Real.exp ((2 : ℝ) * Real.pi * t) ≤
      (2 *
        (|Real.log (w.re / (3 * ‖w‖))| +
          max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| +
          Real.pi)) *
        Real.exp (-Real.pi * ‖w‖) := by
  let N : ℝ := ‖w‖
  let K : ℝ :=
    2 *
      (|Real.log (w.re / (3 * ‖w‖))| +
        max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| +
        Real.pi)
  let F : ℝ → ℝ := fun t : ℝ =>
    Real.exp (-((2 : ℝ) * Real.pi) * t)
  have hK_nonneg : 0 ≤ K := by
    have hfixed_nonneg :
        0 ≤ max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| :=
      le_max_of_le_left (abs_nonneg (Real.log (1 : ℝ)))
    have hinside_nonneg :
        0 ≤
          |Real.log (w.re / (3 * ‖w‖))| +
            max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| +
            Real.pi :=
      add_nonneg
        (add_nonneg (abs_nonneg (Real.log (w.re / (3 * ‖w‖)))) hfixed_nonneg)
        Real.pi_nonneg
    exact mul_nonneg Real.zero_le_two hinside_nonneg
  have htail_integrable :
      IntegrableOn F (Set.Ioi (N / 2)) := by
    have hcoeff_pos : 0 < (2 : ℝ) * Real.pi :=
      mul_pos two_pos Real.pi_pos
    exact exp_neg_integrableOn_Ioi (N / 2) hcoeff_pos
  have htail_nonneg :
      0 ≤ᵐ[volume.restrict (Set.Ioi (N / 2))] F :=
    Filter.Eventually.of_forall
      (fun t => le_of_lt (Real.exp_pos (-((2 : ℝ) * Real.pi) * t)))
  have hsubset :
      Set.Ioc (N / 2) (2 * N) ≤ᵐ[volume] Set.Ioi (N / 2) :=
    Filter.Eventually.of_forall (fun t ht => ht.1)
  have hmono :
      ∫ t : ℝ in Set.Ioc (N / 2) (2 * N), F t ≤
        ∫ t : ℝ in Set.Ioi (N / 2), F t :=
    setIntegral_mono_set htail_integrable htail_nonneg hsubset
  have hscaled_mono :
      K * (∫ t : ℝ in Set.Ioc (N / 2) (2 * N), F t) ≤
        K * (∫ t : ℝ in Set.Ioi (N / 2), F t) :=
    mul_le_mul_of_nonneg_left hmono hK_nonneg
  have htail_bound :
      ∫ t : ℝ in Set.Ioi (N / 2), F t ≤
        Real.exp (-((2 : ℝ) * Real.pi) * (N / 2)) :=
    Real.exp_neg_two_pi_tail_integral_le_exp (N / 2)
  have hexponent :
      -((2 : ℝ) * Real.pi) * (N / 2) = -Real.pi * ‖w‖ := by
    calc
      -((2 : ℝ) * Real.pi) * (N / 2) =
          -(((2 : ℝ) * Real.pi) * (N / 2)) := by
        exact neg_mul ((2 : ℝ) * Real.pi) (N / 2)
      _ = -(Real.pi * ‖w‖) := by
        have hinside :
            ((2 : ℝ) * Real.pi) * (N / 2) =
              Real.pi * ‖w‖ := by
          calc
            ((2 : ℝ) * Real.pi) * (N / 2) =
                ((2 : ℝ) * Real.pi) * (‖w‖ / 2) := by
              rfl
            _ = (((2 : ℝ) * Real.pi) * ‖w‖) / 2 := by
              exact mul_div_assoc ((2 : ℝ) * Real.pi) ‖w‖ 2
            _ = ((Real.pi * ‖w‖) * 2) / 2 := by
              exact
                congrArg (fun x : ℝ => x / 2)
                  (calc
                    ((2 : ℝ) * Real.pi) * ‖w‖ =
                        2 * (Real.pi * ‖w‖) := by
                      exact mul_assoc 2 Real.pi ‖w‖
                    _ = (Real.pi * ‖w‖) * 2 := by
                      exact mul_comm 2 (Real.pi * ‖w‖))
            _ = Real.pi * ‖w‖ := by
              exact mul_div_cancel_right₀ (Real.pi * ‖w‖) two_ne_zero
        exact congrArg Neg.neg hinside
      _ = -Real.pi * ‖w‖ := by
        exact (neg_mul Real.pi ‖w‖).symm
  have htail_scale :
      K * (∫ t : ℝ in Set.Ioi (N / 2), F t) ≤
        K * Real.exp (-Real.pi * ‖w‖) := by
    exact
      mul_le_mul_of_nonneg_left
        (Eq.subst
          (motive := fun x : ℝ =>
            ∫ t : ℝ in Set.Ioi (N / 2), F t ≤ Real.exp x)
          hexponent
          htail_bound)
        hK_nonneg
  have hintegrand_eq :
      ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
          (2 *
            (|Real.log (w.re / (3 * ‖w‖))| +
              max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| +
              Real.pi)) /
            Real.exp ((2 : ℝ) * Real.pi * t) =
        K * ∫ t : ℝ in Set.Ioc (N / 2) (2 * N), F t := by
    calc
      ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
          (2 *
            (|Real.log (w.re / (3 * ‖w‖))| +
              max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| +
              Real.pi)) /
            Real.exp ((2 : ℝ) * Real.pi * t) =
          ∫ t : ℝ in Set.Ioc (N / 2) (2 * N), K * F t := by
        exact
          setIntegral_congr_fun measurableSet_Ioc
            (fun t _ht =>
              calc
                (2 *
                    (|Real.log (w.re / (3 * ‖w‖))| +
                      max |Real.log (1 : ℝ)|
                        |Real.log ((3 * ‖w‖) / w.re)| +
                      Real.pi)) /
                    Real.exp ((2 : ℝ) * Real.pi * t) =
                    K * (Real.exp ((2 : ℝ) * Real.pi * t))⁻¹ := by
                  rfl
                _ = K * Real.exp (-((2 : ℝ) * Real.pi * t)) := by
                  exact congrArg (fun x : ℝ => K * x)
                    (Real.exp_neg ((2 : ℝ) * Real.pi * t)).symm
                _ = K * F t := by
                  exact congrArg (fun x : ℝ => K * Real.exp x)
                    (neg_mul ((2 : ℝ) * Real.pi) t))
      _ = K * ∫ t : ℝ in Set.Ioc (N / 2) (2 * N), F t := by
        exact integral_mul_left K F
  exact
    Eq.subst
      (motive := fun x : ℝ =>
        x ≤
          (2 *
            (|Real.log (w.re / (3 * ‖w‖))| +
              max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| +
              Real.pi)) *
            Real.exp (-Real.pi * ‖w‖))
      hintegrand_eq.symm
      (le_trans hscaled_mono htail_scale)

/-- Local-indentation pointwise domination of the principal Binet tail kernel
by the branch-wall logarithmic spike on the bounded tail window. -/
theorem Complex.binetSecondFormula_principalTailKernel_norm_le_branchWall_logSpike_boundedTailWindow
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    {t : ℝ}
    (ht_mem : t ∈ Set.Icc (‖w‖ / 2) (2 * ‖w‖)) :
    ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
      (max |Real.log (w.re / (3 * ‖w‖))|
            |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi) /
        (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  let z : ℂ := (t : ℂ) / w
  let R : ℂ :=
    (1 + z * Complex.I) / (1 - z * Complex.I)
  let D : ℝ := Real.exp ((2 : ℝ) * Real.pi * t) - 1
  let m : ℝ := w.re / (3 * ‖w‖)
  let M : ℝ := (3 * ‖w‖) / max w.re |w.im - t|
  have hw_norm_pos : 0 < ‖w‖ :=
    Complex.norm_pos_of_re_pos hw_re_pos
  have ht_lower : ‖w‖ / 2 ≤ t :=
    ht_mem.1
  have ht_upper : t ≤ 2 * ‖w‖ :=
    ht_mem.2
  have hhalf_pos : 0 < ‖w‖ / 2 :=
    div_pos hw_norm_pos zero_lt_two
  have ht_pos : 0 < t :=
    lt_of_lt_of_le hhalf_pos ht_lower
  have ht_nonneg : 0 ≤ t :=
    le_of_lt ht_pos
  have hm_pos : 0 < m :=
    div_pos hw_re_pos (mul_pos Real.zero_lt_three hw_norm_pos)
  have hratio_lower :
      m ≤ ‖R‖ := by
    have hw_ne_zero : w ≠ 0 := by
      intro hw_zero
      cases hw_zero
      exact (lt_irrefl (0 : ℝ)) hw_re_pos
    have hnum_lower :
        w.re ≤ ‖w + (t : ℂ) * Complex.I‖ :=
      Complex.binetSecondFormula_arctan_tail_ratio_numerator_lower
        hw_re_pos t
    have hden_upper :
        ‖w - (t : ℂ) * Complex.I‖ ≤ 3 * ‖w‖ :=
      calc
        ‖w - (t : ℂ) * Complex.I‖ ≤ ‖w‖ + ‖(t : ℂ) * Complex.I‖ := by
          calc
            ‖w - (t : ℂ) * Complex.I‖ =
                ‖w + -((t : ℂ) * Complex.I)‖ := by
              exact congrArg norm (sub_eq_add_neg w ((t : ℂ) * Complex.I))
            _ ≤ ‖w‖ + ‖-((t : ℂ) * Complex.I)‖ :=
              norm_add_le w (-((t : ℂ) * Complex.I))
            _ = ‖w‖ + ‖(t : ℂ) * Complex.I‖ := by
              exact congrArg (fun x : ℝ => ‖w‖ + x)
                (norm_neg ((t : ℂ) * Complex.I))
        _ = ‖w‖ + t := by
          have htI_norm : ‖(t : ℂ) * Complex.I‖ = t := by
            calc
              ‖(t : ℂ) * Complex.I‖ = |t| :=
                Complex.norm_real_mul_I t
              _ = t := abs_of_nonneg ht_nonneg
          exact congrArg (fun x : ℝ => ‖w‖ + x) htI_norm
        _ ≤ ‖w‖ + 2 * ‖w‖ :=
          add_le_add_left ht_upper ‖w‖
        _ = 3 * ‖w‖ :=
          Real.add_two_mul_eq_three_mul ‖w‖
    have hden_pos : 0 < ‖w - (t : ℂ) * Complex.I‖ := by
      have hden_lower :
          w.re ≤ ‖w - (t : ℂ) * Complex.I‖ :=
        Complex.binetSecondFormula_arctan_tail_ratio_denominator_lower
          hw_re_pos t
      exact lt_of_lt_of_le hw_re_pos hden_lower
    have hcleared :
        w.re / (3 * ‖w‖) ≤
          ‖(w + (t : ℂ) * Complex.I) /
            (w - (t : ℂ) * Complex.I)‖ := by
      calc
        w.re / (3 * ‖w‖) ≤
            ‖w + (t : ℂ) * Complex.I‖ /
              ‖w - (t : ℂ) * Complex.I‖ :=
          Real.div_le_div_of_le_of_le'
            hw_re_pos
            (mul_pos Real.zero_lt_three hw_norm_pos)
            hden_pos
            hden_upper
            hnum_lower
        _ =
            ‖(w + (t : ℂ) * Complex.I) /
              (w - (t : ℂ) * Complex.I)‖ := by
          exact Eq.symm (norm_div _ _)
    calc
      m = w.re / (3 * ‖w‖) := rfl
      _ ≤ ‖(w + (t : ℂ) * Complex.I) /
              (w - (t : ℂ) * Complex.I)‖ := hcleared
      _ = ‖R‖ := by
        exact Eq.symm (Complex.binetSecondFormula_arctan_tail_ratio_eq_norm
          w hw_ne_zero t)
  have hratio_upper : ‖R‖ ≤ M := by
    calc
      ‖R‖ =
          ‖(1 + ((t : ℂ) / w) * Complex.I) /
            (1 - ((t : ℂ) / w) * Complex.I)‖ := rfl
      _ ≤ (3 * ‖w‖) / max w.re |w.im - t| :=
        Complex.binetSecondFormula_arctan_tail_ratio_norm_le_three_norm_div_branchWall_distance
          hw_re_pos ht_nonneg ht_upper
  have hmM : m ≤ M :=
    le_trans hratio_lower hratio_upper
  have hlog :
      ‖Complex.log R‖ ≤
        max |Real.log m| |Real.log M| + Real.pi :=
    Complex.log_norm_le_of_norm_bounds
      hm_pos hmM hratio_lower hratio_upper
  have harctan :
      ‖Complex.arctan ((t : ℂ) / w)‖ ≤
        max |Real.log m| |Real.log M| + Real.pi := by
    have hfactor_norm_le_one : ‖(-Complex.I / 2 : ℂ)‖ ≤ (1 : ℝ) :=
      Complex.norm_neg_I_div_two_le_one
    have hmul :
        ‖(-Complex.I / 2 : ℂ) * Complex.log R‖ ≤
          ‖Complex.log R‖ := by
      calc
        ‖(-Complex.I / 2 : ℂ) * Complex.log R‖ ≤
            ‖(-Complex.I / 2 : ℂ)‖ * ‖Complex.log R‖ :=
          norm_mul_le _ _
        _ ≤ 1 * ‖Complex.log R‖ :=
          mul_le_mul_of_nonneg_right hfactor_norm_le_one
            (norm_nonneg (Complex.log R))
        _ = ‖Complex.log R‖ :=
          one_mul ‖Complex.log R‖
    calc
      ‖Complex.arctan ((t : ℂ) / w)‖ =
          ‖(-Complex.I / 2 : ℂ) * Complex.log R‖ := by
        exact congrArg norm
          (Complex.binetSecondFormula_arctan_tail_expr_eq w t)
      _ ≤ ‖Complex.log R‖ := hmul
      _ ≤ max |Real.log m| |Real.log M| + Real.pi := hlog
  have hden_norm :
      ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ = D :=
    Complex.exp_tail_denominator_norm_eq t ht_pos
  have hD_nonneg : 0 ≤ D :=
    le_of_lt (Real.binetSecondFormula_exp_denominator_pos ht_pos)
  calc
    ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ =
        ‖Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ := by
      rfl
    _ =
        ‖Complex.arctan ((t : ℂ) / w)‖ /
          ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ := by
      exact norm_div _ _
    _ = ‖Complex.arctan ((t : ℂ) / w)‖ / D := by
      exact congrArg
        (fun x : ℝ => ‖Complex.arctan ((t : ℂ) / w)‖ / x)
        hden_norm
    _ ≤ (max |Real.log m| |Real.log M| + Real.pi) / D :=
      div_le_div_of_nonneg_right harctan hD_nonneg

/-- Pointwise constant envelope for the local-indentation principal-tail
kernel on the bounded branch-wall window. -/
theorem Complex.binetSecondFormula_principalTailKernel_norm_le_branchWall_localIndentation_constant_boundedTailWindow
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    {t : ℝ}
    (ht_mem : t ∈ Set.Icc (‖w‖ / 2) (2 * ‖w‖)) :
    ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
      ((max |Real.log (w.re / (3 * ‖w‖))|
            (max |Real.log (1 : ℝ)|
              |Real.log ((3 * ‖w‖) / w.re)|) + Real.pi) /
        (Real.exp (Real.pi * ‖w‖) - 1)) := by
  let B : ℝ := max w.re |w.im - t|
  let M : ℝ := (3 * ‖w‖) / B
  let U : ℝ := (3 * ‖w‖) / w.re
  let E : ℝ := Real.exp ((2 : ℝ) * Real.pi * t) - 1
  let E₀ : ℝ := Real.exp (Real.pi * ‖w‖) - 1
  let N : ℝ :=
    max |Real.log (w.re / (3 * ‖w‖))| |Real.log M| + Real.pi
  let C : ℝ :=
    max |Real.log (w.re / (3 * ‖w‖))|
      (max |Real.log (1 : ℝ)| |Real.log U|) + Real.pi
  have hw_norm_pos : 0 < ‖w‖ :=
    Complex.norm_pos_of_re_pos hw_re_pos
  have ht_lower : ‖w‖ / 2 ≤ t :=
    ht_mem.1
  have ht_upper : t ≤ 2 * ‖w‖ :=
    ht_mem.2
  have hhalf_pos : 0 < ‖w‖ / 2 :=
    div_pos hw_norm_pos zero_lt_two
  have ht_pos : 0 < t :=
    lt_of_lt_of_le hhalf_pos ht_lower
  have ht_nonneg : 0 ≤ t :=
    le_of_lt ht_pos
  have hB_pos : 0 < B :=
    lt_of_lt_of_le hw_re_pos (le_max_left w.re |w.im - t|)
  have hB_lower : w.re ≤ B :=
    le_max_left w.re |w.im - t|
  have hnum_pos : 0 < 3 * ‖w‖ :=
    mul_pos Real.zero_lt_three hw_norm_pos
  have hre_le_norm : w.re ≤ ‖w‖ := by
    calc
      w.re = |w.re| := Eq.symm (abs_of_pos hw_re_pos)
      _ ≤ ‖w‖ := Complex.abs_re_le_abs w
  have hre_le_three : w.re ≤ 3 * ‖w‖ := by
    calc
      w.re ≤ ‖w‖ := hre_le_norm
      _ ≤ 3 * ‖w‖ :=
        le_mul_of_one_le_left (le_of_lt hw_norm_pos) Real.one_le_three_real
  have hU_ge_one : (1 : ℝ) ≤ U := by
    exact (le_div_iff₀ hw_re_pos).2
      (calc
        (1 : ℝ) * w.re = w.re := one_mul w.re
        _ ≤ 3 * ‖w‖ := hre_le_three)
  have hB_upper : B ≤ 3 * ‖w‖ := by
    have him_le_three : |w.im - t| ≤ 3 * ‖w‖ := by
      calc
        |w.im - t| ≤ ‖w - (t : ℂ) * Complex.I‖ :=
          Complex.binetSecondFormula_arctan_tail_denominator_branchWall_distance_le
            w t
        _ ≤ ‖w‖ + ‖(t : ℂ) * Complex.I‖ := by
          calc
            ‖w - (t : ℂ) * Complex.I‖ =
                ‖w + -((t : ℂ) * Complex.I)‖ := by
              exact congrArg norm (sub_eq_add_neg w ((t : ℂ) * Complex.I))
            _ ≤ ‖w‖ + ‖-((t : ℂ) * Complex.I)‖ :=
              norm_add_le w (-((t : ℂ) * Complex.I))
            _ = ‖w‖ + ‖(t : ℂ) * Complex.I‖ := by
              exact congrArg (fun x : ℝ => ‖w‖ + x)
                (norm_neg ((t : ℂ) * Complex.I))
        _ = ‖w‖ + t := by
          have htI_norm : ‖(t : ℂ) * Complex.I‖ = t := by
            calc
              ‖(t : ℂ) * Complex.I‖ = |t| :=
                Complex.norm_real_mul_I t
              _ = t := abs_of_nonneg ht_nonneg
          exact congrArg (fun x : ℝ => ‖w‖ + x) htI_norm
        _ ≤ ‖w‖ + 2 * ‖w‖ :=
          add_le_add_left ht_upper ‖w‖
        _ = 3 * ‖w‖ :=
          Real.add_two_mul_eq_three_mul ‖w‖
    exact max_le hre_le_three him_le_three
  have hM_lower : (1 : ℝ) ≤ M := by
    exact (le_div_iff₀ hB_pos).2
      (calc
        (1 : ℝ) * B = B := one_mul B
        _ ≤ 3 * ‖w‖ := hB_upper)
  have hM_upper : M ≤ U :=
    div_le_div_of_nonneg_left (le_of_lt hnum_pos) hw_re_pos hB_lower
  have hlogM :
      |Real.log M| ≤
        max |Real.log (1 : ℝ)| |Real.log U| :=
    Real.abs_log_le_max_abs_log_of_bounds
      zero_lt_one hU_ge_one hM_lower hM_upper
  have hN_le_C : N ≤ C := by
    have hmax :
        max |Real.log (w.re / (3 * ‖w‖))| |Real.log M| ≤
          max |Real.log (w.re / (3 * ‖w‖))|
            (max |Real.log (1 : ℝ)| |Real.log U|) :=
      max_le
        (le_max_left _ _)
        (le_trans hlogM (le_max_right _ _))
    exact add_le_add_right hmax Real.pi
  have hE0_pos : 0 < E₀ := by
    have hpi_norm_pos : 0 < Real.pi * ‖w‖ :=
      mul_pos Real.pi_pos hw_norm_pos
    exact sub_pos.mpr
      (calc
        (1 : ℝ) = Real.exp 0 := Eq.symm Real.exp_zero
        _ < Real.exp (Real.pi * ‖w‖) :=
          Real.exp_lt_exp.mpr hpi_norm_pos)
  have hE_lower : E₀ ≤ E := by
    have hpi_le : Real.pi * ‖w‖ ≤ (2 : ℝ) * Real.pi * t := by
      have hmul_lower :
          Real.pi * (‖w‖ / 2) ≤ Real.pi * t :=
        mul_le_mul_of_nonneg_left ht_lower (le_of_lt Real.pi_pos)
      calc
        Real.pi * ‖w‖ =
            (2 : ℝ) * (Real.pi * (‖w‖ / 2)) := by
          exact Eq.symm <| by
            calc
              (2 : ℝ) * (Real.pi * (‖w‖ / 2)) =
                  ((2 : ℝ) * Real.pi) * (‖w‖ / 2) := by
                exact (mul_assoc (2 : ℝ) Real.pi (‖w‖ / 2)).symm
              _ = (Real.pi * 2) * (‖w‖ / 2) := by
                exact congrArg (fun x : ℝ => x * (‖w‖ / 2))
                  (mul_comm (2 : ℝ) Real.pi)
              _ = Real.pi * (2 * (‖w‖ / 2)) := by
                exact mul_assoc Real.pi 2 (‖w‖ / 2)
              _ = Real.pi * ‖w‖ := by
                exact congrArg (fun x : ℝ => Real.pi * x)
                  (Real.two_mul_div_two ‖w‖)
        _ ≤ (2 : ℝ) * (Real.pi * t) :=
          mul_le_mul_of_nonneg_left hmul_lower Real.zero_le_two_real
        _ = (2 : ℝ) * Real.pi * t :=
          (mul_assoc (2 : ℝ) Real.pi t).symm
    exact sub_le_sub_right (Real.exp_le_exp.mpr hpi_le) 1
  have hN_nonneg : 0 ≤ N :=
    add_nonneg
      (le_max_of_le_left
        (abs_nonneg (Real.log (w.re / (3 * ‖w‖)))))
      Real.pi_nonneg
  have hkernel :
      ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤ N / E :=
    Complex.binetSecondFormula_principalTailKernel_norm_le_branchWall_logSpike_boundedTailWindow
      hw_re_pos ht_mem
  have hratio : N / E ≤ C / E₀ :=
    Real.div_le_div_of_le_of_le hE0_pos hN_nonneg hN_le_C hE_lower
  exact le_trans hkernel hratio

/-- Integrated local-indentation estimate for the principal Binet tail kernel
over the bounded branch-wall window. -/
theorem Complex.binetSecondFormula_principalTailKernel_integral_le_branchWall_localIndentation_boundedTailWindow
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∫ t : ℝ in Set.Icc (‖w‖ / 2) (2 * ‖w‖),
        ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
      ((max |Real.log (w.re / (3 * ‖w‖))|
            (max |Real.log (1 : ℝ)|
              |Real.log ((3 * ‖w‖) / w.re)|) + Real.pi) /
        (Real.exp (Real.pi * ‖w‖) - 1)) *
        (volume (Set.Icc (‖w‖ / 2) (2 * ‖w‖))).toReal := by
  let S : Set ℝ := Set.Icc (‖w‖ / 2) (2 * ‖w‖)
  let F : ℝ → ℝ := fun t : ℝ =>
    ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖
  let C : ℝ :=
    (max |Real.log (w.re / (3 * ‖w‖))|
        (max |Real.log (1 : ℝ)|
          |Real.log ((3 * ‖w‖) / w.re)|) + Real.pi) /
      (Real.exp (Real.pi * ‖w‖) - 1)
  have hF_bound : ∀ t : ℝ, t ∈ S → ‖F t‖ ≤ C := by
    intro t ht
    have hpoint :
        F t ≤ C :=
      Complex.binetSecondFormula_principalTailKernel_norm_le_branchWall_localIndentation_constant_boundedTailWindow
        hw_re_pos ht
    have hF_nonneg : 0 ≤ F t :=
      norm_nonneg (Complex.binetSecondFormulaPrincipalTailKernel w t)
    calc
      ‖F t‖ = |F t| := Real.norm_eq_abs (F t)
      _ = F t := abs_of_nonneg hF_nonneg
      _ ≤ C := hpoint
  have hnorm_integral :
      ‖∫ t : ℝ in S, F t‖ ≤ C * (volume S).toReal :=
    norm_setIntegral_le_of_norm_le_const'
      measure_Icc_lt_top measurableSet_Icc hF_bound
  calc
    ∫ t : ℝ in S, F t ≤ |∫ t : ℝ in S, F t| :=
      le_abs_self (∫ t : ℝ in S, F t)
    _ = ‖∫ t : ℝ in S, F t‖ :=
      Eq.symm (Real.norm_eq_abs (∫ t : ℝ in S, F t))
    _ ≤ C * (volume S).toReal :=
      hnorm_integral

/-- Integrated local-indentation estimate for the principal Binet tail kernel
over the half-open bounded branch-wall window.  This is the interval form that
splits exactly with the far tail into `Ioi (‖w‖ / 2)`. -/
theorem Complex.binetSecondFormula_principalTailKernel_integral_le_branchWall_localIndentation_boundedTailWindow_Ioc
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
      ((max |Real.log (w.re / (3 * ‖w‖))|
            (max |Real.log (1 : ℝ)|
              |Real.log ((3 * ‖w‖) / w.re)|) + Real.pi) /
        (Real.exp (Real.pi * ‖w‖) - 1)) *
        (volume (Set.Ioc (‖w‖ / 2) (2 * ‖w‖))).toReal := by
  let S : Set ℝ := Set.Ioc (‖w‖ / 2) (2 * ‖w‖)
  let F : ℝ → ℝ := fun t : ℝ =>
    ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖
  let C : ℝ :=
    (max |Real.log (w.re / (3 * ‖w‖))|
        (max |Real.log (1 : ℝ)|
          |Real.log ((3 * ‖w‖) / w.re)|) + Real.pi) /
      (Real.exp (Real.pi * ‖w‖) - 1)
  have hmeasure : volume S < ∞ :=
    measure_Ioc_lt_top
  have hF_bound : ∀ t : ℝ, t ∈ S → ‖F t‖ ≤ C := by
    intro t ht
    have ht_Icc : t ∈ Set.Icc (‖w‖ / 2) (2 * ‖w‖) :=
      And.intro (le_of_lt ht.1) ht.2
    have hpoint :
        F t ≤ C :=
      Complex.binetSecondFormula_principalTailKernel_norm_le_branchWall_localIndentation_constant_boundedTailWindow
        hw_re_pos ht_Icc
    have hF_nonneg : 0 ≤ F t :=
      norm_nonneg (Complex.binetSecondFormulaPrincipalTailKernel w t)
    calc
      ‖F t‖ = |F t| := Real.norm_eq_abs (F t)
      _ = F t := abs_of_nonneg hF_nonneg
      _ ≤ C := hpoint
  have hnorm_integral :
      ‖∫ t : ℝ in S, F t‖ ≤ C * (volume S).toReal :=
    norm_setIntegral_le_of_norm_le_const'
      hmeasure measurableSet_Ioc hF_bound
  calc
    ∫ t : ℝ in S, F t ≤ |∫ t : ℝ in S, F t| :=
      le_abs_self (∫ t : ℝ in S, F t)
    _ = ‖∫ t : ℝ in S, F t‖ :=
      Eq.symm (Real.norm_eq_abs (∫ t : ℝ in S, F t))
    _ ≤ C * (volume S).toReal :=
      hnorm_integral

/-- Integrated local-indentation estimate for the principal Binet tail kernel
with the Binet denominator replaced by a pure exponential weight.

This is the real-variable local estimate immediately upstream of the C5
branch-spike absorption: it retains the full logarithmic envelope required by
the principal-branch arctangent bound, but no longer contains
`exp (2πt) - 1`. -/
theorem Complex.binetSecondFormula_principalTailKernel_integral_le_expWeighted_fullLogEnvelope_boundedTailWindow_Ioc
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hw_large : 2 ≤ ‖w‖) :
    ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
      ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        (2 *
          (max |Real.log (w.re / (3 * ‖w‖))|
            |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi)) /
          Real.exp ((2 : ℝ) * Real.pi * t) := by
  let S : Set ℝ := Set.Ioc (‖w‖ / 2) (2 * ‖w‖)
  let P : ℝ → ℝ := fun t : ℝ =>
    ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖
  let G : ℝ → ℝ := fun t : ℝ =>
    (2 *
      (max |Real.log (w.re / (3 * ‖w‖))|
        |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi)) /
      Real.exp ((2 : ℝ) * Real.pi * t)
  have hP_integrable :
      IntegrableOn P S :=
    (Complex.binetSecondFormula_arctanKernel_integrableOn_tail_interval
      (w := w) hw_re_pos).norm.mono_set Ioc_subset_Ioi_self
  have hG_integrable : IntegrableOn G S := by
    let Scc : Set ℝ := Set.Icc (‖w‖ / 2) (2 * ‖w‖)
    let B : ℝ → ℝ := fun t : ℝ => max w.re |w.im - t|
    let A : ℝ → ℝ := fun t : ℝ => (3 * ‖w‖) / B t
    let H : ℝ → ℝ := fun t : ℝ =>
      (2 *
        (max |Real.log (w.re / (3 * ‖w‖))|
          |Real.log (A t)| + Real.pi)) /
        Real.exp ((2 : ℝ) * Real.pi * t)
    have hw_norm_pos : 0 < ‖w‖ :=
      Complex.norm_pos_of_re_pos hw_re_pos
    have hB_pos : ∀ t : ℝ, 0 < B t := by
      intro t
      exact lt_of_lt_of_le hw_re_pos (le_max_left w.re |w.im - t|)
    have hA_pos : ∀ t : ℝ, 0 < A t := by
      intro t
      exact div_pos (mul_pos Real.zero_lt_three hw_norm_pos) (hB_pos t)
    have hdist_cont : Continuous fun t : ℝ => |w.im - t| :=
      (continuous_const.sub continuous_id).abs
    have hB_cont : Continuous B :=
      continuous_const.max hdist_cont
    have hA_cont : Continuous A :=
      continuous_const.div hB_cont (fun t => (hB_pos t).ne')
    have hlog_contOn :
        ContinuousOn (fun t : ℝ => Real.log (A t)) Scc :=
      (hA_cont.continuousOn).log (fun t ht => (hA_pos t).ne')
    have hfull_log_contOn :
        ContinuousOn
          (fun t : ℝ =>
            max |Real.log (w.re / (3 * ‖w‖))|
              |Real.log (A t)| + Real.pi)
          Scc :=
      (continuousOn_const.max hlog_contOn.abs).add continuousOn_const
    have hnum_contOn :
        ContinuousOn
          (fun t : ℝ =>
            2 *
              (max |Real.log (w.re / (3 * ‖w‖))|
                |Real.log (A t)| + Real.pi))
          Scc :=
      continuousOn_const.mul hfull_log_contOn
    have hlinear_cont : Continuous fun t : ℝ => (2 : ℝ) * Real.pi * t :=
      (continuous_const.mul continuous_const).mul continuous_id
    have hden_cont : Continuous fun t : ℝ =>
        Real.exp ((2 : ℝ) * Real.pi * t) :=
      Real.continuous_exp.comp hlinear_cont
    have hden_ne : ∀ t : ℝ, t ∈ Scc →
        Real.exp ((2 : ℝ) * Real.pi * t) ≠ 0 := by
      intro t ht
      exact (Real.exp_pos ((2 : ℝ) * Real.pi * t)).ne'
    have hH_contOn : ContinuousOn H Scc :=
      hnum_contOn.div hden_cont.continuousOn hden_ne
    have hH_integrable_Icc : IntegrableOn H Scc :=
      hH_contOn.integrableOn_Icc
    exact hH_integrable_Icc.mono_set Ioc_subset_Icc_self
  have hpoint :
      ∀ᵐ t ∂volume.restrict S, P t ≤ G t :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun t ht => by
        have ht_Icc : t ∈ Set.Icc (‖w‖ / 2) (2 * ‖w‖) :=
          And.intro (le_of_lt ht.1) ht.2
        let N : ℝ :=
          max |Real.log (w.re / (3 * ‖w‖))|
            |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi
        have hkernel :
            P t ≤
              N / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
          Complex.binetSecondFormula_principalTailKernel_norm_le_branchWall_logSpike_boundedTailWindow
            hw_re_pos ht_Icc
        have hhalf_ge_one : (1 : ℝ) ≤ ‖w‖ / 2 := by
          exact (le_div_iff₀ zero_lt_two).2
            (calc
              (1 : ℝ) * 2 = 2 := one_mul 2
              _ ≤ ‖w‖ := hw_large)
        have ht_gt_one : t ∈ Set.Ioi (1 : ℝ) :=
          lt_of_le_of_lt hhalf_ge_one ht.1
        have hN_nonneg : 0 ≤ N :=
          add_nonneg
            (le_max_of_le_left
              (abs_nonneg (Real.log (w.re / (3 * ‖w‖)))))
            Real.pi_nonneg
        have hexp :
            N / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) ≤
              (2 * N) / Real.exp ((2 : ℝ) * Real.pi * t) :=
          Real.binetSecondFormula_nonneg_div_exp_denominator_le_two_mul_div_exp
            hN_nonneg ht_gt_one
        exact le_trans hkernel hexp)
  exact
    setIntegral_mono_ae_restrict hP_integrable hG_integrable hpoint

/-- The bounded branch-wall window of the principal Binet tail has the
explicit exponential scale forced by the lower endpoint of the window.

This is the low-level scalar theorem available before any contour-level
paired-branch cancellation: it still records the fixed branch-wall logarithmic
window depending on `w.re`. -/
theorem Complex.binetSecondFormula_principalTailKernel_integral_le_expScale_boundedTailWindow_Ioc
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hw_large : 2 ≤ ‖w‖) :
    ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
        ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
      (2 *
        (|Real.log (w.re / (3 * ‖w‖))| +
          max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| +
          Real.pi)) *
        Real.exp (-Real.pi * ‖w‖) := by
  have hprincipal_to_moving :
      ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
          ‖Complex.binetSecondFormulaPrincipalTailKernel w t‖ ≤
        ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
          (2 *
            (max |Real.log (w.re / (3 * ‖w‖))|
              |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi)) /
            Real.exp ((2 : ℝ) * Real.pi * t) :=
    Complex.binetSecondFormula_principalTailKernel_integral_le_expWeighted_fullLogEnvelope_boundedTailWindow_Ioc
      hw_re_pos hw_large
  have hmoving_to_fixed :
      ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
          (2 *
            (max |Real.log (w.re / (3 * ‖w‖))|
              |Real.log ((3 * ‖w‖) / max w.re |w.im - t|)| + Real.pi)) /
            Real.exp ((2 : ℝ) * Real.pi * t) ≤
        ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
          (2 *
            (|Real.log (w.re / (3 * ‖w‖))| +
              max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| +
              Real.pi)) /
            Real.exp ((2 : ℝ) * Real.pi * t) :=
    Complex.binetSecondFormula_branchWall_expWeighted_fullLogEnvelope_integral_le_fixedWindowSum_Ioc
      hw_re_pos
  have hfixed_to_scale :
      ∫ t : ℝ in Set.Ioc (‖w‖ / 2) (2 * ‖w‖),
          (2 *
            (|Real.log (w.re / (3 * ‖w‖))| +
              max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| +
              Real.pi)) /
            Real.exp ((2 : ℝ) * Real.pi * t) ≤
        (2 *
          (|Real.log (w.re / (3 * ‖w‖))| +
            max |Real.log (1 : ℝ)| |Real.log ((3 * ‖w‖) / w.re)| +
            Real.pi)) *
          Real.exp (-Real.pi * ‖w‖) :=
    Complex.binetSecondFormula_branchWall_fixedWindowSum_expWeighted_integral_le_expScale_Ioc
      hw_re_pos
  exact
    le_trans hprincipal_to_moving
      (le_trans hmoving_to_fixed hfixed_to_scale)

/-- On the bounded part of the tail, the unnormalized denominator is bounded
by `3 * ‖w‖`. -/
theorem Complex.binetSecondFormula_arctan_tail_denominator_le_three_norm
    {w : ℂ}
    {t : ℝ}
    (ht_nonneg : 0 ≤ t)
    (ht_le : t ≤ 2 * ‖w‖) :
    ‖w - (t : ℂ) * Complex.I‖ ≤ 3 * ‖w‖ := by
  have htI_norm : ‖(t : ℂ) * Complex.I‖ = t := by
    calc
      ‖(t : ℂ) * Complex.I‖ = |t| := Complex.norm_real_mul_I t
      _ = t := abs_of_nonneg ht_nonneg
  calc
    ‖w - (t : ℂ) * Complex.I‖ ≤ ‖w‖ + ‖(t : ℂ) * Complex.I‖ := by
      calc
        ‖w - (t : ℂ) * Complex.I‖ = ‖w + -((t : ℂ) * Complex.I)‖ := by
          exact congrArg norm (sub_eq_add_neg w ((t : ℂ) * Complex.I))
        _ ≤ ‖w‖ + ‖-((t : ℂ) * Complex.I)‖ := by
          exact norm_add_le _ _
        _ = ‖w‖ + ‖(t : ℂ) * Complex.I‖ := by
          exact congrArg (fun x : ℝ => ‖w‖ + x) (norm_neg ((t : ℂ) * Complex.I))
    _ = ‖w‖ + t := by
      exact congrArg (fun x : ℝ => ‖w‖ + x) htI_norm
    _ ≤ ‖w‖ + 2 * ‖w‖ := add_le_add_left ht_le _
    _ = 3 * ‖w‖ := by
      exact Real.add_two_mul_eq_three_mul ‖w‖

/-- On the far part of the tail, the two unnormalized branch distances are
within a factor `3` of one another. -/
theorem Complex.binetSecondFormula_arctan_tail_far_ratio_bounds
    {w : ℂ}
    {t : ℝ}
    (ht_far : 2 * ‖w‖ ≤ t) :
    ‖w + (t : ℂ) * Complex.I‖ ≤
        3 * ‖w - (t : ℂ) * Complex.I‖ ∧
      ‖w - (t : ℂ) * Complex.I‖ ≤
        3 * ‖w + (t : ℂ) * Complex.I‖ := by
  have ht_nonneg : 0 ≤ t :=
    le_trans (mul_nonneg Real.zero_le_two_real (norm_nonneg w)) ht_far
  have htI_norm : ‖(t : ℂ) * Complex.I‖ = t := by
    calc
      ‖(t : ℂ) * Complex.I‖ = |t| := Complex.norm_real_mul_I t
      _ = t := abs_of_nonneg ht_nonneg
  have htail_sub_nonneg : 0 ≤ t - ‖w‖ := by
    have hnorm_le_two_norm : ‖w‖ ≤ 2 * ‖w‖ :=
      le_mul_of_one_le_left (norm_nonneg w) one_le_two
    exact sub_nonneg.mpr (le_trans hnorm_le_two_norm ht_far)
  have htail_upper : ‖w‖ + t ≤ 3 * (t - ‖w‖) := by
    exact
      Real.add_le_three_mul_sub_of_two_mul_le
        (norm_nonneg w)
        ht_far
  have hminus_lower :
      t - ‖w‖ ≤ ‖w - (t : ℂ) * Complex.I‖ := by
    have hrev :
        ‖(t : ℂ) * Complex.I‖ - ‖w‖ ≤
          ‖(t : ℂ) * Complex.I - w‖ :=
      norm_sub_norm_le ((t : ℂ) * Complex.I) w
    have hnorm_eq :
        ‖(t : ℂ) * Complex.I - w‖ =
          ‖w - (t : ℂ) * Complex.I‖ := by
      exact by
        calc
          ‖(t : ℂ) * Complex.I - w‖ = ‖-(w - (t : ℂ) * Complex.I)‖ := by
            congr 1
            exact Complex.sub_swap_eq_neg_sub w ((t : ℂ) * Complex.I)
          _ = ‖w - (t : ℂ) * Complex.I‖ := by
            exact norm_neg _
    exact by
      have hleft :
          t - ‖w‖ = ‖(t : ℂ) * Complex.I‖ - ‖w‖ :=
        congrArg (fun x : ℝ => x - ‖w‖) htI_norm.symm
      have hrev' : ‖(t : ℂ) * Complex.I‖ - ‖w‖ ≤
          ‖w - (t : ℂ) * Complex.I‖ :=
        hnorm_eq ▸ hrev
      exact hleft.trans_le hrev'
  have hplus_lower :
      t - ‖w‖ ≤ ‖w + (t : ℂ) * Complex.I‖ := by
    have hrev :
        ‖(t : ℂ) * Complex.I‖ - ‖w‖ ≤
          ‖(t : ℂ) * Complex.I - (-w)‖ := by
      have hrev0 :
          ‖(t : ℂ) * Complex.I‖ - ‖-w‖ ≤
            ‖(t : ℂ) * Complex.I - (-w)‖ :=
        norm_sub_norm_le ((t : ℂ) * Complex.I) (-w)
      calc
        ‖(t : ℂ) * Complex.I‖ - ‖w‖ =
            ‖(t : ℂ) * Complex.I‖ - ‖-w‖ := by
          exact congrArg (fun x : ℝ => ‖(t : ℂ) * Complex.I‖ - x) (norm_neg w).symm
        _ ≤ ‖(t : ℂ) * Complex.I - (-w)‖ := hrev0
    have hnorm_eq :
        ‖(t : ℂ) * Complex.I - (-w)‖ =
          ‖w + (t : ℂ) * Complex.I‖ := by
      exact congrArg norm
        (Complex.sub_neg_eq_add_comm ((t : ℂ) * Complex.I) w)
    exact by
      have hleft :
          t - ‖w‖ = ‖(t : ℂ) * Complex.I‖ - ‖w‖ :=
        congrArg (fun x : ℝ => x - ‖w‖) htI_norm.symm
      have hrev' : ‖(t : ℂ) * Complex.I‖ - ‖w‖ ≤
          ‖w + (t : ℂ) * Complex.I‖ :=
        hnorm_eq ▸ hrev
      exact hleft.trans_le hrev'
  have hplus_upper :
      ‖w + (t : ℂ) * Complex.I‖ ≤ ‖w‖ + t := by
    calc
      ‖w + (t : ℂ) * Complex.I‖ ≤ ‖w‖ + ‖(t : ℂ) * Complex.I‖ :=
        norm_add_le _ _
      _ = ‖w‖ + t := by exact congrArg (fun x : ℝ => ‖w‖ + x) htI_norm
  have hminus_upper :
      ‖w - (t : ℂ) * Complex.I‖ ≤ ‖w‖ + t := by
    calc
      ‖w - (t : ℂ) * Complex.I‖ ≤ ‖w‖ + ‖(t : ℂ) * Complex.I‖ := by
        calc
          ‖w - (t : ℂ) * Complex.I‖ = ‖w + -((t : ℂ) * Complex.I)‖ := by
            exact congrArg norm (sub_eq_add_neg w ((t : ℂ) * Complex.I))
          _ ≤ ‖w‖ + ‖-((t : ℂ) * Complex.I)‖ := by
            exact norm_add_le _ _
          _ = ‖w‖ + ‖(t : ℂ) * Complex.I‖ := by
            exact congrArg (fun x : ℝ => ‖w‖ + x) (norm_neg ((t : ℂ) * Complex.I))
      _ = ‖w‖ + t := by
        exact congrArg (fun x : ℝ => ‖w‖ + x) htI_norm
  constructor
  · calc
      ‖w + (t : ℂ) * Complex.I‖ ≤ ‖w‖ + t := hplus_upper
      _ ≤ 3 * (t - ‖w‖) := htail_upper
      _ ≤ 3 * ‖w - (t : ℂ) * Complex.I‖ :=
        mul_le_mul_of_nonneg_left hminus_lower
          Real.zero_le_three
  · calc
      ‖w - (t : ℂ) * Complex.I‖ ≤ ‖w‖ + t := hminus_upper
      _ ≤ 3 * (t - ‖w‖) := htail_upper
      _ ≤ 3 * ‖w + (t : ℂ) * Complex.I‖ :=
        mul_le_mul_of_nonneg_left hplus_lower
          Real.zero_le_three

/-- The fixed-tail ratio bound, expressed after clearing the common factor
`w`.  The interval is split into `t ≤ 2‖w‖` and `2‖w‖ ≤ t`; the bounded part
uses real-part separation and the far part uses triangle comparison. -/
theorem Complex.binetSecondFormula_arctan_tail_ratio_norm_bounds_cleared
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ m M : ℝ,
      0 < m ∧
      m ≤ M ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          m ≤ ‖(w + (t : ℂ) * Complex.I) /
              (w - (t : ℂ) * Complex.I)‖ ∧
          ‖(w + (t : ℂ) * Complex.I) /
              (w - (t : ℂ) * Complex.I)‖ ≤ M := by
  have hw_ne_zero : w ≠ 0 := by
    intro hw_zero
    cases hw_zero
    exact (lt_irrefl (0 : ℝ)) hw_re_pos
  have hw_norm_pos : 0 < ‖w‖ :=
    norm_pos_iff.mpr hw_ne_zero
  let m : ℝ := min (w.re / (3 * ‖w‖)) (1 / 3)
  let M : ℝ := max (3 * ‖w‖ / w.re) 3
  have hthree_pos : (0 : ℝ) < 3 := Real.zero_lt_three
  have hden_const_pos : 0 < 3 * ‖w‖ :=
    mul_pos hthree_pos hw_norm_pos
  have hm_pos : 0 < m := by
    show 0 < min (w.re / (3 * ‖w‖)) (1 / 3)
    exact
      lt_min
        (div_pos hw_re_pos hden_const_pos)
        (div_pos zero_lt_one hthree_pos)
  have hM_ge_three : 3 ≤ M := by
    show 3 ≤ max (3 * ‖w‖ / w.re) 3
    exact le_max_right _ _
  have hm_le_third : m ≤ (1 / 3 : ℝ) := by
    show min (w.re / (3 * ‖w‖)) (1 / 3) ≤ (1 / 3 : ℝ)
    exact min_le_right _ _
  have hm_le_bounded : m ≤ w.re / (3 * ‖w‖) := by
    show min (w.re / (3 * ‖w‖)) (1 / 3) ≤ w.re / (3 * ‖w‖)
    exact min_le_left _ _
  have hbounded_le_M : 3 * ‖w‖ / w.re ≤ M := by
    show 3 * ‖w‖ / w.re ≤ max (3 * ‖w‖ / w.re) 3
    exact le_max_left _ _
  refine ⟨m, M, hm_pos, ?_, ?_⟩
  · exact le_trans hm_le_third (le_trans Real.one_div_three_le_three_real hM_ge_three)
  · intro t ht_tail
    have ht_nonneg : 0 ≤ t := by
      have hcut_nonneg : 0 ≤ ‖w‖ / 2 :=
        div_nonneg (norm_nonneg w) Real.zero_le_two_real
      exact le_trans hcut_nonneg (le_of_lt ht_tail)
    have hnum_lower :
        w.re ≤ ‖w + (t : ℂ) * Complex.I‖ :=
      Complex.binetSecondFormula_arctan_tail_ratio_numerator_lower
        hw_re_pos t
    have hden_lower :
        w.re ≤ ‖w - (t : ℂ) * Complex.I‖ :=
      Complex.binetSecondFormula_arctan_tail_ratio_denominator_lower
        hw_re_pos t
    have hden_pos : 0 < ‖w - (t : ℂ) * Complex.I‖ :=
      lt_of_lt_of_le hw_re_pos hden_lower
    by_cases ht_bounded : t ≤ 2 * ‖w‖
    · have hnum_upper :
          ‖w + (t : ℂ) * Complex.I‖ ≤ 3 * ‖w‖ :=
        Complex.binetSecondFormula_arctan_tail_numerator_le_three_norm
          ht_nonneg ht_bounded
      have hden_upper :
          ‖w - (t : ℂ) * Complex.I‖ ≤ 3 * ‖w‖ :=
        Complex.binetSecondFormula_arctan_tail_denominator_le_three_norm
          ht_nonneg ht_bounded
      constructor
      · have hlower :
            w.re / (3 * ‖w‖) ≤
              ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ :=
          Real.div_le_div_of_le_of_le'
            hw_re_pos hden_const_pos hden_pos
            hden_upper hnum_lower
        calc
          m ≤ w.re / (3 * ‖w‖) := hm_le_bounded
          _ ≤ ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ := hlower
          _ = ‖(w + (t : ℂ) * Complex.I) /
                (w - (t : ℂ) * Complex.I)‖ := by
            exact (norm_div _ _).symm
      · have hupper :
            ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ ≤
              3 * ‖w‖ / w.re :=
          Real.div_le_div_of_le_of_le
            hw_re_pos (norm_nonneg _)
            hnum_upper hden_lower
        calc
          ‖(w + (t : ℂ) * Complex.I) /
              (w - (t : ℂ) * Complex.I)‖ =
              ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ := by
            exact norm_div _ _
          _ ≤ 3 * ‖w‖ / w.re := hupper
          _ ≤ M := hbounded_le_M
    · have ht_far : 2 * ‖w‖ ≤ t := le_of_not_ge ht_bounded
      rcases
          Complex.binetSecondFormula_arctan_tail_far_ratio_bounds
            (w := w) (t := t) ht_far with
        ⟨hnum_le, hden_le⟩
      constructor
      · have hthird :
            (1 / 3 : ℝ) ≤
              ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ := by
          have hmul :
              (1 / 3 : ℝ) *
                  ‖w - (t : ℂ) * Complex.I‖ ≤
                  (1 / 3 : ℝ) *
                    (3 * ‖w + (t : ℂ) * Complex.I‖) :=
            mul_le_mul_of_nonneg_left hden_le
              (div_nonneg zero_le_one (le_of_lt hthree_pos))
          have hmul' :
              (1 / 3 : ℝ) *
                  ‖w - (t : ℂ) * Complex.I‖ ≤
                  ‖w + (t : ℂ) * Complex.I‖ := by
            exact hmul.trans_eq (Real.one_div_three_mul_three_mul
              ‖w + (t : ℂ) * Complex.I‖)
          exact (le_div_iff₀ hden_pos).2 hmul'
        calc
          m ≤ (1 / 3 : ℝ) := hm_le_third
          _ ≤ ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ := hthird
          _ = ‖(w + (t : ℂ) * Complex.I) /
                (w - (t : ℂ) * Complex.I)‖ := by
            exact (norm_div _ _).symm
      · have hthree :
            ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ ≤ 3 := by
          exact (div_le_iff₀ hden_pos).2 hnum_le
        calc
          ‖(w + (t : ℂ) * Complex.I) /
              (w - (t : ℂ) * Complex.I)‖ =
              ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ := by
            exact norm_div _ _
          _ ≤ 3 := hthree
          _ ≤ M := hM_ge_three

/-- On the fixed upper split interval the Möbius ratio entering the arctangent
has norm bounded above and below by positive constants depending only on `w`.

This is the real-variable tail root: after rewriting the ratio as
`(w + tI) / (w - tI)`, it is a two-sided bound for a rational expression in
`t` on `t > ‖w‖ / 2`. -/
theorem Complex.binetSecondFormula_arctan_tail_ratio_norm_bounds
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ m M : ℝ,
      0 < m ∧
      m ≤ M ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          m ≤
            ‖(1 + ((t : ℂ) / w) * Complex.I) /
              (1 - ((t : ℂ) / w) * Complex.I)‖ ∧
          ‖(1 + ((t : ℂ) / w) * Complex.I) /
              (1 - ((t : ℂ) / w) * Complex.I)‖ ≤ M := by
  rcases
      Complex.binetSecondFormula_arctan_tail_ratio_norm_bounds_cleared
        hw_re_pos with
    ⟨m, M, hm_pos, hmM, hbounds⟩
  have hw_ne_zero : w ≠ 0 := by
    intro hw_zero
    cases hw_zero
    exact (lt_irrefl (0 : ℝ)) hw_re_pos
  refine ⟨m, M, hm_pos, hmM, ?_⟩
  intro t ht_tail
  have h := hbounds t ht_tail
  constructor
  · calc
      m ≤ ‖(w + (t : ℂ) * Complex.I) /
            (w - (t : ℂ) * Complex.I)‖ := h.1
      _ = ‖(1 + ((t : ℂ) / w) * Complex.I) /
            (1 - ((t : ℂ) / w) * Complex.I)‖ := by
        exact (Complex.binetSecondFormula_arctan_tail_ratio_eq_norm w hw_ne_zero t).symm
  · calc
      ‖(1 + ((t : ℂ) / w) * Complex.I) /
          (1 - ((t : ℂ) / w) * Complex.I)‖ =
          ‖(w + (t : ℂ) * Complex.I) /
            (w - (t : ℂ) * Complex.I)‖ := by
        exact Complex.binetSecondFormula_arctan_tail_ratio_eq_norm w hw_ne_zero t
      _ ≤ M := h.2

/-- Fixed-ray branch separation gives a uniform bound for the principal
arctangent on the upper split interval. -/
theorem Complex.binetSecondFormula_arctan_tail_log_ratio_bounded
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ L : ℝ,
      0 ≤ L ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          ‖Complex.log
            ((1 + ((t : ℂ) / w) * Complex.I) /
              (1 - ((t : ℂ) / w) * Complex.I))‖ ≤ L := by
  rcases
      Complex.binetSecondFormula_arctan_tail_ratio_norm_bounds
        hw_re_pos with
    ⟨m, M, hm_pos, hmM, hbounds⟩
  refine ⟨max |Real.log m| |Real.log M| + Real.pi, ?_, ?_⟩
  · exact add_nonneg (le_max_of_le_left (abs_nonneg _)) Real.pi_pos.le
  · intro t ht_tail
    rcases hbounds t ht_tail with ⟨hlower, hupper⟩
    exact
      Complex.log_norm_le_of_norm_bounds
        hm_pos hmM hlower hupper

/-- A uniform logarithm bound for the separated arctangent ratio bounds the
principal arctangent itself. -/
theorem Complex.binetSecondFormula_arctan_tail_bounded_of_log_ratio_bound
    {w : ℂ}
    (_hw_re_pos : 0 < w.re)
    (hlog :
      ∃ L : ℝ,
        0 ≤ L ∧
        ∀ t : ℝ,
          t ∈ Set.Ioi (‖w‖ / 2) →
            ‖Complex.log
              ((1 + ((t : ℂ) / w) * Complex.I) /
                (1 - ((t : ℂ) / w) * Complex.I))‖ ≤ L) :
    ∃ B : ℝ,
      0 ≤ B ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          ‖Complex.arctan ((t : ℂ) / w)‖ ≤ B := by
  rcases hlog with ⟨L, hL_nonneg, hL⟩
  refine ⟨L, hL_nonneg, ?_⟩
  intro t ht_tail
  let z : ℂ := (t : ℂ) / w
  have hfactor_norm_le_one : ‖(-Complex.I / 2 : ℂ)‖ ≤ (1 : ℝ) :=
    Complex.norm_neg_I_div_two_le_one
  have hmul :
      ‖(-Complex.I / 2 : ℂ) *
          Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ ≤
        ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ := by
    calc
      ‖(-Complex.I / 2 : ℂ) *
          Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ ≤
          ‖(-Complex.I / 2 : ℂ)‖ *
            ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ :=
        norm_mul_le _ _
      _ ≤ 1 *
            ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ :=
        mul_le_mul_of_nonneg_right hfactor_norm_le_one (norm_nonneg _)
      _ = ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ := by
        exact one_mul _
  calc
    ‖Complex.arctan ((t : ℂ) / w)‖ =
        ‖(-Complex.I / 2 : ℂ) *
          Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ := by
      exact congrArg norm (Complex.binetSecondFormula_arctan_tail_expr_eq w t)
    _ ≤ ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ := hmul
    _ ≤ L := hL t ht_tail

/-- Fixed-ray branch separation gives a uniform bound for the principal
arctangent on the upper split interval. -/
theorem Complex.binetSecondFormula_arctan_tail_bounded_of_branch_separation
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ B : ℝ,
      0 ≤ B ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          ‖Complex.arctan ((t : ℂ) / w)‖ ≤ B := by
  exact
    Complex.binetSecondFormula_arctan_tail_bounded_of_log_ratio_bound
      hw_re_pos
      (Complex.binetSecondFormula_arctan_tail_log_ratio_bounded
        hw_re_pos)

/-- A uniform arctangent bound on the upper split interval becomes a linear
bound because the split cutoff is strictly positive in the open right
half-plane. -/
theorem Complex.binetSecondFormula_arctan_tail_linear_bound_of_bounded
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (hbounded :
      ∃ B : ℝ,
        0 ≤ B ∧
        ∀ t : ℝ,
          t ∈ Set.Ioi (‖w‖ / 2) →
            ‖Complex.arctan ((t : ℂ) / w)‖ ≤ B) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          ‖Complex.arctan ((t : ℂ) / w)‖ ≤ C * t := by
  rcases hbounded with ⟨B, hB_nonneg, hB⟩
  have hw_ne_zero : w ≠ 0 := by
    intro hw_zero
    cases hw_zero
    exact (lt_irrefl (0 : ℝ)) hw_re_pos
  have hw_norm_pos : 0 < ‖w‖ :=
    norm_pos_iff.mpr hw_ne_zero
  let C : ℝ := 2 * B / ‖w‖
  have hC_nonneg : 0 ≤ C :=
    div_nonneg (mul_nonneg Real.zero_le_two_real hB_nonneg)
      (le_of_lt hw_norm_pos)
  refine ⟨C, hC_nonneg, ?_⟩
  intro t ht_tail
  have ht_lower : ‖w‖ / 2 ≤ t :=
    le_of_lt ht_tail
  have hC_mul_lower : B ≤ C * t := by
    have hmul :
        B ≤ C * (‖w‖ / 2) := by
      calc
        B = (2 * B / ‖w‖) * (‖w‖ / 2) :=
          (Real.two_mul_div_mul_half_eq
            (B := B) (r := ‖w‖) hw_norm_pos.ne').symm
        _ = C * (‖w‖ / 2) := rfl
        _ ≤ C * (‖w‖ / 2) := le_rfl
    have hC_mul_mono :
        C * (‖w‖ / 2) ≤ C * t :=
      mul_le_mul_of_nonneg_left ht_lower hC_nonneg
    exact le_trans hmul hC_mul_mono
  exact le_trans (hB t ht_tail) hC_mul_lower

/-- Along the fixed open-half-plane ray `t / w`, the principal arctangent is
linearly bounded on the upper split interval. -/
theorem Complex.binetSecondFormula_arctan_tail_linear_bound
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          ‖Complex.arctan ((t : ℂ) / w)‖ ≤ C * t := by
  exact
    Complex.binetSecondFormula_arctan_tail_linear_bound_of_bounded
      hw_re_pos
      (Complex.binetSecondFormula_arctan_tail_bounded_of_branch_separation
        hw_re_pos)

/-- On a fixed separated wedge, the arctangent ratio has two-sided norm
bounds independent of the scale of `w`. -/
theorem Complex.binetSecondFormula_arctan_tail_ratio_norm_bounds_sectorSeparated
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ m M : ℝ,
      0 < m ∧
      m ≤ M ∧
      ∀ w : ℂ,
        0 < w.re →
          ε ≤ w.re / ‖w‖ →
          ∀ t : ℝ,
            t ∈ Set.Ioi (‖w‖ / 2) →
              m ≤
                ‖(1 + ((t : ℂ) / w) * Complex.I) /
                  (1 - ((t : ℂ) / w) * Complex.I)‖ ∧
              ‖(1 + ((t : ℂ) / w) * Complex.I) /
                  (1 - ((t : ℂ) / w) * Complex.I)‖ ≤ M := by
  let m : ℝ := min (ε / 3) (1 / 3)
  let M : ℝ := max (3 / ε) 3
  have hthree_pos : (0 : ℝ) < 3 := Real.zero_lt_three
  have hm_pos : 0 < m := by
    show 0 < min (ε / 3) (1 / 3)
    exact
      lt_min
        (div_pos hε hthree_pos)
        (div_pos zero_lt_one hthree_pos)
  have hM_ge_three : 3 ≤ M := by
    show 3 ≤ max (3 / ε) 3
    exact le_max_right _ _
  have hm_le_eps_third : m ≤ ε / 3 := by
    show min (ε / 3) (1 / 3) ≤ ε / 3
    exact min_le_left _ _
  have hm_le_third : m ≤ (1 / 3 : ℝ) := by
    show min (ε / 3) (1 / 3) ≤ (1 / 3 : ℝ)
    exact min_le_right _ _
  have hthree_div_eps_le_M : 3 / ε ≤ M := by
    show 3 / ε ≤ max (3 / ε) 3
    exact le_max_left _ _
  refine ⟨m, M, hm_pos, ?_, ?_⟩
  · exact le_trans hm_le_third (le_trans Real.one_div_three_le_three_real hM_ge_three)
  · intro w hw_re_pos hw_sep t ht_tail
    have hw_ne_zero : w ≠ 0 := by
      intro hw_zero
      cases hw_zero
      exact (lt_irrefl (0 : ℝ)) hw_re_pos
    have hw_norm_pos : 0 < ‖w‖ :=
      Complex.norm_pos_of_re_pos hw_re_pos
    have ht_nonneg : 0 ≤ t := by
      have hcut_nonneg : 0 ≤ ‖w‖ / 2 :=
        div_nonneg (norm_nonneg w) Real.zero_le_two_real
      exact le_trans hcut_nonneg (le_of_lt ht_tail)
    have hnum_lower :
        w.re ≤ ‖w + (t : ℂ) * Complex.I‖ :=
      Complex.binetSecondFormula_arctan_tail_ratio_numerator_lower
        hw_re_pos t
    have hden_lower :
        w.re ≤ ‖w - (t : ℂ) * Complex.I‖ :=
      Complex.binetSecondFormula_arctan_tail_ratio_denominator_lower
        hw_re_pos t
    have hden_pos : 0 < ‖w - (t : ℂ) * Complex.I‖ :=
      lt_of_lt_of_le hw_re_pos hden_lower
    have hsep_mul : ε * ‖w‖ ≤ w.re :=
      Complex.sep_mul_le_re hw_re_pos hw_sep
    have heps_third_lower :
        ε / 3 ≤ w.re / (3 * ‖w‖) := by
      have hden_pos : 0 < 3 * ‖w‖ :=
        mul_pos hthree_pos hw_norm_pos
      exact (div_le_div_iff₀ hthree_pos hden_pos).2
        (calc
        ε * (3 * ‖w‖) = 3 * (ε * ‖w‖) := by
          exact Real.mul_three_mul_reassoc ε ‖w‖
        _ ≤ 3 * w.re :=
          mul_le_mul_of_nonneg_left hsep_mul (le_of_lt hthree_pos)
        _ = w.re * 3 := by
          exact mul_comm 3 w.re)
    have hbounded_upper_const :
        3 * ‖w‖ / w.re ≤ 3 / ε := by
      exact (div_le_div_iff₀ hw_re_pos hε).2
        (calc
        3 * ‖w‖ * ε = 3 * (ε * ‖w‖) := by
          exact Real.three_mul_mul_reassoc ε ‖w‖
        _ ≤ 3 * w.re :=
          mul_le_mul_of_nonneg_left hsep_mul (le_of_lt hthree_pos))
    by_cases ht_bounded : t ≤ 2 * ‖w‖
    · have hnum_upper :
          ‖w + (t : ℂ) * Complex.I‖ ≤ 3 * ‖w‖ :=
        Complex.binetSecondFormula_arctan_tail_numerator_le_three_norm
          ht_nonneg ht_bounded
      have hden_upper :
          ‖w - (t : ℂ) * Complex.I‖ ≤ 3 * ‖w‖ :=
        Complex.binetSecondFormula_arctan_tail_denominator_le_three_norm
          ht_nonneg ht_bounded
      constructor
      · have hden_const_pos : 0 < 3 * ‖w‖ :=
          mul_pos hthree_pos hw_norm_pos
        have hlower :
            w.re / (3 * ‖w‖) ≤
              ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ :=
          Real.div_le_div_of_le_of_le'
            hw_re_pos hden_const_pos hden_pos
            hden_upper hnum_lower
        calc
          m ≤ ε / 3 := hm_le_eps_third
          _ ≤ w.re / (3 * ‖w‖) := heps_third_lower
          _ ≤ ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ := hlower
          _ = ‖(1 + ((t : ℂ) / w) * Complex.I) /
                (1 - ((t : ℂ) / w) * Complex.I)‖ := by
            exact (norm_div _ _).symm.trans
              (Complex.binetSecondFormula_arctan_tail_ratio_eq_norm w hw_ne_zero t).symm
      · have hupper :
            ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ ≤
              3 * ‖w‖ / w.re :=
          Real.div_le_div_of_le_of_le
            hw_re_pos (norm_nonneg _)
            hnum_upper hden_lower
        calc
          ‖(1 + ((t : ℂ) / w) * Complex.I) /
              (1 - ((t : ℂ) / w) * Complex.I)‖ =
              ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ := by
            exact (Complex.binetSecondFormula_arctan_tail_ratio_eq_norm w hw_ne_zero t).trans
              (norm_div _ _)
          _ ≤ 3 * ‖w‖ / w.re := hupper
          _ ≤ 3 / ε := hbounded_upper_const
          _ ≤ M := hthree_div_eps_le_M
    · have ht_far : 2 * ‖w‖ ≤ t := le_of_not_ge ht_bounded
      rcases
          Complex.binetSecondFormula_arctan_tail_far_ratio_bounds
            (w := w) (t := t) ht_far with
        ⟨hnum_le, hden_le⟩
      constructor
      · have hthird :
            (1 / 3 : ℝ) ≤
              ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ := by
          have hmul :
              (1 / 3 : ℝ) *
                  ‖w - (t : ℂ) * Complex.I‖ ≤
                  (1 / 3 : ℝ) *
                    (3 * ‖w + (t : ℂ) * Complex.I‖) :=
            mul_le_mul_of_nonneg_left hden_le
              (div_nonneg zero_le_one (le_of_lt hthree_pos))
          have hmul' :
              (1 / 3 : ℝ) *
                  ‖w - (t : ℂ) * Complex.I‖ ≤
                  ‖w + (t : ℂ) * Complex.I‖ :=
            hmul.trans_eq
              (Real.one_div_three_mul_three_mul
                ‖w + (t : ℂ) * Complex.I‖)
          exact (le_div_iff₀ hden_pos).2 hmul'
        calc
          m ≤ (1 / 3 : ℝ) := hm_le_third
          _ ≤ ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ := hthird
          _ = ‖(1 + ((t : ℂ) / w) * Complex.I) /
                (1 - ((t : ℂ) / w) * Complex.I)‖ := by
            exact (norm_div _ _).symm.trans
              (Complex.binetSecondFormula_arctan_tail_ratio_eq_norm w hw_ne_zero t).symm
      · have hthree :
            ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ ≤ 3 := by
          exact (div_le_iff₀ hden_pos).2 hnum_le
        calc
          ‖(1 + ((t : ℂ) / w) * Complex.I) /
              (1 - ((t : ℂ) / w) * Complex.I)‖ =
              ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ := by
            exact (Complex.binetSecondFormula_arctan_tail_ratio_eq_norm w hw_ne_zero t).trans
              (norm_div _ _)
          _ ≤ 3 := hthree
          _ ≤ M := hM_ge_three

/-- On a fixed separated wedge, the principal arctangent is bounded uniformly
on the upper split interval, independently of the scale of `w`. -/
theorem Complex.binetSecondFormula_arctan_tail_bounded_sectorSeparated
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ B : ℝ,
      0 ≤ B ∧
      ∀ w : ℂ,
        0 < w.re →
          ε ≤ w.re / ‖w‖ →
          ∀ t : ℝ,
            t ∈ Set.Ioi (‖w‖ / 2) →
              ‖Complex.arctan ((t : ℂ) / w)‖ ≤ B := by
  rcases
      Complex.binetSecondFormula_arctan_tail_ratio_norm_bounds_sectorSeparated
        ε hε with
    ⟨m, M, hm_pos, hmM, hbounds⟩
  let B : ℝ := max |Real.log m| |Real.log M| + Real.pi
  have hB_nonneg : 0 ≤ B :=
    add_nonneg (le_max_of_le_left (abs_nonneg _)) Real.pi_pos.le
  refine ⟨B, hB_nonneg, ?_⟩
  intro w hw_re_pos hw_sep t ht_tail
  let z : ℂ := (t : ℂ) / w
  rcases hbounds w hw_re_pos hw_sep t ht_tail with ⟨hlower, hupper⟩
  have hlog :
      ‖Complex.log
        ((1 + z * Complex.I) / (1 - z * Complex.I))‖ ≤ B :=
    Complex.log_norm_le_of_norm_bounds hm_pos hmM hlower hupper
  have hfactor_norm_le_one : ‖(-Complex.I / 2 : ℂ)‖ ≤ (1 : ℝ) := by
    exact Complex.norm_neg_I_div_two_le_one
  have hmul :
      ‖(-Complex.I / 2 : ℂ) *
          Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ ≤
        ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ := by
    calc
      ‖(-Complex.I / 2 : ℂ) *
          Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ ≤
          ‖(-Complex.I / 2 : ℂ)‖ *
            ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ :=
        norm_mul_le _ _
      _ ≤ 1 *
            ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ :=
        mul_le_mul_of_nonneg_right hfactor_norm_le_one (norm_nonneg _)
      _ = ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ :=
        one_mul _
  calc
    ‖Complex.arctan ((t : ℂ) / w)‖ =
        ‖(-Complex.I / 2 : ℂ) *
          Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ := by
      exact congrArg norm (Complex.binetSecondFormula_arctan_tail_expr_eq w t)
    _ ≤ ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ := hmul
    _ ≤ B := hlog

/-- Uniform arctangent tail linear bound on a fixed wedge of the open
right half-plane.

The constant depends only on the wedge separation parameter `ε`, not on the
particular point `w`.  This is the sector-uniform replacement for the
fixed-`w` tail constant in `Complex.binetSecondFormula_arctan_tail_linear_bound`.
The large-radius hypothesis is necessary because the conclusion is linear in
the unscaled variable `t`.
-/
theorem Complex.binetSecondFormula_arctan_tail_linear_bound_sectorSeparated
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ w : ℂ,
        0 < w.re →
          ε ≤ w.re / ‖w‖ →
          1 ≤ ‖w‖ →
          ∀ t : ℝ,
            t ∈ Set.Ioi (‖w‖ / 2) →
              ‖Complex.arctan ((t : ℂ) / w)‖ ≤ C * t := by
  rcases
      Complex.binetSecondFormula_arctan_tail_bounded_sectorSeparated
        ε hε with
    ⟨B, hB_nonneg, hB⟩
  refine ⟨2 * B, mul_nonneg Real.zero_le_two_real hB_nonneg, ?_⟩
  intro w hw_re_pos hw_sep hw_large t ht_tail
  have ht_lower : (1 / 2 : ℝ) ≤ t := by
    calc
      (1 / 2 : ℝ) ≤ ‖w‖ / 2 :=
        div_le_div_of_nonneg_right hw_large Real.zero_le_two_real
      _ ≤ t := le_of_lt ht_tail
  have hB_le : B ≤ (2 * B) * t := by
    have hB_eq : B = (2 * B) * (1 / 2 : ℝ) :=
      Real.eq_two_mul_mul_half B
    calc
      B = (2 * B) * (1 / 2 : ℝ) := hB_eq
      _ ≤ (2 * B) * t :=
        mul_le_mul_of_nonneg_left ht_lower
          (mul_nonneg Real.zero_le_two_real hB_nonneg)
  exact le_trans (hB w hw_re_pos hw_sep t ht_tail) hB_le

/-- The Binet kernel is integrable on the lower split interval. -/
theorem Complex.binetSecondFormula_kernel_integrableOn_small_interval
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    IntegrableOn
      (fun t : ℝ =>
        Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
      (Set.Ioc (0 : ℝ) (‖w‖ / 2)) := by
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  let M : ℝ → ℝ := fun t : ℝ =>
    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  let c : ℝ := 2 / ‖w‖
  have hw_ne_zero : w ≠ 0 := by
    intro hw_zero
    cases hw_zero
    exact (lt_irrefl (0 : ℝ)) hw_re_pos
  have hw_norm_pos : 0 < ‖w‖ :=
    norm_pos_iff.mpr hw_ne_zero
  have hM_integrable_Ioi : IntegrableOn M (Set.Ioi (0 : ℝ)) :=
    Real.binetSecondFormula_kernel_majorant_integrableOn
  have hcM_integrable :
      Integrable (fun t : ℝ => c * M t)
        (volume.restrict (Set.Ioc (0 : ℝ) (‖w‖ / 2))) :=
    (hM_integrable_Ioi.mono_set Ioc_subset_Ioi_self).const_mul c
  have hK_meas :
      AEStronglyMeasurable K
        (volume.restrict (Set.Ioc (0 : ℝ) (‖w‖ / 2))) := by
    have hmeas : Measurable K :=
      Complex.measurable_binetSecondFormula_kernel w
    exact hmeas.aestronglyMeasurable
  have hpointwise :
      ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) (‖w‖ / 2)),
        ‖K t‖ ≤ c * M t :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun t ht => by
        have hkernel :
            ‖K t‖ ≤
              (2 * (t / ‖w‖)) /
                (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
          Complex.binetSecondFormula_kernel_norm_le_on_small_interval
            hw_re_pos ht
        have hrewrite :
            (2 * (t / ‖w‖)) /
                (Real.exp ((2 : ℝ) * Real.pi * t) - 1) =
              c * M t := by
          show
            (2 * (t / ‖w‖)) /
                (Real.exp ((2 : ℝ) * Real.pi * t) - 1) =
              (2 / ‖w‖) *
                (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
          exact Real.two_mul_div_norm_div_exp_sub_one_eq t ‖w‖
        exact hrewrite ▸ hkernel)
  exact
    hcM_integrable.mono' hK_meas hpointwise

/-- Tail pointwise domination for the Binet kernel on the open right
half-plane after the split at `‖w‖ / 2`, with a constant depending on the
fixed open-half-plane point `w`.

The uniform constant `(2 / ‖w‖)` is false pointwise near the principal
arctangent singularity on rays approaching the imaginary axis. -/
theorem Complex.binetSecondFormula_kernel_tail_norm_le_majorant
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          ‖Complex.arctan ((t : ℂ) / w) /
              (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
            C *
              (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  rcases
      Complex.binetSecondFormula_arctan_tail_linear_bound
        hw_re_pos with
    ⟨C, hC_nonneg, harctan_bound⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro t ht_tail
  have ht_pos : 0 < t :=
    lt_of_le_of_lt
      (div_nonneg (norm_nonneg w) Real.zero_le_two_real)
      ht_tail
  have hden_norm :=
    Complex.exp_tail_denominator_norm_eq t ht_pos
  have hden_nonneg :
      0 ≤ Real.exp ((2 : ℝ) * Real.pi * t) - 1 :=
    le_of_lt (Real.binetSecondFormula_exp_denominator_pos ht_pos)
  have harctan :
      ‖Complex.arctan ((t : ℂ) / w)‖ ≤ C * t :=
    harctan_bound t ht_tail
  calc
    ‖Complex.arctan ((t : ℂ) / w) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ =
        ‖Complex.arctan ((t : ℂ) / w)‖ /
          ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ := by
      exact norm_div _ _
    _ =
        ‖Complex.arctan ((t : ℂ) / w)‖ /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
      exact congrArg
        (fun d : ℝ => ‖Complex.arctan ((t : ℂ) / w)‖ / d)
        hden_norm
    _ ≤ (C * t) /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
      div_le_div_of_nonneg_right harctan hden_nonneg
    _ =
        C * (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
      exact mul_div_assoc C t (Real.exp ((2 : ℝ) * Real.pi * t) - 1)

/-- Uniform tail pointwise domination for the Binet kernel on a fixed wedge.

This is the sector-uniform version of
`Complex.binetSecondFormula_kernel_tail_norm_le_majorant`; the constant depends
only on `ε`. -/
theorem Complex.binetSecondFormula_kernel_tail_norm_le_majorant_sectorSeparated
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ w : ℂ,
        0 < w.re →
          ε ≤ w.re / ‖w‖ →
          1 ≤ ‖w‖ →
          ∀ t : ℝ,
            t ∈ Set.Ioi (‖w‖ / 2) →
              ‖Complex.arctan ((t : ℂ) / w) /
                  (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
                C *
                  (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  rcases
      Complex.binetSecondFormula_arctan_tail_linear_bound_sectorSeparated
        ε hε with
    ⟨C, hC_nonneg, harctan_bound⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro w hw_re_pos hw_sep hw_large t ht_tail
  have ht_pos : 0 < t :=
    lt_of_le_of_lt
      (div_nonneg (norm_nonneg w) Real.zero_le_two_real)
      ht_tail
  have hden_norm :=
    Complex.exp_tail_denominator_norm_eq t ht_pos
  have hden_nonneg :
      0 ≤ Real.exp ((2 : ℝ) * Real.pi * t) - 1 :=
    le_of_lt (Real.binetSecondFormula_exp_denominator_pos ht_pos)
  have harctan :
      ‖Complex.arctan ((t : ℂ) / w)‖ ≤ C * t :=
    harctan_bound w hw_re_pos hw_sep hw_large t ht_tail
  calc
    ‖Complex.arctan ((t : ℂ) / w) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ =
        ‖Complex.arctan ((t : ℂ) / w)‖ /
          ‖Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1‖ := by
      exact norm_div _ _
    _ =
        ‖Complex.arctan ((t : ℂ) / w)‖ /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
      exact congrArg
        (fun d : ℝ => ‖Complex.arctan ((t : ℂ) / w)‖ / d)
        hden_norm
    _ ≤ (C * t) /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
      div_le_div_of_nonneg_right harctan hden_nonneg
    _ =
        C * (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
      exact mul_div_assoc C t (Real.exp ((2 : ℝ) * Real.pi * t) - 1)

/-- The Binet kernel is integrable on the upper split interval. -/
theorem Complex.binetSecondFormula_kernel_integrableOn_tail_interval
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    IntegrableOn
      (fun t : ℝ =>
        Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
      (Set.Ioi (‖w‖ / 2)) := by
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  let M : ℝ → ℝ := fun t : ℝ =>
    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  rcases
      Complex.binetSecondFormula_kernel_tail_norm_le_majorant
        hw_re_pos with
    ⟨c, hc_nonneg, htail_bound⟩
  have hM_integrable_Ioi : IntegrableOn M (Set.Ioi (0 : ℝ)) :=
    Real.binetSecondFormula_kernel_majorant_integrableOn
  have hcut_nonneg : (0 : ℝ) ≤ ‖w‖ / 2 :=
    div_nonneg (norm_nonneg w) Real.zero_le_two_real
  have hcM_integrable :
      Integrable (fun t : ℝ => c * M t)
        (volume.restrict (Set.Ioi (‖w‖ / 2))) :=
    (hM_integrable_Ioi.mono_set (Ioi_subset_Ioi hcut_nonneg)).const_mul c
  have hK_meas :
      AEStronglyMeasurable K
        (volume.restrict (Set.Ioi (‖w‖ / 2))) := by
    have hmeas : Measurable K :=
      Complex.measurable_binetSecondFormula_kernel w
    exact hmeas.aestronglyMeasurable
  have hpointwise :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (‖w‖ / 2)),
        ‖K t‖ ≤ c * M t :=
    (ae_restrict_mem measurableSet_Ioi).mono
      (fun t ht => htail_bound t ht)
  exact
    hcM_integrable.mono' hK_meas hpointwise

/-- The complex Binet kernel is integrable on the positive half-line in the
open right half-plane. -/
theorem Complex.binetSecondFormula_kernel_integrableOn_Ioi_openRightHalfPlane
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    IntegrableOn
      (fun t : ℝ =>
        Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1))
      (Set.Ioi (0 : ℝ)) := by
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  have hcut_nonneg : (0 : ℝ) ≤ ‖w‖ / 2 :=
    div_nonneg (norm_nonneg w) Real.zero_le_two_real
  have hsmall : IntegrableOn K (Set.Ioc (0 : ℝ) (‖w‖ / 2)) :=
    Complex.binetSecondFormula_kernel_integrableOn_small_interval
      hw_re_pos
  have htail : IntegrableOn K (Set.Ioi (‖w‖ / 2)) :=
    Complex.binetSecondFormula_kernel_integrableOn_tail_interval
      hw_re_pos
  have hunion :
      Set.Ioc (0 : ℝ) (‖w‖ / 2) ∪ Set.Ioi (‖w‖ / 2) =
        Set.Ioi (0 : ℝ) :=
    Set.Ioc_union_Ioi_eq_Ioi hcut_nonneg
  exact
    hunion ▸ hsmall.union htail

/-- The Binet remainder integral splits at `‖w‖ / 2` into its small-argument
and tail pieces. -/
theorem Complex.binetSecondFormulaRemainder_eq_small_add_tail
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    Complex.binetSecondFormulaRemainder w =
      (2 * ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)) +
        (2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)) := by
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  have hK_integrable_Ioi : IntegrableOn K (Set.Ioi (0 : ℝ)) :=
    Complex.binetSecondFormula_kernel_integrableOn_Ioi_openRightHalfPlane
      hw_re_pos
  have hcut_nonneg : (0 : ℝ) ≤ ‖w‖ / 2 :=
    div_nonneg (norm_nonneg w) Real.zero_le_two_real
  have hsmall_integrable :
      IntegrableOn K (Set.Ioc (0 : ℝ) (‖w‖ / 2)) :=
    hK_integrable_Ioi.mono_set Ioc_subset_Ioi_self
  have htail_integrable :
      IntegrableOn K (Set.Ioi (‖w‖ / 2)) :=
    hK_integrable_Ioi.mono_set (Ioi_subset_Ioi hcut_nonneg)
  have hsplit :
      ∫ t : ℝ in Set.Ioi (0 : ℝ), K t =
        (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t) +
          (∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t) := by
    have hunion :
        Set.Ioc (0 : ℝ) (‖w‖ / 2) ∪ Set.Ioi (‖w‖ / 2) =
          Set.Ioi (0 : ℝ) :=
      Set.Ioc_union_Ioi_eq_Ioi hcut_nonneg
    have hdisjoint :
        Disjoint (Set.Ioc (0 : ℝ) (‖w‖ / 2))
          (Set.Ioi (‖w‖ / 2)) :=
      Ioc_disjoint_Ioi le_rfl
    calc
      ∫ t : ℝ in Set.Ioi (0 : ℝ), K t =
          ∫ t : ℝ in
            Set.Ioc (0 : ℝ) (‖w‖ / 2) ∪ Set.Ioi (‖w‖ / 2), K t := by
        exact
          congrArg
            (fun s : Set ℝ => ∫ t : ℝ in s, K t)
            hunion.symm
      _ =
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t) +
            (∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t) := by
        change
          ∫ t : ℝ in
              Set.Ioc (0 : ℝ) (‖w‖ / 2) ∪ Set.Ioi (‖w‖ / 2), K t ∂volume =
            ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t ∂volume +
              ∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t ∂volume
        exact
          setIntegral_union hdisjoint measurableSet_Ioi
            hsmall_integrable htail_integrable
  calc
    Complex.binetSecondFormulaRemainder w =
        2 * ∫ t : ℝ in Set.Ioi (0 : ℝ), K t := by
      rfl
    _ =
        2 *
            ((∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t) +
              (∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t)) := by
      exact congrArg (fun z : ℂ => 2 * z) hsplit
    _ =
        (2 * ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t) +
          (2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t) := by
      exact
        Complex.two_mul_add_eq_add_two_mul
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t)
          (∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t)

/-- Small-argument part of the Binet remainder integral, where the principal
arctangent is controlled by its power-series disk estimate. -/
theorem Complex.binetSecondFormulaRemainder_small_norm_le_integral_majorant
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ‖2 * ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
        Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
      4 *
        (∫ t : ℝ in Set.Ioi (0 : ℝ),
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) / ‖w‖ := by
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  let M : ℝ → ℝ := fun t : ℝ =>
    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  let c : ℝ := 2 / ‖w‖
  have hw_ne_zero : w ≠ 0 := by
    intro hw_zero
    cases hw_zero
    exact (lt_irrefl (0 : ℝ)) hw_re_pos
  have hw_norm_pos : 0 < ‖w‖ :=
    norm_pos_iff.mpr hw_ne_zero
  have hc_nonneg : 0 ≤ c :=
    div_nonneg Real.zero_le_two_real (le_of_lt hw_norm_pos)
  have hM_integrable_Ioi : IntegrableOn M (Set.Ioi (0 : ℝ)) :=
    Real.binetSecondFormula_kernel_majorant_integrableOn
  have hcM_integrable_Ioc :
      Integrable (fun t : ℝ => c * M t)
        (volume.restrict (Set.Ioc (0 : ℝ) (‖w‖ / 2))) :=
    (hM_integrable_Ioi.mono_set Ioc_subset_Ioi_self).const_mul c
  have hpointwise :
      ∀ᵐ t ∂volume.restrict (Set.Ioc (0 : ℝ) (‖w‖ / 2)),
        ‖K t‖ ≤ c * M t :=
    (ae_restrict_mem measurableSet_Ioc).mono
      (fun t ht => by
        have hkernel :
            ‖K t‖ ≤
              (2 * (t / ‖w‖)) /
                (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
          Complex.binetSecondFormula_kernel_norm_le_on_small_interval
            hw_re_pos ht
        have hrewrite :
            (2 * (t / ‖w‖)) /
                (Real.exp ((2 : ℝ) * Real.pi * t) - 1) =
              c * M t := by
          show
            (2 * (t / ‖w‖)) /
                (Real.exp ((2 : ℝ) * Real.pi * t) - 1) =
              (2 / ‖w‖) *
                (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
          exact Real.two_mul_div_norm_div_exp_sub_one_eq t ‖w‖
        exact hrewrite ▸ hkernel)
  have hnorm_integral :
      ‖∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t‖ ≤
        ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), c * M t :=
    norm_integral_le_of_norm_le hcM_integrable_Ioc hpointwise
  have hmono :
      ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), M t ≤
        ∫ t : ℝ in Set.Ioi (0 : ℝ), M t :=
    setIntegral_mono_set hM_integrable_Ioi
      ((ae_restrict_mem measurableSet_Ioi).mono
        (fun t ht => Real.binetSecondFormula_kernel_majorant_nonneg_on_Ioi t ht))
      (Filter.Eventually.of_forall (fun t ht => ht.1))
  have hscaled_mono :
      ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), c * M t ≤
        c * ∫ t : ℝ in Set.Ioi (0 : ℝ), M t := by
    calc
      ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), c * M t =
          c * ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), M t := by
        exact MeasureTheory.integral_mul_left c M
      _ ≤ c * ∫ t : ℝ in Set.Ioi (0 : ℝ), M t :=
        mul_le_mul_of_nonneg_left hmono hc_nonneg
  calc
    ‖2 * ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t‖ =
        2 * ‖∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t‖ := by
      exact
        Eq.trans (norm_mul (2 : ℂ)
          (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t))
          (congrArg
            (fun r : ℝ =>
              r * ‖∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t‖)
            (Complex.norm_natCast 2))
    _ ≤ 2 * (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), c * M t) :=
      mul_le_mul_of_nonneg_left hnorm_integral Real.zero_le_two_real
    _ ≤ 2 * (c * ∫ t : ℝ in Set.Ioi (0 : ℝ), M t) :=
      mul_le_mul_of_nonneg_left hscaled_mono Real.zero_le_two_real
    _ =
        4 *
          (∫ t : ℝ in Set.Ioi (0 : ℝ), M t) / ‖w‖ := by
      show
        2 * ((2 / ‖w‖) *
            ∫ t : ℝ in Set.Ioi (0 : ℝ), M t) =
          4 * (∫ t : ℝ in Set.Ioi (0 : ℝ), M t) / ‖w‖
      exact
        Real.two_mul_two_div_mul_eq_four_mul_div
          (∫ t : ℝ in Set.Ioi (0 : ℝ), M t) ‖w‖

/-- Tail part of the Binet remainder integral.  This is where one uses the
principal-branch arctangent bound away from the branch singularities together
with the exponential denominator. -/
theorem Complex.binetSecondFormulaRemainder_tail_norm_le_fixed_majorant
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ‖2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
        2 * C *
          (∫ t : ℝ in Set.Ioi (0 : ℝ),
            t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  let M : ℝ → ℝ := fun t : ℝ =>
    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  rcases
      Complex.binetSecondFormula_kernel_tail_norm_le_majorant
        hw_re_pos with
    ⟨C, hC_nonneg, htail_bound⟩
  refine ⟨C, hC_nonneg, ?_⟩
  have hM_integrable_Ioi : IntegrableOn M (Set.Ioi (0 : ℝ)) :=
    Real.binetSecondFormula_kernel_majorant_integrableOn
  have hcut_nonneg : (0 : ℝ) ≤ ‖w‖ / 2 :=
    div_nonneg (norm_nonneg w) Real.zero_le_two_real
  have hCM_integrable_tail :
      Integrable (fun t : ℝ => C * M t)
        (volume.restrict (Set.Ioi (‖w‖ / 2))) :=
    (hM_integrable_Ioi.mono_set (Ioi_subset_Ioi hcut_nonneg)).const_mul C
  have hpointwise :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (‖w‖ / 2)),
        ‖K t‖ ≤ C * M t :=
    (ae_restrict_mem measurableSet_Ioi).mono
      (fun t ht => htail_bound t ht)
  have hnorm_integral :
      ‖∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t‖ ≤
        ∫ t : ℝ in Set.Ioi (‖w‖ / 2), C * M t :=
    norm_integral_le_of_norm_le hCM_integrable_tail hpointwise
  have hmono :
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2), M t ≤
        ∫ t : ℝ in Set.Ioi (0 : ℝ), M t :=
    setIntegral_mono_set hM_integrable_Ioi
      ((ae_restrict_mem measurableSet_Ioi).mono
        (fun t ht => Real.binetSecondFormula_kernel_majorant_nonneg_on_Ioi t ht))
      (Filter.Eventually.of_forall (fun t ht => lt_of_le_of_lt hcut_nonneg ht))
  have hscaled_mono :
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2), C * M t ≤
        C * ∫ t : ℝ in Set.Ioi (0 : ℝ), M t := by
    calc
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2), C * M t =
          C * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), M t := by
        exact MeasureTheory.integral_mul_left C M
      _ ≤ C * ∫ t : ℝ in Set.Ioi (0 : ℝ), M t :=
        mul_le_mul_of_nonneg_left hmono hC_nonneg
  calc
    ‖2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t‖ =
        2 * ‖∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t‖ := by
      exact
        Eq.trans (norm_mul (2 : ℂ)
          (∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t))
          (congrArg
            (fun r : ℝ =>
              r * ‖∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t‖)
            (Complex.norm_natCast 2))
    _ ≤ 2 * (∫ t : ℝ in Set.Ioi (‖w‖ / 2), C * M t) :=
      mul_le_mul_of_nonneg_left hnorm_integral Real.zero_le_two_real
    _ ≤ 2 * (C * ∫ t : ℝ in Set.Ioi (0 : ℝ), M t) :=
      mul_le_mul_of_nonneg_left hscaled_mono Real.zero_le_two_real
    _ = 2 * C * (∫ t : ℝ in Set.Ioi (0 : ℝ), M t) := by
      exact (mul_assoc _ _ _).symm

/-- Tail part of the Binet remainder integral, in the honest fixed-`w`
form supplied by the tail pointwise majorant. -/
theorem Complex.binetSecondFormulaRemainder_tail_norm_le_integral_majorant
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ‖2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
        2 * C *
          (∫ t : ℝ in Set.Ioi (0 : ℝ),
            t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  exact
    Complex.binetSecondFormulaRemainder_tail_norm_le_fixed_majorant
      hw_re_pos

/-- Tail part of the Binet remainder integral with a constant uniform on a
fixed wedge of the open right half-plane. -/
theorem Complex.binetSecondFormulaRemainder_tail_norm_le_sectorSeparated_majorant
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ w : ℂ,
        0 < w.re →
          ε ≤ w.re / ‖w‖ →
          1 ≤ ‖w‖ →
          ‖2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
              Complex.arctan ((t : ℂ) / w) /
                (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)‖ ≤
            2 * C *
              (∫ t : ℝ in Set.Ioi (0 : ℝ),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  let M : ℝ → ℝ := fun t : ℝ =>
    t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  rcases
      Complex.binetSecondFormula_kernel_tail_norm_le_majorant_sectorSeparated
        ε hε with
    ⟨C, hC_nonneg, htail_bound⟩
  refine ⟨C, hC_nonneg, ?_⟩
  intro w hw_re_pos hw_sep hw_large
  let K : ℝ → ℂ := fun t : ℝ =>
    Complex.arctan ((t : ℂ) / w) /
      (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  have hM_integrable_Ioi : IntegrableOn M (Set.Ioi (0 : ℝ)) :=
    Real.binetSecondFormula_kernel_majorant_integrableOn
  have hcut_nonneg : (0 : ℝ) ≤ ‖w‖ / 2 :=
    div_nonneg (norm_nonneg w) Real.zero_le_two_real
  have hCM_integrable_tail :
      Integrable (fun t : ℝ => C * M t)
        (volume.restrict (Set.Ioi (‖w‖ / 2))) :=
    (hM_integrable_Ioi.mono_set (Ioi_subset_Ioi hcut_nonneg)).const_mul C
  have hpointwise :
      ∀ᵐ t ∂volume.restrict (Set.Ioi (‖w‖ / 2)),
        ‖K t‖ ≤ C * M t :=
    (ae_restrict_mem measurableSet_Ioi).mono
      (fun t ht => htail_bound w hw_re_pos hw_sep hw_large t ht)
  have hnorm_integral :
      ‖∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t‖ ≤
        ∫ t : ℝ in Set.Ioi (‖w‖ / 2), C * M t :=
    norm_integral_le_of_norm_le hCM_integrable_tail hpointwise
  have hmono :
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2), M t ≤
        ∫ t : ℝ in Set.Ioi (0 : ℝ), M t :=
    setIntegral_mono_set hM_integrable_Ioi
      ((ae_restrict_mem measurableSet_Ioi).mono
        (fun t ht => Real.binetSecondFormula_kernel_majorant_nonneg_on_Ioi t ht))
      (Filter.Eventually.of_forall (fun t ht => lt_of_le_of_lt hcut_nonneg ht))
  have hscaled_mono :
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2), C * M t ≤
        C * ∫ t : ℝ in Set.Ioi (0 : ℝ), M t := by
    calc
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2), C * M t =
          C * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), M t := by
        exact MeasureTheory.integral_mul_left C M
      _ ≤ C * ∫ t : ℝ in Set.Ioi (0 : ℝ), M t :=
        mul_le_mul_of_nonneg_left hmono hC_nonneg
  calc
    ‖2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t‖ =
        2 * ‖∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t‖ := by
      exact
        Eq.trans (norm_mul (2 : ℂ)
          (∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t))
          (congrArg
            (fun r : ℝ =>
              r * ‖∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t‖)
            (Complex.norm_natCast 2))
    _ ≤ 2 * (∫ t : ℝ in Set.Ioi (‖w‖ / 2), C * M t) :=
      mul_le_mul_of_nonneg_left hnorm_integral Real.zero_le_two_real
    _ ≤ 2 * (C * ∫ t : ℝ in Set.Ioi (0 : ℝ), M t) :=
      mul_le_mul_of_nonneg_left hscaled_mono Real.zero_le_two_real
    _ = 2 * C * (∫ t : ℝ in Set.Ioi (0 : ℝ), M t) := by
      exact (mul_assoc _ _ _).symm

/-- Splitting the Binet integral at `‖w‖ / 2` gives the global open-half-plane
remainder bound. -/
theorem Complex.binetSecondFormulaRemainder_norm_le_integral_majorant_from_split
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ‖Complex.binetSecondFormulaRemainder w‖ ≤
        4 *
          (∫ t : ℝ in Set.Ioi (0 : ℝ),
            t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) / ‖w‖ +
          2 * C *
            (∫ t : ℝ in Set.Ioi (0 : ℝ),
              t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  let J : ℝ :=
    ∫ t : ℝ in Set.Ioi (0 : ℝ),
      t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  let S : ℂ :=
    2 * ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
      Complex.arctan ((t : ℂ) / w) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  let T : ℂ :=
    2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
      Complex.arctan ((t : ℂ) / w) /
        (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
  have hsplit : Complex.binetSecondFormulaRemainder w = S + T := by
    unfold S
    unfold T
    exact Complex.binetSecondFormulaRemainder_eq_small_add_tail hw_re_pos
  have hS : ‖S‖ ≤ 4 * J / ‖w‖ :=
    Complex.binetSecondFormulaRemainder_small_norm_le_integral_majorant
      hw_re_pos
  rcases
    Complex.binetSecondFormulaRemainder_tail_norm_le_integral_majorant
      hw_re_pos with
    ⟨C, hC_nonneg, hT⟩
  refine ⟨C, hC_nonneg, ?_⟩
  have hsum : ‖S + T‖ ≤ 4 * J / ‖w‖ + 2 * C * J := by
    calc
      ‖S + T‖ ≤ ‖S‖ + ‖T‖ := norm_add_le S T
      _ ≤ 4 * J / ‖w‖ + 2 * C * J := add_le_add hS hT
  exact
    Eq.subst
      (motive := fun x : ℂ => ‖x‖ ≤ 4 * J / ‖w‖ + 2 * C * J)
      hsplit.symm
      hsum

/-- The pointwise Binet-kernel majorant integrates to a norm bound for the
Binet remainder in the open right half-plane. -/
theorem Complex.binetSecondFormulaRemainder_norm_le_integral_majorant_from_kernel_bound
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ‖Complex.binetSecondFormulaRemainder w‖ ≤
        4 *
          (∫ t : ℝ in Set.Ioi (0 : ℝ),
            t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) / ‖w‖ +
          2 * C *
            (∫ t : ℝ in Set.Ioi (0 : ℝ),
              t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  exact
    Complex.binetSecondFormulaRemainder_norm_le_integral_majorant_from_split
      hw_re_pos

/-- Integration of the pointwise Binet-kernel majorant on the open right
half-plane. -/
theorem Complex.binetSecondFormulaRemainder_norm_le_integral_majorant_openRightHalfPlane
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ‖Complex.binetSecondFormulaRemainder w‖ ≤
        4 *
          (∫ t : ℝ in Set.Ioi (0 : ℝ),
            t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) / ‖w‖ +
          2 * C *
            (∫ t : ℝ in Set.Ioi (0 : ℝ),
              t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  exact
    Complex.binetSecondFormulaRemainder_norm_le_integral_majorant_from_kernel_bound
      hw_re_pos

/-- The Binet second-formula remainder is uniformly bounded on each fixed
wedge of the open right half-plane after a large-radius cutoff. -/
theorem Complex.binetSecondFormulaRemainder_norm_le_sectorSeparated
    (ε : ℝ)
    (hε : 0 < ε) :
    ∃ C : ℝ,
      0 < C ∧
      ∀ w : ℂ,
        0 < w.re →
          ε ≤ w.re / ‖w‖ →
          1 ≤ ‖w‖ →
            ‖Complex.binetSecondFormulaRemainder w‖ ≤ C := by
  let J : ℝ :=
    ∫ t : ℝ in Set.Ioi (0 : ℝ),
      t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)
  rcases
      Complex.binetSecondFormulaRemainder_tail_norm_le_sectorSeparated_majorant
        ε hε with
    ⟨Ct, hCt_nonneg, htail⟩
  refine ⟨4 * J + 2 * Ct * J + 1, ?_, ?_⟩
  · have hJ_nonneg : 0 ≤ J :=
      integral_nonneg_of_ae
        ((ae_restrict_mem measurableSet_Ioi).mono
          (fun t ht =>
            Real.binetSecondFormula_kernel_majorant_nonneg_on_Ioi t ht))
    have hfourJ_nonneg : 0 ≤ 4 * J :=
      mul_nonneg Real.zero_le_four hJ_nonneg
    have htail_nonneg : 0 ≤ 2 * Ct * J :=
      mul_nonneg (mul_nonneg Real.zero_le_two_real hCt_nonneg)
        hJ_nonneg
    have hsum_nonneg : 0 ≤ 4 * J + 2 * Ct * J :=
      add_nonneg hfourJ_nonneg htail_nonneg
    calc
      (0 : ℝ) < 1 := zero_lt_one
      _ = 0 + 1 := Eq.symm (zero_add 1)
      _ ≤ 4 * J + 2 * Ct * J + 1 :=
        add_le_add_right hsum_nonneg 1
  · intro w hw_re_pos hw_sep hw_large
    let S : ℂ :=
      2 * ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
        Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
    let T : ℂ :=
      2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
        Complex.arctan ((t : ℂ) / w) /
          (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1)
    have hsplit : Complex.binetSecondFormulaRemainder w = S + T := by
      unfold S
      unfold T
      exact Complex.binetSecondFormulaRemainder_eq_small_add_tail hw_re_pos
    have hsmall :
        ‖S‖ ≤ 4 * J := by
      have hsmall_raw :
          ‖S‖ ≤ 4 * J / ‖w‖ :=
        Complex.binetSecondFormulaRemainder_small_norm_le_integral_majorant
          hw_re_pos
      have hJ_nonneg : 0 ≤ J :=
        integral_nonneg_of_ae
          ((ae_restrict_mem measurableSet_Ioi).mono
            (fun t ht =>
              Real.binetSecondFormula_kernel_majorant_nonneg_on_Ioi t ht))
      have hfourJ_nonneg : 0 ≤ 4 * J :=
        mul_nonneg Real.zero_le_four hJ_nonneg
      have hdiv_le : 4 * J / ‖w‖ ≤ 4 * J := by
        exact div_le_of_le_mul₀ (norm_nonneg w) hfourJ_nonneg
          (by
            calc
              4 * J ≤ 4 * J * 1 := by
                exact le_of_eq (Eq.symm (mul_one (4 * J)))
              _ ≤ 4 * J * ‖w‖ :=
                mul_le_mul_of_nonneg_left hw_large hfourJ_nonneg)
      exact le_trans hsmall_raw hdiv_le
    have htail_bound :
        ‖T‖ ≤ 2 * Ct * J :=
      htail w hw_re_pos hw_sep hw_large
    have hsum :
        ‖S + T‖ ≤ 4 * J + 2 * Ct * J := by
      calc
        ‖S + T‖ ≤ ‖S‖ + ‖T‖ := norm_add_le S T
        _ ≤ 4 * J + 2 * Ct * J := add_le_add hsmall htail_bound
    calc
      ‖Complex.binetSecondFormulaRemainder w‖ = ‖S + T‖ := by
        exact congrArg norm hsplit
      _ ≤ 4 * J + 2 * Ct * J := hsum
      _ ≤ 4 * J + 2 * Ct * J + 1 := by
        exact le_add_of_nonneg_right zero_le_one

/-- A positive integrable function on an open real interval has positive
integral. -/
theorem Real.setIntegral_pos_of_integrableOn_of_pos_on_Ioo
    {f : ℝ → ℝ}
    {a b : ℝ}
    (hab : a < b)
    (h_integrable : IntegrableOn f (Set.Ioo a b))
    (hpos : ∀ t : ℝ, t ∈ Set.Ioo a b → 0 < f t) :
    0 < ∫ t : ℝ in Set.Ioo a b, f t := by
  have hnonneg_ae :
      0 ≤ᵐ[volume.restrict (Set.Ioo a b)] f :=
    (ae_restrict_mem measurableSet_Ioo).mono
      (fun t ht => le_of_lt (hpos t ht))
  have hsupport_pos :
      0 < volume (Function.support f ∩ Set.Ioo a b) := by
    have hIoo_pos : 0 < volume (Set.Ioo a b) :=
      (Measure.measure_Ioo_pos volume).mpr hab
    have hsubset :
        Set.Ioo a b ⊆ Function.support f ∩ Set.Ioo a b := by
      intro t ht
      exact ⟨fun hzero => (ne_of_gt (hpos t ht)) hzero, ht⟩
    exact lt_of_lt_of_le hIoo_pos (measure_mono hsubset)
  exact
    (setIntegral_pos_iff_support_of_nonneg_ae
      hnonneg_ae h_integrable).mpr hsupport_pos

/-- The Binet majorant is integrable on `(0,1)`. -/
theorem Real.binetSecondFormula_kernel_majorant_integrableOn_Ioo_zero_one :
    IntegrableOn
      (fun t : ℝ => t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
      (Set.Ioo (0 : ℝ) 1) := by
  exact
    IntegrableOn.mono_set
      Real.binetSecondFormula_kernel_majorant_integrableOn_zero_one
      Set.Ioo_subset_Ioc_self

/-- The Binet majorant has strictly positive integral on `(0,1)`. -/
theorem Real.binetSecondFormula_kernel_majorant_integral_pos_on_zero_one :
    0 <
      ∫ t : ℝ in Set.Ioo (0 : ℝ) 1,
        t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  exact
    Real.setIntegral_pos_of_integrableOn_of_pos_on_Ioo
      zero_lt_one
      Real.binetSecondFormula_kernel_majorant_integrableOn_Ioo_zero_one
      (fun t ht =>
        Real.binetSecondFormula_kernel_majorant_pos ht.1)

/-- Positivity of an integral on a subinterval propagates to the larger
positive half-line for a nonnegative integrable function. -/
theorem Real.integral_pos_on_Ioi_zero_of_integral_pos_on_Ioo_zero_one_of_nonneg
    {f : ℝ → ℝ}
    (h_integrable : IntegrableOn f (Set.Ioi (0 : ℝ)))
    (hpos_subinterval :
      0 <
        ∫ t : ℝ in Set.Ioo (0 : ℝ) 1, f t)
    (hnonneg :
      ∀ t : ℝ,
        t ∈ Set.Ioi (0 : ℝ) →
          0 ≤ f t) :
    0 <
      ∫ t : ℝ in Set.Ioi (0 : ℝ), f t := by
  have hnonneg_ae :
      0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))] f :=
    (ae_restrict_mem measurableSet_Ioi).mono
      (fun t ht => hnonneg t ht)
  have hsubset_ae :
      Set.Ioo (0 : ℝ) 1 ≤ᵐ[volume] Set.Ioi (0 : ℝ) :=
    Filter.Eventually.of_forall (fun t ht => ht.1)
  have hmono :
      ∫ t : ℝ in Set.Ioo (0 : ℝ) 1, f t ≤
        ∫ t : ℝ in Set.Ioi (0 : ℝ), f t :=
    setIntegral_mono_set h_integrable hnonneg_ae hsubset_ae
  exact lt_of_lt_of_le hpos_subinterval hmono

/-- A strict lower bound on `(0,1)` propagates to a strict lower bound for the half-line integral
for the nonnegative Binet majorant. -/
theorem Real.binetSecondFormula_kernel_majorant_integral_pos_of_zero_one
    (hpos_subinterval :
      0 <
        ∫ t : ℝ in Set.Ioo (0 : ℝ) 1,
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1))
    (hnonneg :
      ∀ t : ℝ,
        t ∈ Set.Ioi (0 : ℝ) →
          0 ≤ t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) :
    0 <
      ∫ t : ℝ in Set.Ioi (0 : ℝ),
        t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  exact
    Real.integral_pos_on_Ioi_zero_of_integral_pos_on_Ioo_zero_one_of_nonneg
      Real.binetSecondFormula_kernel_majorant_integrableOn
      hpos_subinterval hnonneg

/-- The Binet majorant integral is a positive finite constant. -/
theorem Real.binetSecondFormula_kernel_majorant_integral_pos :
    0 <
      ∫ t : ℝ in Set.Ioi (0 : ℝ),
        t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) := by
  have hpos_subinterval :
      0 <
        ∫ t : ℝ in Set.Ioo (0 : ℝ) 1,
          t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
    Real.binetSecondFormula_kernel_majorant_integral_pos_on_zero_one
  have hnonneg :
      ∀ t : ℝ,
        t ∈ Set.Ioi (0 : ℝ) →
          0 ≤ t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
    Real.binetSecondFormula_kernel_majorant_nonneg_on_Ioi
  exact
    Real.binetSecondFormula_kernel_majorant_integral_pos_of_zero_one
      hpos_subinterval hnonneg

/-- The Binet second-formula remainder is bounded in the open right half-plane
by the small-argument `1 / ‖w‖` contribution plus a fixed-`w` tail
contribution. -/
theorem Complex.binetSecondFormulaRemainder_norm_le_openRightHalfPlane :
    ∀ w : ℂ,
      0 < w.re →
        ∃ C : ℝ,
          0 ≤ C ∧
          ‖Complex.binetSecondFormulaRemainder w‖ ≤
            4 *
              (∫ t : ℝ in Set.Ioi (0 : ℝ),
                t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) / ‖w‖ +
              2 * C *
                (∫ t : ℝ in Set.Ioi (0 : ℝ),
                  t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
  intro w hw_re_pos
  exact
    Complex.binetSecondFormulaRemainder_norm_le_integral_majorant_openRightHalfPlane
      hw_re_pos

end

end LFunctions
end Boundary
