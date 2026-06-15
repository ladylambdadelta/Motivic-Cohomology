import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.Arctan

/-!
# Arctangent bounds for the Binet kernel

This file owns the small-argument principal-arctangent norm estimates used by
the Binet kernel.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Squaring preserves the closed half-disk bound used in the arctangent
majorant. -/
theorem Real.sq_le_quarter_of_nonneg_le_half
    {x : ℝ}
    (hx_nonneg : 0 ≤ x)
    (hx_half : x ≤ (1 / 2 : ℝ)) :
    x ^ 2 ≤ (1 / 2 : ℝ) ^ 2 := by
  have hhalf_nonneg : 0 ≤ (1 / 2 : ℝ) :=
    zero_le_one' ℝ |> fun h => div_nonneg h zero_le_two
  have hneg_half_le_zero : -(1 / 2 : ℝ) ≤ 0 :=
    neg_nonpos.mpr hhalf_nonneg
  have hneg_half_le_x : -(1 / 2 : ℝ) ≤ x :=
    le_trans hneg_half_le_zero hx_nonneg
  exact sq_le_sq' hneg_half_le_x hx_half

/-- The odd positive integer denominator in the arctangent series has complex
norm at least one. -/
theorem Complex.one_le_norm_natCast_odd
    (n : ℕ) :
    (1 : ℝ) ≤ ‖((2 * n + 1 : ℕ) : ℂ)‖ := by
  have hone_le_nat : (1 : ℝ) ≤ (2 * n + 1 : ℕ) := by
    exact Nat.cast_le.mpr (Nat.succ_le_succ (Nat.zero_le (2 * n)))
  have hnorm_eq :
      ‖((2 * n + 1 : ℕ) : ℂ)‖ = ((2 * n + 1 : ℕ) : ℝ) := by
    calc
      ‖((2 * n + 1 : ℕ) : ℂ)‖ = |((2 * n + 1 : ℕ) : ℂ)| := by
        exact Complex.norm_eq_abs _
      _ = ((2 * n + 1 : ℕ) : ℝ) := by
        exact Complex.abs_ofReal (2 * n + 1)
  exact hnorm_eq ▸ hone_le_nat

/-- Odd powers split into one linear factor and a square-power factor. -/
theorem Real.pow_two_mul_add_one_eq_mul_sq_pow
    (x : ℝ)
    (n : ℕ) :
    x ^ (2 * n + 1) = x * (x ^ 2) ^ n := by
  have hodd : 2 * n + 1 = 1 + 2 * n :=
    Nat.add_comm (2 * n) 1
  calc
    x ^ (2 * n + 1) = x ^ (1 + 2 * n) := by
      exact congrArg (fun k : ℕ => x ^ k) hodd
    _ = x ^ 1 * x ^ (2 * n) := by
      exact pow_add x 1 (2 * n)
    _ = x * x ^ (2 * n) := by
      exact congrArg (fun y : ℝ => y * x ^ (2 * n)) (pow_one x)
    _ = x * (x ^ 2) ^ n := by
      exact congrArg (fun y : ℝ => x * y) (pow_mul x 2 n).symm

/-- The reciprocal of `1 - 1/2` is `2`. -/
theorem Real.one_sub_half_inv_eq_two :
    ((1 : ℝ) - (1 / 2 : ℝ))⁻¹ = 2 := by
  have htwo_ne_zero : (2 : ℝ) ≠ 0 :=
    ne_of_gt zero_lt_two
  have hhalf : (1 : ℝ) - (1 / 2 : ℝ) = 1 / 2 := by
    calc
      (1 : ℝ) - (1 / 2 : ℝ) = (2 / 2 : ℝ) - (1 / 2 : ℝ) := by
        exact congrArg (fun x : ℝ => x - (1 / 2 : ℝ))
          (Eq.symm (div_self htwo_ne_zero))
      _ = (2 - 1 : ℝ) / 2 := by
        exact (sub_div 2 1 2).symm
      _ = 1 / 2 := by
        exact congrArg (fun x : ℝ => x / 2)
          (sub_eq_iff_eq_add.mpr (show (2 : ℝ) = 1 + 1 by rfl))
  calc
    ((1 : ℝ) - (1 / 2 : ℝ))⁻¹ = ((1 / 2 : ℝ))⁻¹ := by
      exact congrArg Inv.inv hhalf
    _ = 2 := by
      exact inv_eq_of_mul_eq_one_right (show (1 / 2 : ℝ) * 2 = 1 by
        exact one_div_mul_cancel htwo_ne_zero)

/-- The real number `1 / 2` is nonnegative. -/
theorem Real.half_nonneg : (0 : ℝ) ≤ 1 / 2 :=
  div_nonneg zero_le_one zero_le_two

/-- The real number `1 / 2` is strictly less than one. -/
theorem Real.half_lt_one : (1 / 2 : ℝ) < 1 :=
  (div_lt_one zero_lt_two).mpr one_lt_two

/-- The real number `1 / 2` is at most one. -/
theorem Real.half_le_one : (1 / 2 : ℝ) ≤ 1 :=
  le_of_lt Real.half_lt_one

/-- Squaring `1 / 2` remains below `1 / 2`. -/
theorem Real.half_sq_le_half : (1 / 2 : ℝ) ^ 2 ≤ 1 / 2 := by
  calc
    (1 / 2 : ℝ) ^ 2 = (1 / 2 : ℝ) * (1 / 2 : ℝ) :=
      pow_two (1 / 2 : ℝ)
    _ ≤ 1 * (1 / 2 : ℝ) :=
      mul_le_mul_of_nonneg_right Real.half_le_one Real.half_nonneg
    _ = 1 / 2 :=
      one_mul (1 / 2 : ℝ)

/-- The real number `1 / 3` is at most `3`. -/
theorem Real.one_div_three_le_three : (1 / 3 : ℝ) ≤ 3 := by
  have hthree_pos : (0 : ℝ) < 3 :=
    Nat.cast_pos.mpr (Nat.succ_pos 2)
  have hone_le_three : (1 : ℝ) ≤ 3 :=
    Nat.cast_le.mpr (Nat.succ_le_succ (Nat.zero_le 2))
  exact le_trans ((div_le_one hthree_pos).mpr hone_le_three) hone_le_three

/-- The norm of an integral sign factor is one. -/
theorem Complex.norm_neg_one_pow
    (n : ℕ) :
    ‖(-1 : ℂ) ^ n‖ = 1 := by
  calc
    ‖(-1 : ℂ) ^ n‖ = ‖(-1 : ℂ)‖ ^ n :=
      norm_pow (-1 : ℂ) n
    _ = ‖(1 : ℂ)‖ ^ n := by
      exact congrArg (fun x : ℝ => x ^ n) (norm_neg (1 : ℂ))
    _ = 1 ^ n := by
      exact congrArg (fun x : ℝ => x ^ n) (norm_one : ‖(1 : ℂ)‖ = 1)
    _ = 1 :=
      one_pow n

/-- Norm identity for the arctangent series term. -/
theorem Complex.arctan_series_term_norm_eq
    (z : ℂ)
    (n : ℕ) :
    ‖(-1 : ℂ) ^ n * z ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℂ)‖ =
      ‖z‖ ^ (2 * n + 1) / ‖((2 * n + 1 : ℕ) : ℂ)‖ := by
  calc
    ‖(-1 : ℂ) ^ n * z ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℂ)‖ =
        ‖(-1 : ℂ) ^ n * z ^ (2 * n + 1)‖ /
          ‖((2 * n + 1 : ℕ) : ℂ)‖ := by
      exact norm_div _ _
    _ = (‖(-1 : ℂ) ^ n‖ * ‖z ^ (2 * n + 1)‖) /
          ‖((2 * n + 1 : ℕ) : ℂ)‖ := by
      exact congrArg
        (fun x : ℝ => x / ‖((2 * n + 1 : ℕ) : ℂ)‖)
        (norm_mul ((-1 : ℂ) ^ n) (z ^ (2 * n + 1)))
    _ = (1 * ‖z‖ ^ (2 * n + 1)) /
          ‖((2 * n + 1 : ℕ) : ℂ)‖ := by
      exact congrArg
        (fun x : ℝ => x / ‖((2 * n + 1 : ℕ) : ℂ)‖)
        (congrArg₂ (fun x y : ℝ => x * y)
          (Complex.norm_neg_one_pow n)
          (norm_pow z (2 * n + 1)))
    _ = ‖z‖ ^ (2 * n + 1) / ‖((2 * n + 1 : ℕ) : ℂ)‖ := by
      exact congrArg (fun x : ℝ => x / ‖((2 * n + 1 : ℕ) : ℂ)‖)
        (one_mul (‖z‖ ^ (2 * n + 1)))

/-- Principal arctangent series terms are bounded by a geometric majorant on the
closed disk `‖z‖ ≤ 1 / 2`. -/
theorem Complex.arctan_series_term_norm_le_geometric
    {z : ℂ}
    (hz : ‖z‖ ≤ (1 / 2 : ℝ)) :
    ∀ n : ℕ,
      ‖(-1 : ℂ) ^ n * z ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℂ)‖ ≤
        ‖z‖ * ((1 / 2 : ℝ) ^ n) := by
  intro n
  have hz_nonneg : 0 ≤ ‖z‖ :=
    norm_nonneg z
  have hsq_le_half : ‖z‖ ^ 2 ≤ (1 / 2 : ℝ) := by
    have hsq_le_quarter : ‖z‖ ^ 2 ≤ (1 / 2 : ℝ) ^ 2 :=
      Real.sq_le_quarter_of_nonneg_le_half hz_nonneg hz
    have hquarter_le_half : (1 / 2 : ℝ) ^ 2 ≤ (1 / 2 : ℝ) := by
      exact Real.half_sq_le_half
    exact le_trans hsq_le_quarter hquarter_le_half
  have hpow_bound :
      ‖z‖ ^ (2 * n + 1) ≤ ‖z‖ * ((1 / 2 : ℝ) ^ n) := by
    calc
      ‖z‖ ^ (2 * n + 1) = ‖z‖ * (‖z‖ ^ 2) ^ n := by
        exact Real.pow_two_mul_add_one_eq_mul_sq_pow ‖z‖ n
      _ ≤ ‖z‖ * ((1 / 2 : ℝ) ^ n) := by
        exact
          mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (sq_nonneg ‖z‖) hsq_le_half n)
            hz_nonneg
  have hden_ge_one : (1 : ℝ) ≤ ‖((2 * n + 1 : ℕ) : ℂ)‖ := by
    exact Complex.one_le_norm_natCast_odd n
  have hden_pos : 0 < ‖((2 * n + 1 : ℕ) : ℂ)‖ :=
    lt_of_lt_of_le zero_lt_one hden_ge_one
  have hdiv_le :
      ‖z‖ ^ (2 * n + 1) / ‖((2 * n + 1 : ℕ) : ℂ)‖ ≤
        ‖z‖ ^ (2 * n + 1) := by
    exact
      div_le_of_le_mul₀
        (norm_nonneg _)
        (pow_nonneg hz_nonneg (2 * n + 1))
        (by
          calc
            ‖z‖ ^ (2 * n + 1) ≤ ‖z‖ ^ (2 * n + 1) * 1 := by
              exact le_of_eq (Eq.symm (mul_one _))
            _ ≤ ‖z‖ ^ (2 * n + 1) * ‖((2 * n + 1 : ℕ) : ℂ)‖ :=
              mul_le_mul_of_nonneg_left hden_ge_one
                (pow_nonneg hz_nonneg (2 * n + 1)))
  calc
    ‖(-1 : ℂ) ^ n * z ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℂ)‖ =
        ‖z‖ ^ (2 * n + 1) / ‖((2 * n + 1 : ℕ) : ℂ)‖ := by
      exact Complex.arctan_series_term_norm_eq z n
    _ ≤ ‖z‖ ^ (2 * n + 1) := hdiv_le
    _ ≤ ‖z‖ * ((1 / 2 : ℝ) ^ n) := hpow_bound

/-- The geometric majorant for the arctangent series sums to `2 * ‖z‖`. -/
theorem Complex.arctan_geometric_majorant_hasSum
    (z : ℂ) :
    HasSum (fun n : ℕ => ‖z‖ * ((1 / 2 : ℝ) ^ n)) (2 * ‖z‖) := by
  have hgeom :
    HasSum (fun n : ℕ => ((1 / 2 : ℝ) ^ n)) ((1 - (1 / 2 : ℝ))⁻¹) :=
    hasSum_geometric_of_lt_one
      Real.half_nonneg
      Real.half_lt_one
  have hmul :
      HasSum (fun n : ℕ => ‖z‖ * ((1 / 2 : ℝ) ^ n))
        (‖z‖ * (1 - (1 / 2 : ℝ))⁻¹) :=
    hgeom.mul_left ‖z‖
  have hsum_eq :
      ‖z‖ * (1 - (1 / 2 : ℝ))⁻¹ = 2 * ‖z‖ := by
    calc
      ‖z‖ * (1 - (1 / 2 : ℝ))⁻¹ = ‖z‖ * 2 := by
        exact congrArg (fun x : ℝ => ‖z‖ * x) Real.one_sub_half_inv_eq_two
      _ = 2 * ‖z‖ := by
        exact mul_comm ‖z‖ 2
  exact Eq.ndrec hmul hsum_eq

set_option maxHeartbeats 0 in
/-- Principal arctangent is bounded by twice the argument norm on the closed
disk `‖z‖ ≤ 1 / 2`, proved from the arctangent power series. -/
theorem Complex.norm_arctan_le_two_norm_of_norm_le_half_from_series
    {z : ℂ}
    (hz : ‖z‖ ≤ (1 / 2 : ℝ)) :
    ‖Complex.arctan z‖ ≤ 2 * ‖z‖ := by
  have hz_lt_one : ‖z‖ < (1 : ℝ) :=
    lt_of_le_of_lt hz Real.half_lt_one
  have hseries :
      HasSum
        (fun n : ℕ =>
          (-1 : ℂ) ^ n * z ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℂ))
        (Complex.arctan z) :=
    Complex.hasSum_arctan hz_lt_one
  have hmajorant :
      HasSum (fun n : ℕ => ‖z‖ * ((1 / 2 : ℝ) ^ n)) (2 * ‖z‖) :=
    Complex.arctan_geometric_majorant_hasSum z
  exact
    hseries.norm_le_of_bounded hmajorant
      (Complex.arctan_series_term_norm_le_geometric hz)

/-- Principal arctangent is bounded by twice the argument norm on the closed
disk `‖z‖ ≤ 1 / 2`. -/
theorem Complex.norm_arctan_le_two_norm_of_norm_le_half
    {z : ℂ}
    (hz : ‖z‖ ≤ (1 / 2 : ℝ)) :
    ‖Complex.arctan z‖ ≤ 2 * ‖z‖ := by
  exact
    Complex.norm_arctan_le_two_norm_of_norm_le_half_from_series hz

/-- Arithmetic used to turn a bounded fixed-tail arctangent estimate into a
linear estimate. -/
theorem Real.arctan_fixed_tail_two_mul_div_mul_half_eq
    {B r : ℝ}
    (hr : r ≠ 0) :
    (2 * B / r) * (r / 2) = B := by
  calc
    (2 * B / r) * (r / 2) =
        ((2 * B) * r⁻¹) * (r * (2 : ℝ)⁻¹) := by
      exact congrArg₂ (fun x y : ℝ => x * y)
        (div_eq_mul_inv (2 * B) r)
        (div_eq_mul_inv r 2)
    _ = (2 * B) * (r⁻¹ * r) * (2 : ℝ)⁻¹ := by
      calc
        ((2 * B) * r⁻¹) * (r * (2 : ℝ)⁻¹) =
            (((2 * B) * r⁻¹) * r) * (2 : ℝ)⁻¹ := by
          exact mul_assoc ((2 * B) * r⁻¹) r (2 : ℝ)⁻¹
        _ = ((2 * B) * (r⁻¹ * r)) * (2 : ℝ)⁻¹ := by
          exact congrArg (fun x : ℝ => x * (2 : ℝ)⁻¹)
            (mul_assoc (2 * B) r⁻¹ r)
    _ = (2 * B) * 1 * (2 : ℝ)⁻¹ := by
      exact congrArg (fun x : ℝ => (2 * B) * x * (2 : ℝ)⁻¹)
        (inv_mul_cancel₀ hr)
    _ = (2 * B) * (2 : ℝ)⁻¹ := by
      exact congrArg (fun x : ℝ => x * (2 : ℝ)⁻¹) (mul_one (2 * B))
    _ = B * (2 * (2 : ℝ)⁻¹) := by
      calc
        (2 * B) * (2 : ℝ)⁻¹ = B * 2 * (2 : ℝ)⁻¹ := by
          exact congrArg (fun x : ℝ => x * (2 : ℝ)⁻¹) (mul_comm 2 B)
        _ = B * (2 * (2 : ℝ)⁻¹) := by
          exact mul_assoc B 2 (2 : ℝ)⁻¹
    _ = B * 1 := by
      exact congrArg (fun x : ℝ => B * x)
        (mul_inv_cancel₀ (show (2 : ℝ) ≠ 0 by exact ne_of_gt zero_lt_two))
    _ = B := by
      exact mul_one B

/-- Upper bound for a quotient from an upper numerator bound and a lower
denominator bound. -/
theorem Real.arctan_fixed_tail_div_le_div_of_le_of_le
    {a A d n : ℝ}
    (ha_pos : 0 < a)
    (hn_nonneg : 0 ≤ n)
    (hnA : n ≤ A)
    (had : a ≤ d) :
    n / d ≤ A / a := by
  have hd_pos : 0 < d := lt_of_lt_of_le ha_pos had
  have hA_nonneg : 0 ≤ A := le_trans hn_nonneg hnA
  exact
    le_trans
      (mul_le_mul_of_nonneg_right hnA (le_of_lt ha_pos))
      (mul_le_mul_of_nonneg_left had hA_nonneg)

/-- Lower bound for a quotient from a lower numerator bound and an upper
denominator bound. -/
theorem Real.arctan_fixed_tail_div_le_div_of_le_of_le'
    {a A d n : ℝ}
    (ha_pos : 0 < a)
    (hA_pos : 0 < A)
    (hd_pos : 0 < d)
    (had : d ≤ A)
    (han : a ≤ n) :
    a / A ≤ n / d := by
  exact
    le_trans
      (mul_le_mul_of_nonneg_left had (le_of_lt ha_pos))
      (mul_le_mul_of_nonneg_right han (le_of_lt hA_pos))

/-- The real number `3` is positive. -/
theorem Real.arctan_fixed_tail_zero_lt_three : (0 : ℝ) < 3 :=
  Nat.cast_pos.mpr (Nat.succ_pos 2)

/-- Multiplying by `1 / 3` cancels a leading factor `3`. -/
theorem Real.arctan_fixed_tail_one_div_three_mul_three_mul
    (x : ℝ) :
    (1 / 3 : ℝ) * (3 * x) = x := by
  calc
    (1 / 3 : ℝ) * (3 * x)
        = ((1 / 3 : ℝ) * 3) * x :=
            (mul_assoc (1 / 3 : ℝ) 3 x).symm
    _ = 1 * x := by
            exact congrArg (fun y : ℝ => y * x)
              (one_div_mul_cancel
                (ne_of_gt Real.arctan_fixed_tail_zero_lt_three))
    _ = x :=
            one_mul x

/-- A number plus twice itself is three times itself. -/
theorem Real.add_two_mul_self_eq_three_mul
    (x : ℝ) :
    x + 2 * x = 3 * x := by
  calc
    x + 2 * x = 1 * x + 2 * x := by
      exact congrArg (fun y : ℝ => y + 2 * x) (one_mul x).symm
    _ = (1 + 2) * x := by
      exact (add_mul 1 2 x).symm
    _ = 3 * x := rfl

/-- Four times a number is twice that number plus twice that number. -/
theorem Real.four_mul_eq_two_mul_add_two_mul
    (x : ℝ) :
    4 * x = 2 * x + 2 * x := by
  calc
    4 * x = (2 + 2) * x := rfl
    _ = 2 * x + 2 * x := by
      exact add_mul 2 2 x

/-- Twice a number is the number plus itself. -/
theorem Real.two_mul_eq_add_self
    (x : ℝ) :
    2 * x = x + x := by
  exact two_mul x

/-- Left normalization for the far-tail linear comparison. -/
theorem Real.arctan_fixed_tail_far_tail_left_eq
    (a t : ℝ) :
    4 * a + (t - 3 * a) = a + t := by
  calc
    4 * a + (t - 3 * a) =
        (2 * a + 2 * a) + (t - 3 * a) := by
      exact congrArg (fun x : ℝ => x + (t - 3 * a))
        (Real.four_mul_eq_two_mul_add_two_mul a)
    _ = (2 * a + 2 * a) + t - 3 * a := by
      exact (add_sub_assoc (2 * a + 2 * a) t (3 * a)).symm
    _ = (4 * a + t) - 3 * a := by
      exact congrArg (fun x : ℝ => x - 3 * a)
        (congrArg (fun x : ℝ => x + t)
          (Real.four_mul_eq_two_mul_add_two_mul a).symm)
    _ = ((3 + 1) * a + t) - 3 * a := rfl
    _ = ((3 * a + 1 * a) + t) - 3 * a := by
      exact congrArg (fun x : ℝ => (x + t) - 3 * a)
        (add_mul 3 1 a)
    _ = (3 * a + (1 * a + t)) - 3 * a := by
      exact congrArg (fun x : ℝ => x - 3 * a)
        (add_assoc (3 * a) (1 * a) t).symm
    _ = (1 * a + t) + 3 * a - 3 * a := by
      exact congrArg (fun x : ℝ => x - 3 * a)
        (add_comm (3 * a) (1 * a + t))
    _ = 1 * a + t := by
      exact add_sub_cancel (1 * a + t) (3 * a)
    _ = a + t := by
      exact congrArg (fun x : ℝ => x + t) (one_mul a)

/-- Right normalization for the far-tail linear comparison. -/
theorem Real.arctan_fixed_tail_far_tail_right_eq
    (a t : ℝ) :
    2 * t + (t - 3 * a) = 3 * (t - a) := by
  calc
    2 * t + (t - 3 * a) =
        2 * t + t - 3 * a := by
      exact (add_sub_assoc (2 * t) t (3 * a)).symm
    _ = (2 * t + 1 * t) - 3 * a := by
      exact congrArg (fun x : ℝ => (2 * t + x) - 3 * a) (one_mul t).symm
    _ = ((2 + 1) * t) - 3 * a := by
      exact congrArg (fun x : ℝ => x - 3 * a) (add_mul 2 1 t).symm
    _ = 3 * t - 3 * a := rfl
    _ = 3 * t - 3 * a := rfl
    _ = 3 * t - 3 * a := rfl
    _ = 3 * t - 3 * a := rfl
    _ = 3 * (t - a) := by
      exact (mul_sub 3 t a).symm

/-- Far-tail linear arithmetic for the fixed-tail arctangent comparison. -/
theorem Real.arctan_fixed_tail_far_tail_upper
    {a t : ℝ}
    (ht_far : 2 * a ≤ t) :
    a + t ≤ 3 * (t - a) := by
  have hfour_le_two : 4 * a ≤ 2 * t := by
    calc
      4 * a = 2 * a + 2 * a :=
        Real.four_mul_eq_two_mul_add_two_mul a
      _ ≤ t + t :=
        add_le_add ht_far ht_far
      _ = 2 * t :=
        (Real.two_mul_eq_add_self t).symm
  have hshift :
      4 * a + (t - 3 * a) ≤ 2 * t + (t - 3 * a) :=
    add_le_add_right hfour_le_two (t - 3 * a)
  exact Eq.subst
    (motive := fun x : ℝ => x ≤ 3 * (t - a))
    (Real.arctan_fixed_tail_far_tail_left_eq a t)
    (Eq.subst
      (motive := fun x : ℝ => 4 * a + (t - 3 * a) ≤ x)
      (Real.arctan_fixed_tail_far_tail_right_eq a t)
      hshift)

/-- Algebraic normalization of the first arctangent branch denominator. -/
theorem Complex.arctan_fixed_tail_one_sub_real_div_mul_I_eq
    (w : ℂ)
    (hw : w ≠ 0)
    (t : ℝ) :
    1 - ((t : ℂ) / w) * Complex.I =
      (w - (t : ℂ) * Complex.I) / w := by
  have hdiv_mul_I :
      ((t : ℂ) / w) * Complex.I = ((t : ℂ) * Complex.I) / w := by
    calc
      ((t : ℂ) / w) * Complex.I =
          ((t : ℂ) * w⁻¹) * Complex.I := by
        exact congrArg (fun x : ℂ => x * Complex.I) (div_eq_mul_inv (t : ℂ) w)
      _ = (t : ℂ) * (w⁻¹ * Complex.I) := by
        exact mul_assoc (t : ℂ) w⁻¹ Complex.I
      _ = (t : ℂ) * (Complex.I * w⁻¹) := by
        exact congrArg (fun x : ℂ => (t : ℂ) * x) (mul_comm w⁻¹ Complex.I)
      _ = ((t : ℂ) * Complex.I) * w⁻¹ := by
        exact (mul_assoc (t : ℂ) Complex.I w⁻¹).symm
      _ = ((t : ℂ) * Complex.I) / w := by
        exact (div_eq_mul_inv ((t : ℂ) * Complex.I) w).symm
  calc
    1 - ((t : ℂ) / w) * Complex.I =
        1 - ((t : ℂ) * Complex.I) / w := by
      exact congrArg (fun x : ℂ => 1 - x) hdiv_mul_I
    _ = w / w - ((t : ℂ) * Complex.I) / w := by
      exact congrArg (fun x : ℂ => x - ((t : ℂ) * Complex.I) / w)
        (div_self hw).symm
    _ = (w - (t : ℂ) * Complex.I) / w := by
      exact (sub_div w ((t : ℂ) * Complex.I) w).symm

/-- Algebraic normalization of the second arctangent branch denominator. -/
theorem Complex.arctan_fixed_tail_one_add_real_div_mul_I_eq
    (w : ℂ)
    (hw : w ≠ 0)
    (t : ℝ) :
    1 + ((t : ℂ) / w) * Complex.I =
      (w + (t : ℂ) * Complex.I) / w := by
  have hdiv_mul_I :
      ((t : ℂ) / w) * Complex.I = ((t : ℂ) * Complex.I) / w := by
    calc
      ((t : ℂ) / w) * Complex.I =
          ((t : ℂ) * w⁻¹) * Complex.I := by
        exact congrArg (fun x : ℂ => x * Complex.I) (div_eq_mul_inv (t : ℂ) w)
      _ = (t : ℂ) * (w⁻¹ * Complex.I) := by
        exact mul_assoc (t : ℂ) w⁻¹ Complex.I
      _ = (t : ℂ) * (Complex.I * w⁻¹) := by
        exact congrArg (fun x : ℂ => (t : ℂ) * x) (mul_comm w⁻¹ Complex.I)
      _ = ((t : ℂ) * Complex.I) * w⁻¹ := by
        exact (mul_assoc (t : ℂ) Complex.I w⁻¹).symm
      _ = ((t : ℂ) * Complex.I) / w := by
        exact (div_eq_mul_inv ((t : ℂ) * Complex.I) w).symm
  calc
    1 + ((t : ℂ) / w) * Complex.I =
        1 + ((t : ℂ) * Complex.I) / w := by
      exact congrArg (fun x : ℂ => 1 + x) hdiv_mul_I
    _ = w / w + ((t : ℂ) * Complex.I) / w := by
      exact congrArg (fun x : ℂ => x + ((t : ℂ) * Complex.I) / w)
        (div_self hw).symm
    _ = (w + (t : ℂ) * Complex.I) / w := by
      exact (add_div w ((t : ℂ) * Complex.I) w).symm

/-- Subtracting a real multiple of `I` does not change the real part. -/
theorem Complex.sub_real_mul_I_re
    (w : ℂ)
    (t : ℝ) :
    (w - (t : ℂ) * Complex.I).re = w.re := by
  calc
    (w - (t : ℂ) * Complex.I).re =
        w.re - ((t : ℂ) * Complex.I).re := by
      exact Complex.sub_re w ((t : ℂ) * Complex.I)
    _ = w.re - ((t : ℂ).re * Complex.I.re - (t : ℂ).im * Complex.I.im) := by
      exact congrArg (fun x : ℝ => w.re - x)
        (Complex.mul_re (t : ℂ) Complex.I)
    _ = w.re - (t * 0 - 0 * 1) := by
      exact congrArg
        (fun x : ℝ => w.re - x)
        (congrArg₂ (fun a b : ℝ => a - b)
          (congrArg₂ (fun a b : ℝ => a * b)
            (Complex.ofReal_re t)
            Complex.I_re)
          (congrArg₂ (fun a b : ℝ => a * b)
            (Complex.ofReal_im t)
            Complex.I_im))
    _ = w.re - (0 - 0) := by
      exact congrArg
        (fun x : ℝ => w.re - (x - 0 * 1))
        (mul_zero t)
    _ = w.re - 0 := by
      exact congrArg
        (fun x : ℝ => w.re - x)
        (sub_self 0)
    _ = w.re := by
      exact sub_zero w.re

/-- Adding a real multiple of `I` does not change the real part. -/
theorem Complex.add_real_mul_I_re
    (w : ℂ)
    (t : ℝ) :
    (w + (t : ℂ) * Complex.I).re = w.re := by
  calc
    (w + (t : ℂ) * Complex.I).re =
        w.re + ((t : ℂ) * Complex.I).re := by
      exact Complex.add_re w ((t : ℂ) * Complex.I)
    _ = w.re + ((t : ℂ).re * Complex.I.re - (t : ℂ).im * Complex.I.im) := by
      exact congrArg (fun x : ℝ => w.re + x)
        (Complex.mul_re (t : ℂ) Complex.I)
    _ = w.re + (t * 0 - 0 * 1) := by
      exact congrArg
        (fun x : ℝ => w.re + x)
        (congrArg₂ (fun a b : ℝ => a - b)
          (congrArg₂ (fun a b : ℝ => a * b)
            (Complex.ofReal_re t)
            Complex.I_re)
          (congrArg₂ (fun a b : ℝ => a * b)
            (Complex.ofReal_im t)
            Complex.I_im))
    _ = w.re + (0 - 0) := by
      exact congrArg
        (fun x : ℝ => w.re + (x - 0 * 1))
        (mul_zero t)
    _ = w.re + 0 := by
      exact congrArg
        (fun x : ℝ => w.re + x)
        (sub_self 0)
    _ = w.re := by
      exact add_zero w.re

/-- Absolute value of the real part after subtracting a real multiple of `I`. -/
theorem Complex.abs_re_sub_real_mul_I_eq_of_re_pos
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (t : ℝ) :
    |(w - (t : ℂ) * Complex.I).re| = w.re := by
  have hre_eq : (w - (t : ℂ) * Complex.I).re = w.re :=
    Complex.sub_real_mul_I_re w t
  have hre_nonneg : 0 ≤ (w - (t : ℂ) * Complex.I).re :=
    Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      hre_eq.symm
      (le_of_lt hw_re_pos)
  exact Eq.trans (abs_of_nonneg hre_nonneg) hre_eq

/-- Absolute value of the real part after adding a real multiple of `I`. -/
theorem Complex.abs_re_add_real_mul_I_eq_of_re_pos
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (t : ℝ) :
    |(w + (t : ℂ) * Complex.I).re| = w.re := by
  have hre_eq : (w + (t : ℂ) * Complex.I).re = w.re :=
    Complex.add_real_mul_I_re w t
  have hre_nonneg : 0 ≤ (w + (t : ℂ) * Complex.I).re :=
    Eq.subst
      (motive := fun x : ℝ => 0 ≤ x)
      hre_eq.symm
      (le_of_lt hw_re_pos)
  exact Eq.trans (abs_of_nonneg hre_nonneg) hre_eq

/-- Norm of a nonnegative real multiple of `I`. -/
theorem Complex.norm_real_mul_I_of_nonneg
    {t : ℝ}
    (ht_nonneg : 0 ≤ t) :
    ‖(t : ℂ) * Complex.I‖ = t := by
  have hreal_norm : ‖(t : ℂ)‖ = t := by
    calc
      ‖(t : ℂ)‖ = Complex.abs (t : ℂ) :=
        Complex.norm_eq_abs _
      _ = |t| :=
        Complex.abs_ofReal t
      _ = t :=
        abs_of_nonneg ht_nonneg
  calc
    ‖(t : ℂ) * Complex.I‖ = ‖(t : ℂ)‖ * ‖Complex.I‖ :=
      norm_mul (t : ℂ) Complex.I
    _ = t * 1 := by
      exact congrArg₂ (fun x y : ℝ => x * y) hreal_norm Complex.norm_I
    _ = t :=
      mul_one t

/-- The complex norm of the scalar two is two. -/
theorem Complex.norm_two : ‖(2 : ℂ)‖ = (2 : ℝ) := by
  calc
    ‖(2 : ℂ)‖ = Complex.abs (2 : ℂ) :=
      Complex.norm_eq_abs _
    _ = |(2 : ℝ)| :=
      Complex.abs_ofReal 2
    _ = (2 : ℝ) :=
      abs_of_nonneg zero_le_two

/-- The arctangent logarithm scalar has norm `1 / 2`. -/
theorem Complex.norm_neg_I_div_two_eq_half :
    ‖(-Complex.I / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
  calc
    ‖(-Complex.I / 2 : ℂ)‖ = ‖(-Complex.I : ℂ)‖ / ‖(2 : ℂ)‖ := by
      exact norm_div _ _
    _ = (1 : ℝ) / 2 := by
      exact congrArg₂ (fun x y : ℝ => x / y)
        (Eq.trans (norm_neg Complex.I) Complex.norm_I)
        Complex.norm_two
    _ = (1 / 2 : ℝ) :=
      rfl

/-- The first normalized branch denominator is bounded below by the real part
of the fixed open-half-plane point. -/
theorem Complex.arctan_fixed_tail_one_sub_real_div_mul_I_norm_lower
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
  have hre_abs_eq :
      |(w - (t : ℂ) * Complex.I).re| = w.re :=
    Complex.abs_re_sub_real_mul_I_eq_of_re_pos hw_re_pos t
  have hre_le_norm :
      w.re ≤ ‖w - (t : ℂ) * Complex.I‖ := by
    calc
      w.re = |(w - (t : ℂ) * Complex.I).re| := hre_abs_eq.symm
      _ ≤ ‖w - (t : ℂ) * Complex.I‖ := by
        calc
          |(w - (t : ℂ) * Complex.I).re| ≤
              Complex.abs (w - (t : ℂ) * Complex.I) :=
            Complex.abs_re_le_abs (w - (t : ℂ) * Complex.I)
          _ = ‖w - (t : ℂ) * Complex.I‖ :=
            Eq.symm (Complex.norm_eq_abs _)
  calc
    w.re / ‖w‖ ≤ ‖w - (t : ℂ) * Complex.I‖ / ‖w‖ :=
      div_le_div_of_nonneg_right hre_le_norm (le_of_lt hw_norm_pos)
    _ = ‖(w - (t : ℂ) * Complex.I) / w‖ := by
      exact Eq.symm (norm_div _ _)
    _ = ‖1 - ((t : ℂ) / w) * Complex.I‖ := by
      exact congrArg norm
        (Complex.arctan_fixed_tail_one_sub_real_div_mul_I_eq w hw_ne_zero t).symm

/-- The second normalized branch denominator is bounded below by the real part
of the fixed open-half-plane point. -/
theorem Complex.arctan_fixed_tail_one_add_real_div_mul_I_norm_lower
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
  have hre_abs_eq :
      |(w + (t : ℂ) * Complex.I).re| = w.re :=
    Complex.abs_re_add_real_mul_I_eq_of_re_pos hw_re_pos t
  have hre_le_norm :
      w.re ≤ ‖w + (t : ℂ) * Complex.I‖ := by
    calc
      w.re = |(w + (t : ℂ) * Complex.I).re| := hre_abs_eq.symm
      _ ≤ ‖w + (t : ℂ) * Complex.I‖ := by
        calc
          |(w + (t : ℂ) * Complex.I).re| ≤
              Complex.abs (w + (t : ℂ) * Complex.I) :=
            Complex.abs_re_le_abs (w + (t : ℂ) * Complex.I)
          _ = ‖w + (t : ℂ) * Complex.I‖ :=
            Eq.symm (Complex.norm_eq_abs _)
  calc
    w.re / ‖w‖ ≤ ‖w + (t : ℂ) * Complex.I‖ / ‖w‖ :=
      div_le_div_of_nonneg_right hre_le_norm (le_of_lt hw_norm_pos)
    _ = ‖(w + (t : ℂ) * Complex.I) / w‖ := by
      exact Eq.symm (norm_div _ _)
    _ = ‖1 + ((t : ℂ) / w) * Complex.I‖ := by
      exact congrArg norm
        (Complex.arctan_fixed_tail_one_add_real_div_mul_I_eq w hw_ne_zero t).symm

/-- The principal logarithm is bounded by the absolute logarithm of the norm
plus the universal argument bound. -/
theorem Complex.arctan_fixed_tail_log_norm_le_abs_log_norm_add_pi
    (z : ℂ) :
    ‖Complex.log z‖ ≤ |Real.log ‖z‖| + Real.pi := by
  have hlog_re :
      |(Complex.log z).re| = |Real.log ‖z‖| := by
    have hre :
        (Complex.log z).re = Real.log ‖z‖ := by
      calc
        (Complex.log z).re = Real.log (Complex.abs z) :=
          Complex.log_re z
        _ = Real.log ‖z‖ := by
          exact congrArg Real.log (Eq.symm (Complex.norm_eq_abs z))
    exact congrArg abs hre
  have hlog_im :
      |(Complex.log z).im| = |Complex.arg z| := by
    exact congrArg abs (Complex.log_im z)
  calc
    ‖Complex.log z‖ = Complex.abs (Complex.log z) := Complex.norm_eq_abs _
    _ ≤ |(Complex.log z).re| + |(Complex.log z).im| :=
      Complex.abs_le_abs_re_add_abs_im (Complex.log z)
    _ = |Real.log ‖z‖| + |Complex.arg z| := by
      exact congrArg₂ (fun x y : ℝ => x + y) hlog_re hlog_im
    _ ≤ |Real.log ‖z‖| + Real.pi :=
      add_le_add_left (Complex.abs_arg_le_pi z) _

/-- A positive two-sided bound for a real argument gives a finite bound for
the absolute value of its logarithm. -/
theorem Real.arctan_fixed_tail_abs_log_le_max_abs_log_of_bounds
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
theorem Complex.arctan_fixed_tail_log_norm_le_of_norm_bounds
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
    Real.arctan_fixed_tail_abs_log_le_max_abs_log_of_bounds
      hm_pos hmM hmz hzM
  calc
    ‖Complex.log z‖ ≤ |Real.log ‖z‖| + Real.pi :=
      Complex.arctan_fixed_tail_log_norm_le_abs_log_norm_add_pi z
    _ ≤ max |Real.log m| |Real.log M| + Real.pi :=
      add_le_add_right hlog _

/-- The upper-tail ratio can be rewritten without the common factor `w`. -/
theorem Complex.arctan_fixed_tail_ratio_eq
    (w : ℂ)
    (hw : w ≠ 0)
  (t : ℝ) :
    ((1 + ((t : ℂ) / w) * Complex.I) /
        (1 - ((t : ℂ) / w) * Complex.I)) =
      (w + (t : ℂ) * Complex.I) /
        (w - (t : ℂ) * Complex.I) := by
  calc
    ((1 + ((t : ℂ) / w) * Complex.I) /
        (1 - ((t : ℂ) / w) * Complex.I))
        =
      ((w + (t : ℂ) * Complex.I) / w) /
        ((w - (t : ℂ) * Complex.I) / w) := by
      congr 1
      · exact Complex.arctan_fixed_tail_one_add_real_div_mul_I_eq w hw t
      · exact Complex.arctan_fixed_tail_one_sub_real_div_mul_I_eq w hw t
    _ = (w + (t : ℂ) * Complex.I) /
          (w - (t : ℂ) * Complex.I) := by
      exact div_div_div_cancel_right
        (w + (t : ℂ) * Complex.I)
        (w - (t : ℂ) * Complex.I)
        w

/-- The numerator in the arctangent ratio has norm bounded below by the fixed
positive real part. -/
theorem Complex.arctan_fixed_tail_ratio_numerator_lower
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (t : ℝ) :
    w.re ≤ ‖w + (t : ℂ) * Complex.I‖ := by
  have hre_nonneg : 0 ≤ (w + (t : ℂ) * Complex.I).re := by
    have hre_eq : (w + (t : ℂ) * Complex.I).re = w.re :=
      Complex.add_real_mul_I_re w t
    exact hre_eq.symm ▸ le_of_lt hw_re_pos
  have hre_abs_eq :
      |(w + (t : ℂ) * Complex.I).re| = w.re := by
    have hre_eq : (w + (t : ℂ) * Complex.I).re = w.re :=
      Complex.add_real_mul_I_re w t
    exact congrArg abs hre_eq
  calc
    w.re = |(w + (t : ℂ) * Complex.I).re| := hre_abs_eq.symm
    _ ≤ ‖w + (t : ℂ) * Complex.I‖ := by
      calc
        |(w + (t : ℂ) * Complex.I).re| ≤
            Complex.abs (w + (t : ℂ) * Complex.I) :=
          Complex.abs_re_le_abs (w + (t : ℂ) * Complex.I)
        _ = ‖w + (t : ℂ) * Complex.I‖ :=
          Eq.symm (Complex.norm_eq_abs _)

/-- The denominator in the arctangent ratio has norm bounded below by the fixed
positive real part. -/
theorem Complex.arctan_fixed_tail_ratio_denominator_lower
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
    (t : ℝ) :
    w.re ≤ ‖w - (t : ℂ) * Complex.I‖ := by
  have hre_nonneg : 0 ≤ (w - (t : ℂ) * Complex.I).re := by
    have hre_eq : (w - (t : ℂ) * Complex.I).re = w.re :=
      Complex.sub_real_mul_I_re w t
    exact hre_eq.symm ▸ le_of_lt hw_re_pos
  have hre_abs_eq :
      |(w - (t : ℂ) * Complex.I).re| = w.re := by
    have hre_eq : (w - (t : ℂ) * Complex.I).re = w.re :=
      Complex.sub_real_mul_I_re w t
    exact congrArg abs hre_eq
  calc
    w.re = |(w - (t : ℂ) * Complex.I).re| := hre_abs_eq.symm
    _ ≤ ‖w - (t : ℂ) * Complex.I‖ := by
      calc
        |(w - (t : ℂ) * Complex.I).re| ≤
            Complex.abs (w - (t : ℂ) * Complex.I) :=
          Complex.abs_re_le_abs (w - (t : ℂ) * Complex.I)
        _ = ‖w - (t : ℂ) * Complex.I‖ :=
          Eq.symm (Complex.norm_eq_abs _)

/-- On the bounded part of the tail, the unnormalized numerator is bounded by
`3 * ‖w‖`. -/
theorem Complex.arctan_fixed_tail_numerator_le_three_norm
    {w : ℂ}
    {t : ℝ}
    (ht_nonneg : 0 ≤ t)
    (ht_le : t ≤ 2 * ‖w‖) :
    ‖w + (t : ℂ) * Complex.I‖ ≤ 3 * ‖w‖ := by
  have htI_norm : ‖(t : ℂ) * Complex.I‖ = t := by
    exact Complex.norm_real_mul_I_of_nonneg ht_nonneg
  calc
    ‖w + (t : ℂ) * Complex.I‖ ≤ ‖w‖ + ‖(t : ℂ) * Complex.I‖ :=
      norm_add_le _ _
    _ = ‖w‖ + t := by
      exact congrArg (fun x : ℝ => ‖w‖ + x) htI_norm
    _ ≤ ‖w‖ + 2 * ‖w‖ := add_le_add_left ht_le _
    _ = 3 * ‖w‖ := Real.add_two_mul_self_eq_three_mul ‖w‖

/-- On the bounded part of the tail, the unnormalized denominator is bounded
by `3 * ‖w‖`. -/
theorem Complex.arctan_fixed_tail_denominator_le_three_norm
    {w : ℂ}
    {t : ℝ}
    (ht_nonneg : 0 ≤ t)
    (ht_le : t ≤ 2 * ‖w‖) :
    ‖w - (t : ℂ) * Complex.I‖ ≤ 3 * ‖w‖ := by
  have htI_norm : ‖(t : ℂ) * Complex.I‖ = t := by
    exact Complex.norm_real_mul_I_of_nonneg ht_nonneg
  calc
    ‖w - (t : ℂ) * Complex.I‖ ≤ ‖w‖ + ‖(t : ℂ) * Complex.I‖ := by
      have h := norm_add_le w (-((t : ℂ) * Complex.I))
      exact h
    _ = ‖w‖ + t := by
      exact congrArg (fun x : ℝ => ‖w‖ + x) htI_norm
    _ ≤ ‖w‖ + 2 * ‖w‖ := add_le_add_left ht_le _
    _ = 3 * ‖w‖ := Real.add_two_mul_self_eq_three_mul ‖w‖

/-- On the far part of the tail, the two unnormalized branch distances are
within a factor `3` of one another. -/
theorem Complex.arctan_fixed_tail_far_ratio_bounds
    {w : ℂ}
    {t : ℝ}
    (ht_far : 2 * ‖w‖ ≤ t) :
    ‖w + (t : ℂ) * Complex.I‖ ≤
        3 * ‖w - (t : ℂ) * Complex.I‖ ∧
      ‖w - (t : ℂ) * Complex.I‖ ≤
        3 * ‖w + (t : ℂ) * Complex.I‖ := by
  have ht_nonneg : 0 ≤ t :=
    le_trans (mul_nonneg zero_le_two (norm_nonneg w)) ht_far
  have htI_norm : ‖(t : ℂ) * Complex.I‖ = t := by
    exact Complex.norm_real_mul_I_of_nonneg ht_nonneg
  have htail_upper : ‖w‖ + t ≤ 3 * (t - ‖w‖) := by
    exact Real.arctan_fixed_tail_far_tail_upper ht_far
  have hminus_lower :
      t - ‖w‖ ≤ ‖w - (t : ℂ) * Complex.I‖ := by
    have hrev :
        ‖(t : ℂ) * Complex.I‖ - ‖w‖ ≤
          ‖(t : ℂ) * Complex.I - w‖ :=
      norm_sub_norm_le ((t : ℂ) * Complex.I) w
    have hnorm_eq :
        ‖(t : ℂ) * Complex.I - w‖ =
          ‖w - (t : ℂ) * Complex.I‖ := by
      calc
        ‖(t : ℂ) * Complex.I - w‖ = ‖- (w - (t : ℂ) * Complex.I)‖ := by
          congr 1
          abel
        _ = ‖w - (t : ℂ) * Complex.I‖ := by
          exact norm_neg _
    calc
      t - ‖w‖ = ‖(t : ℂ) * Complex.I‖ - ‖w‖ := by
        exact htI_norm
      _ ≤ ‖(t : ℂ) * Complex.I - w‖ := hrev
      _ = ‖w - (t : ℂ) * Complex.I‖ := hnorm_eq
  have hplus_lower :
      t - ‖w‖ ≤ ‖w + (t : ℂ) * Complex.I‖ := by
    have hrev0 :
        ‖(t : ℂ) * Complex.I‖ - ‖-w‖ ≤
          ‖(t : ℂ) * Complex.I - (-w)‖ :=
      norm_sub_norm_le ((t : ℂ) * Complex.I) (-w)
    have hrev :
        ‖(t : ℂ) * Complex.I‖ - ‖w‖ ≤
          ‖(t : ℂ) * Complex.I - (-w)‖ :=
      norm_neg w ▸ hrev0
    have hnorm_eq :
        ‖(t : ℂ) * Complex.I - (-w)‖ =
          ‖w + (t : ℂ) * Complex.I‖ := by
      have harg_eq :
          (t : ℂ) * Complex.I - (-w) =
            w + (t : ℂ) * Complex.I := by
        calc
          (t : ℂ) * Complex.I - (-w) = (t : ℂ) * Complex.I + w := by
            exact sub_neg_eq_add _ _
          _ = w + (t : ℂ) * Complex.I := by
            exact add_comm _ _
      exact congrArg norm harg_eq
    have hrev' : t - ‖w‖ ≤ ‖w + (t : ℂ) * Complex.I‖ := by
      calc
        t - ‖w‖ = ‖(t : ℂ) * Complex.I‖ - ‖w‖ := by
          exact htI_norm
        _ ≤ ‖(t : ℂ) * Complex.I - (-w)‖ := hrev
        _ = ‖w + (t : ℂ) * Complex.I‖ := hnorm_eq
    exact hrev'
  have hplus_upper :
      ‖w + (t : ℂ) * Complex.I‖ ≤ ‖w‖ + t := by
    calc
      ‖w + (t : ℂ) * Complex.I‖ ≤ ‖w‖ + ‖(t : ℂ) * Complex.I‖ :=
        norm_add_le _ _
      _ = ‖w‖ + t := by
        exact congrArg (fun x : ℝ => ‖w‖ + x) htI_norm
  have hminus_upper :
      ‖w - (t : ℂ) * Complex.I‖ ≤ ‖w‖ + t := by
    calc
      ‖w - (t : ℂ) * Complex.I‖ ≤ ‖w‖ + ‖(t : ℂ) * Complex.I‖ := by
        have h : ‖w - (t : ℂ) * Complex.I‖ ≤ ‖w‖ + ‖(t : ℂ) * Complex.I‖ := by
          exact norm_add_le w (-((t : ℂ) * Complex.I))
        exact h
      _ = ‖w‖ + t := by
        exact congrArg (fun x : ℝ => ‖w‖ + x) htI_norm
  constructor
  · calc
      ‖w + (t : ℂ) * Complex.I‖ ≤ ‖w‖ + t := hplus_upper
      _ ≤ 3 * (t - ‖w‖) := htail_upper
      _ ≤ 3 * ‖w - (t : ℂ) * Complex.I‖ :=
        mul_le_mul_of_nonneg_left hminus_lower
          (le_of_lt Real.arctan_fixed_tail_zero_lt_three)
  · calc
      ‖w - (t : ℂ) * Complex.I‖ ≤ ‖w‖ + t := hminus_upper
      _ ≤ 3 * (t - ‖w‖) := htail_upper
      _ ≤ 3 * ‖w + (t : ℂ) * Complex.I‖ :=
        mul_le_mul_of_nonneg_left hplus_lower
          (le_of_lt Real.arctan_fixed_tail_zero_lt_three)

/-- Fixed-tail ratio bounds after clearing the common factor `w`. -/
theorem Complex.arctan_fixed_tail_ratio_norm_bounds_cleared
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
    have hzero : (0 : ℝ) < 0 := by
      exact hw_re_pos
    exact (lt_irrefl (0 : ℝ)) hzero
  have hw_norm_pos : 0 < ‖w‖ :=
    norm_pos_iff.mpr hw_ne_zero
  let m : ℝ := min (w.re / (3 * ‖w‖)) (1 / 3)
  let M : ℝ := max (3 * ‖w‖ / w.re) 3
  have hthree_pos : (0 : ℝ) < 3 :=
    Real.arctan_fixed_tail_zero_lt_three
  have hden_const_pos : 0 < 3 * ‖w‖ :=
    mul_pos hthree_pos hw_norm_pos
  have hm_pos : 0 < m := by
    dsimp [m]
    exact
      lt_min
        (div_pos hw_re_pos hden_const_pos)
        (div_pos zero_lt_one hthree_pos)
  have hM_ge_three : 3 ≤ M := by
    dsimp [M]
    exact le_max_right _ _
  have hm_le_third : m ≤ (1 / 3 : ℝ) := by
    dsimp [m]
    exact min_le_right _ _
  have hm_le_bounded : m ≤ w.re / (3 * ‖w‖) := by
    dsimp [m]
    exact min_le_left _ _
  have hbounded_le_M : 3 * ‖w‖ / w.re ≤ M := by
    dsimp [M]
    exact le_max_left _ _
  refine ⟨m, M, hm_pos, ?_, ?_⟩
  · exact
      le_trans hm_le_third
        (le_trans Real.one_div_three_le_three hM_ge_three)
  · intro t ht_tail
    have ht_nonneg : 0 ≤ t := by
      have hcut_nonneg : 0 ≤ ‖w‖ / 2 :=
        div_nonneg (norm_nonneg w) zero_le_two
      exact le_trans hcut_nonneg (le_of_lt ht_tail)
    have hnum_lower :
        w.re ≤ ‖w + (t : ℂ) * Complex.I‖ :=
      Complex.arctan_fixed_tail_ratio_numerator_lower hw_re_pos t
    have hden_lower :
        w.re ≤ ‖w - (t : ℂ) * Complex.I‖ :=
      Complex.arctan_fixed_tail_ratio_denominator_lower hw_re_pos t
    have hden_pos : 0 < ‖w - (t : ℂ) * Complex.I‖ :=
      lt_of_lt_of_le hw_re_pos hden_lower
    by_cases ht_bounded : t ≤ 2 * ‖w‖
    · have hnum_upper :
          ‖w + (t : ℂ) * Complex.I‖ ≤ 3 * ‖w‖ :=
        Complex.arctan_fixed_tail_numerator_le_three_norm
          ht_nonneg ht_bounded
      have hden_upper :
          ‖w - (t : ℂ) * Complex.I‖ ≤ 3 * ‖w‖ :=
        Complex.arctan_fixed_tail_denominator_le_three_norm
          ht_nonneg ht_bounded
      constructor
      · have hlower :
            w.re / (3 * ‖w‖) ≤
              ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ :=
          Real.arctan_fixed_tail_div_le_div_of_le_of_le'
            hw_re_pos hden_const_pos hden_pos
            hden_upper hnum_lower
        calc
          m ≤ w.re / (3 * ‖w‖) := hm_le_bounded
          _ ≤ ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ := hlower
          _ = ‖(w + (t : ℂ) * Complex.I) /
                (w - (t : ℂ) * Complex.I)‖ := by
            exact Eq.symm (norm_div _ _)
      · have hupper :
            ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ ≤
              3 * ‖w‖ / w.re :=
          Real.arctan_fixed_tail_div_le_div_of_le_of_le
            hw_re_pos (norm_nonneg _)
            hnum_upper hden_lower
        calc
          ‖(w + (t : ℂ) * Complex.I) /
              (w - (t : ℂ) * Complex.I)‖ =
              ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ := by
            exact Eq.symm (norm_div _ _)
          _ ≤ 3 * ‖w‖ / w.re := hupper
          _ ≤ M := hbounded_le_M
    · have ht_far : 2 * ‖w‖ ≤ t := le_of_not_ge ht_bounded
      rcases
          Complex.arctan_fixed_tail_far_ratio_bounds
            (w := w) (t := t) ht_far with
        ⟨hnum_le, hden_le⟩
      constructor
      · have hthird :
            (1 / 3 : ℝ) ≤
              ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ := by
          have htmp :
              (1 / 3 : ℝ) * ‖w - (t : ℂ) * Complex.I‖ ≤
                ‖w + (t : ℂ) * Complex.I‖ := by
            calc
              (1 / 3 : ℝ) *
                  ‖w - (t : ℂ) * Complex.I‖ ≤
                  (1 / 3 : ℝ) *
                    (3 * ‖w + (t : ℂ) * Complex.I‖) :=
                mul_le_mul_of_nonneg_left hden_le
                  (div_nonneg zero_le_one (le_of_lt hthree_pos))
              _ = ‖w + (t : ℂ) * Complex.I‖ :=
                Real.arctan_fixed_tail_one_div_three_mul_three_mul
                  ‖w + (t : ℂ) * Complex.I‖
          exact (le_div_iff₀ hden_pos).2 htmp
        calc
          m ≤ (1 / 3 : ℝ) := hm_le_third
          _ ≤ ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ := hthird
          _ = ‖(w + (t : ℂ) * Complex.I) /
                (w - (t : ℂ) * Complex.I)‖ := by
            exact Eq.symm (norm_div _ _)
      · have hthree :
            ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ ≤ 3 := by
          exact (div_le_iff₀ hden_pos).2 hnum_le
        calc
          ‖(w + (t : ℂ) * Complex.I) /
              (w - (t : ℂ) * Complex.I)‖ =
              ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ := by
            exact Eq.symm (norm_div _ _)
          _ ≤ 3 := hthree
          _ ≤ M := hM_ge_three

/-- On the fixed upper split interval the Möbius ratio entering the arctangent
has norm bounded above and below by positive constants depending only on `w`. -/
theorem Complex.arctan_fixed_tail_ratio_norm_bounds
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
      Complex.arctan_fixed_tail_ratio_norm_bounds_cleared
        hw_re_pos with
    ⟨m, M, hm_pos, hmM, hbounds⟩
  refine ⟨m, M, hm_pos, hmM, ?_⟩
  intro t ht_tail
  have hw_ne_zero : w ≠ 0 := by
    intro hw_zero
    have : (0 : ℝ) < 0 := by
      exact hw_re_pos
    exact (lt_irrefl (0 : ℝ)) this
  have hratio_eq :
      ‖(1 + ((t : ℂ) / w) * Complex.I) /
        (1 - ((t : ℂ) / w) * Complex.I)‖ =
        ‖(w + (t : ℂ) * Complex.I) /
          (w - (t : ℂ) * Complex.I)‖ := by
    exact congrArg norm (Complex.arctan_fixed_tail_ratio_eq w hw_ne_zero t)
  have hbounds' := hbounds t ht_tail
  constructor
  · have hle : ‖(w + (t : ℂ) * Complex.I) /
          (w - (t : ℂ) * Complex.I)‖ ≤
          ‖(1 + ((t : ℂ) / w) * Complex.I) /
            (1 - ((t : ℂ) / w) * Complex.I)‖ :=
        le_of_eq hratio_eq.symm
    exact le_trans hbounds'.1 hle
  · have hle : ‖(1 + ((t : ℂ) / w) * Complex.I) /
          (1 - ((t : ℂ) / w) * Complex.I)‖ ≤
          ‖(w + (t : ℂ) * Complex.I) /
            (w - (t : ℂ) * Complex.I)‖ :=
        le_of_eq hratio_eq
    exact le_trans hle hbounds'.2

/-- Fixed-ray branch separation gives a uniform bound for the logarithm in
the principal-arctangent formula. -/
theorem Complex.arctan_fixed_tail_log_ratio_bounded
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
      Complex.arctan_fixed_tail_ratio_norm_bounds
        hw_re_pos with
    ⟨m, M, hm_pos, hmM, hbounds⟩
  refine ⟨max |Real.log m| |Real.log M| + Real.pi, ?_, ?_⟩
  · exact add_nonneg (le_max_of_le_left (abs_nonneg _)) Real.pi_pos.le
  · intro t ht_tail
    rcases hbounds t ht_tail with ⟨hlower, hupper⟩
    exact
      Complex.arctan_fixed_tail_log_norm_le_of_norm_bounds
        hm_pos hmM hlower hupper

/-- A uniform logarithm bound for the separated arctangent ratio bounds the
principal arctangent itself. -/
theorem Complex.arctan_fixed_tail_bounded_of_log_ratio_bound
    {w : ℂ}
    (hw_re_pos : 0 < w.re)
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
  have hfactor_norm_le_one : ‖(-Complex.I / 2 : ℂ)‖ ≤ (1 : ℝ) := by
    have hfactor_norm : ‖(-Complex.I / 2 : ℂ)‖ = (1 / 2 : ℝ) := by
      exact Complex.norm_neg_I_div_two_eq_half
    calc
      ‖(-Complex.I / 2 : ℂ)‖ = (1 / 2 : ℝ) := hfactor_norm
      _ ≤ (1 : ℝ) := Real.half_le_one
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
      exact rfl
    _ ≤ ‖Complex.log ((1 + z * Complex.I) / (1 - z * Complex.I))‖ := hmul
    _ ≤ L := hL t ht_tail

/-- Fixed-ray ratio bounds give a uniform bound for the principal arctangent
on the upper split interval. -/
theorem Complex.arctan_fixed_tail_bounded
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ B : ℝ,
      0 ≤ B ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          ‖Complex.arctan ((t : ℂ) / w)‖ ≤ B := by
  exact
    Complex.arctan_fixed_tail_bounded_of_log_ratio_bound
      hw_re_pos
      (Complex.arctan_fixed_tail_log_ratio_bounded hw_re_pos)

/-- A uniform arctangent bound on the upper split interval becomes a linear
bound because the split cutoff is strictly positive in the open right
half-plane. -/
theorem Complex.arctan_fixed_openRightHalfPlane_ray_tail_linear_bound_of_bounded
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
    have : (0 : ℝ) < 0 := by
      exact hw_re_pos
    exact (lt_irrefl (0 : ℝ)) this
  have hw_norm_pos : 0 < ‖w‖ :=
    norm_pos_iff.mpr hw_ne_zero
  let C : ℝ := 2 * B / ‖w‖
  have hC_nonneg : 0 ≤ C :=
    div_nonneg (mul_nonneg zero_le_two hB_nonneg)
      (le_of_lt hw_norm_pos)
  refine ⟨C, hC_nonneg, ?_⟩
  intro t ht_tail
  have ht_lower : ‖w‖ / 2 ≤ t :=
    le_of_lt ht_tail
  have hC_mul_lower : B ≤ C * t := by
    have hmul :
        B ≤ C * (‖w‖ / 2) := by
      have hmul_eq : B = C * (‖w‖ / 2) := by
        calc
          B = (2 * B / ‖w‖) * (‖w‖ / 2) :=
            (Real.arctan_fixed_tail_two_mul_div_mul_half_eq
              (B := B) (r := ‖w‖) hw_norm_pos.ne').symm
          _ = C * (‖w‖ / 2) := rfl
      exact le_of_eq hmul_eq
    have hC_mul_mono :
        C * (‖w‖ / 2) ≤ C * t :=
      mul_le_mul_of_nonneg_left ht_lower hC_nonneg
    exact le_trans hmul hC_mul_mono
  exact le_trans (hB t ht_tail) hC_mul_lower

/-- Along a fixed ray in the open right half-plane, the principal arctangent
is linearly bounded on every tail.

This is the exact fixed-ray arctangent owner estimate needed to prove
integrability of the Binet kernel before the downstream sectorial split file is
available. -/
theorem Complex.arctan_fixed_openRightHalfPlane_ray_tail_linear_bound
    {w : ℂ}
    (hw_re_pos : 0 < w.re) :
    ∃ C : ℝ,
      0 ≤ C ∧
      ∀ t : ℝ,
        t ∈ Set.Ioi (‖w‖ / 2) →
          ‖Complex.arctan ((t : ℂ) / w)‖ ≤ C * t := by
  exact
    Complex.arctan_fixed_openRightHalfPlane_ray_tail_linear_bound_of_bounded
      hw_re_pos
      (Complex.arctan_fixed_tail_bounded hw_re_pos)

end

end LFunctions
end Boundary
