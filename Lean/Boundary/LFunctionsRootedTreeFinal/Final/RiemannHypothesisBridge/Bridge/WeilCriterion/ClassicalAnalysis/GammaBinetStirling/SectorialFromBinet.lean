import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.Binet

/-!
# Sectorial estimates from Binet

This file owns the sectorial remainder estimate extracted from the
Binet-kernel majorant package.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology

/-- Trivial real nonnegativity of `2`, named to keep arithmetic side
conditions out of the Binet estimates. -/
theorem Real.zero_le_two_real : (0 : ℝ) ≤ 2 :=
  zero_le_two

/-- Trivial strict lower bound for `8`, named to keep arithmetic side conditions
out of the Binet estimates. -/
theorem Real.zero_lt_eight_real : (0 : ℝ) < 8 := by
  exact lt_of_lt_of_le zero_lt_one one_le_ofNat

/-- Multiplying by two twice gives the explicit coefficient four. -/
theorem Real.two_mul_two_mul
    (x : ℝ) :
    2 * (2 * x) = 4 * x := by
  calc
    2 * (2 * x) = (2 * 2 : ℝ) * x := mul_assoc 2 2 x
    _ = 4 * x := rfl

/-- Multiplying coefficient four by two gives coefficient eight. -/
theorem Real.two_mul_four_mul
    (x : ℝ) :
    2 * (4 * x) = 8 * x := by
  calc
    2 * (4 * x) = (2 * 4 : ℝ) * x := mul_assoc 2 4 x
    _ = 8 * x := rfl

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
      exact div_eq_mul_inv (2 * B) 2
    _ = B := by
      exact Eq.symm (Real.eq_two_mul_mul_half B)

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
  calc
    x + 2 * x = x + (x + x) := by
      exact congrArg (fun z : ℝ => x + z) (two_mul x)
    _ = x + x + x := by
      exact Eq.symm (add_assoc x x x)
    _ = 3 * x := by
      exact Eq.symm (three_mul x)

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

/-- Multiplying by `1 / 3` cancels a leading factor `3`. -/
theorem Real.one_div_three_mul_three_mul
    (x : ℝ) :
    (1 / 3 : ℝ) * (3 * x) = x := by
  calc
    (1 / 3 : ℝ) * (3 * x)
        = ((1 / 3 : ℝ) * 3) * x :=
            mul_assoc (1 / 3 : ℝ) 3 x
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
      congr 1
      exact Real.norm_of_nonneg (abs_nonneg t)
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
    Eq.symm (sub_add_cancel_of_le hn_le_t)
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
    exact le_of_lt hw_re_pos
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
    exact le_of_lt hw_re_pos
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
    ‖Complex.log z‖ = Complex.abs (Complex.log z) := norm_eq_abs _
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
  norm_pos_iff.mpr (Complex.ne_zero_of_re_pos hw_re_pos)

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
    exact le_of_lt hw_re_pos
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
              exact Complex.mul_re (t : ℂ) Complex.I
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
    exact le_of_lt hw_re_pos
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
              exact Complex.mul_re (t : ℂ) Complex.I
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
      show ‖w + -((t : ℂ) * Complex.I)‖ ≤ ‖w‖ + ‖-((t : ℂ) * Complex.I)‖
      exact norm_add_le _ _
    _ = ‖w‖ + t := by
      exact congrArg (fun x : ℝ => ‖w‖ + x) (norm_neg ((t : ℂ) * Complex.I) ▸ htI_norm)
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
      have hrev' : ‖(t : ℂ) * Complex.I‖ - ‖w‖ ≤ ‖w - (t : ℂ) * Complex.I‖ := by
        exact hnorm_eq.symm ▸ htI_norm ▸ hrev
      exact hrev'
  have hplus_lower :
      t - ‖w‖ ≤ ‖w + (t : ℂ) * Complex.I‖ := by
    have hrev :
        ‖(t : ℂ) * Complex.I‖ - ‖w‖ ≤
          ‖(t : ℂ) * Complex.I - (-w)‖ :=
      norm_sub_norm_le ((t : ℂ) * Complex.I) (-w)
    have hnorm_eq :
        ‖(t : ℂ) * Complex.I - (-w)‖ =
          ‖w + (t : ℂ) * Complex.I‖ := by
      exact by
        calc
          ‖(t : ℂ) * Complex.I - (-w)‖ = ‖w + (t : ℂ) * Complex.I‖ := by
            congr 1
            exact Complex.sub_neg_eq_add_comm ((t : ℂ) * Complex.I) w
    exact by
      have hrev' : ‖(t : ℂ) * Complex.I‖ - ‖w‖ ≤ ‖w + (t : ℂ) * Complex.I‖ := by
        exact hnorm_eq.symm ▸ htI_norm ▸ hrev
      exact hrev'
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
        exact norm_add_le _ _
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
  · exact le_trans (le_of_lt hm_pos) hM_ge_three
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
              ‖w + (t : ℂ) * Complex.I‖).symm.le
          exact (le_div_iff₀ hden_pos).mp hmul'
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
          exact (div_le_iff₀ hden_pos).2 hthird
          exact hnum_le
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
  have hw_ne_zero : w ≠ 0 :=
    Complex.ne_zero_of_re_pos hw_re_pos
  refine ⟨m, M, hm_pos, hmM, ?_⟩
  intro t ht_tail
  have h := hbounds t ht_tail
  constructor
  · exact Eq.trans h.1 (Complex.binetSecondFormula_arctan_tail_ratio_eq_norm w hw_ne_zero t)
  · exact Eq.trans h.2 (Complex.binetSecondFormula_arctan_tail_ratio_eq_norm w hw_ne_zero t).symm

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
  · exact le_trans (le_of_lt hm_pos) hM_ge_three
  · intro w hw_re_pos hw_sep t ht_tail
    have hw_ne_zero : w ≠ 0 :=
      Complex.ne_zero_of_re_pos hw_re_pos
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
      calc
        ε * (3 * ‖w‖) = 3 * (ε * ‖w‖) := by
          exact Real.mul_three_mul_reassoc ε ‖w‖
        _ ≤ 3 * w.re :=
          mul_le_mul_of_nonneg_left hsep_mul (le_of_lt hthree_pos)
    have hbounded_upper_const :
        3 * ‖w‖ / w.re ≤ 3 / ε := by
      exact (div_le_div_iff₀ hw_re_pos hε).2
      calc
        3 * ‖w‖ * ε = 3 * (ε * ‖w‖) := by
          exact Real.three_mul_mul_reassoc ε ‖w‖
        _ ≤ 3 * w.re :=
          mul_le_mul_of_nonneg_left hsep_mul (le_of_lt hthree_pos)
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
              (Complex.binetSecondFormula_arctan_tail_ratio_eq_norm w hw_ne_zero t)
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
            exact (Complex.binetSecondFormula_arctan_tail_ratio_eq_norm w hw_ne_zero t).symm.trans
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
          exact (le_div_iff₀ hden_pos).2 hthird
          calc
            (1 / 3 : ℝ) *
                ‖w - (t : ℂ) * Complex.I‖ ≤
                (1 / 3 : ℝ) *
                  (3 * ‖w + (t : ℂ) * Complex.I‖) :=
              mul_le_mul_of_nonneg_left hden_le
                (div_nonneg zero_le_one (le_of_lt hthree_pos))
            _ = ‖w + (t : ℂ) * Complex.I‖ :=
              Real.one_div_three_mul_three_mul
                ‖w + (t : ℂ) * Complex.I‖
        calc
          m ≤ (1 / 3 : ℝ) := hm_le_third
          _ ≤ ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ := hthird
          _ = ‖(1 + ((t : ℂ) / w) * Complex.I) /
                (1 - ((t : ℂ) / w) * Complex.I)‖ := by
            exact (norm_div _ _).symm.trans
              (Complex.binetSecondFormula_arctan_tail_ratio_eq_norm w hw_ne_zero t)
      · have hthree :
            ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ ≤ 3 := by
          exact (div_le_iff₀ hden_pos).2 hthree
          exact hnum_le
        calc
          ‖(1 + ((t : ℂ) / w) * Complex.I) /
              (1 - ((t : ℂ) / w) * Complex.I)‖ =
              ‖w + (t : ℂ) * Complex.I‖ /
                ‖w - (t : ℂ) * Complex.I‖ := by
            exact (Complex.binetSecondFormula_arctan_tail_ratio_eq_norm w hw_ne_zero t).symm.trans
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
    have hmeas : Measurable K := by
      fun_prop
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
      exact hden_norm
    _ ≤ (C * t) /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
      div_le_div_of_nonneg_right harctan hden_nonneg
    _ =
        C * (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
      exact (mul_div_assoc _ _ _).symm

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
      exact hden_norm
    _ ≤ (C * t) /
          (Real.exp ((2 : ℝ) * Real.pi * t) - 1) :=
      div_le_div_of_nonneg_right harctan hden_nonneg
    _ =
        C * (t / (Real.exp ((2 : ℝ) * Real.pi * t) - 1)) := by
      exact (mul_div_assoc _ _ _).symm

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
    have hmeas : Measurable K := by
      fun_prop
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
      2 * ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2),
          Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) +
        2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2),
          Complex.arctan ((t : ℂ) / w) /
            (Complex.exp (((2 : ℝ) * Real.pi * t : ℝ) : ℂ) - 1) := by
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
        ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t +
          ∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t := by
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
        exact hunion
      _ =
          ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t +
            ∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t := by
        exact
          setIntegral_union hdisjoint measurableSet_Ioi
            hsmall_integrable htail_integrable
  calc
    Complex.binetSecondFormulaRemainder w =
        2 * ∫ t : ℝ in Set.Ioi (0 : ℝ), K t := by
      rfl
    _ =
        2 *
            (∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t +
              ∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t) := by
      exact hsplit
    _ =
        2 * ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t +
          2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t := by
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
      (Eventually.of_forall (fun t ht => ht.1))
  have hscaled_mono :
      ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), c * M t ≤
        c * ∫ t : ℝ in Set.Ioi (0 : ℝ), M t := by
    calc
      ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), c * M t =
          c * ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), M t := by
        exact integral_const_mul c M
      _ ≤ c * ∫ t : ℝ in Set.Ioi (0 : ℝ), M t :=
        mul_le_mul_of_nonneg_left hmono hc_nonneg
  calc
    ‖2 * ∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t‖ =
        2 * ‖∫ t : ℝ in Set.Ioc (0 : ℝ) (‖w‖ / 2), K t‖ := by
      exact norm_mul _ _
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
      (Eventually.of_forall (fun t ht => lt_of_le_of_lt hcut_nonneg ht))
  have hscaled_mono :
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2), C * M t ≤
        C * ∫ t : ℝ in Set.Ioi (0 : ℝ), M t := by
    calc
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2), C * M t =
          C * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), M t := by
        exact integral_const_mul C M
      _ ≤ C * ∫ t : ℝ in Set.Ioi (0 : ℝ), M t :=
        mul_le_mul_of_nonneg_left hmono hC_nonneg
  calc
    ‖2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t‖ =
        2 * ‖∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t‖ := by
      exact norm_mul _ _
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
      (Eventually.of_forall (fun t ht => lt_of_le_of_lt hcut_nonneg ht))
  have hscaled_mono :
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2), C * M t ≤
        C * ∫ t : ℝ in Set.Ioi (0 : ℝ), M t := by
    calc
      ∫ t : ℝ in Set.Ioi (‖w‖ / 2), C * M t =
          C * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), M t := by
        exact integral_const_mul C M
      _ ≤ C * ∫ t : ℝ in Set.Ioi (0 : ℝ), M t :=
        mul_le_mul_of_nonneg_left hmono hC_nonneg
  calc
    ‖2 * ∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t‖ =
        2 * ‖∫ t : ℝ in Set.Ioi (‖w‖ / 2), K t‖ := by
      exact norm_mul _ _
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
  · have hJ_pos : 0 < J :=
      Real.binetSecondFormula_kernel_majorant_integral_pos
    have hJ_nonneg : 0 ≤ J :=
      le_of_lt hJ_pos
    have hfourJ_nonneg : 0 ≤ 4 * J :=
      mul_nonneg Real.zero_le_four hJ_nonneg
    have htail_nonneg : 0 ≤ 2 * Ct * J :=
      mul_nonneg (mul_nonneg Real.zero_le_two_real hCt_nonneg)
        hJ_nonneg
    exact add_nonneg (add_nonneg hfourJ_nonneg htail_nonneg) zero_le_one
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
      exact Complex.binetSecondFormulaRemainder_eq_small_add_tail hw_re_pos
    have hsmall :
        ‖S‖ ≤ 4 * J := by
      have hsmall_raw :
          ‖S‖ ≤ 4 * J / ‖w‖ :=
        Complex.binetSecondFormulaRemainder_small_norm_le_integral_majorant
          hw_re_pos
      have hJ_nonneg : 0 ≤ J :=
        le_of_lt Real.binetSecondFormula_kernel_majorant_integral_pos
      have hfourJ_nonneg : 0 ≤ 4 * J :=
        mul_nonneg Real.zero_le_four hJ_nonneg
      have hdiv_le : 4 * J / ‖w‖ ≤ 4 * J := by
        exact div_le_of_le_mul₀ hfourJ_nonneg
          (lt_of_lt_of_le zero_lt_one hw_large)
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
        exact hsplit
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
    Eventually.of_forall (fun t ht => ht.1)
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
