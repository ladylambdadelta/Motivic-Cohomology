import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.SetIntegral
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteHoleSubdivision

/-!
# Endpoint cap-collar Cauchy balances for finite Abel-Plana

This file owns the left and right endpoint half-collar domains, oriented boundary
identifications, and normalized endpoint cap-collar balance theorems.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open MeasureTheory

-- Notation for closed intervals: [[a, b]] now maps to Set.Icc a b
-- This replaces legacy Lean 3 interval notation with Lean 4 Mathlib syntax
notation:max "[[" a "," b "]]" => Set.Icc a b

/-- Algebraic cancellation for the finite-hole subdivision once the cap/collar
boundary has been identified with the missing deleted-arc contribution. -/
theorem Complex.finiteAbelPlana_log_verticalStrip_add_deleted_sub_verticalStrip_sub_deleted
    (A B : ℂ) :
    A + (B - A) - B = 0 := by
  calc
    A + (B - A) - B = B - B := by
      exact congrArg (fun u : ℂ => u - B) (add_sub_cancel_left A B)
    _ = 0 := sub_self B

/-- Left distributivity over two summands, oriented for collection. -/
theorem Complex.left_mul_add_two_collect
    (a b c : ℂ) :
    a * b + a * c = a * (b + c) :=
  Eq.symm (mul_add a b c)

/-- Left distributivity over three summands, oriented for collection. -/
theorem Complex.left_mul_add_three_collect
    (a b c d : ℂ) :
    a * b + a * c + a * d = a * (b + c + d) := by
  calc
    a * b + a * c + a * d = a * (b + c) + a * d := by
      exact congrArg (fun u : ℂ => u + a * d)
        (Complex.left_mul_add_two_collect a b c)
    _ = a * ((b + c) + d) := by
      exact Complex.left_mul_add_two_collect a (b + c) d
    _ = a * (b + c + d) := rfl

/-- Collect the three left endpoint cap/collar boundary pieces after the chord
terms cancel. -/
theorem Complex.leftEndpointCapCollarBoundary_collect
    (lowerT upperT lowerChord upperChord safeLower safeMiddle safeUpper
      pvLower pvUpper arc : ℂ) :
    (lowerT - lowerChord + Complex.I * safeLower - Complex.I * pvLower) +
        (upperChord - upperT + Complex.I * safeUpper - Complex.I * pvUpper) +
          (lowerChord - upperChord + Complex.I * safeMiddle - arc) =
      lowerT - upperT +
          Complex.I * (safeLower + safeMiddle + safeUpper) -
        Complex.I * (pvLower + pvUpper) - arc := by
  calc
    (lowerT - lowerChord + Complex.I * safeLower - Complex.I * pvLower) +
        (upperChord - upperT + Complex.I * safeUpper - Complex.I * pvUpper) +
          (lowerChord - upperChord + Complex.I * safeMiddle - arc) =
      lowerT - upperT +
          (Complex.I * safeLower + Complex.I * safeMiddle + Complex.I * safeUpper) -
        (Complex.I * pvLower + Complex.I * pvUpper) - arc := by
      abel_nf
    _ =
      lowerT - upperT +
          Complex.I * (safeLower + safeMiddle + safeUpper) -
        Complex.I * (pvLower + pvUpper) - arc := by
      exact congrArg₂
        (fun safe pv : ℂ => lowerT - upperT + safe - pv - arc)
        (Complex.left_mul_add_three_collect
          Complex.I safeLower safeMiddle safeUpper)
        (Complex.left_mul_add_two_collect
          Complex.I pvLower pvUpper)

/-- Collect the three right endpoint cap/collar boundary pieces after the chord
terms cancel. -/
theorem Complex.rightEndpointCapCollarBoundary_collect
    (lowerT upperT lowerChord upperChord pvLower pvUpper safeLower safeMiddle
      safeUpper arc : ℂ) :
    (lowerT - lowerChord + Complex.I * pvLower - Complex.I * safeLower) +
        (upperChord - upperT + Complex.I * pvUpper - Complex.I * safeUpper) +
          (lowerChord - upperChord - Complex.I * safeMiddle - arc) =
      lowerT - upperT + Complex.I * (pvLower + pvUpper) -
        Complex.I * (safeLower + safeMiddle + safeUpper) - arc := by
  calc
    (lowerT - lowerChord + Complex.I * pvLower - Complex.I * safeLower) +
        (upperChord - upperT + Complex.I * pvUpper - Complex.I * safeUpper) +
          (lowerChord - upperChord - Complex.I * safeMiddle - arc) =
      lowerT - upperT +
          (Complex.I * pvLower + Complex.I * pvUpper) -
        (Complex.I * safeLower + Complex.I * safeMiddle + Complex.I * safeUpper) -
        arc := by
      abel_nf
    _ =
      lowerT - upperT + Complex.I * (pvLower + pvUpper) -
        Complex.I * (safeLower + safeMiddle + safeUpper) - arc := by
      exact congrArg₂
        (fun pv safe : ℂ => lowerT - upperT + pv - safe - arc)
        (Complex.left_mul_add_two_collect
          Complex.I pvLower pvUpper)
        (Complex.left_mul_add_three_collect
          Complex.I safeLower safeMiddle safeUpper)

/-- The norm of a purely vertical complex displacement is the absolute value
of its real height. -/
theorem Complex.norm_I_mul_real (y : ℝ) :
    ‖Complex.I * (y : ℂ)‖ = |y| := by
  calc
    ‖Complex.I * (y : ℂ)‖ = ‖Complex.I‖ * ‖(y : ℂ)‖ :=
      norm_mul Complex.I (y : ℂ)
    _ = (1 : ℝ) * ‖(y : ℂ)‖ :=
      congrArg (fun r : ℝ => r * ‖(y : ℂ)‖) Complex.norm_I
    _ = ‖(y : ℂ)‖ := one_mul ‖(y : ℂ)‖
    _ = |y| := RCLike.norm_ofReal y

/-- Cancelling a real center from a vertical translate leaves only the
vertical displacement. -/
theorem Complex.norm_centered_vertical_translate_sub_center
    (M : ℂ)
    (y : ℝ) :
    ‖(M + Complex.I * (y : ℂ)) - M‖ = |y| := by
  have hcancel :
      (M + Complex.I * (y : ℂ)) - M = Complex.I * (y : ℂ) :=
    add_sub_cancel_left M (Complex.I * (y : ℂ))
  calc
    ‖(M + Complex.I * (y : ℂ)) - M‖ =
        ‖Complex.I * (y : ℂ)‖ :=
      congrArg norm hcancel
    _ = |y| := Complex.norm_I_mul_real y

/-- A positive natural number is at least one after coercion to `ℝ`. -/
theorem Real.one_le_natCast_of_pos
    {m : ℕ}
    (hm : 0 < m) :
    (1 : ℝ) ≤ (m : ℝ) :=
  (Nat.cast_le : ((1 : ℝ) ≤ (m : ℝ) ↔ 1 ≤ m)).mpr
    (Nat.succ_le_iff.mpr hm)

/-- The successor of a natural number is at least one after coercion to `ℝ`. -/
theorem Real.one_le_natCast_succ
    (N : ℕ) :
    (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) :=
  (Nat.cast_le : ((1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) ↔ 1 ≤ N + 1)).mpr
    (Nat.succ_le_succ (Nat.zero_le N))

/-- Natural-number order transports to real coercions. -/
theorem Real.natCast_le_natCast
    {m N : ℕ}
    (h : m ≤ N) :
    (m : ℝ) ≤ (N : ℝ) :=
  (Nat.cast_le : ((m : ℝ) ≤ (N : ℝ) ↔ m ≤ N)).mpr h

/-- Successor coercion to `ℝ`. -/
theorem Real.natCast_succ_eq
    (N : ℕ) :
    (((N + 1 : ℕ) : ℝ) : ℝ) = (N : ℝ) + 1 :=
  Nat.cast_succ N

/-- The Abel-Plana quarter gap is smaller than a half gap. -/
theorem Real.lt_one_div_two_of_lt_one_div_four
    {ρ : ℝ}
    (hρ : ρ < (1 : ℝ) / 4) :
    ρ < (1 : ℝ) / 2 :=
  lt_trans hρ Real.finiteAbelPlana_one_div_four_lt_one_div_two

/-- Subtracting a nonnegative real number moves weakly left. -/
theorem Real.sub_nonneg_le_self
    (x ρ : ℝ)
    (hρ : 0 ≤ ρ) :
    x - ρ ≤ x :=
  sub_le_self x hρ

/-- Negation reverses a real inequality, named for endpoint-height interval
normalization. -/
theorem Real.endpoint_neg_le_neg_of_le
    {a b : ℝ}
    (h : a ≤ b) :
    -b ≤ -a :=
  neg_le_neg h

/-- If `0 < ρ` and `0 < T`, then the lower indentation height is inside the
ambient upper height. -/
theorem Real.endpoint_neg_radius_le_height
    {T ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ) :
    -ρ ≤ T := by
  exact (neg_nonpos.mpr hρ.le).trans hT.le

/-- If `0 < T` and `0 < ρ`, then the lower ambient height is below the upper
indentation height. -/
theorem Real.endpoint_neg_height_le_radius
    {T ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ) :
    -T ≤ ρ := by
  exact (neg_nonpos.mpr hT.le).trans hρ.le

/-- If `0 < ρ < T`, then the lower ambient height is below the lower
indentation height. -/
theorem Real.endpoint_neg_height_le_neg_radius
    {T ρ : ℝ}
    (hρT : ρ < T) :
    -T ≤ -ρ :=
  Real.endpoint_neg_le_neg_of_le hρT.le

/-- The deleted-geometry half-height condition implies the indentation radius
is smaller than the positive ambient height. -/
theorem Real.endpoint_radius_lt_height_of_lt_abs_height_half
    {T ρ : ℝ}
    (hT : 0 < T)
    (hρ_abs : ρ < |T| / 2) :
    ρ < T := by
  have hT_abs : |T| = T := abs_of_pos hT
  have hρ_half : ρ < T / 2 := by
    exact hT_abs ▸ hρ_abs
  exact hρ_half.trans (half_lt_self hT)

/-- A radius below a positive height is below the absolute height. -/
theorem Real.endpoint_radius_lt_abs_height
    {T ρ : ℝ}
    (hT : 0 < T)
    (hρT : ρ < T) :
    ρ < |T| :=
  Eq.mpr
    (congrArg (fun r : ℝ => ρ < r) (abs_of_pos hT).symm)
    hρT

/-- The lower endpoint indentation interval lies inside the full vertical
height interval. -/
theorem Real.endpoint_lower_interval_subset_height
    {T ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρT : ρ < T) :
    ∀ y ∈ [[(-T), (-ρ)]], y ∈ [[-T, T]] := by
  intro y hy
  have horder : -T ≤ -ρ :=
    Real.endpoint_neg_height_le_neg_radius hρT
  have hyIcc : y ∈ Set.Icc (-T) (-ρ) :=
    Eq.mp
      (congrArg (fun S : Set ℝ => y ∈ S) (Set.uIcc_of_le horder))
      hy
  have hy_le_T : y ≤ T :=
    hyIcc.2.trans
      (Real.endpoint_neg_radius_le_height (hρ.trans hρT) hρ)
  exact
    Eq.mpr
      (congrArg (fun S : Set ℝ => y ∈ S)
        (Set.uIcc_of_le (neg_le_self (le_of_lt (hρ.trans hρT)))))
      (And.intro hyIcc.1 hy_le_T)

/-- The middle endpoint indentation interval lies inside the full vertical
height interval. -/
theorem Real.endpoint_middle_interval_subset_height
    {T ρ : ℝ}
    (hρ : 0 < ρ)
    (hρT : ρ < T) :
    ∀ y ∈ [[(-ρ), ρ]], y ∈ [[-T, T]] := by
  intro y hy
  have horder : -ρ ≤ ρ :=
    (neg_nonpos.mpr hρ.le).trans hρ.le
  have hyIcc : y ∈ Set.Icc (-ρ) ρ :=
    Eq.mp
      (congrArg (fun S : Set ℝ => y ∈ S) (Set.uIcc_of_le horder))
      hy
  have hy_ge_negT : -T ≤ y :=
    (Real.endpoint_neg_height_le_neg_radius hρT).trans hyIcc.1
  have hy_le_T : y ≤ T :=
    hyIcc.2.trans hρT.le
  exact
    Eq.mpr
      (congrArg (fun S : Set ℝ => y ∈ S)
        (Set.uIcc_of_le (neg_le_self (le_of_lt (hρ.trans hρT)))))
      (And.intro hy_ge_negT hy_le_T)

/-- The upper endpoint indentation interval lies inside the full vertical
height interval. -/
theorem Real.endpoint_upper_interval_subset_height
    {T ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρT : ρ < T) :
    ∀ y ∈ [[ρ, T]], y ∈ [[-T, T]] := by
  intro y hy
  have horder : ρ ≤ T := le_of_lt hρT
  have hyIcc : y ∈ Set.Icc ρ T :=
    Eq.mp
      (congrArg (fun S : Set ℝ => y ∈ S) (Set.uIcc_of_le horder))
      hy
  have hy_ge_negT : -T ≤ y :=
    (Real.endpoint_neg_height_le_radius hT hρ).trans hyIcc.1
  exact
    Eq.mpr
      (congrArg (fun S : Set ℝ => y ∈ S)
        (Set.uIcc_of_le (neg_le_self hT.le)))
      (And.intro hy_ge_negT hyIcc.2)

/-- A radius smaller than `1/2` has doubled radius at most `1`. -/
theorem Real.endpoint_two_radius_le_one_of_lt_half
    {ρ : ℝ}
    (hρ : ρ < (1 : ℝ) / 2) :
    ρ + ρ ≤ (1 : ℝ) := by
  have hsum : ρ + ρ ≤ (1 : ℝ) / 2 + (1 : ℝ) / 2 :=
    add_le_add hρ.le hρ.le
  exact hsum.trans_eq (add_halves (1 : ℝ))

/-- A radius smaller than `1/2` satisfies the endpoint disk-separation
inequality `ρ - 1 ≤ -ρ`. -/
theorem Real.endpoint_radius_sub_one_le_neg_radius_of_lt_half
    {ρ : ℝ}
    (hρ : ρ < (1 : ℝ) / 2) :
    ρ - 1 ≤ -ρ := by
  have hdouble : ρ + ρ ≤ (1 : ℝ) :=
    Real.endpoint_two_radius_le_one_of_lt_half hρ
  have hle_sub : ρ ≤ 1 - ρ :=
    le_sub_iff_add_le.mpr hdouble
  have hle_add : ρ ≤ -ρ + 1 := by
    calc
      ρ ≤ 1 - ρ := hle_sub
      _ = 1 + -ρ := sub_eq_add_neg 1 ρ
      _ = -ρ + 1 := add_comm 1 (-ρ)
  exact sub_le_iff_le_add.mpr hle_add

/-- Left endpoint collar separation from a nonzero integer center. -/
theorem Real.endpoint_left_re_sub_integer_le_neg_radius
    {x ρ m : ℝ}
    (hx : x ≤ ρ)
    (hm : 1 ≤ m)
    (hρ : ρ < (1 : ℝ) / 2) :
    x - m ≤ -ρ := by
  have hxm : x - m ≤ ρ - 1 :=
    sub_le_sub hx hm
  exact hxm.trans
    (Real.endpoint_radius_sub_one_le_neg_radius_of_lt_half hρ)

/-- Rebracketing `M + (1 - ρ)` as `(M + 1) - ρ`. -/
theorem Real.endpoint_add_one_sub_radius_eq
    (M ρ : ℝ) :
    M + (1 - ρ) = (M + 1) - ρ := by
  calc
    M + (1 - ρ) = M + (1 + -ρ) :=
      congrArg (fun x : ℝ => M + x) (sub_eq_add_neg 1 ρ)
    _ = (M + 1) + -ρ :=
      add_assoc M 1 (-ρ)
    _ = (M + 1) - ρ :=
      (sub_eq_add_neg (M + 1) ρ).symm

/-- Right endpoint collar separation from the previous integer center. -/
theorem Real.endpoint_radius_le_successor_minus_radius_sub_nat
    (N : ℕ)
    {ρ : ℝ}
    (hρ : ρ < (1 : ℝ) / 2) :
    ρ ≤ (((N + 1 : ℕ) : ℝ) - ρ) - (N : ℝ) := by
  have hdouble : ρ + ρ ≤ (1 : ℝ) :=
    Real.endpoint_two_radius_le_one_of_lt_half hρ
  have htarget : ρ ≤ 1 - ρ :=
    le_sub_iff_add_le.mpr hdouble
  have hbase : ρ ≤ (((N : ℝ) + 1) - ρ) - (N : ℝ) := by
    calc
      ρ ≤ 1 - ρ := htarget
      _ = ((N : ℝ) + (1 - ρ)) - (N : ℝ) :=
        (add_sub_cancel_left (N : ℝ) (1 - ρ)).symm
      _ = (((N : ℝ) + 1) - ρ) - (N : ℝ) :=
        congrArg (fun x : ℝ => x - (N : ℝ))
          (Real.endpoint_add_one_sub_radius_eq (N : ℝ) ρ)
  exact
    hbase.trans_eq
      (congrArg (fun x : ℝ => (x - ρ) - (N : ℝ))
        (Real.natCast_succ_eq N).symm)

/-- Endpoint-local transport from ordered closed-interval bounds to `uIcc`
membership. -/
theorem Real.endpoint_mem_uIcc_of_bounds
    {a b x : ℝ}
    (horder : a ≤ b)
    (h : a ≤ x ∧ x ≤ b) :
    x ∈ Set.uIcc a b :=
  Eq.mpr
    (congrArg (fun S : Set ℝ => x ∈ S) (Set.uIcc_of_le horder))
    h

/-- Endpoint-local transport from `uIcc` membership to ordered closed-interval
bounds. -/
theorem Real.endpoint_bounds_of_mem_uIcc
    {a b x : ℝ}
    (horder : a ≤ b)
    (h : x ∈ Set.uIcc a b) :
    a ≤ x ∧ x ≤ b :=
  Eq.mp
    (congrArg (fun S : Set ℝ => x ∈ S) (Set.uIcc_of_le horder))
    h

/-- Endpoint-local equality transport for `uIcc` membership. -/
theorem Real.endpoint_mem_uIcc_congr
    {a b x y : ℝ}
    (hxy : x = y)
    (hy : y ∈ Set.uIcc a b) :
    x ∈ Set.uIcc a b :=
  Eq.mp
    (congrArg (fun t : ℝ => t ∈ Set.uIcc a b) hxy.symm)
    hy

/-- Endpoint-local equality transport for `uIcc` membership, with equality in
the reverse orientation. -/
theorem Real.endpoint_mem_uIcc_congr_symm
    {a b x y : ℝ}
    (hxy : x = y)
    (hx : x ∈ Set.uIcc a b) :
    y ∈ Set.uIcc a b :=
  Eq.mp
    (congrArg (fun t : ℝ => t ∈ Set.uIcc a b) hxy)
    hx

/-- Ball membership as the norm inequality for endpoint collar estimates. -/
theorem Complex.endpoint_norm_lt_of_mem_ball
    (z c : ℂ)
    {ρ : ℝ}
    (h : z ∈ Metric.ball c ρ) :
    ‖z - c‖ < ρ :=
  Eq.mp
    (congrArg (fun r : ℝ => r < ρ) (dist_eq_norm z c))
    (Metric.mem_ball.mp h)

/-- The real part of subtracting a natural-number point on the real axis. -/
theorem Complex.endpoint_sub_natCast_re
    (z : ℂ)
    (m : ℕ) :
    (z - (m : ℂ)).re = z.re - (m : ℝ) := by
  calc
    (z - (m : ℂ)).re = z.re - (m : ℂ).re :=
      Complex.sub_re z (m : ℂ)
    _ = z.re - (m : ℝ) := rfl

/-- The imaginary part of subtracting a natural-number point on the real axis. -/
theorem Complex.endpoint_sub_natCast_im
    (z : ℂ)
    (m : ℕ) :
    (z - (m : ℂ)).im = z.im := by
  calc
    (z - (m : ℂ)).im = z.im - (m : ℂ).im :=
      Complex.sub_im z (m : ℂ)
    _ = z.im - 0 := rfl
    _ = z.im := sub_zero z.im

/-- The norm dominates the absolute value of the real coordinate. -/
theorem Complex.endpoint_abs_re_le_norm
    (z : ℂ) :
    |z.re| ≤ ‖z‖ :=
  Complex.abs_re_le_abs z

/-- The norm dominates the absolute value of the imaginary coordinate. -/
theorem Complex.endpoint_abs_im_le_norm
    (z : ℂ) :
    |z.im| ≤ ‖z‖ :=
  Complex.abs_im_le_abs z

/-- A point whose imaginary coordinate has absolute value at least `ρ` cannot
lie in the centered endpoint disk of radius `ρ`. -/
theorem Complex.endpoint_not_mem_center_ball_of_radius_le_abs_im
    {z : ℂ}
    {ρ : ℝ}
    (hρ : ρ ≤ |z.im|) :
    z ∉ Metric.ball (0 : ℂ) ρ :=
  fun hball =>
    let hdist : ‖z‖ < ρ :=
      Complex.endpoint_norm_lt_of_mem_ball z (0 : ℂ) hball
    let him_norm : |z.im| ≤ ‖z‖ :=
      Complex.endpoint_abs_im_le_norm z
    not_lt_of_ge (hρ.trans him_norm) hdist

/-- A point whose centered real coordinate has absolute value at least `ρ`
cannot lie in the endpoint disk of radius `ρ`. -/
theorem Complex.endpoint_not_mem_ball_of_radius_le_abs_re_sub_center
    {z c : ℂ}
    {ρ : ℝ}
    (hρ : ρ ≤ |(z - c).re|) :
    z ∉ Metric.ball c ρ :=
  fun hball =>
    let hdist : ‖z - c‖ < ρ :=
      Complex.endpoint_norm_lt_of_mem_ball z c hball
    let hre_norm : |(z - c).re| ≤ ‖z - c‖ :=
      Complex.endpoint_abs_re_le_norm (z - c)
    not_lt_of_ge (hρ.trans hre_norm) hdist

/-- The left endpoint cap/collar domain: the rectangular cap
`0 ≤ Re z ≤ ρ`, `-T ≤ Im z ≤ T`, with the deleted endpoint disk removed.

This is the local planar domain used in the classical Abel-Plana contour proof
near the endpoint pole at `0`. -/
def Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain
    (T ρ : ℝ) : Set ℂ :=
  ({z : ℂ | z.re ∈ [[(0 : ℝ), ρ]] ∧ z.im ∈ [[-T, T]]} : Set ℂ) \
    Metric.ball (0 : ℂ) ρ

/-- Membership in the left endpoint cap/collar domain is coordinatewise
membership in the endpoint rectangular cap plus avoidance of the deleted
endpoint disk. -/
theorem Complex.mem_finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain_iff
    {T ρ : ℝ}
    {z : ℂ} :
    z ∈ Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ ↔
      z.re ∈ [[(0 : ℝ), ρ]] ∧ z.im ∈ [[-T, T]] ∧
        z ∉ Metric.ball (0 : ℂ) ρ := by
  show
    z ∈ ({z : ℂ | z.re ∈ [[(0 : ℝ), ρ]] ∧ z.im ∈ [[-T, T]]} : Set ℂ) \
        Metric.ball (0 : ℂ) ρ ↔
      z.re ∈ [[(0 : ℝ), ρ]] ∧ z.im ∈ [[-T, T]] ∧
        z ∉ Metric.ball (0 : ℂ) ρ
  constructor
  · intro hz
    exact ⟨hz.1.1, hz.1.2, hz.2⟩
  · intro hz
    exact ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩

/-- A point in the left endpoint cap rectangle, after deleting the endpoint
disk, avoids every deleted integer disk in the finite Abel-Plana rectangle. -/
theorem Complex.finiteAbelPlanaLogLeftEndpointCapCollarPoint_not_mem_deletedDisk
    {N m : ℕ}
    {T ρ : ℝ}
    (_hm : m ∈ Finset.range (N + 2))
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4)
    {z : ℂ}
    (hzre : z.re ∈ [[(0 : ℝ), ρ]])
    (_hzim : z.im ∈ [[-T, T]])
    (hzcentral : z ∉ Metric.ball (0 : ℂ) ρ) :
    z ∉ Metric.ball (m : ℂ) ρ := by
  by_cases hmzero : m = 0
  · subst m
    exact hzcentral
  · intro hzball
    have hm_pos : 0 < m := Nat.pos_of_ne_zero hmzero
    have hone_le_m : (1 : ℝ) ≤ (m : ℝ) := by
      exact Real.one_le_natCast_of_pos hm_pos
    have hρ_lt_half : ρ < (1 : ℝ) / 2 := by
      exact Real.lt_one_div_two_of_lt_one_div_four hρquarter
    have hzIcc : z.re ∈ Set.Icc (0 : ℝ) ρ := by
      exact Real.endpoint_bounds_of_mem_uIcc hρnonneg hzre
    have hzre_le : z.re ≤ ρ := hzIcc.2
    have hdist_lt : ‖z - (m : ℂ)‖ < ρ := by
      exact Complex.endpoint_norm_lt_of_mem_ball z (m : ℂ) hzball
    have hre_norm :
        |(z - (m : ℂ)).re| ≤ ‖z - (m : ℂ)‖ := by
      exact Complex.abs_re_le_abs (z - (m : ℂ))
    have hre_le_neg : (z - (m : ℂ)).re ≤ -ρ := by
      have hreal :
          z.re - (m : ℝ) ≤ -ρ :=
        Real.endpoint_left_re_sub_integer_le_neg_radius
          hzre_le hone_le_m hρ_lt_half
      exact (Complex.endpoint_sub_natCast_re z m).symm ▸ hreal
    have hρ_le_abs : ρ ≤ |(z - (m : ℂ)).re| := by
      have hneg : ρ ≤ -((z - (m : ℂ)).re) :=
        neg_le_neg hre_le_neg
      exact hneg.trans (neg_le_abs _)
    exact not_lt_of_ge (hρ_le_abs.trans hre_norm) hdist_lt

/-- The closed left endpoint cap rectangle lies in the ambient finite
Abel-Plana rectangle. -/
theorem Complex.finiteAbelPlanaLogLeftEndpointCapCollarClosedRectangle_subset_closedRectangle
    {N : ℕ}
    {T ρ : ℝ}
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4) :
    ({z : ℂ | z.re ∈ [[(0 : ℝ), ρ]] ∧ z.im ∈ [[-T, T]]} : Set ℂ) ⊆
      Complex.finiteAbelPlanaClosedRectangle N T := by
  intro z hz
  have hzIcc : z.re ∈ Set.Icc (0 : ℝ) ρ := by
    exact Real.endpoint_bounds_of_mem_uIcc hρnonneg hz.1
  have hρ_lt_one : ρ < 1 := by
    exact Real.lt_one_of_lt_one_div_four hρquarter
  refine Complex.mem_reProdIm.mpr ⟨?_, hz.2⟩
  have hone_le_succ : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
    exact Real.one_le_natCast_succ N
  exact ⟨hzIcc.1, hzIcc.2.trans (le_of_lt hρ_lt_one).trans hone_le_succ⟩

/-- The left endpoint cap/collar domain lies in the finite Abel-Plana
punctured rectangle. -/
theorem Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain_subset_puncturedRectangle
    {N : ℕ}
    (T : ℝ)
    {ρ : ℝ}
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ ⊆
      Complex.finiteAbelPlanaPuncturedRectangle N T ρ := by
  intro z hz
  have hzdata :
      z.re ∈ [[(0 : ℝ), ρ]] ∧ z.im ∈ [[-T, T]] ∧
        z ∉ Metric.ball (0 : ℂ) ρ :=
    Complex.mem_finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain_iff.mp hz
  have hclosed :
      z ∈ Complex.finiteAbelPlanaClosedRectangle N T :=
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarClosedRectangle_subset_closedRectangle
      hρnonneg hρquarter ⟨hzdata.1, hzdata.2.1⟩
  have havoid :
      ∀ m ∈ Finset.range (N + 2), z ∉ Metric.ball (m : ℂ) ρ := by
    intro m hm
    exact
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarPoint_not_mem_deletedDisk
        hm hρnonneg hρquarter hzdata.1 hzdata.2.1 hzdata.2.2
  exact
    Complex.mem_finiteAbelPlanaPuncturedRectangle_iff.mpr
      ⟨hclosed, havoid⟩

/-- Continuity of the Abel-Plana rectangle integrand on the left endpoint
cap/collar domain, transported from the ambient punctured rectangle. -/
theorem Complex.continuousOn_finiteAbelPlanaLogRectangleIntegrand_leftEndpointCapCollar
    {w : ℂ}
    {N : ℕ}
    {T ρ : ℝ}
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    ContinuousOn
      (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
      (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ) := by
  exact
    hcont.mono
      (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain_subset_puncturedRectangle
        T hρnonneg hρquarter)

/-- Holomorphy of the Abel-Plana rectangle integrand on the left endpoint
cap/collar domain, transported from the ambient punctured rectangle. -/
theorem Complex.differentiableOn_finiteAbelPlanaLogRectangleIntegrand_leftEndpointCapCollar
    {w : ℂ}
    {N : ℕ}
    {T ρ : ℝ}
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4)
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    DifferentiableOn ℂ
      (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
      (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ) := by
  exact
    hdiff.mono
      (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain_subset_puncturedRectangle
        T hρnonneg hρquarter)

/-- A point on the right semicircle around the left endpoint lies in the
left endpoint punctured cap/collar domain.

This is the endpoint-specific geometric fact that replaces the false full-disk
containment statement: only the right semicircle, not the whole disk, belongs
to the left cap. -/
theorem Complex.finiteAbelPlanaLogLeftEndpointSemicirclePoint_mem_capCollar
    {T ρ θ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρT : ρ < T)
    (hθ : θ ∈ Set.Icc (-(Real.pi / 2)) (Real.pi / 2)) :
    ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) ∈
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ := by
  have hρnonneg : 0 ≤ ρ := le_of_lt hρ
  have hre :
      (((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).re) =
        ρ * Real.cos θ := by
    ring_nf
  have him :
      (((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im) =
        ρ * Real.sin θ := by
    ring_nf
  have hcos_nonneg : 0 ≤ Real.cos θ :=
    Real.cos_nonneg_of_mem_Icc hθ
  have hre_mem :
      (((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).re) ∈
        [[(0 : ℝ), ρ]] := by
    have hleft : 0 ≤ ρ * Real.cos θ :=
      mul_nonneg hρnonneg hcos_nonneg
    have hright : ρ * Real.cos θ ≤ ρ :=
      mul_le_of_le_one_right hρnonneg (Real.cos_le_one θ)
    exact
      Eq.mp
        (congrArg
          (fun x : ℝ => x ∈ [[(0 : ℝ), ρ]])
          hre.symm)
        (Real.endpoint_mem_uIcc_of_bounds hρnonneg (And.intro hleft hright))
  have hsin_abs : |Real.sin θ| ≤ 1 := by
    exact abs_le.mpr (Real.sin_mem_Icc θ)
  have him_abs : |ρ * Real.sin θ| ≤ ρ := by
    calc
      |ρ * Real.sin θ| = ρ * |Real.sin θ| := by
        exact (abs_mul ρ (Real.sin θ)).trans
          (congrArg (fun r : ℝ => r * |Real.sin θ|)
            (abs_of_nonneg hρnonneg))
      _ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hsin_abs hρnonneg
      _ = ρ := mul_one ρ
  have him_mem :
      (((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im) ∈
        [[-T, T]] := by
    have habsT : |ρ * Real.sin θ| ≤ T :=
      him_abs.trans (le_of_lt hρT)
    have hb := abs_le.mp habsT
    exact
      Eq.mp
        (congrArg
          (fun y : ℝ => y ∈ [[-T, T]])
          him.symm)
        (Real.endpoint_mem_uIcc_of_bounds (neg_le_self hT.le) hb)
  have hnot_ball :
      ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) ∉
        Metric.ball (0 : ℂ) ρ := by
      have hz_eq :
        ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
          circleMap (0 : ℂ) ρ θ := by
      unfold circleMap
      ring_nf
    exact hz_eq ▸ circleMap_not_mem_ball (0 : ℂ) ρ θ
  exact
    Complex.mem_finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain_iff.mpr
      ⟨hre_mem, him_mem, hnot_ball⟩

/-- Points on the left principal-value vertical side belong to the left
endpoint punctured cap/collar domain. -/
theorem Complex.finiteAbelPlanaLogLeftEndpointPVVerticalPoint_mem_capCollar
    {T ρ y : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hy : y ∈ [[-T, -ρ]] ∨ y ∈ [[ρ, T]]) :
    (Complex.I * (y : ℂ)) ∈
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ := by
  have hρnonneg : 0 ≤ ρ := le_of_lt hρ
  have hre_mem :
      (Complex.I * (y : ℂ)).re ∈ [[(0 : ℝ), ρ]] := by
    have hre : (Complex.I * (y : ℂ)).re = 0 := by
      ring_nf
    exact
      Real.endpoint_mem_uIcc_congr hre
        (Real.endpoint_mem_uIcc_of_bounds hρnonneg
          (And.intro le_rfl hρnonneg))
  have him_mem :
      (Complex.I * (y : ℂ)).im ∈ [[-T, T]] := by
    rcases hy with hy | hy
    · have horder : -T ≤ -ρ := hy.1
      have hyIcc : y ∈ Set.Icc (-T) (-ρ) :=
        Real.endpoint_bounds_of_mem_uIcc horder hy
      have hleT : y ≤ T :=
        hyIcc.2.trans (Real.endpoint_neg_radius_le_height hT hρ)
      exact
        Real.endpoint_mem_uIcc_of_bounds (neg_le_self hT.le)
          (And.intro hyIcc.1 hleT)
    · have horder : ρ ≤ T := hy.1
      have hyIcc : y ∈ Set.Icc ρ T :=
        Real.endpoint_bounds_of_mem_uIcc horder hy
      have hge_negT : -T ≤ y :=
        (Real.endpoint_neg_height_le_radius hT hρ).trans hyIcc.1
      exact
        Real.endpoint_mem_uIcc_of_bounds (neg_le_self hT.le)
          (And.intro hge_negT hyIcc.2)
  have hnot_ball :
      (Complex.I * (y : ℂ)) ∉ Metric.ball (0 : ℂ) ρ := by
    intro hball
    have hdist : ‖Complex.I * (y : ℂ)‖ < ρ := by
      exact
        Complex.endpoint_norm_lt_of_mem_ball
          (Complex.I * (y : ℂ)) (0 : ℂ) hball
    have hρ_le_abs_y : ρ ≤ |y| := by
      rcases hy with hy | hy
      · have horder : -T ≤ -ρ := hy.1
        have hyIcc : y ∈ Set.Icc (-T) (-ρ) :=
          Real.endpoint_bounds_of_mem_uIcc horder hy
        have hneg : ρ ≤ -y :=
          Real.endpoint_neg_le_neg_of_le hyIcc.2
        exact hneg.trans (neg_le_abs y)
      · have horder : ρ ≤ T := hy.1
        have hyIcc : y ∈ Set.Icc ρ T :=
          Real.endpoint_bounds_of_mem_uIcc horder hy
        exact hyIcc.1.trans (le_abs_self y)
    have hnorm : ‖Complex.I * (y : ℂ)‖ = |y| :=
      Complex.norm_I_mul_real y
    have hdist_abs : |y| < ρ :=
      Eq.subst (motive := fun r : ℝ => r < ρ) hnorm hdist
    exact not_lt_of_ge hρ_le_abs_y hdist_abs
  exact
    Complex.mem_finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain_iff.mpr
      ⟨hre_mem, him_mem, hnot_ball⟩

/-- Points on the safe vertical side `Re z = ρ` belong to the left endpoint
punctured cap/collar domain. -/
theorem Complex.finiteAbelPlanaLogLeftEndpointSafeVerticalPoint_mem_capCollar
    {T ρ y : ℝ}
    (hρ : 0 < ρ)
    (hy : y ∈ [[-T, T]]) :
    ((ρ : ℂ) + Complex.I * (y : ℂ)) ∈
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ := by
  have hρnonneg : 0 ≤ ρ := le_of_lt hρ
  have hre_mem :
      (((ρ : ℂ) + Complex.I * (y : ℂ)).re) ∈ [[(0 : ℝ), ρ]] := by
    have hre : ((ρ : ℂ) + Complex.I * (y : ℂ)).re = ρ := by
      ring_nf
    exact
      Real.endpoint_mem_uIcc_congr hre
        (Real.endpoint_mem_uIcc_of_bounds hρnonneg
          (And.intro hρnonneg le_rfl))
  have him_mem :
      (((ρ : ℂ) + Complex.I * (y : ℂ)).im) ∈ [[-T, T]] := by
    exact hy
  have hnot_ball :
      ((ρ : ℂ) + Complex.I * (y : ℂ)) ∉ Metric.ball (0 : ℂ) ρ := by
    intro hball
    have hdist : ‖((ρ : ℂ) + Complex.I * (y : ℂ))‖ < ρ := by
      exact
        Complex.endpoint_norm_lt_of_mem_ball
          ((ρ : ℂ) + Complex.I * (y : ℂ)) (0 : ℂ) hball
    have hre_norm :
        |(((ρ : ℂ) + Complex.I * (y : ℂ))).re| ≤
          ‖((ρ : ℂ) + Complex.I * (y : ℂ))‖ := by
      exact
        Complex.endpoint_abs_re_le_norm
          ((ρ : ℂ) + Complex.I * (y : ℂ))
    have hρ_le_norm : ρ ≤ ‖((ρ : ℂ) + Complex.I * (y : ℂ))‖ := by
      have hre_abs : |(((ρ : ℂ) + Complex.I * (y : ℂ))).re| = ρ := by
        have hre : (((ρ : ℂ) + Complex.I * (y : ℂ))).re = ρ := by
          ring_nf
        exact hre ▸ abs_of_nonneg hρnonneg
      exact hre_abs ▸ hre_norm
    exact not_lt_of_ge hρ_le_norm hdist
  exact
    Complex.mem_finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain_iff.mpr
      ⟨hre_mem, him_mem, hnot_ball⟩

/-- The lower left endpoint rectangle
`0 ≤ Re z ≤ ρ`, `-T ≤ Im z ≤ -ρ` lies in the left endpoint punctured
cap/collar domain. -/
theorem Complex.finiteAbelPlanaLogLeftEndpointLowerRectangle_subset_capCollar
    {T ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρT : ρ < T) :
    ([[((0 : ℂ).re), ((ρ : ℂ) - Complex.I * (ρ : ℂ)).re]] ×ℂ
        [[(-T), (-ρ)]]) ⊆
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ := by
  intro z hz
  have hzre : z.re ∈ [[(0 : ℝ), ρ]] := by
    exact (Complex.mem_reProdIm.mp hz).1
  have hzim_lower : z.im ∈ [[-T, -ρ]] := by
    exact (Complex.mem_reProdIm.mp hz).2
  have horder : -T ≤ -ρ :=
    Real.endpoint_neg_height_le_neg_radius hρT
  have hzimIcc : z.im ∈ Set.Icc (-T) (-ρ) :=
    Real.endpoint_bounds_of_mem_uIcc horder hzim_lower
  have hzim : z.im ∈ [[-T, T]] := by
    have hleT : z.im ≤ T :=
      hzimIcc.2.trans
        (Real.endpoint_neg_radius_le_height (hρ.trans hρT) hρ)
    exact
      Real.endpoint_mem_uIcc_of_bounds (neg_le_self (le_of_lt (hρ.trans hρT)))
        (And.intro hzimIcc.1 hleT)
  have hnot_ball : z ∉ Metric.ball (0 : ℂ) ρ := by
    have hρ_le_abs_im : ρ ≤ |z.im| := by
      have hneg : ρ ≤ -z.im :=
        Real.endpoint_neg_le_neg_of_le hzimIcc.2
      exact hneg.trans (neg_le_abs z.im)
    exact
      Complex.endpoint_not_mem_center_ball_of_radius_le_abs_im
        hρ_le_abs_im
  exact
    Complex.mem_finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain_iff.mpr
      ⟨hzre, hzim, hnot_ball⟩

/-- The upper left endpoint rectangle
`0 ≤ Re z ≤ ρ`, `ρ ≤ Im z ≤ T` lies in the left endpoint punctured
cap/collar domain. -/
theorem Complex.finiteAbelPlanaLogLeftEndpointUpperRectangle_subset_capCollar
    {T ρ : ℝ}
    (hρ : 0 < ρ)
    (hρT : ρ < T) :
    ([[((0 : ℂ).re), ((ρ : ℂ) + Complex.I * (ρ : ℂ)).re]] ×ℂ
        [[ρ, T]]) ⊆
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ := by
  intro z hz
  have hzre : z.re ∈ [[(0 : ℝ), ρ]] := by
    exact (Complex.mem_reProdIm.mp hz).1
  have hzim_upper : z.im ∈ [[ρ, T]] := by
    exact (Complex.mem_reProdIm.mp hz).2
  have horder : ρ ≤ T := le_of_lt hρT
  have hzimIcc : z.im ∈ Set.Icc ρ T :=
    Real.endpoint_bounds_of_mem_uIcc horder hzim_upper
  have hzim : z.im ∈ [[-T, T]] := by
    have hge_negT : -T ≤ z.im :=
      (Real.endpoint_neg_height_le_radius (hρ.trans hρT) hρ).trans
        hzimIcc.1
    exact
      Real.endpoint_mem_uIcc_of_bounds (neg_le_self (le_of_lt (hρ.trans hρT)))
        (And.intro hge_negT hzimIcc.2)
  have hnot_ball : z ∉ Metric.ball (0 : ℂ) ρ := by
    have hρ_le_abs_im : ρ ≤ |z.im| :=
      hzimIcc.1.trans (le_abs_self z.im)
    exact
      Complex.endpoint_not_mem_center_ball_of_radius_le_abs_im
        hρ_le_abs_im
  exact
    Complex.mem_finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain_iff.mpr
      ⟨hzre, hzim, hnot_ball⟩

/-- Coordinate normalization for the lower left endpoint rectangle boundary. -/
theorem Complex.leftEndpointLowerRectangleBoundaryIntegral_normalize_rectBoundary
    (f : ℂ → ℂ)
    (T ρ : ℝ)
    (hrect :
      (∫ x : ℝ in (-Complex.I * (T : ℂ)).re..
          (((ρ : ℂ) - Complex.I * (ρ : ℂ)).re),
          f ((x : ℂ) + ((-Complex.I * (T : ℂ)).im : ℂ) * Complex.I)) -
          (∫ x : ℝ in (-Complex.I * (T : ℂ)).re..
            (((ρ : ℂ) - Complex.I * (ρ : ℂ)).re),
            f ((x : ℂ) + ((((ρ : ℂ) - Complex.I * (ρ : ℂ)).im) : ℂ) *
              Complex.I)) +
            Complex.I •
              (∫ y : ℝ in (-Complex.I * (T : ℂ)).im..
                (((ρ : ℂ) - Complex.I * (ρ : ℂ)).im),
                f (((((ρ : ℂ) - Complex.I * (ρ : ℂ)).re) : ℂ) +
                  (y : ℂ) * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in (-Complex.I * (T : ℂ)).im..
                  (((ρ : ℂ) - Complex.I * (ρ : ℂ)).im),
                  f (((-Complex.I * (T : ℂ)).re : ℂ) + (y : ℂ) * Complex.I)) =
        0) :
    (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (T : ℂ))) -
        (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (ρ : ℂ))) +
          Complex.I *
            (∫ y : ℝ in (-T)..(-ρ), f ((ρ : ℂ) + Complex.I * (y : ℂ))) -
            Complex.I *
              (∫ y : ℝ in (-T)..(-ρ), f (Complex.I * (y : ℂ))) =
      0 := by
  ring_nf at hrect
  exact hrect

/-- Transport the generic rectangular Cauchy-Goursat boundary to the lower
left endpoint cap coordinates. -/
theorem Complex.leftEndpointLowerRectangleBoundaryIntegral_of_rectBoundary
    (f : ℂ → ℂ)
    (T : ℝ)
    {ρ : ℝ}
    (z₀ z₁ : ℂ)
    (hz₀ : z₀ = -Complex.I * (T : ℂ))
    (hz₁ : z₁ = (ρ : ℂ) - Complex.I * (ρ : ℂ))
    (hrect :
      (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₀.im : ℂ) * Complex.I)) -
          (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₁.im : ℂ) * Complex.I)) +
            Complex.I •
              (∫ y : ℝ in z₀.im..z₁.im, f ((z₁.re : ℂ) + (y : ℂ) * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in z₀.im..z₁.im, f ((z₀.re : ℂ) + (y : ℂ) * Complex.I)) =
        0) :
    (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (T : ℂ))) -
        (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (ρ : ℂ))) +
          Complex.I *
            (∫ y : ℝ in (-T)..(-ρ), f ((ρ : ℂ) + Complex.I * (y : ℂ))) -
            Complex.I *
              (∫ y : ℝ in (-T)..(-ρ), f (Complex.I * (y : ℂ))) =
      0 := by
  subst z₀
  subst z₁
  exact
    Complex.leftEndpointLowerRectangleBoundaryIntegral_normalize_rectBoundary
      f T ρ hrect

/-- Cauchy-Goursat on the lower ordinary rectangle in the left endpoint cap.

This is the lower rectangular piece of the classical endpoint indentation
argument.  The remaining endpoint cap theorem is obtained by adding this to
the corresponding upper rectangle and the circular cap deformation. -/
theorem Complex.leftEndpointLowerRectangleBoundaryIntegral_eq_zero
    (f : ℂ → ℂ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρT : ρ < T)
    (hcont :
      ContinuousOn f
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ)) :
    (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (T : ℂ))) -
        (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (ρ : ℂ))) +
          Complex.I *
            (∫ y : ℝ in (-T)..(-ρ), f ((ρ : ℂ) + Complex.I * (y : ℂ))) -
            Complex.I *
              (∫ y : ℝ in (-T)..(-ρ), f (Complex.I * (y : ℂ))) =
      0 := by
  let z₀ : ℂ := -Complex.I * (T : ℂ)
  let z₁ : ℂ := (ρ : ℂ) - Complex.I * (ρ : ℂ)
  have hclosed :
      ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) ⊆
        Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ := by
    unfold z₀
    unfold z₁
    exact
      Complex.finiteAbelPlanaLogLeftEndpointLowerRectangle_subset_capCollar
        hT hρ hρT
  have hopen :
      (Set.Ioo (min z₀.re z₁.re) (max z₀.re z₁.re) ×ℂ
          Set.Ioo (min z₀.im z₁.im) (max z₀.im z₁.im)) ⊆
        Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ := by
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
  exact
    Complex.leftEndpointLowerRectangleBoundaryIntegral_of_rectBoundary
      f T z₀ z₁ rfl rfl hcauchy

/-- Transport the generic rectangular Cauchy-Goursat boundary to the upper
left endpoint cap coordinates. -/
theorem Complex.leftEndpointUpperRectangleBoundaryIntegral_of_rectBoundary
    (f : ℂ → ℂ)
    (T : ℝ)
    {ρ : ℝ}
    (z₀ z₁ : ℂ)
    (hz₀ : z₀ = Complex.I * (ρ : ℂ))
    (hz₁ : z₁ = (ρ : ℂ) + Complex.I * (T : ℂ))
    (hrect :
      (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₀.im : ℂ) * Complex.I)) -
          (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₁.im : ℂ) * Complex.I)) +
            Complex.I •
              (∫ y : ℝ in z₀.im..z₁.im, f ((z₁.re : ℂ) + (y : ℂ) * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in z₀.im..z₁.im, f ((z₀.re : ℂ) + (y : ℂ) * Complex.I)) =
        0) :
    (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) + Complex.I * (ρ : ℂ))) -
        (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) + Complex.I * (T : ℂ))) +
          Complex.I *
            (∫ y : ℝ in ρ..T, f ((ρ : ℂ) + Complex.I * (y : ℂ))) -
            Complex.I *
              (∫ y : ℝ in ρ..T, f (Complex.I * (y : ℂ))) =
      0 := by
  subst z₀
  subst z₁
  ring_nf at hrect
  exact hrect

/-- Cauchy-Goursat on the upper ordinary rectangle in the left endpoint cap. -/
theorem Complex.leftEndpointUpperRectangleBoundaryIntegral_eq_zero
    (f : ℂ → ℂ)
    (T : ℝ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hρT : ρ < T)
    (hcont :
      ContinuousOn f
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ)) :
    (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) + Complex.I * (ρ : ℂ))) -
        (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) + Complex.I * (T : ℂ))) +
          Complex.I *
            (∫ y : ℝ in ρ..T, f ((ρ : ℂ) + Complex.I * (y : ℂ))) -
            Complex.I *
              (∫ y : ℝ in ρ..T, f (Complex.I * (y : ℂ))) =
      0 := by
  let z₀ : ℂ := Complex.I * (ρ : ℂ)
  let z₁ : ℂ := (ρ : ℂ) + Complex.I * (T : ℂ)
  have hclosed :
      ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) ⊆
        Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ := by
    unfold z₀
    unfold z₁
    exact
      Complex.finiteAbelPlanaLogLeftEndpointUpperRectangle_subset_capCollar
        hρ hρT
  have hopen :
      (Set.Ioo (min z₀.re z₁.re) (max z₀.re z₁.re) ×ℂ
          Set.Ioo (min z₀.im z₁.im) (max z₀.im z₁.im)) ⊆
        Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ := by
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
  exact
    Complex.leftEndpointUpperRectangleBoundaryIntegral_of_rectBoundary
      f T z₀ z₁ rfl rfl hcauchy

/-- Transport the right-half deleted-disk model boundary to the left endpoint
half-collar coordinates. -/
theorem Complex.leftEndpointHalfRectangleDeletedDiskBoundary_of_model
    (f : ℂ → ℂ)
    {ρ : ℝ}
    (hmodel :
      (∫ x : ℝ in (0 : ℝ)..((0 : ℂ).re + ρ),
          f (((x : ℝ) : ℂ) + Complex.I * (((0 : ℂ).im - ρ : ℝ) : ℂ))) +
          -(∫ x : ℝ in (0 : ℝ)..((0 : ℂ).re + ρ),
            f (((x : ℝ) : ℂ) + Complex.I * (((0 : ℂ).im + ρ : ℝ) : ℂ))) +
            Complex.I *
              (∫ y : ℝ in ((0 : ℂ).im - ρ)..((0 : ℂ).im + ρ),
                f ((((0 : ℂ).re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
          ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
            f ((0 : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        0) :
    (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (ρ : ℂ))) -
        (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) + Complex.I * (ρ : ℂ))) +
          Complex.I * (∫ y : ℝ in (-ρ)..ρ, f ((ρ : ℂ) + Complex.I * (y : ℂ))) -
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          f ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
      0 := by
  ring_nf at hmodel
  exact hmodel

/-- The local Cauchy-Goursat deformation across the left endpoint
half-rectangle collar outside the deleted disk.

This is the precise topological core of the left endpoint principal-value
indentation.  The two horizontal chord integrals at heights `±ρ`, the middle
safe vertical segment, and the counterclockwise right semicircle bound the
right half-rectangle with the endpoint disk removed.  Since `f` is
holomorphic on the punctured endpoint cap, the oriented boundary integral of
this collar vanishes. -/
theorem Complex.leftEndpointHalfRectangleDeletedDiskBoundary_eq_zero
    (f : ℂ → ℂ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρT : ρ < T)
    (hcont :
      ContinuousOn f
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ)) :
    (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (ρ : ℂ))) -
        (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) + Complex.I * (ρ : ℂ))) +
          Complex.I * (∫ y : ℝ in (-ρ)..ρ, f ((ρ : ℂ) + Complex.I * (y : ℂ))) -
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          f ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
      0 := by
  have hcont_model :
      ContinuousOn f (Complex.rightHalfRectangleDeletedDiskDomain (0 : ℂ) T ρ ρ) := by
    unfold Complex.rightHalfRectangleDeletedDiskDomain
    unfold Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain at hcont
    exact hcont
  have hdiff_model :
      DifferentiableOn ℂ f (Complex.rightHalfRectangleDeletedDiskDomain (0 : ℂ) T ρ ρ) := by
    unfold Complex.rightHalfRectangleDeletedDiskDomain
    unfold Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain at hdiff
    exact hdiff
  have hmodel :
      (∫ x : ℝ in (0 : ℝ)..((0 : ℂ).re + ρ),
          f (((x : ℝ) : ℂ) + Complex.I * (((0 : ℂ).im - ρ : ℝ) : ℂ))) +
          -(∫ x : ℝ in (0 : ℝ)..((0 : ℂ).re + ρ),
            f (((x : ℝ) : ℂ) + Complex.I * (((0 : ℂ).im + ρ : ℝ) : ℂ))) +
            Complex.I *
              (∫ y : ℝ in ((0 : ℂ).im - ρ)..((0 : ℂ).im + ρ),
                f ((((0 : ℂ).re + ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
          ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
            f ((0 : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        0 :=
    Complex.rightHalfRectangleDeletedDiskBoundary_eq_zero
      f (0 : ℂ) T ρ le_rfl hρ
      (Real.endpoint_radius_lt_abs_height hT hρT)
      hcont_model hdiff_model
  exact
    Complex.leftEndpointHalfRectangleDeletedDiskBoundary_of_model
      f hmodel

/-- The full safe vertical side in the left endpoint cap is the concatenation
of its lower, middle, and upper pieces. -/
theorem Complex.leftEndpointSafeVerticalIntegral_split_three
    (f : ℂ → ℂ)
    (T ρ : ℝ)
    (hlower :
      IntervalIntegrable
        (fun y : ℝ => f ((ρ : ℂ) + Complex.I * (y : ℂ)))
        volume (-T) (-ρ))
    (hmiddle :
      IntervalIntegrable
        (fun y : ℝ => f ((ρ : ℂ) + Complex.I * (y : ℂ)))
        volume (-ρ) ρ)
    (hupper :
      IntervalIntegrable
        (fun y : ℝ => f ((ρ : ℂ) + Complex.I * (y : ℂ)))
        volume ρ T) :
    ∫ y : ℝ in (-T)..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)) =
      (∫ y : ℝ in (-T)..(-ρ), f ((ρ : ℂ) + Complex.I * (y : ℂ))) +
        (∫ y : ℝ in (-ρ)..ρ, f ((ρ : ℂ) + Complex.I * (y : ℂ))) +
          ∫ y : ℝ in ρ..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)) := by
  have hleft :
      (∫ y : ℝ in (-T)..(-ρ), f ((ρ : ℂ) + Complex.I * (y : ℂ))) +
          ∫ y : ℝ in (-ρ)..ρ, f ((ρ : ℂ) + Complex.I * (y : ℂ)) =
        ∫ y : ℝ in (-T)..ρ, f ((ρ : ℂ) + Complex.I * (y : ℂ)) :=
    intervalIntegral.integral_add_adjacent_intervals hlower hmiddle
  have hleft_integrable :
      IntervalIntegrable
        (fun y : ℝ => f ((ρ : ℂ) + Complex.I * (y : ℂ)))
        volume (-T) ρ :=
    hlower.trans hmiddle
  have hright :
      (∫ y : ℝ in (-T)..ρ, f ((ρ : ℂ) + Complex.I * (y : ℂ))) +
          ∫ y : ℝ in ρ..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)) =
        ∫ y : ℝ in (-T)..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)) :=
    intervalIntegral.integral_add_adjacent_intervals hleft_integrable hupper
  calc
    ∫ y : ℝ in (-T)..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)) =
        (∫ y : ℝ in (-T)..ρ, f ((ρ : ℂ) + Complex.I * (y : ℂ))) +
          ∫ y : ℝ in ρ..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)) := hright.symm
    _ =
        ((∫ y : ℝ in (-T)..(-ρ), f ((ρ : ℂ) + Complex.I * (y : ℂ))) +
            ∫ y : ℝ in (-ρ)..ρ, f ((ρ : ℂ) + Complex.I * (y : ℂ))) +
          ∫ y : ℝ in ρ..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)) := by
      exact congrArg
        (fun left : ℂ =>
          left + ∫ y : ℝ in ρ..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)))
        hleft.symm
    _ =
        (∫ y : ℝ in (-T)..(-ρ), f ((ρ : ℂ) + Complex.I * (y : ℂ))) +
          (∫ y : ℝ in (-ρ)..ρ, f ((ρ : ℂ) + Complex.I * (y : ℂ))) +
            ∫ y : ℝ in ρ..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)) := by
      rfl

/-- Complex-linear algebra assembling the two rectangular endpoint identities
and the deleted-disk collar identity into the full left endpoint cap/collar boundary
identity. -/
theorem Complex.leftEndpointCapCollarBoundary_algebra
    (lowerT upperT lowerChord upperChord safe safeLower safeMiddle safeUpper
      pvLower pvUpper arc : ℂ)
    (hsafe : safe = safeLower + safeMiddle + safeUpper)
    (hlower :
      lowerT - lowerChord + Complex.I * safeLower - Complex.I * pvLower = 0)
    (hupper :
      upperChord - upperT + Complex.I * safeUpper - Complex.I * pvUpper = 0)
    (hhalf :
      lowerChord - upperChord + Complex.I * safeMiddle - arc = 0) :
    lowerT - upperT + Complex.I * safe -
        Complex.I * (pvLower + pvUpper) - arc =
      0 := by
  have hsum :
      (lowerT - lowerChord + Complex.I * safeLower - Complex.I * pvLower) +
          (upperChord - upperT + Complex.I * safeUpper - Complex.I * pvUpper) +
            (lowerChord - upperChord + Complex.I * safeMiddle - arc) =
        0 := by
    calc
      (lowerT - lowerChord + Complex.I * safeLower - Complex.I * pvLower) +
          (upperChord - upperT + Complex.I * safeUpper - Complex.I * pvUpper) +
            (lowerChord - upperChord + Complex.I * safeMiddle - arc) =
        0 + 0 + 0 := by
          exact congrArg₂
            (fun firstTwo third : ℂ => firstTwo + third)
            (congrArg₂
              (fun first second : ℂ => first + second)
              hlower
              hupper)
            hhalf
      _ = 0 := by
        exact (add_zero (0 + 0 : ℂ)).trans (zero_add 0)
  calc
    lowerT - upperT + Complex.I * safe -
        Complex.I * (pvLower + pvUpper) - arc =
        (lowerT - lowerChord + Complex.I * safeLower - Complex.I * pvLower) +
          (upperChord - upperT + Complex.I * safeUpper - Complex.I * pvUpper) +
            (lowerChord - upperChord + Complex.I * safeMiddle - arc) := by
      have hcollected :
          lowerT - upperT +
              Complex.I * (safeLower + safeMiddle + safeUpper) -
            Complex.I * (pvLower + pvUpper) - arc =
            (lowerT - lowerChord + Complex.I * safeLower - Complex.I * pvLower) +
              (upperChord - upperT + Complex.I * safeUpper - Complex.I * pvUpper) +
                (lowerChord - upperChord + Complex.I * safeMiddle - arc) :=
        (Complex.leftEndpointCapCollarBoundary_collect
          lowerT upperT lowerChord upperChord safeLower safeMiddle safeUpper
          pvLower pvUpper arc).symm
      exact
        Eq.subst
          (motive := fun safeTotal : ℂ =>
            lowerT - upperT + Complex.I * safeTotal -
                Complex.I * (pvLower + pvUpper) - arc =
              (lowerT - lowerChord + Complex.I * safeLower - Complex.I * pvLower) +
                (upperChord - upperT + Complex.I * safeUpper - Complex.I * pvUpper) +
                  (lowerChord - upperChord + Complex.I * safeMiddle - arc))
          hsafe.symm
          hcollected
    _ = 0 := hsum

/-- Generic oriented boundary integral of a left endpoint cap/collar.

This is the local topological object behind the Abel-Plana endpoint at `0`.
The Abel-Plana rectangle integrand is only a later specialization of this
ordinary deleted-disk collar Cauchy-Goursat boundary. -/
noncomputable def Complex.leftEndpointCapCollarOrientedBoundaryIntegral
    (f : ℂ → ℂ)
    (T ρ : ℝ) : ℂ :=
  (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (T : ℂ))) -
      (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) + Complex.I * (T : ℂ))) +
        Complex.I * (∫ y : ℝ in (-T)..T, f ((ρ : ℂ) + Complex.I * (y : ℂ))) -
          Complex.I *
            ((∫ y : ℝ in (-T)..(-ρ), f (Complex.I * (y : ℂ))) +
              ∫ y : ℝ in ρ..T, f (Complex.I * (y : ℂ))) -
    ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
      f ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Generic Cauchy-Goursat theorem for the left endpoint cap/collar.

This is the classical local deleted-disk collar contour theorem: if `f` is
continuous and holomorphic on the rectangular cap with the endpoint disk
deleted, the oriented boundary integral of that cap is zero. -/
theorem Complex.leftEndpointCapCollarOrientedBoundaryIntegral_eq_zero
    (f : ℂ → ℂ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρT : ρ < T)
    (hcont :
      ContinuousOn f
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ)) :
    Complex.leftEndpointCapCollarOrientedBoundaryIntegral f T ρ = 0 := by
  let g : ℝ → ℂ := fun y : ℝ => f ((ρ : ℂ) + Complex.I * (y : ℂ))
  have hsafe_integrable :
      ∀ a b : ℝ,
        (∀ y ∈ [[a, b]], y ∈ [[-T, T]]) →
          IntervalIntegrable g volume a b := by
    intro a b hinterval_subset
    have hpath_cont :
        ContinuousOn
          (fun y : ℝ => ((ρ : ℂ) + Complex.I * (y : ℂ)))
          [[a, b]] := by
      exact (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).continuousOn
    have hpath_mem :
        ∀ y ∈ [[a, b]],
          ((ρ : ℂ) + Complex.I * (y : ℂ)) ∈
            Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ := by
      intro y hy
      exact
        Complex.finiteAbelPlanaLogLeftEndpointSafeVerticalPoint_mem_capCollar
          hρ (hinterval_subset y hy)
    have hg_cont :
        ContinuousOn g [[a, b]] :=
      hcont.comp_continuousOn hpath_cont hpath_mem
    exact hg_cont.intervalIntegrable
  have hlower_interval :
      ∀ y ∈ [[(-T), (-ρ)]], y ∈ [[-T, T]] := by
    exact Real.endpoint_lower_interval_subset_height hT hρ hρT
  have hmiddle_interval :
      ∀ y ∈ [[(-ρ), ρ]], y ∈ [[-T, T]] := by
    exact Real.endpoint_middle_interval_subset_height hρ hρT
  have hupper_interval :
      ∀ y ∈ [[ρ, T]], y ∈ [[-T, T]] := by
    exact Real.endpoint_upper_interval_subset_height hT hρ hρT
  have hsafe_split :
      ∫ y : ℝ in (-T)..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)) =
        (∫ y : ℝ in (-T)..(-ρ), f ((ρ : ℂ) + Complex.I * (y : ℂ))) +
          (∫ y : ℝ in (-ρ)..ρ, f ((ρ : ℂ) + Complex.I * (y : ℂ))) +
            ∫ y : ℝ in ρ..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)) := by
    exact
      Complex.leftEndpointSafeVerticalIntegral_split_three
        f T ρ
        (hsafe_integrable (-T) (-ρ) hlower_interval)
        (hsafe_integrable (-ρ) ρ hmiddle_interval)
        (hsafe_integrable ρ T hupper_interval)
  have hlower_zero :
      (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (T : ℂ))) -
          (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (ρ : ℂ))) +
            Complex.I *
              (∫ y : ℝ in (-T)..(-ρ), f ((ρ : ℂ) + Complex.I * (y : ℂ))) -
              Complex.I *
                (∫ y : ℝ in (-T)..(-ρ), f (Complex.I * (y : ℂ))) =
        0 :=
    Complex.leftEndpointLowerRectangleBoundaryIntegral_eq_zero
      f T hT hρ hρT hcont hdiff
  have hupper_zero :
      (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) + Complex.I * (ρ : ℂ))) -
          (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) + Complex.I * (T : ℂ))) +
            Complex.I *
              (∫ y : ℝ in ρ..T, f ((ρ : ℂ) + Complex.I * (y : ℂ))) -
              Complex.I *
                (∫ y : ℝ in ρ..T, f (Complex.I * (y : ℂ))) =
        0 :=
    Complex.leftEndpointUpperRectangleBoundaryIntegral_eq_zero
      f T hρ hρT hcont hdiff
  have hhalf_zero :
      (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (ρ : ℂ))) -
          (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) + Complex.I * (ρ : ℂ))) +
            Complex.I * (∫ y : ℝ in (-ρ)..ρ, f ((ρ : ℂ) + Complex.I * (y : ℂ))) -
          ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
            f ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        0 :=
    Complex.leftEndpointHalfRectangleDeletedDiskBoundary_eq_zero
      f T hT hρ hρT hcont hdiff
  unfold Complex.leftEndpointCapCollarOrientedBoundaryIntegral
  exact
    Complex.leftEndpointCapCollarBoundary_algebra
      (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (T : ℂ)))
      (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) + Complex.I * (T : ℂ)))
      (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) - Complex.I * (ρ : ℂ)))
      (∫ x : ℝ in (0 : ℝ)..ρ, f ((x : ℂ) + Complex.I * (ρ : ℂ)))
      (∫ y : ℝ in (-T)..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)))
      (∫ y : ℝ in (-T)..(-ρ), f ((ρ : ℂ) + Complex.I * (y : ℂ)))
      (∫ y : ℝ in (-ρ)..ρ, f ((ρ : ℂ) + Complex.I * (y : ℂ)))
      (∫ y : ℝ in ρ..T, f ((ρ : ℂ) + Complex.I * (y : ℂ)))
      (∫ y : ℝ in (-T)..(-ρ), f (Complex.I * (y : ℂ)))
      (∫ y : ℝ in ρ..T, f (Complex.I * (y : ℂ)))
      (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
        f ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      hsafe_split
      hlower_zero
      hupper_zero
      hhalf_zero

/-- Oriented unnormalized boundary expression of the left endpoint cap/collar.

The five terms are, in order: lower collar, upper collar with opposite
orientation, right safe-strip edge, principal-value left edge with opposite
orientation, and the endpoint semicircle with the punctured-domain orientation
moved to the left-hand side. -/
noncomputable def Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
      Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
        Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
          Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ -
    ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
      Complex.finiteAbelPlanaLogRectangleIntegrand w
          ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Unfolding of the left endpoint cap/collar oriented boundary into its
straight collar sides and right semicircular deleted-boundary side. -/
theorem Complex.finiteAbelPlana_log_leftEndpointCapCollarOrientedBoundary_unfold
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ =
      Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
          Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ -
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  rfl

/-- The Abel-Plana left endpoint oriented boundary is the generic left cap
boundary specialized to the logarithmic cotangent rectangle integrand. -/
theorem Complex.finiteAbelPlana_log_leftEndpointCapCollarOrientedBoundary_eq_generic
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ =
      Complex.leftEndpointCapCollarOrientedBoundaryIntegral
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        T ρ := by
  rfl

/-- Solving the left endpoint oriented-boundary Cauchy equation gives the
left endpoint half-collar balance. -/
theorem Complex.finiteAbelPlana_log_leftEndpointHalfCollar_balance_of_orientedBoundary_zero
    (w : ℂ)
    (T ρ : ℝ)
    (hboundary :
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0) :
    Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
          Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ =
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  unfold Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary at hboundary
  exact sub_eq_zero.mp hboundary

/-- Cauchy-Goursat on the left endpoint cap/collar domain, with the boundary
orientation identified with the existing named side and indentation integrals.

This is the local deleted-disk collar theorem for the endpoint pole at `0`:
the boundary of the right endpoint collar, after deleting the endpoint
semicircle, has zero integral. -/
theorem Complex.finiteAbelPlana_log_leftEndpointCapCollar_orientedBoundary_eq_zero_owner
    {w : ℂ}
    {N : ℕ}
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont_left :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ))
    (hdiff_left :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ)) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 := by
  calc
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ =
        Complex.leftEndpointCapCollarOrientedBoundaryIntegral
          (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
          T ρ := by
      exact
        Complex.finiteAbelPlana_log_leftEndpointCapCollarOrientedBoundary_eq_generic
          w T ρ
    _ = 0 := by
      exact
        Complex.leftEndpointCapCollarOrientedBoundaryIntegral_eq_zero
          (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
          T hT hρ (by
            have hρ_abs : ρ < |T| / 2 := hdeleted_geometry.2.1
            exact
              Real.endpoint_radius_lt_height_of_lt_abs_height_half hT hρ_abs)
          hcont_left hdiff_left

/-- The right endpoint cap/collar domain: the rectangular cap
`N + 1 - ρ ≤ Re z ≤ N + 1`, `-T ≤ Im z ≤ T`, with the deleted endpoint
disk removed.

This is the local planar domain used in the classical Abel-Plana contour proof
near the endpoint pole at `N + 1`. -/
def Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain
    (N : ℕ)
    (T ρ : ℝ) : Set ℂ :=
  ({z : ℂ | z.re ∈ [[((N + 1 : ℕ) : ℝ) - ρ, ((N + 1 : ℕ) : ℝ)]] ∧
      z.im ∈ [[-T, T]]} : Set ℂ) \
    Metric.ball ((N + 1 : ℕ) : ℂ) ρ

/-- Membership in the right endpoint cap/collar domain is coordinatewise
membership in the endpoint rectangular cap plus avoidance of the deleted
right endpoint disk. -/
theorem Complex.mem_finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain_iff
    {N : ℕ}
    {T ρ : ℝ}
    {z : ℂ} :
    z ∈ Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ ↔
      z.re ∈ [[((N + 1 : ℕ) : ℝ) - ρ, ((N + 1 : ℕ) : ℝ)]] ∧
        z.im ∈ [[-T, T]] ∧
          z ∉ Metric.ball ((N + 1 : ℕ) : ℂ) ρ := by
  show
    z ∈
        ({z : ℂ |
            z.re ∈ [[((N + 1 : ℕ) : ℝ) - ρ, ((N + 1 : ℕ) : ℝ)]] ∧
              z.im ∈ [[-T, T]]} : Set ℂ) \
          Metric.ball ((N + 1 : ℕ) : ℂ) ρ ↔
      z.re ∈ [[((N + 1 : ℕ) : ℝ) - ρ, ((N + 1 : ℕ) : ℝ)]] ∧
        z.im ∈ [[-T, T]] ∧
          z ∉ Metric.ball ((N + 1 : ℕ) : ℂ) ρ
  constructor
  · intro hz
    exact ⟨hz.1.1, hz.1.2, hz.2⟩
  · intro hz
    exact ⟨⟨hz.1, hz.2.1⟩, hz.2.2⟩

/-- A point in the right endpoint cap rectangle, after deleting the endpoint
disk, avoids every deleted integer disk in the finite Abel-Plana rectangle. -/
theorem Complex.finiteAbelPlanaLogRightEndpointCapCollarPoint_not_mem_deletedDisk
    {N m : ℕ}
    {T ρ : ℝ}
    (hm : m ∈ Finset.range (N + 2))
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4)
    {z : ℂ}
    (hzre : z.re ∈ [[((N + 1 : ℕ) : ℝ) - ρ, ((N + 1 : ℕ) : ℝ)]])
    (_hzim : z.im ∈ [[-T, T]])
    (hzcentral : z ∉ Metric.ball ((N + 1 : ℕ) : ℂ) ρ) :
    z ∉ Metric.ball (m : ℂ) ρ := by
  by_cases hmcenter : m = N + 1
  · subst m
    exact hzcentral
  · intro hzball
    have hm_lt_succ : m < N + 1 := by
      have hm_lt : m < N + 2 := Finset.mem_range.mp hm
      exact Nat.lt_of_le_of_ne (Nat.lt_succ_iff.mp hm_lt) hmcenter
    have hm_le_N : m ≤ N := Nat.lt_succ_iff.mp hm_lt_succ
    have hm_real_le_N : ((m : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact Real.natCast_le_natCast hm_le_N
    have hρ_lt_half : ρ < (1 : ℝ) / 2 := by
      exact Real.lt_one_div_two_of_lt_one_div_four hρquarter
    have hleft_le_right :
        ((N + 1 : ℕ) : ℝ) - ρ ≤ ((N + 1 : ℕ) : ℝ) := by
      exact Real.sub_nonneg_le_self (((N + 1 : ℕ) : ℝ)) ρ hρnonneg
    have hzIcc :
        z.re ∈ Set.Icc (((N + 1 : ℕ) : ℝ) - ρ) (((N + 1 : ℕ) : ℝ)) := by
      exact Real.endpoint_bounds_of_mem_uIcc hleft_le_right hzre
    have hzre_ge : ((N + 1 : ℕ) : ℝ) - ρ ≤ z.re := hzIcc.1
    have hdist_lt : ‖z - (m : ℂ)‖ < ρ := by
      exact Complex.endpoint_norm_lt_of_mem_ball z (m : ℂ) hzball
    have hre_norm :
        |(z - (m : ℂ)).re| ≤ ‖z - (m : ℂ)‖ := by
      exact Complex.endpoint_abs_re_le_norm (z - (m : ℂ))
    have hre_ge : ρ ≤ (z - (m : ℂ)).re := by
      have hbase :
          ρ ≤ (((N + 1 : ℕ) : ℝ) - ρ) - (N : ℝ) :=
        Real.endpoint_radius_le_successor_minus_radius_sub_nat N hρ_lt_half
      have hmono :
          (((N + 1 : ℕ) : ℝ) - ρ) - (N : ℝ) ≤
            z.re - (m : ℝ) :=
        sub_le_sub hzre_ge hm_real_le_N
      have hreal : ρ ≤ z.re - (m : ℝ) :=
        hbase.trans hmono
      exact
        Eq.mpr
          (congrArg (fun r : ℝ => ρ ≤ r)
            (Complex.endpoint_sub_natCast_re z m).symm)
          hreal
    have hρ_le_abs : ρ ≤ |(z - (m : ℂ)).re| :=
      hre_ge.trans (le_abs_self _)
    exact not_lt_of_ge (hρ_le_abs.trans hre_norm) hdist_lt

/-- The closed right endpoint cap rectangle lies in the ambient finite
Abel-Plana rectangle. -/
theorem Complex.finiteAbelPlanaLogRightEndpointCapCollarClosedRectangle_subset_closedRectangle
    {N : ℕ}
    {T ρ : ℝ}
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4) :
    ({z : ℂ | z.re ∈ [[((N + 1 : ℕ) : ℝ) - ρ, ((N + 1 : ℕ) : ℝ)]] ∧
        z.im ∈ [[-T, T]]} : Set ℂ) ⊆
      Complex.finiteAbelPlanaClosedRectangle N T := by
  intro z hz
  have hleft_le_right :
      ((N + 1 : ℕ) : ℝ) - ρ ≤ ((N + 1 : ℕ) : ℝ) := by
    exact Real.sub_nonneg_le_self ((N + 1 : ℕ) : ℝ) ρ hρnonneg
  have hzIcc :
      z.re ∈ Set.Icc (((N + 1 : ℕ) : ℝ) - ρ) (((N + 1 : ℕ) : ℝ)) := by
    exact Real.endpoint_bounds_of_mem_uIcc hleft_le_right hz.1
  have hρ_lt_one : ρ < 1 := by
    exact Real.lt_one_of_lt_one_div_four hρquarter
  refine Complex.mem_reProdIm.mpr ⟨?_, hz.2⟩
  have hnonneg : 0 ≤ ((N + 1 : ℕ) : ℝ) - ρ := by
    have hone_le_succ : (1 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) :=
      Real.one_le_natCast_succ N
    have hρ_le_succ : ρ ≤ ((N + 1 : ℕ) : ℝ) :=
      (le_of_lt hρ_lt_one).trans hone_le_succ
    exact sub_nonneg.mpr hρ_le_succ
  exact ⟨hnonneg.trans hzIcc.1, hzIcc.2⟩

/-- The right endpoint cap/collar domain lies in the finite Abel-Plana
punctured rectangle. -/
theorem Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain_subset_puncturedRectangle
    {N : ℕ}
    (T : ℝ)
    {ρ : ℝ}
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4) :
    Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ ⊆
      Complex.finiteAbelPlanaPuncturedRectangle N T ρ := by
  intro z hz
  have hzdata :
      z.re ∈ [[((N + 1 : ℕ) : ℝ) - ρ, ((N + 1 : ℕ) : ℝ)]] ∧
        z.im ∈ [[-T, T]] ∧
          z ∉ Metric.ball ((N + 1 : ℕ) : ℂ) ρ :=
    Complex.mem_finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain_iff.mp hz
  have hclosed :
      z ∈ Complex.finiteAbelPlanaClosedRectangle N T :=
    Complex.finiteAbelPlanaLogRightEndpointCapCollarClosedRectangle_subset_closedRectangle
      hρnonneg hρquarter ⟨hzdata.1, hzdata.2.1⟩
  have havoid :
      ∀ m ∈ Finset.range (N + 2), z ∉ Metric.ball (m : ℂ) ρ := by
    intro m hm
    exact
      Complex.finiteAbelPlanaLogRightEndpointCapCollarPoint_not_mem_deletedDisk
        hm hρnonneg hρquarter hzdata.1 hzdata.2.1 hzdata.2.2
  exact
    Complex.mem_finiteAbelPlanaPuncturedRectangle_iff.mpr
      ⟨hclosed, havoid⟩

/-- Continuity of the Abel-Plana rectangle integrand on the right endpoint
cap/collar domain, transported from the ambient punctured rectangle. -/
theorem Complex.continuousOn_finiteAbelPlanaLogRectangleIntegrand_rightEndpointCapCollar
    {w : ℂ}
    {N : ℕ}
    {T ρ : ℝ}
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    ContinuousOn
      (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
      (Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ) := by
  exact
    hcont.mono
      (Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain_subset_puncturedRectangle
        T hρnonneg hρquarter)

/-- Holomorphy of the Abel-Plana rectangle integrand on the right endpoint
cap/collar domain, transported from the ambient punctured rectangle. -/
theorem Complex.differentiableOn_finiteAbelPlanaLogRectangleIntegrand_rightEndpointCapCollar
    {w : ℂ}
    {N : ℕ}
    {T ρ : ℝ}
    (hρnonneg : 0 ≤ ρ)
    (hρquarter : ρ < (1 : ℝ) / 4)
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    DifferentiableOn ℂ
      (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
      (Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ) := by
  exact
    hdiff.mono
      (Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain_subset_puncturedRectangle
        T hρnonneg hρquarter)

/-- A point on the left semicircle around the right endpoint lies in the
right endpoint punctured cap/collar domain.

This is the reflected endpoint geometry for the cap at `N + 1`: on
`π / 2 ≤ θ ≤ 3π / 2`, the cosine is nonpositive, so the circle lies to the
left of the endpoint. -/
theorem Complex.finiteAbelPlanaLogRightEndpointSemicirclePoint_mem_capCollar
    {N : ℕ}
    {T ρ θ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρT : ρ < T)
    (hθ : θ ∈ Set.Icc (Real.pi / 2) (3 * Real.pi / 2)) :
    (((N + 1 : ℕ) : ℂ) +
        (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) ∈
      Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ := by
  let M : ℕ := N + 1
  have hρnonneg : 0 ≤ ρ := le_of_lt hρ
  have hre :
      ((((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).re)) =
        ((M : ℝ) + ρ * Real.cos θ) := by
    unfold M
    ring_nf
  have him :
      ((((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im)) =
        ρ * Real.sin θ := by
    unfold M
    ring_nf
  have hcos_nonpos : Real.cos θ ≤ 0 :=
    Real.cos_nonpos_of_pi_div_two_le_of_le hθ.1 hθ.2
  have hcos_ge_neg_one : -1 ≤ Real.cos θ :=
    (Real.cos_mem_Icc θ).1
  have hre_mem :
      (((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).re) ∈
        [[((N + 1 : ℕ) : ℝ) - ρ, ((N + 1 : ℕ) : ℝ)]] := by
    have hleft : (M : ℝ) - ρ ≤ (M : ℝ) + ρ * Real.cos θ := by
      have hmul : -ρ ≤ ρ * Real.cos θ := by
        calc
          -ρ = ρ * (-1) := (mul_neg_one ρ).symm
          _ ≤ ρ * Real.cos θ :=
            mul_le_mul_of_nonneg_left hcos_ge_neg_one hρnonneg
      exact
        calc
          (M : ℝ) - ρ = (M : ℝ) + -ρ :=
            sub_eq_add_neg (M : ℝ) ρ
          _ ≤ (M : ℝ) + ρ * Real.cos θ :=
            add_le_add_left hmul (M : ℝ)
    have hright : (M : ℝ) + ρ * Real.cos θ ≤ (M : ℝ) := by
      have hmul : ρ * Real.cos θ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos hρnonneg hcos_nonpos
      exact add_le_of_nonpos_right hmul
    have hinterval :
        ((M : ℝ) + ρ * Real.cos θ) ∈
          [[((N + 1 : ℕ) : ℝ) - ρ, ((N + 1 : ℕ) : ℝ)]] := by
      unfold M at hleft hright ⊢
      exact
        Real.endpoint_mem_uIcc_of_bounds
          (Real.sub_nonneg_le_self ((N + 1 : ℕ) : ℝ) ρ hρnonneg)
          (And.intro hleft hright)
    exact Real.endpoint_mem_uIcc_congr hre hinterval
  have hsin_abs : |Real.sin θ| ≤ 1 := by
    exact abs_le.mpr (Real.sin_mem_Icc θ)
  have him_abs : |ρ * Real.sin θ| ≤ ρ := by
    calc
      |ρ * Real.sin θ| = ρ * |Real.sin θ| := by
        calc
          |ρ * Real.sin θ| = |ρ| * |Real.sin θ| :=
            abs_mul ρ (Real.sin θ)
          _ = ρ * |Real.sin θ| :=
            congrArg (fun r : ℝ => r * |Real.sin θ|)
              (abs_of_nonneg hρnonneg)
      _ ≤ ρ * 1 := mul_le_mul_of_nonneg_left hsin_abs hρnonneg
      _ = ρ := mul_one ρ
  have him_mem :
      (((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))).im) ∈
        [[-T, T]] := by
    have habsT : |ρ * Real.sin θ| ≤ T :=
      him_abs.trans (le_of_lt hρT)
    have hb := abs_le.mp habsT
    exact
      Real.endpoint_mem_uIcc_congr him
        (Real.endpoint_mem_uIcc_of_bounds (neg_le_self hT.le) hb)
  have hnot_ball :
      (((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) ∉
        Metric.ball ((N + 1 : ℕ) : ℂ) ρ := by
    have hz_eq :
        (((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
          circleMap ((N + 1 : ℕ) : ℂ) ρ θ := by
      unfold circleMap
      unfold M
      ring_nf
    exact hz_eq ▸ circleMap_not_mem_ball ((N + 1 : ℕ) : ℂ) ρ θ
  exact
    Complex.mem_finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain_iff.mpr
      ⟨hre_mem, him_mem, hnot_ball⟩

/-- Points on the right principal-value vertical side belong to the right
endpoint punctured cap/collar domain. -/
theorem Complex.finiteAbelPlanaLogRightEndpointPVVerticalPoint_mem_capCollar
    {N : ℕ}
    {T ρ y : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hy : y ∈ [[-T, -ρ]] ∨ y ∈ [[ρ, T]]) :
    (((N + 1 : ℕ) : ℂ) + Complex.I * (y : ℂ)) ∈
      Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ := by
  let M : ℕ := N + 1
  have hρnonneg : 0 ≤ ρ := le_of_lt hρ
  have hre_mem :
      (((M : ℂ) + Complex.I * (y : ℂ)).re) ∈
        [[((N + 1 : ℕ) : ℝ) - ρ, ((N + 1 : ℕ) : ℝ)]] := by
    have hre : ((M : ℂ) + Complex.I * (y : ℂ)).re = (M : ℝ) := by
      unfold M
      ring_nf
    have hleft : ((N + 1 : ℕ) : ℝ) - ρ ≤ ((N + 1 : ℕ) : ℝ) := by
      exact Real.sub_nonneg_le_self ((N + 1 : ℕ) : ℝ) ρ hρnonneg
    exact
      Real.endpoint_mem_uIcc_congr hre
        (Real.endpoint_mem_uIcc_of_bounds hleft
          (And.intro hleft le_rfl))
  have him_mem :
      (((M : ℂ) + Complex.I * (y : ℂ)).im) ∈ [[-T, T]] := by
    rcases hy with hy | hy
    · have horder : -T ≤ -ρ := hy.1
      have hyIcc : y ∈ Set.Icc (-T) (-ρ) :=
        Real.endpoint_bounds_of_mem_uIcc horder hy
      have hleT : y ≤ T :=
        hyIcc.2.trans (Real.endpoint_neg_radius_le_height hT hρ)
      have hy_uIcc : y ∈ [[-T, T]] :=
        Real.endpoint_mem_uIcc_of_bounds (neg_le_self hT.le)
          (And.intro hyIcc.1 hleT)
      have him : (((M : ℂ) + Complex.I * (y : ℂ)).im) = y := by
        unfold M
        ring_nf
      exact Real.endpoint_mem_uIcc_congr him hy_uIcc
    · have horder : ρ ≤ T := hy.1
      have hyIcc : y ∈ Set.Icc ρ T :=
        Real.endpoint_bounds_of_mem_uIcc horder hy
      have hge_negT : -T ≤ y :=
        (Real.endpoint_neg_height_le_radius hT hρ).trans hyIcc.1
      have hy_uIcc : y ∈ [[-T, T]] :=
        Real.endpoint_mem_uIcc_of_bounds (neg_le_self hT.le)
          (And.intro hge_negT hyIcc.2)
      have him : (((M : ℂ) + Complex.I * (y : ℂ)).im) = y := by
        unfold M
        ring_nf
      exact Real.endpoint_mem_uIcc_congr him hy_uIcc
  have hnot_ball :
      (((M : ℂ) + Complex.I * (y : ℂ))) ∉
        Metric.ball ((N + 1 : ℕ) : ℂ) ρ := by
    intro hball
    have hdist : ‖(((M : ℂ) + Complex.I * (y : ℂ)) - ((N + 1 : ℕ) : ℂ))‖ < ρ := by
      exact
        Complex.endpoint_norm_lt_of_mem_ball
          (((M : ℂ) + Complex.I * (y : ℂ)))
          ((N + 1 : ℕ) : ℂ)
          hball
    have hρ_le_abs_y : ρ ≤ |y| := by
      rcases hy with hy | hy
      · have horder : -T ≤ -ρ := hy.1
        have hyIcc : y ∈ Set.Icc (-T) (-ρ) :=
          Real.endpoint_bounds_of_mem_uIcc horder hy
        have hneg : ρ ≤ -y :=
          Real.endpoint_neg_le_neg_of_le hyIcc.2
        exact hneg.trans (neg_le_abs y)
      · have horder : ρ ≤ T := hy.1
        have hyIcc : y ∈ Set.Icc ρ T :=
          Real.endpoint_bounds_of_mem_uIcc horder hy
        exact hyIcc.1.trans (le_abs_self y)
    have hnorm :
        ‖(((M : ℂ) + Complex.I * (y : ℂ)) - ((N + 1 : ℕ) : ℂ))‖ = |y| := by
      unfold M
      exact
        Complex.norm_centered_vertical_translate_sub_center
          (((N + 1 : ℕ) : ℂ))
          y
    have hdist_abs : |y| < ρ :=
      Eq.subst (motive := fun r : ℝ => r < ρ) hnorm hdist
    exact not_lt_of_ge hρ_le_abs_y hdist_abs
  exact
    Complex.mem_finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain_iff.mpr
      ⟨hre_mem, him_mem, hnot_ball⟩

/-- Points on the safe vertical side `Re z = N + 1 - ρ` belong to the right
endpoint punctured cap/collar domain. -/
theorem Complex.finiteAbelPlanaLogRightEndpointSafeVerticalPoint_mem_capCollar
    {N : ℕ}
    {T ρ y : ℝ}
    (hρ : 0 < ρ)
    (hy : y ∈ [[-T, T]]) :
    ((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)) ∈
      Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ := by
  have hρnonneg : 0 ≤ ρ := le_of_lt hρ
  have hleft_le_right :
      ((N + 1 : ℕ) : ℝ) - ρ ≤ ((N + 1 : ℕ) : ℝ) := by
    exact Real.sub_nonneg_le_self ((N + 1 : ℕ) : ℝ) ρ hρnonneg
  have hre_mem :
      (((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)).re) ∈
        [[((N + 1 : ℕ) : ℝ) - ρ, ((N + 1 : ℕ) : ℝ)]] := by
    have hre :
        (((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)).re) =
          ((N + 1 : ℕ) : ℝ) - ρ := by
      ring_nf
    exact
      Real.endpoint_mem_uIcc_congr hre
        (Real.endpoint_mem_uIcc_of_bounds hleft_le_right
          (And.intro le_rfl hleft_le_right))
  have him_mem :
      (((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)).im) ∈ [[-T, T]] := by
    have him :
        (((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)).im) = y := by
      ring_nf
    exact Real.endpoint_mem_uIcc_congr him hy
  have hnot_ball :
      (((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ))) ∉
        Metric.ball ((N + 1 : ℕ) : ℂ) ρ := by
    intro hball
    have hdist :
        ‖(((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)) -
            ((N + 1 : ℕ) : ℂ))‖ < ρ := by
      exact
        Complex.endpoint_norm_lt_of_mem_ball
          (((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)))
          ((N + 1 : ℕ) : ℂ)
          hball
    have hre_norm :
        |(((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)) -
            ((N + 1 : ℕ) : ℂ)).re| ≤
          ‖(((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)) -
            ((N + 1 : ℕ) : ℂ))‖ := by
      exact
        Complex.endpoint_abs_re_le_norm
          (((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)) -
            ((N + 1 : ℕ) : ℂ))
    have hρ_le_norm :
        ρ ≤ ‖(((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)) -
            ((N + 1 : ℕ) : ℂ))‖ := by
      have hre_abs :
          |(((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)) -
              ((N + 1 : ℕ) : ℂ)).re| = ρ := by
        have hre :
            ((((((N + 1 : ℕ) : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ)) -
                ((N + 1 : ℕ) : ℂ)).re) = -ρ := by
          ring_nf
        exact hre ▸ abs_neg ρ ▸ abs_of_nonneg hρnonneg
      exact hre_abs ▸ hre_norm
    exact not_lt_of_ge hρ_le_norm hdist
  exact
    Complex.mem_finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain_iff.mpr
      ⟨hre_mem, him_mem, hnot_ball⟩

/-- The lower right endpoint rectangle
`N + 1 - ρ ≤ Re z ≤ N + 1`, `-T ≤ Im z ≤ -ρ` lies in the right endpoint
punctured cap/collar domain. -/
theorem Complex.finiteAbelPlanaLogRightEndpointLowerRectangle_subset_capCollar
    {N : ℕ}
    {T ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρT : ρ < T) :
    ([[((((N + 1 : ℕ) : ℝ) - ρ : ℝ) : ℂ).re,
        (((N + 1 : ℕ) : ℂ).re)]] ×ℂ
        [[(-T), (-ρ)]]) ⊆
      Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ := by
  intro z hz
  have hzre :
      z.re ∈ [[((N + 1 : ℕ) : ℝ) - ρ, ((N + 1 : ℕ) : ℝ)]] := by
    exact (Complex.mem_reProdIm.mp hz).1
  have hzim_lower : z.im ∈ [[-T, -ρ]] := by
    exact (Complex.mem_reProdIm.mp hz).2
  have horder : -T ≤ -ρ :=
    Real.endpoint_neg_height_le_neg_radius hρT
  have hzimIcc : z.im ∈ Set.Icc (-T) (-ρ) :=
    Real.endpoint_bounds_of_mem_uIcc horder hzim_lower
  have hzim : z.im ∈ [[-T, T]] := by
    have hleT : z.im ≤ T :=
      hzimIcc.2.trans
        (Real.endpoint_neg_radius_le_height (hρ.trans hρT) hρ)
    exact
      Real.endpoint_mem_uIcc_of_bounds (neg_le_self (le_of_lt (hρ.trans hρT)))
        (And.intro hzimIcc.1 hleT)
  have hnot_ball : z ∉ Metric.ball ((N + 1 : ℕ) : ℂ) ρ := by
    have hρ_le_abs_im : ρ ≤ |(z - ((N + 1 : ℕ) : ℂ)).im| := by
      have hraw : ρ ≤ |z.im| := by
        have hneg : ρ ≤ -z.im :=
          Real.endpoint_neg_le_neg_of_le hzimIcc.2
        exact hneg.trans (neg_le_abs z.im)
      exact
        Eq.mpr
          (congrArg (fun r : ℝ => ρ ≤ |r|)
            (Complex.endpoint_sub_natCast_im z (N + 1)).symm)
          hraw
    exact
      fun hball =>
        let hdist : ‖z - ((N + 1 : ℕ) : ℂ)‖ < ρ :=
          Complex.endpoint_norm_lt_of_mem_ball z ((N + 1 : ℕ) : ℂ) hball
        let him_norm : |(z - ((N + 1 : ℕ) : ℂ)).im| ≤
            ‖z - ((N + 1 : ℕ) : ℂ)‖ :=
          Complex.endpoint_abs_im_le_norm (z - ((N + 1 : ℕ) : ℂ))
        not_lt_of_ge (hρ_le_abs_im.trans him_norm) hdist
  exact
    Complex.mem_finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain_iff.mpr
      ⟨hzre, hzim, hnot_ball⟩

/-- The upper right endpoint rectangle
`N + 1 - ρ ≤ Re z ≤ N + 1`, `ρ ≤ Im z ≤ T` lies in the right endpoint
punctured cap/collar domain. -/
theorem Complex.finiteAbelPlanaLogRightEndpointUpperRectangle_subset_capCollar
    {N : ℕ}
    {T ρ : ℝ}
    (hρ : 0 < ρ)
    (hρT : ρ < T) :
    ([[((((N + 1 : ℕ) : ℝ) - ρ : ℝ) : ℂ).re,
        (((N + 1 : ℕ) : ℂ).re)]] ×ℂ
        [[ρ, T]]) ⊆
      Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ := by
  intro z hz
  have hzre :
      z.re ∈ [[((N + 1 : ℕ) : ℝ) - ρ, ((N + 1 : ℕ) : ℝ)]] := by
    exact (Complex.mem_reProdIm.mp hz).1
  have hzim_upper : z.im ∈ [[ρ, T]] := by
    exact (Complex.mem_reProdIm.mp hz).2
  have horder : ρ ≤ T := le_of_lt hρT
  have hzimIcc : z.im ∈ Set.Icc ρ T :=
    Real.endpoint_bounds_of_mem_uIcc horder hzim_upper
  have hzim : z.im ∈ [[-T, T]] := by
    have hge_negT : -T ≤ z.im :=
      (Real.endpoint_neg_height_le_radius (hρ.trans hρT) hρ).trans
        hzimIcc.1
    exact
      Real.endpoint_mem_uIcc_of_bounds (neg_le_self (le_of_lt (hρ.trans hρT)))
        (And.intro hge_negT hzimIcc.2)
  have hnot_ball : z ∉ Metric.ball ((N + 1 : ℕ) : ℂ) ρ := by
    have hρ_le_abs_im : ρ ≤ |(z - ((N + 1 : ℕ) : ℂ)).im| := by
      have hraw : ρ ≤ |z.im| :=
        hzimIcc.1.trans (le_abs_self z.im)
      exact
        Eq.mpr
          (congrArg (fun r : ℝ => ρ ≤ |r|)
            (Complex.endpoint_sub_natCast_im z (N + 1)).symm)
          hraw
    exact
      fun hball =>
        let hdist : ‖z - ((N + 1 : ℕ) : ℂ)‖ < ρ :=
          Complex.endpoint_norm_lt_of_mem_ball z ((N + 1 : ℕ) : ℂ) hball
        let him_norm : |(z - ((N + 1 : ℕ) : ℂ)).im| ≤
            ‖z - ((N + 1 : ℕ) : ℂ)‖ :=
          Complex.endpoint_abs_im_le_norm (z - ((N + 1 : ℕ) : ℂ))
        not_lt_of_ge (hρ_le_abs_im.trans him_norm) hdist
  exact
    Complex.mem_finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain_iff.mpr
      ⟨hzre, hzim, hnot_ball⟩

/-- Transport the generic rectangular Cauchy-Goursat boundary to the lower
right endpoint cap coordinates. -/
theorem Complex.rightEndpointLowerRectangleBoundaryIntegral_of_rectBoundary
    (f : ℂ → ℂ)
    (N M : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hM : M = N + 1)
    (z₀ z₁ : ℂ)
    (hz₀ : z₀ = (((M : ℝ) - ρ : ℝ) : ℂ) - Complex.I * (T : ℂ))
    (hz₁ : z₁ = (M : ℂ) - Complex.I * (ρ : ℂ))
    (hrect :
      (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₀.im : ℂ) * Complex.I)) -
          (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₁.im : ℂ) * Complex.I)) +
            Complex.I •
              (∫ y : ℝ in z₀.im..z₁.im, f ((z₁.re : ℂ) + (y : ℂ) * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in z₀.im..z₁.im, f ((z₀.re : ℂ) + (y : ℂ) * Complex.I)) =
        0) :
    (let M : ℕ := N + 1
      (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) - Complex.I * (T : ℂ))) -
          (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) - Complex.I * (ρ : ℂ))) +
            Complex.I *
              (∫ y : ℝ in (-T)..(-ρ), f ((M : ℂ) + Complex.I * (y : ℂ))) -
              Complex.I *
                (∫ y : ℝ in (-T)..(-ρ),
                  f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))) =
      0 := by
  subst z₀
  subst z₁
  subst M
  ring_nf at hrect
  exact hrect

/-- Cauchy-Goursat on the lower ordinary rectangle in the right endpoint cap. -/
theorem Complex.rightEndpointLowerRectangleBoundaryIntegral_eq_zero
    (f : ℂ → ℂ)
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρT : ρ < T)
    (hcont :
      ContinuousOn f
        (Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ)) :
    (let M : ℕ := N + 1
      (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) - Complex.I * (T : ℂ))) -
          (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) - Complex.I * (ρ : ℂ))) +
            Complex.I *
              (∫ y : ℝ in (-T)..(-ρ), f ((M : ℂ) + Complex.I * (y : ℂ))) -
              Complex.I *
                (∫ y : ℝ in (-T)..(-ρ),
                  f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))) =
      0 := by
  let M : ℕ := N + 1
  let z₀ : ℂ := (((M : ℝ) - ρ : ℝ) : ℂ) - Complex.I * (T : ℂ)
  let z₁ : ℂ := (M : ℂ) - Complex.I * (ρ : ℂ)
  have hclosed :
      ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) ⊆
        Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ := by
    unfold z₀
    unfold z₁
    unfold M
    exact
      Complex.finiteAbelPlanaLogRightEndpointLowerRectangle_subset_capCollar
        hT hρ hρT
  have hopen :
      (Set.Ioo (min z₀.re z₁.re) (max z₀.re z₁.re) ×ℂ
          Set.Ioo (min z₀.im z₁.im) (max z₀.im z₁.im)) ⊆
        Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ := by
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
  exact
    Complex.rightEndpointLowerRectangleBoundaryIntegral_of_rectBoundary
      f N M T rfl z₀ z₁ rfl rfl hcauchy

/-- Transport the generic rectangular Cauchy-Goursat boundary to the upper
right endpoint cap coordinates. -/
theorem Complex.rightEndpointUpperRectangleBoundaryIntegral_of_rectBoundary
    (f : ℂ → ℂ)
    (N M : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hM : M = N + 1)
    (z₀ z₁ : ℂ)
    (hz₀ : z₀ = (((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (ρ : ℂ))
    (hz₁ : z₁ = (M : ℂ) + Complex.I * (T : ℂ))
    (hrect :
      (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₀.im : ℂ) * Complex.I)) -
          (∫ x : ℝ in z₀.re..z₁.re, f ((x : ℂ) + (z₁.im : ℂ) * Complex.I)) +
            Complex.I •
              (∫ y : ℝ in z₀.im..z₁.im, f ((z₁.re : ℂ) + (y : ℂ) * Complex.I)) -
              Complex.I •
                (∫ y : ℝ in z₀.im..z₁.im, f ((z₀.re : ℂ) + (y : ℂ) * Complex.I)) =
        0) :
    (let M : ℕ := N + 1
      (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) + Complex.I * (ρ : ℂ))) -
          (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) + Complex.I * (T : ℂ))) +
            Complex.I *
              (∫ y : ℝ in ρ..T, f ((M : ℂ) + Complex.I * (y : ℂ))) -
              Complex.I *
                (∫ y : ℝ in ρ..T,
                  f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))) =
      0 := by
  subst z₀
  subst z₁
  subst M
  ring_nf at hrect
  exact hrect

/-- Cauchy-Goursat on the upper ordinary rectangle in the right endpoint cap. -/
theorem Complex.rightEndpointUpperRectangleBoundaryIntegral_eq_zero
    (f : ℂ → ℂ)
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hρ : 0 < ρ)
    (hρT : ρ < T)
    (hcont :
      ContinuousOn f
        (Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ)) :
    (let M : ℕ := N + 1
      (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) + Complex.I * (ρ : ℂ))) -
          (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) + Complex.I * (T : ℂ))) +
            Complex.I *
              (∫ y : ℝ in ρ..T, f ((M : ℂ) + Complex.I * (y : ℂ))) -
              Complex.I *
                (∫ y : ℝ in ρ..T,
                  f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))) =
      0 := by
  let M : ℕ := N + 1
  let z₀ : ℂ := (((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (ρ : ℂ)
  let z₁ : ℂ := (M : ℂ) + Complex.I * (T : ℂ)
  have hclosed :
      ([[z₀.re, z₁.re]] ×ℂ [[z₀.im, z₁.im]]) ⊆
        Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ := by
    unfold z₀
    unfold z₁
    unfold M
    exact
      Complex.finiteAbelPlanaLogRightEndpointUpperRectangle_subset_capCollar
        hρ hρT
  have hopen :
      (Set.Ioo (min z₀.re z₁.re) (max z₀.re z₁.re) ×ℂ
          Set.Ioo (min z₀.im z₁.im) (max z₀.im z₁.im)) ⊆
        Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ := by
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
  exact
    Complex.rightEndpointUpperRectangleBoundaryIntegral_of_rectBoundary
      f N M T rfl z₀ z₁ rfl rfl hcauchy

/-- Transport the left-half deleted-disk model boundary to the right endpoint
half-collar coordinates. -/
theorem Complex.rightEndpointHalfRectangleDeletedDiskBoundary_of_model
    (f : ℂ → ℂ)
    (N M : ℕ)
    {ρ : ℝ}
    (hM : M = N + 1)
    (c : ℂ)
    (hc : c = (M : ℂ))
    (hmodel :
      (∫ x : ℝ in (c.re - ρ)..c.re,
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) +
          -(∫ x : ℝ in (c.re - ρ)..c.re,
            f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) -
            Complex.I *
              (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
                f (((c.re - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
          ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
            f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        0) :
    (let M : ℕ := N + 1
      (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ),
          f ((x : ℂ) - Complex.I * (ρ : ℂ))) +
        -(∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ),
          f ((x : ℂ) + Complex.I * (ρ : ℂ))) -
          Complex.I *
            (∫ y : ℝ in (-ρ)..ρ,
              f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
        ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
          f ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
      0 := by
  subst c
  subst M
  ring_nf at hmodel
  exact hmodel

/-- The local Cauchy-Goursat deformation across the right endpoint
half-rectangle collar outside the deleted disk.

This is the reflected analogue of the left endpoint half-rectangle theorem.  The
two horizontal chord integrals, the middle adjacent safe vertical segment, and
the counterclockwise left semicircle bound the left half-rectangle with the
endpoint disk removed at `N + 1`. -/
theorem Complex.rightEndpointHalfRectangleDeletedDiskBoundary_eq_zero
    (f : ℂ → ℂ)
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρT : ρ < T)
    (hcont :
      ContinuousOn f
        (Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ)) :
    (let M : ℕ := N + 1
      (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ),
          f ((x : ℂ) - Complex.I * (ρ : ℂ))) +
        -(∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ),
          f ((x : ℂ) + Complex.I * (ρ : ℂ))) -
          Complex.I *
            (∫ y : ℝ in (-ρ)..ρ,
              f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
        ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
          f ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
      0 := by
  let M : ℕ := N + 1
  let c : ℂ := (M : ℂ)
  have hcont_model :
      ContinuousOn f (Complex.leftHalfRectangleDeletedDiskDomain c T ρ ρ) := by
    unfold c
    unfold M
    unfold Complex.leftHalfRectangleDeletedDiskDomain
    unfold Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain at hcont
    exact hcont
  have hdiff_model :
      DifferentiableOn ℂ f (Complex.leftHalfRectangleDeletedDiskDomain c T ρ ρ) := by
    unfold c
    unfold M
    unfold Complex.leftHalfRectangleDeletedDiskDomain
    unfold Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain at hdiff
    exact hdiff
  have hmodel :
      (∫ x : ℝ in (c.re - ρ)..c.re,
          f (((x : ℝ) : ℂ) + Complex.I * ((c.im - ρ : ℝ) : ℂ))) +
          -(∫ x : ℝ in (c.re - ρ)..c.re,
            f (((x : ℝ) : ℂ) + Complex.I * ((c.im + ρ : ℝ) : ℂ))) -
            Complex.I *
              (∫ y : ℝ in (c.im - ρ)..(c.im + ρ),
                f (((c.re - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
          ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
            f (c + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) =
        0 :=
    Complex.leftHalfRectangleDeletedDiskBoundary_eq_zero
      f c T ρ le_rfl hρ
      (Real.endpoint_radius_lt_abs_height hT hρT)
      hcont_model hdiff_model
  unfold c at hmodel ⊢
  unfold M at hmodel ⊢
  exact
    Complex.rightEndpointHalfRectangleDeletedDiskBoundary_of_model
      f N (N + 1) rfl ((N + 1 : ℕ) : ℂ) rfl hmodel

/-- The full adjacent safe vertical side in the right endpoint cap is the
concatenation of its lower, middle, and upper pieces. -/
theorem Complex.rightEndpointSafeVerticalIntegral_split_three
    (f : ℂ → ℂ)
    (N : ℕ)
    (T ρ : ℝ)
    (hlower :
      IntervalIntegrable
        (fun y : ℝ =>
          let M : ℕ := N + 1
          f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
        volume (-T) (-ρ))
    (hmiddle :
      IntervalIntegrable
        (fun y : ℝ =>
          let M : ℕ := N + 1
          f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
        volume (-ρ) ρ)
    (hupper :
      IntervalIntegrable
        (fun y : ℝ =>
          let M : ℕ := N + 1
          f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
        volume ρ T) :
    (let M : ℕ := N + 1
      ∫ y : ℝ in (-T)..T,
        f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) =
      (let M : ℕ := N + 1
        (∫ y : ℝ in (-T)..(-ρ),
          f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) +
          (∫ y : ℝ in (-ρ)..ρ,
            f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) +
            ∫ y : ℝ in ρ..T,
              f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) := by
  let M : ℕ := N + 1
  let g : ℝ → ℂ := fun y : ℝ =>
    f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))
  have hleft :
      (∫ y : ℝ in (-T)..(-ρ), g y) +
          ∫ y : ℝ in (-ρ)..ρ, g y =
        ∫ y : ℝ in (-T)..ρ, g y :=
    intervalIntegral.integral_add_adjacent_intervals hlower hmiddle
  have hleft_integrable :
      IntervalIntegrable g volume (-T) ρ :=
    hlower.trans hmiddle
  have hright :
      (∫ y : ℝ in (-T)..ρ, g y) +
          ∫ y : ℝ in ρ..T, g y =
        ∫ y : ℝ in (-T)..T, g y :=
    intervalIntegral.integral_add_adjacent_intervals hleft_integrable hupper
  calc
    (let M : ℕ := N + 1
      ∫ y : ℝ in (-T)..T,
        f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) =
        ∫ y : ℝ in (-T)..T, g y := by
      rfl
    _ =
        (∫ y : ℝ in (-T)..ρ, g y) +
          ∫ y : ℝ in ρ..T, g y := hright.symm
    _ =
        ((∫ y : ℝ in (-T)..(-ρ), g y) +
            ∫ y : ℝ in (-ρ)..ρ, g y) +
          ∫ y : ℝ in ρ..T, g y := by
      exact congrArg
        (fun left : ℂ => left + ∫ y : ℝ in ρ..T, g y)
        hleft.symm
    _ =
      (let M : ℕ := N + 1
        (∫ y : ℝ in (-T)..(-ρ),
          f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) +
          (∫ y : ℝ in (-ρ)..ρ,
            f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) +
            ∫ y : ℝ in ρ..T,
              f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) := by
      unfold g
      unfold M
      rfl

/-- Complex-linear algebra assembling the two rectangular right endpoint
identities and the right deleted-disk collar identity into the full right endpoint
cap/collar boundary identity. -/
theorem Complex.rightEndpointCapCollarBoundary_algebra
    (lowerT upperT lowerChord upperChord pvLower pvUpper safe safeLower
      safeMiddle safeUpper arc : ℂ)
    (hsafe : safe = safeLower + safeMiddle + safeUpper)
    (hlower :
      lowerT - lowerChord + Complex.I * pvLower - Complex.I * safeLower = 0)
    (hupper :
      upperChord - upperT + Complex.I * pvUpper - Complex.I * safeUpper = 0)
    (hhalf :
      lowerChord - upperChord - Complex.I * safeMiddle - arc = 0) :
    lowerT - upperT + Complex.I * (pvLower + pvUpper) -
        Complex.I * safe - arc =
      0 := by
  have hsum :
      (lowerT - lowerChord + Complex.I * pvLower - Complex.I * safeLower) +
          (upperChord - upperT + Complex.I * pvUpper - Complex.I * safeUpper) +
            (lowerChord - upperChord - Complex.I * safeMiddle - arc) =
        0 := by
    calc
      (lowerT - lowerChord + Complex.I * pvLower - Complex.I * safeLower) +
          (upperChord - upperT + Complex.I * pvUpper - Complex.I * safeUpper) +
            (lowerChord - upperChord - Complex.I * safeMiddle - arc) =
        0 + 0 + 0 := by
          exact congrArg₂
            (fun firstTwo third : ℂ => firstTwo + third)
            (congrArg₂
              (fun first second : ℂ => first + second)
              hlower
              hupper)
            hhalf
      _ = 0 := by
        exact (add_zero (0 + 0 : ℂ)).trans (zero_add 0)
  calc
    lowerT - upperT + Complex.I * (pvLower + pvUpper) -
        Complex.I * safe - arc =
        (lowerT - lowerChord + Complex.I * pvLower - Complex.I * safeLower) +
          (upperChord - upperT + Complex.I * pvUpper - Complex.I * safeUpper) +
            (lowerChord - upperChord - Complex.I * safeMiddle - arc) := by
      have hcollected :
          lowerT - upperT + Complex.I * (pvLower + pvUpper) -
              Complex.I * (safeLower + safeMiddle + safeUpper) - arc =
            (lowerT - lowerChord + Complex.I * pvLower - Complex.I * safeLower) +
              (upperChord - upperT + Complex.I * pvUpper - Complex.I * safeUpper) +
                (lowerChord - upperChord - Complex.I * safeMiddle - arc) :=
        (Complex.rightEndpointCapCollarBoundary_collect
          lowerT upperT lowerChord upperChord pvLower pvUpper safeLower
          safeMiddle safeUpper arc).symm
      exact
        Eq.subst
          (motive := fun safeTotal : ℂ =>
            lowerT - upperT + Complex.I * (pvLower + pvUpper) -
                Complex.I * safeTotal - arc =
              (lowerT - lowerChord + Complex.I * pvLower - Complex.I * safeLower) +
                (upperChord - upperT + Complex.I * pvUpper - Complex.I * safeUpper) +
                  (lowerChord - upperChord - Complex.I * safeMiddle - arc))
          hsafe.symm
          hcollected
    _ = 0 := hsum

/-- Oriented unnormalized boundary expression of the right endpoint cap/collar.

The five terms are, in order: lower collar, upper collar with opposite
orientation, principal-value right edge, adjacent safe-strip edge with opposite
orientation, and the endpoint semicircle with the punctured-domain orientation
moved to the left-hand side. -/
noncomputable def Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) : ℂ :=
  Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
      Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
        Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ -
    (let M : ℕ := N + 1
      ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
        Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))

/-- Unfolding of the right endpoint cap/collar oriented boundary into its
straight collar sides and left semicircular deleted-boundary side. -/
theorem Complex.finiteAbelPlana_log_rightEndpointCapCollarOrientedBoundary_unfold
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary N w T ρ =
      Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ -
        (let M : ℕ := N + 1
          ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
            Complex.finiteAbelPlanaLogRectangleIntegrand w
                ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) := by
  rfl

/-- Generic oriented boundary integral of a right endpoint cap/collar. -/
noncomputable def Complex.rightEndpointCapCollarOrientedBoundaryIntegral
    (f : ℂ → ℂ)
    (N : ℕ)
    (T ρ : ℝ) : ℂ :=
  let M : ℕ := N + 1
  (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) - Complex.I * (T : ℂ))) -
      (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) + Complex.I * (T : ℂ))) +
        Complex.I *
          ((∫ y : ℝ in (-T)..(-ρ), f ((M : ℂ) + Complex.I * (y : ℂ))) +
            ∫ y : ℝ in ρ..T, f ((M : ℂ) + Complex.I * (y : ℂ))) -
          Complex.I *
            (∫ y : ℝ in (-T)..T, f (((M : ℝ) - ρ : ℝ) + Complex.I * (y : ℂ))) -
    ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
      f ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
        (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))

/-- Generic Cauchy-Goursat theorem for the right endpoint cap/collar.

This is the reflected local deleted-disk collar contour theorem at the endpoint
`N + 1`. -/
theorem Complex.rightEndpointCapCollarOrientedBoundaryIntegral_eq_zero
    (f : ℂ → ℂ)
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hρT : ρ < T)
    (hcont :
      ContinuousOn f
        (Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ))
    (hdiff :
      DifferentiableOn ℂ f
        (Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ)) :
    Complex.rightEndpointCapCollarOrientedBoundaryIntegral f N T ρ = 0 := by
  let M : ℕ := N + 1
  let g : ℝ → ℂ := fun y : ℝ =>
    f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))
  have hsafe_integrable :
      ∀ a b : ℝ,
        (∀ y ∈ Set.Icc a b, y ∈ Set.Icc (-T) T) →
          IntervalIntegrable g volume a b := by
    intro a b hinterval_subset
    have hpath_cont :
        ContinuousOn
          (fun y : ℝ =>
            ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
          (Set.Icc a b) := by
      exact (continuous_const.add (continuous_const.mul Complex.continuous_ofReal)).continuousOn
    have hpath_mem :
        ∀ y ∈ Set.Icc a b,
          ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)) ∈
            Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ := by
      intro y hy
      have hM : M = N + 1 := rfl
      rw [hM] at hinterval_subset ⊢
      exact
        Complex.finiteAbelPlanaLogRightEndpointSafeVerticalPoint_mem_capCollar
          hρ (hinterval_subset y hy)
    have hg_cont :
        ContinuousOn g (Set.Icc a b) :=
      hcont.comp hpath_cont hpath_mem
    exact hg_cont.intervalIntegrable
  have hlower_interval :
      ∀ y ∈ Set.Icc (-T) (-ρ), y ∈ Set.Icc (-T) T := by
    exact Real.endpoint_lower_interval_subset_height hT hρ hρT
  have hmiddle_interval :
      ∀ y ∈ Set.Icc (-ρ) ρ, y ∈ Set.Icc (-T) T := by
    exact Real.endpoint_middle_interval_subset_height hρ hρT
  have hupper_interval :
      ∀ y ∈ Set.Icc ρ T, y ∈ Set.Icc (-T) T := by
    exact Real.endpoint_upper_interval_subset_height hT hρ hρT
  have hsafe_split :
      (let M : ℕ := N + 1
        ∫ y : ℝ in (-T)..T,
          f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) =
        (let M : ℕ := N + 1
          (∫ y : ℝ in (-T)..(-ρ),
            f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) +
            (∫ y : ℝ in (-ρ)..ρ,
              f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) +
              ∫ y : ℝ in ρ..T,
                f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) := by
    exact
      Complex.rightEndpointSafeVerticalIntegral_split_three
        f N T ρ
        (hsafe_integrable (-T) (-ρ) hlower_interval)
        (hsafe_integrable (-ρ) ρ hmiddle_interval)
        (hsafe_integrable ρ T hupper_interval)
  have hlower_zero :
      (let M : ℕ := N + 1
        (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) - Complex.I * (T : ℂ))) -
            (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) - Complex.I * (ρ : ℂ))) +
              Complex.I *
                (∫ y : ℝ in (-T)..(-ρ), f ((M : ℂ) + Complex.I * (y : ℂ))) -
                Complex.I *
                  (∫ y : ℝ in (-T)..(-ρ),
                    f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))) =
        0 :=
    Complex.rightEndpointLowerRectangleBoundaryIntegral_eq_zero
      f N T hT hρ hρT hcont hdiff
  have hupper_zero :
      (let M : ℕ := N + 1
        (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) + Complex.I * (ρ : ℂ))) -
            (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) + Complex.I * (T : ℂ))) +
              Complex.I *
                (∫ y : ℝ in ρ..T, f ((M : ℂ) + Complex.I * (y : ℂ))) -
                Complex.I *
                  (∫ y : ℝ in ρ..T,
                    f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))) =
        0 :=
    Complex.rightEndpointUpperRectangleBoundaryIntegral_eq_zero
      f N T hρ hρT hcont hdiff
  have hhalf_zero :
      (let M : ℕ := N + 1
        (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ),
            f ((x : ℂ) - Complex.I * (ρ : ℂ))) +
          -(∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ),
            f ((x : ℂ) + Complex.I * (ρ : ℂ))) -
            Complex.I *
              (∫ y : ℝ in (-ρ)..ρ,
                f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ))) -
          ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
            f ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) =
        0 :=
    Complex.rightEndpointHalfRectangleDeletedDiskBoundary_eq_zero
      f N T hT hρ hρT hcont hdiff
  unfold Complex.rightEndpointCapCollarOrientedBoundaryIntegral
  unfold M at hsafe_split
  unfold M at hlower_zero
  unfold M at hupper_zero
  unfold M at hhalf_zero
  exact
    Complex.rightEndpointCapCollarBoundary_algebra
      (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) - Complex.I * (T : ℂ)))
      (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) + Complex.I * (T : ℂ)))
      (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) - Complex.I * (ρ : ℂ)))
      (∫ x : ℝ in ((M : ℝ) - ρ)..(M : ℝ), f ((x : ℂ) + Complex.I * (ρ : ℂ)))
      (∫ y : ℝ in (-T)..(-ρ), f ((M : ℂ) + Complex.I * (y : ℂ)))
      (∫ y : ℝ in ρ..T, f ((M : ℂ) + Complex.I * (y : ℂ)))
      (∫ y : ℝ in (-T)..T,
        f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
      (∫ y : ℝ in (-T)..(-ρ),
        f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
      (∫ y : ℝ in (-ρ)..ρ,
        f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
      (∫ y : ℝ in ρ..T,
        f ((((M : ℝ) - ρ : ℝ) : ℂ) + Complex.I * (y : ℂ)))
      (∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
        f ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
      hsafe_split
      hlower_zero
      hupper_zero
      hhalf_zero

/-- The Abel-Plana right endpoint oriented boundary is the generic right cap
boundary specialized to the logarithmic cotangent rectangle integrand. -/
theorem Complex.finiteAbelPlana_log_rightEndpointCapCollarOrientedBoundary_eq_generic
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary N w T ρ =
      Complex.rightEndpointCapCollarOrientedBoundaryIntegral
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        N T ρ := by
  rfl

/-- Cauchy-Goursat on the right endpoint cap/collar domain.

This is the local deleted-disk collar theorem for the endpoint pole at
`N + 1`: the boundary of the left endpoint collar, after deleting the endpoint
semicircle, has zero integral. -/
theorem Complex.finiteAbelPlana_log_rightEndpointCapCollar_orientedBoundary_eq_zero_owner
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary N w T ρ = 0 := by
  have hρnonneg : 0 ≤ ρ := le_of_lt hρ
  have hcont_right :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ) :=
    Complex.continuousOn_finiteAbelPlanaLogRectangleIntegrand_rightEndpointCapCollar
      hρnonneg hdeleted_geometry.1 hcont
  have hdiff_right :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaLogRightEndpointCapCollarPuncturedDomain N T ρ) :=
    Complex.differentiableOn_finiteAbelPlanaLogRectangleIntegrand_rightEndpointCapCollar
      hρnonneg hdeleted_geometry.1 hdiff
  calc
    Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary N w T ρ =
        Complex.rightEndpointCapCollarOrientedBoundaryIntegral
          (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
          N T ρ := by
      exact
        Complex.finiteAbelPlana_log_rightEndpointCapCollarOrientedBoundary_eq_generic
          N w T ρ
    _ = 0 := by
      exact
        Complex.rightEndpointCapCollarOrientedBoundaryIntegral_eq_zero
          (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
          N T hT hρ (by
            have hρ_abs : ρ < |T| / 2 := hdeleted_geometry.2.1
            exact
              Real.endpoint_radius_lt_height_of_lt_abs_height_half hT hρ_abs)
          hcont_right hdiff_right

/-- Owner Cauchy-Goursat statement for the two endpoint semicollars, in
oriented-boundary form.

Both endpoints use their named oriented-boundary objects. -/
theorem Complex.finiteAbelPlana_log_endpointSemicollarCauchyGoursat_orientedBoundary_pair_owner
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 ∧
      Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary N w T ρ = 0 := by
  have hρnonneg : 0 ≤ ρ := le_of_lt hρ
  have hcont_left :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ) :=
    Complex.continuousOn_finiteAbelPlanaLogRectangleIntegrand_leftEndpointCapCollar
      hρnonneg hdeleted_geometry.1 hcont
  have hdiff_left :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ) :=
    Complex.differentiableOn_finiteAbelPlanaLogRectangleIntegrand_leftEndpointCapCollar
      hρnonneg hdeleted_geometry.1 hdiff
  have hleft :
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 :=
    Complex.finiteAbelPlana_log_leftEndpointCapCollar_orientedBoundary_eq_zero_owner
      (N := N) T hT hρ hdeleted_geometry hcont_left hdiff_left
  have hright :
      Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary N w T ρ = 0 := by
    exact Complex.finiteAbelPlana_log_rightEndpointCapCollar_orientedBoundary_eq_zero_owner
      N T hT hρ hdeleted_geometry hcont hdiff
  exact ⟨hleft, hright⟩

/-- Endpoint half-collar Cauchy-Goursat in balance form.

This is the remaining planar topology input: the left endpoint right
half-collar and the right endpoint left half-collar have oriented boundary
zero, expressed as equality between their straight collar boundary and their
endpoint semicircular indentation.  The statement is deliberately local to the
two endpoint half-collars, not a full rectangle through an endpoint pole. -/
theorem Complex.finiteAbelPlana_log_endpointHalfCollarCauchyGoursat_balance_left_right
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    (Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
          Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ =
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) ∧
      (Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
            Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
              Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
                Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ =
          let M : ℕ := N + 1
          ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
            Complex.finiteAbelPlanaLogRectangleIntegrand w
                ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) := by
  have hboundary :=
    Complex.finiteAbelPlana_log_endpointSemicollarCauchyGoursat_orientedBoundary_pair_owner
      N T hT hρ hdeleted_geometry hcont hdiff
  constructor
  · exact
      Complex.finiteAbelPlana_log_leftEndpointHalfCollar_balance_of_orientedBoundary_zero
        w T ρ hboundary.1
  · unfold Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary at hboundary
    exact sub_eq_zero.mp hboundary.2

/-- Algebraic conversion from the left endpoint half-collar balance to the
oriented-boundary vanishing statement. -/
theorem Complex.finiteAbelPlana_log_leftEndpointHalfCollar_orientedBoundary_eq_zero_of_balance
    (w : ℂ)
    (T ρ : ℝ)
    (hbalance :
      Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
          Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ =
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 := by
  unfold Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary
  exact sub_eq_zero.mpr hbalance

/-- Algebraic conversion from the right endpoint half-collar balance to the
unfolded oriented-boundary vanishing statement. -/
theorem Complex.finiteAbelPlana_log_rightEndpointHalfCollar_orientedBoundary_eq_zero_of_balance
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ)
    (hbalance :
      Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ =
        let M : ℕ := N + 1
        ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) :
    Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
        Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
          Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ -
      (let M : ℕ := N + 1
        ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) = 0 := by
  exact sub_eq_zero.mpr hbalance

/-- The two local endpoint half-collar Cauchy-Goursat identities.

This is the exact local topology input for the endpoint collars.  The left
identity is Cauchy-Goursat on the right half-rectangle based at `0`, with its
right semicircular deleted boundary.  The right identity is the translated
left half-rectangle based at `N + 1`, with its left semicircular deleted
boundary.  The displayed signs are the punctured-domain orientations:
lower collar, minus upper collar, adjacent safe vertical edge, minus
principal-value vertical edge, minus the endpoint semicircle. -/
theorem Complex.finiteAbelPlana_log_endpointHalfCollarCauchyGoursat_left_right
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 ∧
      Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ -
        (let M : ℕ := N + 1
          ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
            Complex.finiteAbelPlanaLogRectangleIntegrand w
                ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) = 0 := by
  have hbalance :=
    Complex.finiteAbelPlana_log_endpointHalfCollarCauchyGoursat_balance_left_right
      N T hT hρ hdeleted_geometry hcont hdiff
  exact
    ⟨Complex.finiteAbelPlana_log_leftEndpointHalfCollar_orientedBoundary_eq_zero_of_balance
        w T ρ hbalance.1,
      Complex.finiteAbelPlana_log_rightEndpointHalfCollar_orientedBoundary_eq_zero_of_balance
        N w T ρ hbalance.2⟩

/-- Left endpoint half-collar Cauchy-Goursat identity, extracted from the
local endpoint half-collar pair. -/
theorem Complex.finiteAbelPlana_log_leftEndpointHalfCollarCauchyGoursat_orientedBoundary_eq_zero
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 := by
  have hρnonneg : 0 ≤ ρ := le_of_lt hρ
  have hcont_left :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ) :=
    Complex.continuousOn_finiteAbelPlanaLogRectangleIntegrand_leftEndpointCapCollar
      hρnonneg hdeleted_geometry.1 hcont
  have hdiff_left :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaLogLeftEndpointCapCollarPuncturedDomain T ρ) :=
    Complex.differentiableOn_finiteAbelPlanaLogRectangleIntegrand_leftEndpointCapCollar
      hρnonneg hdeleted_geometry.1 hdiff
  exact
    Complex.finiteAbelPlana_log_leftEndpointCapCollar_orientedBoundary_eq_zero_owner
      (N := N) T hT hρ hdeleted_geometry hcont_left hdiff_left

/-- Right endpoint half-collar Cauchy-Goursat identity, extracted from the
local endpoint half-collar pair. -/
theorem Complex.finiteAbelPlana_log_rightEndpointHalfCollarCauchyGoursat_orientedBoundary_eq_zero
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
        Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
          Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ -
      (let M : ℕ := N + 1
        ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) = 0 := by
  have hboundary :
      Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary N w T ρ = 0 :=
    Complex.finiteAbelPlana_log_rightEndpointCapCollar_orientedBoundary_eq_zero_owner
      N T hT hρ hdeleted_geometry hcont hdiff
  unfold Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary at hboundary
  exact hboundary

/-- Assembly of the endpoint semicollar pair from the two local half-collar
Cauchy-Goursat identities. -/
theorem Complex.finiteAbelPlana_log_endpointSemicollarCauchyGoursat_pair_of_halfCollars
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hleft :
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0)
    (hright :
      Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ -
        (let M : ℕ := N + 1
          ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
            Complex.finiteAbelPlanaLogRectangleIntegrand w
                ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) = 0) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 ∧
      Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ -
        (let M : ℕ := N + 1
          ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
            Complex.finiteAbelPlanaLogRectangleIntegrand w
                ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) = 0 := by
  exact ⟨hleft, hright⟩

/-- Shared semicollar Cauchy-Goursat owner statement for the endpoint caps.

Each endpoint domain is a half-rectangle with the endpoint disk removed.
Its oriented boundary is
`lower collar - upper collar + safe vertical edge - PV vertical edge -
endpoint semicircle`, with the right endpoint obtained from the same local
semicollar geometry by translation and reflection.  The second conjunct is
written in unfolded form so the same owner theorem can serve the right wrapper
after the right endpoint boundary is named. -/
theorem Complex.finiteAbelPlana_log_endpointSemicollarCauchyGoursat_orientedBoundary_eq_zero_pair
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 ∧
      Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ -
        (let M : ℕ := N + 1
          ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
            Complex.finiteAbelPlanaLogRectangleIntegrand w
                ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) = 0 := by
  have hleft :
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 :=
    Complex.finiteAbelPlana_log_leftEndpointHalfCollarCauchyGoursat_orientedBoundary_eq_zero
      N T hT hρ hdeleted_geometry hcont hdiff
  have hright :
      Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ -
        (let M : ℕ := N + 1
          ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
            Complex.finiteAbelPlanaLogRectangleIntegrand w
                ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
              (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ)))) = 0 :=
    Complex.finiteAbelPlana_log_rightEndpointHalfCollarCauchyGoursat_orientedBoundary_eq_zero
      N T hT hρ hdeleted_geometry hcont hdiff
  exact
    Complex.finiteAbelPlana_log_endpointSemicollarCauchyGoursat_pair_of_halfCollars
      N T hleft hright

/-- Cauchy-Goursat on the left endpoint cap/collar domain, with the boundary
orientation identified with the existing named side and indentation integrals.

This is the exact local classical proof obligation: apply Cauchy-Goursat to the
punctured cap/collar domain and match its oriented boundary to the lower collar,
upper collar, adjacent safe-strip vertical edge, principal-value left edge, and
right endpoint semicircle. -/
theorem Complex.finiteAbelPlana_log_leftEndpointCapCollar_orientedBoundary_eq_zero
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 := by
  exact
    (Complex.finiteAbelPlana_log_endpointSemicollarCauchyGoursat_orientedBoundary_eq_zero_pair
      N T hT hρ hdeleted_geometry hcont hdiff).1

/-- Algebraic extraction of the left endpoint semicircle from the oriented
cap/collar boundary equation. -/
theorem Complex.finiteAbelPlana_log_leftEndpointCapCollar_balance_of_orientedBoundary_eq_zero
    (w : ℂ)
    (T ρ : ℝ)
    (hboundary :
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0) :
    Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
        Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ =
      ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
        Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  unfold Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary at hboundary
  exact sub_eq_zero.mp hboundary

/-- The left endpoint oriented boundary vanishes exactly when the straight
collar boundary equals the right semicircular indentation integral. -/
theorem Complex.finiteAbelPlana_log_leftEndpointCapCollar_orientedBoundary_eq_zero_iff_balance
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 ↔
      Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
          Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ =
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  constructor
  · intro hboundary
    exact
      Complex.finiteAbelPlana_log_leftEndpointCapCollar_balance_of_orientedBoundary_eq_zero
        w T ρ hboundary
  · intro hbalance
    unfold Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary
    exact sub_eq_zero.mpr hbalance

/-- Unnormalized local Cauchy-Goursat balance for the left endpoint collar.

The contour is the left endpoint cap/collar subdomain: the lower horizontal
collar from `0` to `ρ`, the safe-strip vertical edge at `x = ρ`, the upper
horizontal collar with opposite orientation, the principal-value left vertical
edge with opposite orientation, and the right semicircular indentation around
the deleted endpoint pole.  Cauchy's theorem on that punctured collar says the
sum of these oriented pieces is zero; equivalently, the straight cap/collar
boundary equals the endpoint indentation integral with the displayed
orientation. -/
theorem Complex.finiteAbelPlana_log_leftEndpointCapCollar_unnormalizedCauchy_balance
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
        Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
          Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ =
      ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
        Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  have hboundary :
      Complex.finiteAbelPlanaLogLeftEndpointCapCollarOrientedBoundary w T ρ = 0 :=
    Complex.finiteAbelPlana_log_leftEndpointCapCollar_orientedBoundary_eq_zero
      N T hT hρ hdeleted_geometry hcont hdiff
  exact
    Complex.finiteAbelPlana_log_leftEndpointCapCollar_balance_of_orientedBoundary_eq_zero
      w T ρ hboundary

/-- The left endpoint collar, together with the adjacent safe-strip boundary
pieces, contributes exactly the left endpoint deleted semicircle.

This is the one-piece Cauchy-Goursat statement for the left endpoint collar in
the finite Abel-Plana punctured rectangle.  Its proof is the classical local
rectangle argument: apply Cauchy-Goursat on the small endpoint collar
subdomain, then identify the one curved boundary component with the
principal-value left endpoint indentation. -/
theorem Complex.finiteAbelPlana_log_leftEndpointCapCollarCauchy_balance
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogLeftEndpointCapCollarBoundary w T ρ =
      Complex.finiteAbelPlanaLogLeftEndpointIndentationIntegral w ρ := by
  have hlocal :
      Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
          Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ =
        ∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) :=
    Complex.finiteAbelPlana_log_leftEndpointCapCollar_unnormalizedCauchy_balance
      N T hT hρ hdeleted_geometry hcont hdiff
  show
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (Complex.finiteAbelPlanaLogLeftEndpointLowerCollar w T ρ -
          Complex.finiteAbelPlanaLogLeftEndpointUpperCollar w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripLeftSide 0 w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogFiniteHeightLeftSidePV w T ρ) =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (∫ θ : ℝ in (-(Real.pi / 2))..(Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
  exact
    congrArg
      (fun z : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ * z)
      hlocal

/-- Solving the right endpoint oriented-boundary Cauchy equation gives the
right endpoint half-collar balance. -/
theorem Complex.finiteAbelPlana_log_rightEndpointHalfCollar_balance_of_orientedBoundary_zero
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ)
    (hboundary :
      Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary N w T ρ = 0) :
    Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ =
        let M : ℕ := N + 1
        ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  unfold Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary at hboundary
  exact sub_eq_zero.mp hboundary

/-- Cauchy-Goursat on the right endpoint cap/collar domain, with the boundary
orientation identified with the existing named side and indentation integrals.

This is the exact local classical proof obligation: apply Cauchy-Goursat to the
punctured cap/collar domain and match its oriented boundary to the lower collar,
upper collar, principal-value right edge, adjacent safe-strip vertical edge, and
left endpoint semicircle. -/
theorem Complex.finiteAbelPlana_log_rightEndpointCapCollar_orientedBoundary_eq_zero
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary N w T ρ = 0 := by
  exact
    Complex.finiteAbelPlana_log_rightEndpointCapCollar_orientedBoundary_eq_zero_owner
      N T hT hρ hdeleted_geometry hcont hdiff

/-- Algebraic extraction of the right endpoint semicircle from the oriented
cap/collar boundary equation. -/
theorem Complex.finiteAbelPlana_log_rightEndpointCapCollar_balance_of_orientedBoundary_eq_zero
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ)
    (hboundary :
      Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary N w T ρ = 0) :
    Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
        Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
          Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ =
      let M : ℕ := N + 1
      ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
        Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  unfold Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary at hboundary
  exact sub_eq_zero.mp hboundary

/-- The right endpoint oriented boundary vanishes exactly when the straight
collar boundary equals the left semicircular indentation integral. -/
theorem Complex.finiteAbelPlana_log_rightEndpointCapCollar_orientedBoundary_eq_zero_iff_balance
    (N : ℕ)
    (w : ℂ)
    (T ρ : ℝ) :
    Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary N w T ρ = 0 ↔
      Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ =
        let M : ℕ := N + 1
        ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  constructor
  · intro hboundary
    exact
      Complex.finiteAbelPlana_log_rightEndpointCapCollar_balance_of_orientedBoundary_eq_zero
        N w T ρ hboundary
  · intro hbalance
    unfold Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary
    exact sub_eq_zero.mpr hbalance

/-- Unnormalized local Cauchy-Goursat balance for the right endpoint collar.

The contour is the right endpoint cap/collar subdomain: the lower horizontal
collar from `N + 1 - ρ` to `N + 1`, the principal-value right vertical edge,
the upper horizontal collar with opposite orientation, the adjacent safe-strip
vertical edge with opposite orientation, and the left semicircular indentation
around the deleted endpoint pole.  Cauchy's theorem on that punctured collar
says the sum of these oriented pieces is zero; equivalently, the straight
cap/collar boundary equals the endpoint indentation integral with the displayed
orientation. -/
theorem Complex.finiteAbelPlana_log_rightEndpointCapCollar_unnormalizedCauchy_balance
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
        Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
          Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
            Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ =
      let M : ℕ := N + 1
      ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
        Complex.finiteAbelPlanaLogRectangleIntegrand w
            ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
          (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) := by
  have hboundary :
      Complex.finiteAbelPlanaLogRightEndpointCapCollarOrientedBoundary N w T ρ = 0 :=
    Complex.finiteAbelPlana_log_rightEndpointCapCollar_orientedBoundary_eq_zero
      N T hT hρ hdeleted_geometry hcont hdiff
  exact
    Complex.finiteAbelPlana_log_rightEndpointCapCollar_balance_of_orientedBoundary_eq_zero
      N w T ρ hboundary

/-- The right endpoint collar, together with the adjacent safe-strip boundary
pieces, contributes exactly the right endpoint deleted semicircle.

This is the right endpoint version of the local collar Cauchy-Goursat
calculation.  The ordinary straight edges cancel against the adjacent strip
orientation; the surviving curved boundary is the right endpoint indentation. -/
theorem Complex.finiteAbelPlana_log_rightEndpointCapCollarCauchy_balance
    {w : ℂ}
    (N : ℕ)
    (T : ℝ)
    {ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ)
    (hdeleted_geometry :
      ρ < (1 : ℝ) / 4 ∧
        ρ < |T| / 2 ∧
          ∀ n ∈ Finset.range (N + 2),
            ρ < Complex.finiteAbelPlanaLogIntegerResidueIsolationRadius w n)
    (hcont :
      ContinuousOn
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ))
    (hdiff :
      DifferentiableOn ℂ
        (fun z : ℂ => Complex.finiteAbelPlanaLogRectangleIntegrand w z)
        (Complex.finiteAbelPlanaPuncturedRectangle N T ρ)) :
    Complex.finiteAbelPlanaLogRightEndpointCapCollarBoundary N w T ρ =
      Complex.finiteAbelPlanaLogRightEndpointIndentationIntegral N w ρ := by
  have hlocal :
      Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ =
        let M : ℕ := N + 1
        ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) :=
    Complex.finiteAbelPlana_log_rightEndpointCapCollar_unnormalizedCauchy_balance
      N T hT hρ hdeleted_geometry hcont hdiff
  show
    ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (Complex.finiteAbelPlanaLogRightEndpointLowerCollar N w T ρ -
          Complex.finiteAbelPlanaLogRightEndpointUpperCollar N w T ρ +
            Complex.I * Complex.finiteAbelPlanaLogFiniteHeightRightSidePV N w T ρ -
              Complex.I * Complex.finiteAbelPlanaLogVerticalStripRightSide N w T ρ) =
      ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ *
        (let M : ℕ := N + 1
        ∫ θ : ℝ in (Real.pi / 2)..(3 * Real.pi / 2),
          Complex.finiteAbelPlanaLogRectangleIntegrand w
              ((M : ℂ) + (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))) *
            (Complex.I * (ρ : ℂ) * Complex.exp (Complex.I * (θ : ℂ))))
  exact
    congrArg
      (fun z : ℂ => ((2 : ℂ) * (Real.pi : ℂ) * Complex.I)⁻¹ * z)
      hlocal

end

end LFunctions
end Boundary
