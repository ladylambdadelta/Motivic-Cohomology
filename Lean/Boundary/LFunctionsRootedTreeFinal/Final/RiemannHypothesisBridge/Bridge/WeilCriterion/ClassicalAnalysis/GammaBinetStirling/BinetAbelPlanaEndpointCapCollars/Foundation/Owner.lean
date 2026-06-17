import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.MeasureTheory.Integral.SetIntegral
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ClassicalAnalysis.GammaBinetStirling.BinetAbelPlanaFiniteHoleSubdivision

/-!
# Foundation lemmas for endpoint cap-collar Cauchy balances

Basic helper theorems about complex numbers and real interval bounds needed
for the endpoint cap-collar domains and integrand analysis.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Topology
open MeasureTheory

notation:max "[[" a "," b "]]" => Set.Icc a b

/-- Algebraic cancellation for the finite-hole subdivision once the cap/collar
boundary has been identified with the missing deleted-arc contribution. -/
theorem Complex.finiteAbelPlana_log_verticalStrip_add_deleted_sub_verticalStrip_sub_deleted
    (A B : ℂ) :
    A + (B - A) - B = 0 :=
  Eq.trans
    (congrArg (fun u : ℂ => u - B) (add_sub_cancel_left A B))
    (sub_self B)

/-- Left distributivity over two summands, oriented for collection. -/
theorem Complex.left_mul_add_two_collect
    (a b c : ℂ) :
    a * b + a * c = a * (b + c) :=
  Eq.symm (mul_add a b c)

/-- Left distributivity over three summands, oriented for collection. -/
theorem Complex.left_mul_add_three_collect
    (a b c d : ℂ) :
    a * b + a * c + a * d = a * (b + c + d) :=
  Eq.trans
    (congrArg (fun u : ℂ => u + a * d)
      (Complex.left_mul_add_two_collect a b c))
    (Eq.trans
      (Complex.left_mul_add_two_collect a (b + c) d)
      rfl)

/-- Helper: rearrange three-part plus three-part left boundary to normalized form. -/
theorem Complex.leftEndpointCapCollarBoundary_rearrange
    (lowerT upperT lowerChord upperChord safeLower safeMiddle safeUpper
      pvLower pvUpper arc : ℂ) :
    (lowerT - lowerChord + Complex.I * safeLower - Complex.I * pvLower) +
        (upperChord - upperT + Complex.I * safeUpper - Complex.I * pvUpper) +
          (lowerChord - upperChord + Complex.I * safeMiddle - arc) =
      lowerT - upperT +
          (Complex.I * safeLower + Complex.I * safeMiddle + Complex.I * safeUpper) -
        (Complex.I * pvLower + Complex.I * pvUpper) - arc := by
  abel_nf

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
        Complex.I * (pvLower + pvUpper) - arc :=
  let h_rearrange := Complex.leftEndpointCapCollarBoundary_rearrange
    lowerT upperT lowerChord upperChord safeLower safeMiddle safeUpper pvLower pvUpper arc
  let h_safe := Complex.left_mul_add_three_collect Complex.I safeLower safeMiddle safeUpper
  let h_pv := Complex.left_mul_add_two_collect Complex.I pvLower pvUpper
  Eq.trans h_rearrange
    (congrArg₂
      (fun safe pv : ℂ => lowerT - upperT + safe - pv - arc)
      h_safe h_pv)

/-- Helper: rearrange three-part plus three-part right boundary to normalized form. -/
theorem Complex.rightEndpointCapCollarBoundary_rearrange
    (lowerT upperT lowerChord upperChord pvLower pvUpper safeLower safeMiddle
      safeUpper arc : ℂ) :
    (lowerT - lowerChord + Complex.I * pvLower - Complex.I * safeLower) +
        (upperChord - upperT + Complex.I * pvUpper - Complex.I * safeUpper) +
          (lowerChord - upperChord - Complex.I * safeMiddle - arc) =
      lowerT - upperT +
          (Complex.I * pvLower + Complex.I * pvUpper) -
        (Complex.I * safeLower + Complex.I * safeMiddle + Complex.I * safeUpper) -
        arc := by
  abel_nf

/-- Collect the three right endpoint cap/collar boundary pieces after the chord
terms cancel. -/
theorem Complex.rightEndpointCapCollarBoundary_collect
    (lowerT upperT lowerChord upperChord pvLower pvUpper safeLower safeMiddle
      safeUpper arc : ℂ) :
    (lowerT - lowerChord + Complex.I * pvLower - Complex.I * safeLower) +
        (upperChord - upperT + Complex.I * pvUpper - Complex.I * safeUpper) +
          (lowerChord - upperChord - Complex.I * safeMiddle - arc) =
      lowerT - upperT + Complex.I * (pvLower + pvUpper) -
        Complex.I * (safeLower + safeMiddle + safeUpper) - arc :=
  let h_rearrange := Complex.rightEndpointCapCollarBoundary_rearrange
    lowerT upperT lowerChord upperChord pvLower pvUpper safeLower safeMiddle safeUpper arc
  let h_pv := Complex.left_mul_add_two_collect Complex.I pvLower pvUpper
  let h_safe := Complex.left_mul_add_three_collect Complex.I safeLower safeMiddle safeUpper
  Eq.trans h_rearrange
    (congrArg₂
      (fun pv safe : ℂ => lowerT - upperT + pv - safe - arc)
      h_pv h_safe)

/-- The norm of a purely vertical complex displacement is the absolute value
of its real height. -/
theorem Complex.norm_I_mul_real (y : ℝ) :
    ‖Complex.I * (y : ℂ)‖ = |y| :=
  Eq.trans (norm_mul Complex.I (y : ℂ))
    (Eq.trans
      (congrArg (fun r : ℝ => r * ‖(y : ℂ)‖) Complex.norm_I)
      (Eq.trans (one_mul ‖(y : ℂ)‖) (RCLike.norm_ofReal y)))

/-- Cancelling a real center from a vertical translate leaves only the
vertical displacement. -/
theorem Complex.norm_centered_vertical_translate_sub_center
    (M : ℂ)
    (y : ℝ) :
    ‖(M + Complex.I * (y : ℂ)) - M‖ = |y| :=
  let hcancel : (M + Complex.I * (y : ℂ)) - M = Complex.I * (y : ℂ) :=
    add_sub_cancel_left M (Complex.I * (y : ℂ))
  Eq.trans (congrArg norm hcancel) (Complex.norm_I_mul_real y)

/-- A positive natural number is at least one after coercion to `ℝ`. -/
theorem Real.one_le_natCast_of_pos
    {m : ℕ}
    (hm : 0 < m) :
    (1 : ℝ) ≤ (m : ℝ) :=
  (Nat.cast_le : ((1 : ℝ) ≤ (m : ℝ) ↔ 1 ≤ m)).mpr (Nat.succ_le_iff.mpr hm)

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
    -ρ ≤ T :=
  (neg_nonpos.mpr hρ.le).trans hT.le

/-- If `0 < T` and `0 < ρ`, then the lower ambient height is below the upper
indentation height. -/
theorem Real.endpoint_neg_height_le_radius
    {T ρ : ℝ}
    (hT : 0 < T)
    (hρ : 0 < ρ) :
    -T ≤ ρ :=
  (neg_nonpos.mpr hT.le).trans hρ.le

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
    ρ < T :=
  let hT_abs : |T| = T := abs_of_pos hT
  let hρ_half : ρ < T / 2 := hT_abs ▸ hρ_abs
  hρ_half.trans (half_lt_self hT)

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
    ∀ y ∈ [[(-T), (-ρ)]], y ∈ [[-T, T]] :=
  fun y hy =>
    let horder : -T ≤ -ρ := Real.endpoint_neg_height_le_neg_radius hρT
    let hyIcc : y ∈ Set.Icc (-T) (-ρ) :=
      Eq.mp
        (congrArg (fun S : Set ℝ => y ∈ S) (Set.uIcc_of_le horder))
        hy
    let hy_le_T : y ≤ T :=
      hyIcc.2.trans (Real.endpoint_neg_radius_le_height (hρ.trans hρT) hρ)
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
    ∀ y ∈ [[(-ρ), ρ]], y ∈ [[-T, T]] :=
  fun y hy =>
    let horder : -ρ ≤ ρ := (neg_nonpos.mpr hρ.le).trans hρ.le
    let hyIcc : y ∈ Set.Icc (-ρ) ρ :=
      Eq.mp
        (congrArg (fun S : Set ℝ => y ∈ S) (Set.uIcc_of_le horder))
        hy
    let hy_ge_negT : -T ≤ y :=
      (Real.endpoint_neg_height_le_neg_radius hρT).trans hyIcc.1
    let hy_le_T : y ≤ T :=
      hyIcc.2.trans hρT.le
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
    ∀ y ∈ [[ρ, T]], y ∈ [[-T, T]] :=
  fun y hy =>
    let horder : ρ ≤ T := le_of_lt hρT
    let hyIcc : y ∈ Set.Icc ρ T :=
      Eq.mp
        (congrArg (fun S : Set ℝ => y ∈ S) (Set.uIcc_of_le horder))
        hy
    let hy_ge_negT : -T ≤ y :=
      (Real.endpoint_neg_height_le_radius hT hρ).trans hyIcc.1
    Eq.mpr
      (congrArg (fun S : Set ℝ => y ∈ S)
        (Set.uIcc_of_le (neg_le_self hT.le)))
      (And.intro hy_ge_negT hyIcc.2)

/-- A radius smaller than `1/2` has doubled radius at most `1`. -/
theorem Real.endpoint_two_radius_le_one_of_lt_half
    {ρ : ℝ}
    (hρ : ρ < (1 : ℝ) / 2) :
    ρ + ρ ≤ (1 : ℝ) :=
  let hsum : ρ + ρ ≤ (1 : ℝ) / 2 + (1 : ℝ) / 2 :=
    add_le_add hρ.le hρ.le
  hsum.trans_eq (add_halves (1 : ℝ))

/-- A radius smaller than `1/2` satisfies the endpoint disk-separation
inequality `ρ - 1 ≤ -ρ`. -/
theorem Real.endpoint_radius_sub_one_le_neg_radius_of_lt_half
    {ρ : ℝ}
    (hρ : ρ < (1 : ℝ) / 2) :
    ρ - 1 ≤ -ρ :=
  let hdouble : ρ + ρ ≤ (1 : ℝ) :=
    Real.endpoint_two_radius_le_one_of_lt_half hρ
  let hle_sub : ρ ≤ 1 - ρ :=
    le_sub_iff_add_le.mpr hdouble
  let hle_add : ρ ≤ -ρ + 1 :=
    Eq.trans hle_sub
      (Eq.trans (sub_eq_add_neg 1 ρ) (add_comm 1 (-ρ)))
  sub_le_iff_le_add.mpr hle_add

/-- Left endpoint collar separation from a nonzero integer center. -/
theorem Real.endpoint_left_re_sub_integer_le_neg_radius
    {x ρ m : ℝ}
    (hx : x ≤ ρ)
    (hm : 1 ≤ m)
    (hρ : ρ < (1 : ℝ) / 2) :
    x - m ≤ -ρ :=
  let hxm : x - m ≤ ρ - 1 := sub_le_sub hx hm
  hxm.trans (Real.endpoint_radius_sub_one_le_neg_radius_of_lt_half hρ)

/-- Rebracketing `M + (1 - ρ)` as `(M + 1) - ρ`. -/
theorem Real.endpoint_add_one_sub_radius_eq
    (M ρ : ℝ) :
    M + (1 - ρ) = (M + 1) - ρ :=
  Eq.trans
    (congrArg (fun x : ℝ => M + x) (sub_eq_add_neg 1 ρ))
    (Eq.trans (add_assoc M 1 (-ρ)) ((sub_eq_add_neg (M + 1) ρ).symm))

/-- Right endpoint collar separation from the previous integer center. -/
theorem Real.endpoint_radius_le_successor_minus_radius_sub_nat
    (N : ℕ)
    {ρ : ℝ}
    (hρ : ρ < (1 : ℝ) / 2) :
    ρ ≤ (((N + 1 : ℕ) : ℝ) - ρ) - (N : ℝ) :=
  let hdouble : ρ + ρ ≤ (1 : ℝ) :=
    Real.endpoint_two_radius_le_one_of_lt_half hρ
  let htarget : ρ ≤ 1 - ρ :=
    le_sub_iff_add_le.mpr hdouble
  let hbase : ρ ≤ (((N : ℝ) + 1) - ρ) - (N : ℝ) :=
    Eq.trans htarget
      (Eq.trans
        ((add_sub_cancel_left (N : ℝ) (1 - ρ)).symm)
        (congrArg (fun x : ℝ => x - (N : ℝ))
          (Real.endpoint_add_one_sub_radius_eq (N : ℝ) ρ)))
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
    (z - (m : ℂ)).re = z.re - (m : ℝ) :=
  Eq.trans (Complex.sub_re z (m : ℂ)) rfl

/-- The imaginary part of subtracting a natural-number point on the real axis. -/
theorem Complex.endpoint_sub_natCast_im
    (z : ℂ)
    (m : ℕ) :
    (z - (m : ℂ)).im = z.im :=
  Eq.trans (Complex.sub_im z (m : ℂ)) (Eq.trans rfl (sub_zero z.im))

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

end

end LFunctions
end Boundary
