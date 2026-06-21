import Mathlib.Analysis.SpecialFunctions.Exp
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.Core.Owner

/-!
# Finite-order envelope algebra

This file owns the generic algebra used to transport polynomial and
finite-order exponential growth bounds through the completed-zeta
normalization.
-/

namespace Boundary
namespace LFunctions

noncomputable section

theorem complex_one_re_eq_one : ((1 : ℂ).re = (1 : ℝ)) :=
  rfl

theorem complex_one_norm_eq_one : ‖(1 : ℂ)‖ = (1 : ℝ) :=
  norm_one

theorem complex_half_norm_le_one : ‖(1 / 2 : ℂ)‖ ≤ (1 : ℝ) := by
  have hnorm_div : ‖(1 / 2 : ℂ)‖ = ‖(1 : ℂ)‖ / ‖(2 : ℂ)‖ :=
    norm_div (1 : ℂ) (2 : ℂ)
  have hone_norm : ‖(1 : ℂ)‖ = (1 : ℝ) :=
    complex_one_norm_eq_one
  have htwo_norm : ‖(2 : ℂ)‖ = (2 : ℝ) :=
    Complex.norm_ofNat 2
  calc
    ‖(1 / 2 : ℂ)‖ = ‖(1 : ℂ)‖ / ‖(2 : ℂ)‖ := hnorm_div
    _ = 1 / ‖(2 : ℂ)‖ := by
      exact congrArg (fun x : ℝ => x / ‖(2 : ℂ)‖) hone_norm
    _ = (1 / 2 : ℝ) := by
      exact congrArg (fun x : ℝ => 1 / x) htwo_norm
    _ ≤ 1 := le_of_lt one_half_lt_one

theorem complex_one_sub_half_eq_half :
    (1 : ℂ) - (1 / 2 : ℂ) = (1 / 2 : ℂ) := by
  exact sub_eq_iff_eq_add.mpr
    (add_halves (1 : ℂ)).symm

theorem complex_one_sub_half_norm_le_one :
    ‖(1 : ℂ) - (1 / 2 : ℂ)‖ ≤ (1 : ℝ) := by
  exact Eq.subst
    (motive := fun w : ℂ => ‖w‖ ≤ (1 : ℝ))
    complex_one_sub_half_eq_half.symm
    complex_half_norm_le_one

theorem real_zero_lt_four : (0 : ℝ) < 4 := by
  exact zero_lt_four

theorem real_one_add_one_add_eq_two_add (x : ℝ) :
    1 + (1 + x) = 2 + x := by
  calc
    1 + (1 + x) = (1 + 1) + x := by
      exact (add_assoc 1 1 x).symm
    _ = 2 + x := by
      exact congrArg (fun y : ℝ => y + x) one_add_one_eq_two

theorem real_le_two_mul_of_nonneg {x : ℝ} (hx : 0 ≤ x) : x ≤ 2 * x := by
  exact le_mul_of_one_le_left hx one_le_two

theorem real_two_add_le_two_add_two_mul {x : ℝ} (hx : 0 ≤ x) :
    2 + x ≤ 2 + 2 * x :=
  add_le_add_left (real_le_two_mul_of_nonneg hx) 2

theorem real_two_add_two_mul_eq_two_mul_one_add (x : ℝ) :
    2 + 2 * x = 2 * (1 + x) := by
  calc
    2 + 2 * x = 2 * 1 + 2 * x := by
      exact congrArg (fun y : ℝ => y + 2 * x) (mul_one 2).symm
    _ = 2 * (1 + x) := by
      exact (mul_add 2 1 x).symm

theorem real_mul_pair_reassociate (A B X Y : ℝ) :
    (A * X) * (B * Y) = (A * B) * (X * Y) := by
  calc
    (A * X) * (B * Y) = ((A * X) * B) * Y := by
      exact (mul_assoc (A * X) B Y).symm
    _ = (A * (X * B)) * Y := by
      exact congrArg (fun t : ℝ => t * Y) (mul_assoc A X B)
    _ = (A * (B * X)) * Y := by
      exact congrArg (fun t : ℝ => (A * t) * Y) (mul_comm X B)
    _ = ((A * B) * X) * Y := by
      exact congrArg (fun t : ℝ => t * Y) (mul_assoc A B X).symm
    _ = (A * B) * (X * Y) := by
      exact mul_assoc (A * B) X Y

theorem real_two_mul_square_eq_four_mul_sq (H : ℝ) :
    (2 * H) * (2 * H) = 4 * H ^ (2 : ℕ) := by
  calc
    (2 * H) * (2 * H) = ((2 : ℝ) * 2) * (H * H) := by
      exact real_mul_pair_reassociate 2 2 H H
    _ = 4 * (H * H) := by
      exact congrArg (fun c : ℝ => c * (H * H)) ((two_mul (2 : ℝ)).trans two_add_two_eq_four)
    _ = 4 * H ^ (2 : ℕ) := by
      exact congrArg (fun x : ℝ => 4 * x) (pow_two H).symm

theorem real_mul_add_self_eq_add_one_mul (A X : ℝ) :
    A * X + X = (A + 1) * X := by
  calc
    A * X + X = A * X + 1 * X := by
      exact congrArg (fun y : ℝ => A * X + y) (one_mul X).symm
    _ = (A + 1) * X := by
      exact (add_mul A 1 X).symm

theorem real_self_add_mul_eq_add_one_mul (A X : ℝ) :
    X + A * X = (A + 1) * X := by
  calc
    X + A * X = 1 * X + A * X := by
      exact congrArg (fun y : ℝ => y + A * X) (one_mul X).symm
    _ = (1 + A) * X := by
      exact (add_mul 1 A X).symm
    _ = (A + 1) * X := by
      exact congrArg (fun y : ℝ => y * X) (add_comm 1 A)

theorem complex_sub_add_eq_sub_add_neg (a b c : ℂ) :
    a - (b + c) = (a - b) + (-c) := by
  calc
    a - (b + c) = a + -(b + c) := sub_eq_add_neg a (b + c)
    _ = a + (-b + -c) := by
      exact congrArg (fun x : ℂ => a + x) (neg_add b c)
    _ = (a + -b) + -c := by
      exact (add_assoc a (-b) (-c)).symm
    _ = (a - b) + (-c) := by
      exact congrArg (fun x : ℂ => x + -c) (sub_eq_add_neg a b).symm

/-- A finite-order estimate can be enlarged in constants and exponent.

This early algebraic helper is used by the first analytic decompositions before the
general normalization section below. -/
theorem exponentialFiniteOrder_bound_le_of_le_constants_and_exponent_core
    {A B A' B' : ℝ} {m d : ℕ} {z : ℂ}
    (hA : 0 ≤ A)
    (hAle : A ≤ A')
    (hBle : B ≤ B')
    (hBnonneg : 0 ≤ B)
    (hmd : m ≤ d) :
    A * Real.exp (B * (1 + ‖z‖) ^ m) ≤
      A' * Real.exp (B' * (1 + ‖z‖) ^ d) := by
  let H : ℝ := 1 + ‖z‖
  have hH_ge_one : (1 : ℝ) ≤ H :=
    le_add_of_nonneg_right (norm_nonneg z)
  have hH_nonneg : 0 ≤ H :=
    le_trans zero_le_one hH_ge_one
  have hpow_le : H ^ m ≤ H ^ d :=
    pow_le_pow_right₀ hH_ge_one hmd
  have hB_pow_le : B * H ^ m ≤ B * H ^ d :=
    mul_le_mul_of_nonneg_left hpow_le hBnonneg
  have hB_le_B'pow : B * H ^ d ≤ B' * H ^ d :=
    mul_le_mul_of_nonneg_right hBle (pow_nonneg hH_nonneg d)
  have hexponent_le : B * H ^ m ≤ B' * H ^ d :=
    le_trans hB_pow_le hB_le_B'pow
  have hexp_le :
      Real.exp (B * H ^ m) ≤ Real.exp (B' * H ^ d) :=
    Real.exp_le_exp.mpr hexponent_le
  have hexp_nonneg : 0 ≤ Real.exp (B * H ^ m) :=
    le_of_lt (Real.exp_pos (B * H ^ m))
  have hA'nonneg : 0 ≤ A' :=
    le_trans hA hAle
  exact mul_le_mul hAle hexp_le hexp_nonneg hA'nonneg

/-- A finite-order estimate can be enlarged in constants and exponent. -/
theorem exponentialFiniteOrder_bound_le_of_le_constants_and_exponent
    {A B A' B' : ℝ} {m d : ℕ} {z : ℂ}
    (hA : 0 ≤ A)
    (hAle : A ≤ A')
    (hBle : B ≤ B')
    (hBnonneg : 0 ≤ B)
    (hmd : m ≤ d) :
    A * Real.exp (B * (1 + ‖z‖) ^ m) ≤
      A' * Real.exp (B' * (1 + ‖z‖) ^ d) := by
  let H : ℝ := 1 + ‖z‖
  have hH_ge_one : (1 : ℝ) ≤ H :=
    le_add_of_nonneg_right (norm_nonneg z)
  have hH_nonneg : 0 ≤ H :=
    le_trans zero_le_one hH_ge_one
  have hpow_le : H ^ m ≤ H ^ d :=
    pow_le_pow_right₀ hH_ge_one hmd
  have hB_pow_le : B * H ^ m ≤ B * H ^ d :=
    mul_le_mul_of_nonneg_left hpow_le hBnonneg
  have hB_le_B'pow : B * H ^ d ≤ B' * H ^ d :=
    mul_le_mul_of_nonneg_right hBle (pow_nonneg hH_nonneg d)
  have hexponent_le : B * H ^ m ≤ B' * H ^ d :=
    le_trans hB_pow_le hB_le_B'pow
  have hexp_le :
      Real.exp (B * H ^ m) ≤ Real.exp (B' * H ^ d) :=
    Real.exp_le_exp.mpr hexponent_le
  have hexp_nonneg : 0 ≤ Real.exp (B * H ^ m) :=
    le_of_lt (Real.exp_pos (B * H ^ m))
  have hA'nonneg : 0 ≤ A' :=
    le_trans hA hAle
  exact mul_le_mul hAle hexp_le hexp_nonneg hA'nonneg

/-- Strip and far-right estimates combine to a right-half-plane finite-order estimate. -/
theorem completedRiemannZeta₀_rightHalfPlane_finiteOrder_growth_bound_of_strip_and_farRight
    (hstrip :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          z.re ≤ 2 →
          ‖completedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hfar :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          2 ≤ z.re →
          ‖completedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 ≤ z.re →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hstrip with ⟨As, Bs, ms, hAs, hBs, hstrip_bound⟩
  rcases hfar with ⟨Af, Bf, mf, hAf, hBf, hfar_bound⟩
  refine ⟨As + Af, Bs + Bf, ms + mf, add_pos hAs hAf, add_pos hBs hBf, ?_⟩
  intro z hz_re_nonneg
  have hAs_nonneg : 0 ≤ As := le_of_lt hAs
  have hAf_nonneg : 0 ≤ Af := le_of_lt hAf
  have hBs_nonneg : 0 ≤ Bs := le_of_lt hBs
  have hBf_nonneg : 0 ≤ Bf := le_of_lt hBf
  have hA_strip_le : As ≤ As + Af :=
    le_add_of_nonneg_right hAf_nonneg
  have hA_far_le : Af ≤ As + Af :=
    le_add_of_nonneg_left hAs_nonneg
  have hB_strip_le : Bs ≤ Bs + Bf :=
    le_add_of_nonneg_right hBf_nonneg
  have hB_far_le : Bf ≤ Bs + Bf :=
    le_add_of_nonneg_left hBs_nonneg
  match le_total z.re 2 with
  | Or.inl hz_re_le_two =>
      exact le_trans (hstrip_bound z hz_re_nonneg hz_re_le_two)
        (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent
          hAs_nonneg
          hA_strip_le
          hB_strip_le
          hBs_nonneg
          (Nat.le_add_right ms mf))
  | Or.inr htwo_le_re =>
      have hdegree : mf ≤ ms + mf := by
        calc
          mf ≤ mf + ms := Nat.le_add_right mf ms
          _ = ms + mf := Nat.add_comm mf ms
      exact le_trans (hfar_bound z htwo_le_re)
        (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent
          hAf_nonneg
          hA_far_le
          hB_far_le
          hBf_nonneg
          hdegree)

/-- Strict strip and far-right estimates combine to a strict right-half-plane
finite-order estimate. -/
theorem completedRiemannZeta₀_strictRightHalfPlane_finiteOrder_growth_bound_of_strip_and_farRight
    (hstrip :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 < z.re →
          z.re ≤ 2 →
          ‖completedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hfar :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          2 ≤ z.re →
          ‖completedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        0 < z.re →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hstrip with ⟨As, Bs, ms, hAs, hBs, hstrip_bound⟩
  rcases hfar with ⟨Af, Bf, mf, hAf, hBf, hfar_bound⟩
  refine ⟨As + Af, Bs + Bf, ms + mf, add_pos hAs hAf, add_pos hBs hBf, ?_⟩
  intro z hz_re_pos
  have hAs_nonneg : 0 ≤ As := le_of_lt hAs
  have hAf_nonneg : 0 ≤ Af := le_of_lt hAf
  have hBs_nonneg : 0 ≤ Bs := le_of_lt hBs
  have hBf_nonneg : 0 ≤ Bf := le_of_lt hBf
  have hA_strip_le : As ≤ As + Af :=
    le_add_of_nonneg_right hAf_nonneg
  have hA_far_le : Af ≤ As + Af :=
    le_add_of_nonneg_left hAs_nonneg
  have hB_strip_le : Bs ≤ Bs + Bf :=
    le_add_of_nonneg_right hBf_nonneg
  have hB_far_le : Bf ≤ Bs + Bf :=
    le_add_of_nonneg_left hBs_nonneg
  match le_total z.re 2 with
  | Or.inl hz_re_le_two =>
      exact le_trans (hstrip_bound z hz_re_pos hz_re_le_two)
        (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent
          hAs_nonneg
          hA_strip_le
          hB_strip_le
          hBs_nonneg
          (Nat.le_add_right ms mf))
  | Or.inr htwo_le_re =>
      have hdegree : mf ≤ ms + mf := by
        exact Eq.subst
          (motive := fun d : ℕ => mf ≤ d)
          (Nat.add_comm mf ms)
          (Nat.le_add_right mf ms)
      exact le_trans (hfar_bound z htwo_le_re)
        (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent
          hAf_nonneg
          hA_far_le
          hB_far_le
          hBf_nonneg
          hdegree)

/-- The reflected point `1 - z` lies in the right half-plane when `z` lies in the left
half-plane. -/
theorem completedRiemannZeta₀_reflected_re_nonnegative_of_leftHalfPlane
    {z : ℂ}
    (hz : z.re ≤ 0) :
    0 ≤ (1 - z).re := by
  have hone_re : (1 : ℂ).re = (1 : ℝ) := by
    exact complex_one_re_eq_one
  calc
    0 ≤ 1 - z.re := by
      exact sub_nonneg.mpr (le_trans hz zero_le_one)
    _ = (1 : ℂ).re - z.re := by
      exact congrArg (fun x : ℝ => x - z.re) hone_re.symm
    _ = (1 - z).re := by
      exact (Complex.sub_re 1 z).symm

/-- The reflected affine height is controlled by twice the original affine height. -/
theorem completedRiemannZeta₀_reflected_basicHeight_le
    (z : ℂ) :
    1 + ‖1 - z‖ ≤ 2 * (1 + ‖z‖) := by
  have htriangle : ‖(1 : ℂ) - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ :=
    norm_sub_le (1 : ℂ) z
  have hone_norm : ‖(1 : ℂ)‖ = (1 : ℝ) := by
    exact complex_one_norm_eq_one
  have hbound : ‖(1 : ℂ) - z‖ ≤ 1 + ‖z‖ := by
    exact Eq.subst
      (motive := fun x : ℝ => ‖(1 : ℂ) - z‖ ≤ x + ‖z‖)
      hone_norm
      htriangle
  have hnorm_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
  calc
    1 + ‖1 - z‖ ≤ 1 + (1 + ‖z‖) := by
      exact add_le_add_left hbound 1
    _ = 2 + ‖z‖ := by
      exact real_one_add_one_add_eq_two_add ‖z‖
    _ ≤ 2 + 2 * ‖z‖ := by
      exact real_two_add_le_two_add_two_mul hnorm_nonneg
    _ = 2 * (1 + ‖z‖) := by
      exact real_two_add_two_mul_eq_two_mul_one_add ‖z‖

/-- Right half-plane finite-order growth transports to the left half-plane by the
functional equation for the pole-cleared entire completed-zeta part. -/
theorem completedRiemannZeta₀_leftHalfPlane_finiteOrder_growth_bound_of_rightHalfPlane
    (hright :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          ‖completedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hright with ⟨A, B, m, hApos, hBpos, hbound⟩
  refine ⟨A, B * (2 : ℝ) ^ m, m, hApos, ?_, ?_⟩
  · exact mul_pos hBpos (pow_pos zero_lt_two m)
  intro z hz_left
  let w : ℂ := 1 - z
  let H : ℝ := 1 + ‖z‖
  have hw_right : 0 ≤ w.re :=
    completedRiemannZeta₀_reflected_re_nonnegative_of_leftHalfPlane hz_left
  have hreflect_norm :
      ‖completedRiemannZeta₀ z‖ = ‖completedRiemannZeta₀ w‖ := by
    have hsymm : completedRiemannZeta₀ (1 - z) = completedRiemannZeta₀ z :=
      completedRiemannZeta₀_one_sub z
    exact congrArg (fun x : ℂ => ‖x‖) hsymm.symm
  have hraw :
      ‖completedRiemannZeta₀ w‖ ≤
        A * Real.exp (B * (1 + ‖w‖) ^ m) :=
    hbound w hw_right
  have hheight_nonneg : 0 ≤ 1 + ‖w‖ := by
    exact le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg w))
  have hheight_le :
      1 + ‖w‖ ≤ 2 * H :=
    completedRiemannZeta₀_reflected_basicHeight_le z
  have hpow_le :
      (1 + ‖w‖) ^ m ≤ (2 * H) ^ m :=
    pow_le_pow_left₀ hheight_nonneg hheight_le m
  have hscale :
      B * (1 + ‖w‖) ^ m ≤ B * (2 * H) ^ m :=
    mul_le_mul_of_nonneg_left hpow_le (le_of_lt hBpos)
  have hmul_pow :
      (2 * H) ^ m = (2 : ℝ) ^ m * H ^ m :=
    mul_pow 2 H m
  have htarget :
      B * (2 * H) ^ m = (B * (2 : ℝ) ^ m) * H ^ m := by
    calc
      B * (2 * H) ^ m = B * ((2 : ℝ) ^ m * H ^ m) := by
        exact congrArg (fun x : ℝ => B * x) hmul_pow
      _ = (B * (2 : ℝ) ^ m) * H ^ m := by
        exact (mul_assoc B ((2 : ℝ) ^ m) (H ^ m)).symm
  have hexp_le :
      Real.exp (B * (1 + ‖w‖) ^ m) ≤
        Real.exp ((B * (2 : ℝ) ^ m) * H ^ m) :=
    Real.exp_le_exp.mpr (hscale.trans_eq htarget)
  have hscaled :
      A * Real.exp (B * (1 + ‖w‖) ^ m) ≤
        A * Real.exp ((B * (2 : ℝ) ^ m) * H ^ m) :=
    mul_le_mul_of_nonneg_left hexp_le (le_of_lt hApos)
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ A * Real.exp ((B * (2 : ℝ) ^ m) * H ^ m))
    hreflect_norm.symm
    (hraw.trans hscaled)

/-- Strict right half-plane finite-order growth transports to the left half-plane
by reflection, since `z.re ≤ 0` implies `(1 - z).re > 0`. -/
theorem completedRiemannZeta₀_leftHalfPlane_finiteOrder_growth_bound_of_strictRightHalfPlane
    (hright :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 < z.re →
          ‖completedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        z.re ≤ 0 →
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hright with ⟨A, B, m, hApos, hBpos, hbound⟩
  refine ⟨A, B * (2 : ℝ) ^ m, m, hApos, ?_, ?_⟩
  · exact mul_pos hBpos (pow_pos zero_lt_two m)
  intro z hz_left
  let w : ℂ := 1 - z
  let H : ℝ := 1 + ‖z‖
  have hw_right : 0 < w.re := by
    have hw_eq : w.re = 1 - z.re := by
      calc
        w.re = (1 - z).re := rfl
        _ = (1 : ℂ).re - z.re := Complex.sub_re 1 z
        _ = 1 - z.re := by
          exact congrArg (fun x : ℝ => x - z.re) complex_one_re_eq_one
    have hpos : 0 < 1 - z.re := by
      have hneg_nonneg : 0 ≤ -z.re :=
        neg_nonneg.mpr hz_left
      have hone_le : (1 : ℝ) ≤ 1 - z.re := by
        calc
          (1 : ℝ) = 1 + 0 := (add_zero 1).symm
          _ ≤ 1 + -z.re := add_le_add_left hneg_nonneg 1
          _ = 1 - z.re := (sub_eq_add_neg 1 z.re).symm
      exact lt_of_lt_of_le zero_lt_one hone_le
    calc
      0 < 1 - z.re := hpos
      _ = w.re := hw_eq.symm
  have hreflect_norm :
      ‖completedRiemannZeta₀ z‖ = ‖completedRiemannZeta₀ w‖ := by
    have hsymm : completedRiemannZeta₀ (1 - z) = completedRiemannZeta₀ z :=
      completedRiemannZeta₀_one_sub z
    exact congrArg (fun x : ℂ => ‖x‖) hsymm.symm
  have hraw :
      ‖completedRiemannZeta₀ w‖ ≤
        A * Real.exp (B * (1 + ‖w‖) ^ m) :=
    hbound w hw_right
  have hheight_nonneg : 0 ≤ 1 + ‖w‖ := by
    exact le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg w))
  have hheight_le :
      1 + ‖w‖ ≤ 2 * H :=
    completedRiemannZeta₀_reflected_basicHeight_le z
  have hpow_le :
      (1 + ‖w‖) ^ m ≤ (2 * H) ^ m :=
    pow_le_pow_left₀ hheight_nonneg hheight_le m
  have hscale :
      B * (1 + ‖w‖) ^ m ≤ B * (2 * H) ^ m :=
    mul_le_mul_of_nonneg_left hpow_le (le_of_lt hBpos)
  have hmul_pow :
      (2 * H) ^ m = (2 : ℝ) ^ m * H ^ m :=
    mul_pow 2 H m
  have htarget :
      B * (2 * H) ^ m = (B * (2 : ℝ) ^ m) * H ^ m := by
    calc
      B * (2 * H) ^ m = B * ((2 : ℝ) ^ m * H ^ m) := by
        exact congrArg (fun x : ℝ => B * x) hmul_pow
      _ = (B * (2 : ℝ) ^ m) * H ^ m := by
        exact (mul_assoc B ((2 : ℝ) ^ m) (H ^ m)).symm
  have hexp_le :
      Real.exp (B * (1 + ‖w‖) ^ m) ≤
        Real.exp ((B * (2 : ℝ) ^ m) * H ^ m) :=
    Real.exp_le_exp.mpr (hscale.trans_eq htarget)
  have hscaled :
      A * Real.exp (B * (1 + ‖w‖) ^ m) ≤
        A * Real.exp ((B * (2 : ℝ) ^ m) * H ^ m) :=
    mul_le_mul_of_nonneg_left hexp_le (le_of_lt hApos)
  calc
    ‖completedRiemannZeta₀ z‖ = ‖completedRiemannZeta₀ w‖ := hreflect_norm
    _ ≤ A * Real.exp (B * (1 + ‖w‖) ^ m) := hraw
    _ ≤ A * Real.exp ((B * (2 : ℝ) ^ m) * H ^ m) := hscaled

/-- Half-plane finite-order estimates combine to a global finite-order estimate. -/
theorem completedRiemannZeta₀_global_finiteOrder_growth_bound_of_halfPlanes
    (hright :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 ≤ z.re →
          ‖completedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hleft :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re ≤ 0 →
          ‖completedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hright with ⟨Ar, Br, mr, hAr, hBr, hright_bound⟩
  rcases hleft with ⟨Al, Bl, ml, hAl, hBl, hleft_bound⟩
  refine ⟨Ar + Al, Br + Bl, mr + ml, add_pos hAr hAl, add_pos hBr hBl, ?_⟩
  intro z
  have hAr_nonneg : 0 ≤ Ar := le_of_lt hAr
  have hAl_nonneg : 0 ≤ Al := le_of_lt hAl
  have hBr_nonneg : 0 ≤ Br := le_of_lt hBr
  have hBl_nonneg : 0 ≤ Bl := le_of_lt hBl
  have hA_right_le : Ar ≤ Ar + Al :=
    le_add_of_nonneg_right hAl_nonneg
  have hA_left_le : Al ≤ Ar + Al :=
    le_add_of_nonneg_left hAr_nonneg
  have hB_right_le : Br ≤ Br + Bl :=
    le_add_of_nonneg_right hBl_nonneg
  have hB_left_le : Bl ≤ Br + Bl :=
    le_add_of_nonneg_left hBr_nonneg
  match le_total 0 z.re with
  | Or.inl hright_re =>
      exact le_trans (hright_bound z hright_re)
        (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent
          hAr_nonneg
          hA_right_le
          hB_right_le
          hBr_nonneg
          (Nat.le_add_right mr ml))
  | Or.inr hleft_re =>
      have hdegree : ml ≤ mr + ml := by
        calc
          ml ≤ ml + mr := Nat.le_add_right ml mr
          _ = mr + ml := Nat.add_comm ml mr
      exact le_trans (hleft_bound z hleft_re)
        (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent
          hAl_nonneg
          hA_left_le
          hB_left_le
          hBl_nonneg
          hdegree)

/-- Strict right-half-plane and closed left-half-plane finite-order estimates
combine to a global finite-order estimate. -/
theorem completedRiemannZeta₀_global_finiteOrder_growth_bound_of_strictRight_and_leftHalfPlanes
    (hright :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          0 < z.re →
          ‖completedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m))
    (hleft :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          z.re ≤ 0 →
          ‖completedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        ‖completedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hright with ⟨Ar, Br, mr, hAr, hBr, hright_bound⟩
  rcases hleft with ⟨Al, Bl, ml, hAl, hBl, hleft_bound⟩
  refine ⟨Ar + Al, Br + Bl, mr + ml, add_pos hAr hAl, add_pos hBr hBl, ?_⟩
  intro z
  have hAr_nonneg : 0 ≤ Ar := le_of_lt hAr
  have hAl_nonneg : 0 ≤ Al := le_of_lt hAl
  have hBr_nonneg : 0 ≤ Br := le_of_lt hBr
  have hBl_nonneg : 0 ≤ Bl := le_of_lt hBl
  have hA_right_le : Ar ≤ Ar + Al :=
    le_add_of_nonneg_right hAl_nonneg
  have hA_left_le : Al ≤ Ar + Al :=
    le_add_of_nonneg_left hAr_nonneg
  have hB_right_le : Br ≤ Br + Bl :=
    le_add_of_nonneg_right hBl_nonneg
  have hB_left_le : Bl ≤ Br + Bl :=
    le_add_of_nonneg_left hBr_nonneg
  match lt_or_ge 0 z.re with
  | Or.inl hright_re =>
      exact le_trans (hright_bound z hright_re)
        (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent
          hAr_nonneg
          hA_right_le
          hB_right_le
          hBr_nonneg
          (Nat.le_add_right mr ml))
  | Or.inr hleft_re =>
      have hdegree : ml ≤ mr + ml := by
        calc
          ml ≤ ml + mr := Nat.le_add_right ml mr
          _ = mr + ml := Nat.add_comm ml mr
      exact le_trans (hleft_bound z hleft_re)
        (exponentialFiniteOrder_bound_le_of_le_constants_and_exponent
          hAl_nonneg
          hA_left_le
          hB_left_le
          hBl_nonneg
          hdegree)

/-- The centered affine shift is controlled by the basic centered height. -/
theorem centeredCompletedRiemannZeta₀_shiftedBasicHeight_le
    (z : ℂ) :
    1 + ‖(1 / 2 : ℂ) + z‖ ≤ 2 * (1 + ‖z‖) := by
  have hnorm_half : ‖(1 / 2 : ℂ)‖ ≤ (1 : ℝ) := by
    exact complex_half_norm_le_one
  have htriangle :
      ‖(1 / 2 : ℂ) + z‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖z‖ :=
    norm_add_le (1 / 2 : ℂ) z
  have hbound :
      ‖(1 / 2 : ℂ) + z‖ ≤ 1 + ‖z‖ :=
    le_trans htriangle (add_le_add_right hnorm_half ‖z‖)
  have hheight_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
  calc
    1 + ‖(1 / 2 : ℂ) + z‖ ≤ 1 + (1 + ‖z‖) := by
      exact add_le_add_left hbound 1
    _ = 2 + ‖z‖ := by
      exact real_one_add_one_add_eq_two_add ‖z‖
    _ ≤ 2 + 2 * ‖z‖ := by
      exact real_two_add_le_two_add_two_mul hheight_nonneg
    _ = 2 * (1 + ‖z‖) := by
      exact real_two_add_two_mul_eq_two_mul_one_add ‖z‖

/-- Finite-order growth is preserved by centering the entire completed-zeta part. -/
theorem centeredCompletedRiemannZeta₀_finiteOrder_growth_bound_of_uncentered
    (huncentered :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ,
          ‖completedRiemannZeta₀ z‖ ≤
            A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ,
        ‖centeredCompletedRiemannZeta₀ z‖ ≤
          A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases huncentered with ⟨A, B, m, hApos, hBpos, hbound⟩
  refine ⟨A, B * (2 : ℝ) ^ m, m, hApos, ?_, ?_⟩
  · exact mul_pos hBpos (pow_pos zero_lt_two m)
  intro z
  let H : ℝ := 1 + ‖z‖
  have hH_nonneg : 0 ≤ H := by
    exact le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))
  have hshift_nonneg : 0 ≤ 1 + ‖(1 / 2 : ℂ) + z‖ := by
    exact le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg ((1 / 2 : ℂ) + z)))
  have hshift_le :
      1 + ‖(1 / 2 : ℂ) + z‖ ≤ 2 * H :=
    centeredCompletedRiemannZeta₀_shiftedBasicHeight_le z
  have hpow_le :
      (1 + ‖(1 / 2 : ℂ) + z‖) ^ m ≤ (2 * H) ^ m :=
    pow_le_pow_left₀ hshift_nonneg hshift_le m
  have hcenter :
      ‖centeredCompletedRiemannZeta₀ z‖ =
        ‖completedRiemannZeta₀ ((1 / 2 : ℂ) + z)‖ := by
    rfl
  have hraw :
      ‖completedRiemannZeta₀ ((1 / 2 : ℂ) + z)‖ ≤
        A * Real.exp (B * (1 + ‖(1 / 2 : ℂ) + z‖) ^ m) :=
    hbound ((1 / 2 : ℂ) + z)
  have hscale :
      B * (1 + ‖(1 / 2 : ℂ) + z‖) ^ m ≤
        B * (2 * H) ^ m :=
    mul_le_mul_of_nonneg_left hpow_le (le_of_lt hBpos)
  have hmul_pow :
      (2 * H) ^ m = (2 : ℝ) ^ m * H ^ m :=
    mul_pow 2 H m
  have htarget :
      B * (2 * H) ^ m =
        (B * (2 : ℝ) ^ m) * H ^ m := by
    calc
      B * (2 * H) ^ m = B * ((2 : ℝ) ^ m * H ^ m) := by
        exact congrArg (fun x : ℝ => B * x) hmul_pow
      _ = (B * (2 : ℝ) ^ m) * H ^ m := by
        exact (mul_assoc B ((2 : ℝ) ^ m) (H ^ m)).symm
  have hexp_le :
      Real.exp (B * (1 + ‖(1 / 2 : ℂ) + z‖) ^ m) ≤
        Real.exp ((B * (2 : ℝ) ^ m) * H ^ m) :=
    Real.exp_le_exp.mpr (hscale.trans_eq htarget)
  have hscale_exp :
      A * Real.exp (B * (1 + ‖(1 / 2 : ℂ) + z‖) ^ m) ≤
        A * Real.exp ((B * (2 : ℝ) ^ m) * H ^ m) :=
    mul_le_mul_of_nonneg_left hexp_le (le_of_lt hApos)
  exact Eq.subst
    (motive := fun x : ℝ =>
      x ≤ A * Real.exp ((B * (2 : ℝ) ^ m) * H ^ m))
    hcenter.symm
    (hraw.trans hscale_exp)

/-- Each linear factor in the zero-carrier clearing factor is controlled by
`2 * (1 + ‖z‖)`. -/
theorem centeredCompletedRiemannZetaZeroCarrierClearingFactor_linearNorm_le
    (z : ℂ) :
    ‖((1 / 2 : ℂ) + z)‖ ≤ 2 * (1 + ‖z‖) ∧
      ‖(1 - ((1 / 2 : ℂ) + z))‖ ≤ 2 * (1 + ‖z‖) := by
  have hnorm_half : ‖(1 / 2 : ℂ)‖ ≤ (1 : ℝ) := by
    exact complex_half_norm_le_one
  have hnorm_one_sub_half : ‖(1 - (1 / 2 : ℂ))‖ ≤ (1 : ℝ) := by
    exact complex_one_sub_half_norm_le_one
  have hnorm_z_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
  have hfirst_triangle :
      ‖((1 / 2 : ℂ) + z)‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖z‖ :=
    norm_add_le (1 / 2 : ℂ) z
  have hfirst_sum :
      ‖(1 / 2 : ℂ)‖ + ‖z‖ ≤ 1 + ‖z‖ :=
    add_le_add_right hnorm_half ‖z‖
  have hfirst_height :
      1 + ‖z‖ ≤ 2 * (1 + ‖z‖) := by
    exact le_mul_of_one_le_left
      (le_trans zero_le_one (le_add_of_nonneg_right hnorm_z_nonneg))
      one_le_two
  have hfirst :
      ‖((1 / 2 : ℂ) + z)‖ ≤ 2 * (1 + ‖z‖) :=
    le_trans hfirst_triangle (le_trans hfirst_sum hfirst_height)
  have hsecond_rewrite :
      (1 : ℂ) - ((1 / 2 : ℂ) + z) = (1 - (1 / 2 : ℂ)) + (-z) := by
    exact complex_sub_add_eq_sub_add_neg 1 (1 / 2 : ℂ) z
  have hsecond_triangle :
      ‖(1 - ((1 / 2 : ℂ) + z))‖ ≤ ‖(1 - (1 / 2 : ℂ))‖ + ‖-z‖ := by
    calc
      ‖(1 - ((1 / 2 : ℂ) + z))‖ = ‖(1 - (1 / 2 : ℂ)) + (-z)‖ := by
        exact congrArg norm hsecond_rewrite
      _ ≤ ‖(1 - (1 / 2 : ℂ))‖ + ‖-z‖ := norm_add_le _ _
  have hnorm_neg_z : ‖-z‖ = ‖z‖ := norm_neg z
  have hsecond_sum :
      ‖(1 - (1 / 2 : ℂ))‖ + ‖-z‖ ≤ 1 + ‖z‖ := by
    calc
      ‖(1 - (1 / 2 : ℂ))‖ + ‖-z‖ = ‖(1 - (1 / 2 : ℂ))‖ + ‖z‖ := by
        exact congrArg (fun x : ℝ => ‖(1 - (1 / 2 : ℂ))‖ + x) hnorm_neg_z
      _ ≤ 1 + ‖z‖ := add_le_add_right hnorm_one_sub_half ‖z‖
  have hsecond_height :
      1 + ‖z‖ ≤ 2 * (1 + ‖z‖) := by
    exact le_mul_of_one_le_left
      (le_trans zero_le_one (le_add_of_nonneg_right hnorm_z_nonneg))
      one_le_two
  have hsecond :
      ‖(1 - ((1 / 2 : ℂ) + z))‖ ≤ 2 * (1 + ‖z‖) :=
    le_trans hsecond_triangle (le_trans hsecond_sum hsecond_height)
  exact ⟨hfirst, hsecond⟩

/-- The quadratic clearing factor is controlled by the square of the basic height. -/
theorem centeredCompletedRiemannZetaZeroCarrierClearingFactor_norm_le_quadratic
    (z : ℂ) :
    ‖centeredCompletedRiemannZetaZeroCarrierClearingFactor z‖ ≤
      4 * (1 + ‖z‖) ^ (2 : ℕ) := by
  rcases centeredCompletedRiemannZetaZeroCarrierClearingFactor_linearNorm_le z with
    ⟨hleft, hright⟩
  have hheight_nonneg : 0 ≤ 1 + ‖z‖ := by
    exact le_trans zero_le_one (le_add_of_nonneg_right (norm_nonneg z))
  have htwo_height_nonneg : 0 ≤ 2 * (1 + ‖z‖) := by
    exact mul_nonneg zero_le_two hheight_nonneg
  have hnorm_mul :
      ‖centeredCompletedRiemannZetaZeroCarrierClearingFactor z‖ =
        ‖((1 / 2 : ℂ) + z)‖ * ‖(1 - ((1 / 2 : ℂ) + z))‖ := by
    unfold centeredCompletedRiemannZetaZeroCarrierClearingFactor
    exact norm_mul ((1 / 2 : ℂ) + z) (1 - ((1 / 2 : ℂ) + z))
  have hproduct :
      ‖((1 / 2 : ℂ) + z)‖ * ‖(1 - ((1 / 2 : ℂ) + z))‖ ≤
        (2 * (1 + ‖z‖)) * (2 * (1 + ‖z‖)) :=
    mul_le_mul hleft hright (norm_nonneg _) htwo_height_nonneg
  have htarget :
      (2 * (1 + ‖z‖)) * (2 * (1 + ‖z‖)) =
        4 * (1 + ‖z‖) ^ (2 : ℕ) := by
    exact real_two_mul_square_eq_four_mul_sq (1 + ‖z‖)
  exact hnorm_mul.trans_le (hproduct.trans_eq htarget)

/-- The basic centered height is at least one. -/
theorem centeredCompletedRiemannZeta_basicHeight_ge_one
    (z : ℂ) :
    (1 : ℝ) ≤ 1 + ‖z‖ := by
  exact le_add_of_nonneg_right (norm_nonneg z)

/-- The basic centered height is nonnegative. -/
theorem centeredCompletedRiemannZeta_basicHeight_nonnegative
    (z : ℂ) :
    0 ≤ 1 + ‖z‖ := by
  exact le_trans zero_le_one (centeredCompletedRiemannZeta_basicHeight_ge_one z)

/-- Powers of the basic centered height are at least one. -/
theorem centeredCompletedRiemannZeta_basicHeight_pow_ge_one
    (z : ℂ) (m : ℕ) :
    (1 : ℝ) ≤ (1 + ‖z‖) ^ m := by
  exact one_le_pow₀ (centeredCompletedRiemannZeta_basicHeight_ge_one z)

/-- The quadratic clearing factor has polynomial growth. -/
theorem centeredCompletedRiemannZetaZeroCarrierClearingFactor_growth_bound :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ z : ℂ,
        ‖centeredCompletedRiemannZetaZeroCarrierClearingFactor z‖ ≤
          A * (1 + ‖z‖) ^ m := by
  have hfour_pos : (0 : ℝ) < 4 := by
    exact real_zero_lt_four
  exact ⟨4, 2, hfour_pos, fun z =>
    centeredCompletedRiemannZetaZeroCarrierClearingFactor_norm_le_quadratic z⟩

/-- Products of two polynomial-growth functions have polynomial growth. -/
theorem polynomialGrowth_mul
    {u v : ℂ → ℂ}
    (hu :
      ∃ A : ℝ, ∃ m : ℕ,
        0 < A ∧
        ∀ z : ℂ, ‖u z‖ ≤ A * (1 + ‖z‖) ^ m)
    (hv :
      ∃ A : ℝ, ∃ m : ℕ,
        0 < A ∧
        ∀ z : ℂ, ‖v z‖ ≤ A * (1 + ‖z‖) ^ m) :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ z : ℂ, ‖u z * v z‖ ≤ A * (1 + ‖z‖) ^ m := by
  rcases hu with ⟨A, m, hA_pos, hA_bound⟩
  rcases hv with ⟨B, n, hB_pos, hB_bound⟩
  refine ⟨A * B, m + n, mul_pos hA_pos hB_pos, ?_⟩
  intro z
  let H : ℝ := 1 + ‖z‖
  have hH_nonneg : 0 ≤ H := by
    exact centeredCompletedRiemannZeta_basicHeight_nonnegative z
  have hB_pow_nonneg : 0 ≤ B * H ^ n := by
    exact mul_nonneg (le_of_lt hB_pos) (pow_nonneg hH_nonneg n)
  have hA_pow_nonneg : 0 ≤ A * H ^ m := by
    exact mul_nonneg (le_of_lt hA_pos) (pow_nonneg hH_nonneg m)
  have hmul_bound :
      ‖u z‖ * ‖v z‖ ≤ (A * H ^ m) * (B * H ^ n) :=
    mul_le_mul (hA_bound z) (hB_bound z) (norm_nonneg _) hA_pow_nonneg
  have hnorm :
      ‖u z * v z‖ = ‖u z‖ * ‖v z‖ :=
    norm_mul (u z) (v z)
  have hpow :
      H ^ (m + n) = H ^ m * H ^ n :=
    pow_add H m n
  have halg :
      (A * H ^ m) * (B * H ^ n) = (A * B) * H ^ (m + n) := by
    calc
      (A * H ^ m) * (B * H ^ n) = (A * B) * (H ^ m * H ^ n) := by
        exact real_mul_pair_reassociate A B (H ^ m) (H ^ n)
      _ = (A * B) * H ^ (m + n) := by
        exact congrArg (fun x : ℝ => (A * B) * x) hpow.symm
  exact hnorm.trans_le (hmul_bound.trans_eq halg)

/-- Subtracting the constant `1` from a polynomial-growth function preserves polynomial
growth. -/
theorem polynomialGrowth_sub_one
    {u : ℂ → ℂ}
    (hu :
      ∃ A : ℝ, ∃ m : ℕ,
        0 < A ∧
        ∀ z : ℂ, ‖u z‖ ≤ A * (1 + ‖z‖) ^ m) :
    ∃ A : ℝ, ∃ m : ℕ,
      0 < A ∧
      ∀ z : ℂ, ‖u z - 1‖ ≤ A * (1 + ‖z‖) ^ m := by
  rcases hu with ⟨A, m, hA_pos, hA_bound⟩
  refine ⟨A + 1, m, add_pos hA_pos zero_lt_one, ?_⟩
  intro z
  let H : ℝ := 1 + ‖z‖
  have hH_pow_ge_one : (1 : ℝ) ≤ H ^ m :=
    centeredCompletedRiemannZeta_basicHeight_pow_ge_one z m
  have htriangle :
      ‖u z - 1‖ ≤ ‖u z‖ + ‖(1 : ℂ)‖ :=
    norm_sub_le (u z) (1 : ℂ)
  have hone_norm : ‖(1 : ℂ)‖ = (1 : ℝ) := by
    exact complex_one_norm_eq_one
  have hsum_bound :
      ‖u z‖ + ‖(1 : ℂ)‖ ≤ A * H ^ m + H ^ m := by
    calc
      ‖u z‖ + ‖(1 : ℂ)‖ = ‖u z‖ + 1 := by
        exact congrArg (fun x : ℝ => ‖u z‖ + x) hone_norm
      _ ≤ A * H ^ m + H ^ m := add_le_add (hA_bound z) hH_pow_ge_one
  have halg :
      A * H ^ m + H ^ m = (A + 1) * H ^ m := by
    exact real_mul_add_self_eq_add_one_mul A (H ^ m)
  exact htriangle.trans (hsum_bound.trans_eq halg)

/-- A nonnegative real exponent has exponential at least one. -/
theorem one_le_exp_of_nonnegative_exponent
    {x : ℝ} (hx : 0 ≤ x) :
    (1 : ℝ) ≤ Real.exp x := by
  calc
    (1 : ℝ) ≤ x + 1 := by
      exact le_add_of_nonneg_left hx
    _ ≤ Real.exp x := by
      exact Real.add_one_le_exp x

/-- Polynomial powers of the basic centered height are dominated by an exponential of a
higher basic-height power. -/
theorem centeredCompletedRiemannZeta_basicHeight_pow_le_exp_pow_add
    (z : ℂ) (m n : ℕ) :
    (1 + ‖z‖) ^ m ≤ Real.exp ((1 + ‖z‖) ^ (m + n)) := by
  let H : ℝ := 1 + ‖z‖
  have hH_ge_one : (1 : ℝ) ≤ H :=
    centeredCompletedRiemannZeta_basicHeight_ge_one z
  have hH_nonneg : 0 ≤ H :=
    centeredCompletedRiemannZeta_basicHeight_nonnegative z
  have hpow_le :
      H ^ m ≤ H ^ (m + n) :=
    pow_le_pow_right₀ hH_ge_one (Nat.le_add_right m n)
  have hpow_nonneg : 0 ≤ H ^ (m + n) :=
    pow_nonneg hH_nonneg (m + n)
  have hle_exp :
      H ^ (m + n) ≤ Real.exp (H ^ (m + n)) :=
    le_trans
      (le_add_of_nonneg_right zero_le_one)
      (Real.add_one_le_exp (H ^ (m + n)))
  exact le_trans hpow_le hle_exp

/-- Multiplying an exponential finite-order function by a polynomial-growth function
preserves exponential finite-order growth. -/
theorem exponentialFiniteOrder_mul_polynomialGrowth
    {u v : ℂ → ℂ}
    (hu :
      ∃ A : ℝ, ∃ m : ℕ,
        0 < A ∧
        ∀ z : ℂ, ‖u z‖ ≤ A * (1 + ‖z‖) ^ m)
    (hv :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ, ‖v z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ, ‖u z * v z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hu with ⟨A, m, hA_pos, hA_bound⟩
  rcases hv with ⟨B, C, n, hB_pos, hC_pos, hB_bound⟩
  refine ⟨A * B, C + 1, m + n, mul_pos hA_pos hB_pos, add_pos hC_pos zero_lt_one, ?_⟩
  intro z
  let H : ℝ := 1 + ‖z‖
  have hH_ge_one : (1 : ℝ) ≤ H :=
    centeredCompletedRiemannZeta_basicHeight_ge_one z
  have hH_nonneg : 0 ≤ H :=
    centeredCompletedRiemannZeta_basicHeight_nonnegative z
  have hpoly_exp :
      H ^ m ≤ Real.exp (H ^ (m + n)) :=
    centeredCompletedRiemannZeta_basicHeight_pow_le_exp_pow_add z m n
  have hn_pow_le_sum_pow :
      H ^ n ≤ H ^ (m + n) := by
    have hrewrite : m + n = n + m := by
      exact Nat.add_comm m n
    exact Eq.subst
      (motive := fun k : ℕ => H ^ n ≤ H ^ k)
      hrewrite.symm
      (pow_le_pow_right₀ hH_ge_one (Nat.le_add_right n m))
  have hC_scaled :
      C * H ^ n ≤ C * H ^ (m + n) :=
    mul_le_mul_of_nonneg_left hn_pow_le_sum_pow (le_of_lt hC_pos)
  have hexponent_sum :
      H ^ (m + n) + C * H ^ n ≤ (C + 1) * H ^ (m + n) := by
    have hright :
        H ^ (m + n) + C * H ^ (m + n) =
          (C + 1) * H ^ (m + n) := by
      exact real_self_add_mul_eq_add_one_mul C (H ^ (m + n))
    exact (add_le_add_left hC_scaled (H ^ (m + n))).trans_eq hright
  have hexp_bound :
      Real.exp (H ^ (m + n)) * Real.exp (C * H ^ n) ≤
        Real.exp ((C + 1) * H ^ (m + n)) := by
    have hmul_exp :
        Real.exp (H ^ (m + n)) * Real.exp (C * H ^ n) =
          Real.exp (H ^ (m + n) + C * H ^ n) := by
      exact (Real.exp_add (H ^ (m + n)) (C * H ^ n)).symm
    exact hmul_exp.trans_le (Real.exp_le_exp.mpr hexponent_sum)
  have hright_nonneg :
      0 ≤ B * Real.exp (C * H ^ n) :=
    mul_nonneg (le_of_lt hB_pos) (le_of_lt (Real.exp_pos (C * H ^ n)))
  have hleft_nonneg :
      0 ≤ A * H ^ m :=
    mul_nonneg (le_of_lt hA_pos) (pow_nonneg hH_nonneg m)
  have hnorm_mul :
      ‖u z * v z‖ = ‖u z‖ * ‖v z‖ :=
    norm_mul (u z) (v z)
  have hproduct_bound :
      ‖u z‖ * ‖v z‖ ≤
        (A * H ^ m) * (B * Real.exp (C * H ^ n)) :=
    mul_le_mul (hA_bound z) (hB_bound z) (norm_nonneg _) hleft_nonneg
  have hconstant_power :
      (A * H ^ m) * (B * Real.exp (C * H ^ n)) =
        (A * B) * (H ^ m * Real.exp (C * H ^ n)) := by
    exact real_mul_pair_reassociate A B (H ^ m) (Real.exp (C * H ^ n))
  have hpower_exp :
      H ^ m * Real.exp (C * H ^ n) ≤
        Real.exp (H ^ (m + n)) * Real.exp (C * H ^ n) :=
    mul_le_mul_of_nonneg_right hpoly_exp (le_of_lt (Real.exp_pos (C * H ^ n)))
  have hinner :
      H ^ m * Real.exp (C * H ^ n) ≤
        Real.exp ((C + 1) * H ^ (m + n)) :=
    hpower_exp.trans hexp_bound
  have hscaled :
      (A * B) * (H ^ m * Real.exp (C * H ^ n)) ≤
        (A * B) * Real.exp ((C + 1) * H ^ (m + n)) :=
    mul_le_mul_of_nonneg_left hinner (le_of_lt (mul_pos hA_pos hB_pos))
  exact hnorm_mul.trans_le
    (hproduct_bound.trans
      ((le_of_eq hconstant_power).trans hscaled))

/-- Subtracting the constant `1` from an exponential finite-order function preserves
exponential finite-order growth. -/
theorem exponentialFiniteOrder_sub_one
    {u : ℂ → ℂ}
    (hu :
      ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
        0 < A ∧
        0 < B ∧
        ∀ z : ℂ, ‖u z‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m)) :
    ∃ A : ℝ, ∃ B : ℝ, ∃ m : ℕ,
      0 < A ∧
      0 < B ∧
      ∀ z : ℂ, ‖u z - 1‖ ≤ A * Real.exp (B * (1 + ‖z‖) ^ m) := by
  rcases hu with ⟨A, B, m, hA_pos, hB_pos, hbound⟩
  refine ⟨A + 1, B, m, add_pos hA_pos zero_lt_one, hB_pos, ?_⟩
  intro z
  let H : ℝ := 1 + ‖z‖
  have hH_ge_one : (1 : ℝ) ≤ H :=
    centeredCompletedRiemannZeta_basicHeight_ge_one z
  have hH_nonneg : 0 ≤ H :=
    centeredCompletedRiemannZeta_basicHeight_nonnegative z
  have hexponent_nonneg : 0 ≤ B * H ^ m :=
    mul_nonneg (le_of_lt hB_pos) (pow_nonneg hH_nonneg m)
  have hone_le_exp :
      (1 : ℝ) ≤ Real.exp (B * H ^ m) :=
    one_le_exp_of_nonnegative_exponent hexponent_nonneg
  have htriangle :
      ‖u z - 1‖ ≤ ‖u z‖ + ‖(1 : ℂ)‖ :=
    norm_sub_le (u z) (1 : ℂ)
  have hone_norm : ‖(1 : ℂ)‖ = (1 : ℝ) := by
    exact complex_one_norm_eq_one
  have hsum_bound :
      ‖u z‖ + ‖(1 : ℂ)‖ ≤
        A * Real.exp (B * H ^ m) + Real.exp (B * H ^ m) := by
    calc
      ‖u z‖ + ‖(1 : ℂ)‖ = ‖u z‖ + 1 := by
        exact congrArg (fun x : ℝ => ‖u z‖ + x) hone_norm
      _ ≤ A * Real.exp (B * H ^ m) + Real.exp (B * H ^ m) :=
        add_le_add (hbound z) hone_le_exp
  have halg :
      A * Real.exp (B * H ^ m) + Real.exp (B * H ^ m) =
        (A + 1) * Real.exp (B * H ^ m) := by
    exact real_mul_add_self_eq_add_one_mul A (Real.exp (B * H ^ m))
  exact htriangle.trans (hsum_bound.trans_eq halg)

end

end LFunctions
end Boundary
