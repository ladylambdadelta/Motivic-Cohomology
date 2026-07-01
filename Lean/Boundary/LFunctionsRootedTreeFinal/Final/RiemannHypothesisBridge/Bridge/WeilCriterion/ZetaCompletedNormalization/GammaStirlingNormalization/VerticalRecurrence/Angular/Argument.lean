import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.SectorialLog.FixedVerticalPoint
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# Vertical recurrence: angular defect and radius power

This file owns arctangent bounds, principal-argument formulas for vertical rays,
angular-defect analysis, and radius-power comparable bounds.
-/

namespace Boundary
namespace LFunctions

noncomputable section

local notation "π" => Real.pi

/-- Elementary arctangent majorization used to quantify the angular defect of a
right-half-plane vertical ray. -/
theorem Real.arctan_le_self_of_nonneg
    {t : ℝ}
    (ht : 0 ≤ t) :
    Real.arctan t ≤ t := by
  have harctan_nonneg : 0 ≤ Real.arctan t := by
    have hzero_le :
        Real.arctan 0 ≤ Real.arctan t :=
      Real.arctan_strictMono.monotone ht
    calc
      0 = Real.arctan 0 := Real.arctan_zero.symm
      _ ≤ Real.arctan t := hzero_le
  have harctan_lt_half_pi : Real.arctan t < Real.pi / 2 :=
    Real.arctan_lt_pi_div_two t
  have hle_tan :
      Real.arctan t ≤ Real.tan (Real.arctan t) :=
    Real.le_tan harctan_nonneg harctan_lt_half_pi
  calc
    Real.arctan t ≤ Real.tan (Real.arctan t) := hle_tan
    _ = t := Real.tan_arctan t

/-- Multiplicative form of `Real.arctan_le_self_of_nonneg` after substituting
`t = u / |y|`. -/
theorem Real.norm_mul_arctan_div_norm_le_self_of_nonneg
    {u y : ℝ}
    (hu : 0 ≤ u)
    [hy_norm_zero_dec : Decidable (‖y‖ = 0)] :
    ‖y‖ * Real.arctan (u / ‖y‖) ≤ u := by
  match hy_norm_zero_dec with
  | isTrue hy_zero =>
    have hleft_eq_zero :
        ‖y‖ * Real.arctan (u / ‖y‖) = 0 := by
      exact Eq.trans
        (congrArg (fun r : ℝ => r * Real.arctan (u / ‖y‖)) hy_zero)
        (zero_mul (Real.arctan (u / ‖y‖)))
    calc
      ‖y‖ * Real.arctan (u / ‖y‖) = 0 := hleft_eq_zero
      _ ≤ u := hu
  | isFalse hy_ne_zero =>
    have hy_pos : 0 < ‖y‖ :=
      lt_of_le_of_ne (norm_nonneg y) (Ne.symm hy_ne_zero)
    have hratio_nonneg : 0 ≤ u / ‖y‖ :=
      div_nonneg hu (le_of_lt hy_pos)
    have harctan_le : Real.arctan (u / ‖y‖) ≤ u / ‖y‖ :=
      Real.arctan_le_self_of_nonneg hratio_nonneg
    have hmul :
        ‖y‖ * Real.arctan (u / ‖y‖) ≤ ‖y‖ * (u / ‖y‖) :=
      mul_le_mul_of_nonneg_left harctan_le (le_of_lt hy_pos)
    have hcancel :
        ‖y‖ * (u / ‖y‖) = u :=
      mul_div_cancel₀ u hy_ne_zero
    calc
      ‖y‖ * Real.arctan (u / ‖y‖) ≤ ‖y‖ * (u / ‖y‖) := hmul
      _ = u := hcancel

/-- Principal-argument formula for a right-half-plane ray above the real axis,
written in the reciprocal arctangent form suited to the linear defect estimate. -/
theorem Complex.arg_fixedRealPartVerticalPoint_of_pos_im_eq_pi_div_two_sub_arctan
    {u y : ℝ}
    (hu : 0 ≤ u)
    (hy : 0 < y)
    [hu_zero_dec : Decidable (u = 0)] :
    Complex.arg (Complex.fixedRealPartVerticalPoint u y) =
      Real.pi / 2 - Real.arctan (u / y) := by
  let z : ℂ := Complex.fixedRealPartVerticalPoint u y
  match hu_zero_dec with
  | isTrue hu_zero =>
    have hz_re_zero : z.re = 0 := by
      calc
        z.re = u := Complex.fixedRealPartVerticalPoint_re u y
        _ = 0 := hu_zero
    have hz_im_pos : 0 < z.im := by
      calc
        0 < y := hy
        _ = z.im := (Complex.fixedRealPartVerticalPoint_im u y).symm
    have harg_axis : Complex.arg z = Real.pi / 2 :=
      Complex.arg_eq_pi_div_two_iff.mpr ⟨hz_re_zero, hz_im_pos⟩
    have hratio_zero : u / y = 0 := by
      calc
        u / y = 0 / y := congrArg (fun r : ℝ => r / y) hu_zero
        _ = 0 := zero_div y
    have hatan_zero : Real.arctan (u / y) = 0 :=
      Eq.trans (congrArg Real.arctan hratio_zero) Real.arctan_zero
    calc
      Complex.arg (Complex.fixedRealPartVerticalPoint u y) = Real.pi / 2 :=
        harg_axis
      _ = Real.pi / 2 - 0 := (sub_zero (Real.pi / 2)).symm
      _ = Real.pi / 2 - Real.arctan (u / y) := by
        exact congrArg (fun r : ℝ => Real.pi / 2 - r) hatan_zero.symm
  | isFalse hu_ne_zero =>
    have hu_pos : 0 < u :=
      lt_of_le_of_ne hu (Ne.symm hu_ne_zero)
    have hz_re_pos : 0 < z.re := by
      calc
        0 < u := hu_pos
        _ = z.re := (Complex.fixedRealPartVerticalPoint_re u y).symm
    have hz_im_pos : 0 < z.im := by
      calc
        0 < y := hy
        _ = z.im := (Complex.fixedRealPartVerticalPoint_im u y).symm
    have harg_gt_neg_half : -(Real.pi / 2) < Complex.arg z :=
      Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hz_re_pos)
    have harg_lt_half : Complex.arg z < Real.pi / 2 :=
      Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hz_re_pos)
    have htan_arg : Real.tan (Complex.arg z) = y / u := by
      calc
        Real.tan (Complex.arg z) = z.im / z.re := Complex.tan_arg z
        _ = y / z.re := by
          exact congrArg (fun r : ℝ => r / z.re)
            (Complex.fixedRealPartVerticalPoint_im u y)
        _ = y / u := by
          exact congrArg (fun r : ℝ => y / r)
            (Complex.fixedRealPartVerticalPoint_re u y)
    have harg_eq_atan : Real.arctan (y / u) = Complex.arg z :=
      Real.arctan_eq_of_tan_eq htan_arg
        ⟨harg_gt_neg_half, harg_lt_half⟩
    have hratio_pos : 0 < y / u :=
      div_pos hy hu_pos
    have hinv_eq : (y / u)⁻¹ = u / y :=
      inv_div y u
    have hrecip :
        Real.arctan (u / y) = Real.pi / 2 - Real.arctan (y / u) := by
      calc
        Real.arctan (u / y) =
            Real.arctan ((y / u)⁻¹) :=
          congrArg Real.arctan hinv_eq.symm
        _ = Real.pi / 2 - Real.arctan (y / u) :=
          Real.arctan_inv_of_pos hratio_pos
    have hswap :
        Real.arctan (y / u) = Real.pi / 2 - Real.arctan (u / y) := by
      have hsum :
          Real.arctan (u / y) + Real.arctan (y / u) = Real.pi / 2 := by
        exact (eq_sub_iff_add_eq.mp hrecip)
      have hsum_comm :
          Real.arctan (y / u) + Real.arctan (u / y) = Real.pi / 2 := by
        calc
          Real.arctan (y / u) + Real.arctan (u / y) =
              Real.arctan (u / y) + Real.arctan (y / u) :=
            add_comm (Real.arctan (y / u)) (Real.arctan (u / y))
          _ = Real.pi / 2 := hsum
      exact eq_sub_iff_add_eq.mpr hsum_comm
    calc
      Complex.arg (Complex.fixedRealPartVerticalPoint u y) = Complex.arg z := rfl
      _ = Real.arctan (y / u) := harg_eq_atan.symm
      _ = Real.pi / 2 - Real.arctan (u / y) := hswap

/-- Principal-argument formula for a right-half-plane ray below the real axis,
written in the reciprocal arctangent form suited to the linear defect estimate. -/
theorem Complex.arg_fixedRealPartVerticalPoint_of_neg_im_eq_neg_pi_div_two_add_arctan
    {u y : ℝ}
    (hu : 0 ≤ u)
    (hy : y < 0)
    [hu_zero_dec : Decidable (u = 0)] :
    Complex.arg (Complex.fixedRealPartVerticalPoint u y) =
      -(Real.pi / 2) + Real.arctan (u / ‖y‖) := by
  let z : ℂ := Complex.fixedRealPartVerticalPoint u y
  match hu_zero_dec with
  | isTrue hu_zero =>
    have hz_re_zero : z.re = 0 := by
      calc
        z.re = u := Complex.fixedRealPartVerticalPoint_re u y
        _ = 0 := hu_zero
    have hz_im_neg : z.im < 0 := by
      calc
        z.im = y := Complex.fixedRealPartVerticalPoint_im u y
        _ < 0 := hy
    have harg_axis : Complex.arg z = -(Real.pi / 2) :=
      Complex.arg_eq_neg_pi_div_two_iff.mpr ⟨hz_re_zero, hz_im_neg⟩
    have hratio_zero : u / ‖y‖ = 0 := by
      calc
        u / ‖y‖ = 0 / ‖y‖ := congrArg (fun r : ℝ => r / ‖y‖) hu_zero
        _ = 0 := zero_div ‖y‖
    have hatan_zero : Real.arctan (u / ‖y‖) = 0 :=
      Eq.trans (congrArg Real.arctan hratio_zero) Real.arctan_zero
    calc
      Complex.arg (Complex.fixedRealPartVerticalPoint u y) = -(Real.pi / 2) :=
        harg_axis
      _ = -(Real.pi / 2) + 0 := (add_zero (-(Real.pi / 2))).symm
      _ = -(Real.pi / 2) + Real.arctan (u / ‖y‖) := by
        exact congrArg (fun r : ℝ => -(Real.pi / 2) + r) hatan_zero.symm
  | isFalse hu_ne_zero =>
    have hu_pos : 0 < u :=
      lt_of_le_of_ne hu (Ne.symm hu_ne_zero)
    have hy_norm_pos : 0 < ‖y‖ :=
      norm_pos_iff.mpr (ne_of_lt hy)
    have hz_re_pos : 0 < z.re := by
      calc
        0 < u := hu_pos
        _ = z.re := (Complex.fixedRealPartVerticalPoint_re u y).symm
    have hz_im_neg : z.im < 0 := by
      calc
        z.im = y := Complex.fixedRealPartVerticalPoint_im u y
        _ < 0 := hy
    have harg_gt_neg_half : -(Real.pi / 2) < Complex.arg z :=
      Complex.neg_pi_div_two_lt_arg_iff.mpr (Or.inl hz_re_pos)
    have harg_lt_half : Complex.arg z < Real.pi / 2 :=
      Complex.arg_lt_pi_div_two_iff.mpr (Or.inl hz_re_pos)
    have hy_eq_neg_norm : y = -‖y‖ := by
      have hnorm : ‖y‖ = -y :=
        Real.norm_of_nonpos (le_of_lt hy)
      calc
        y = -(-y) := (neg_neg y).symm
        _ = -‖y‖ := congrArg Neg.neg hnorm.symm
    have htan_arg : Real.tan (Complex.arg z) = y / u := by
      calc
        Real.tan (Complex.arg z) = z.im / z.re := Complex.tan_arg z
        _ = y / z.re := by
          exact congrArg (fun r : ℝ => r / z.re)
            (Complex.fixedRealPartVerticalPoint_im u y)
        _ = y / u := by
          exact congrArg (fun r : ℝ => y / r)
            (Complex.fixedRealPartVerticalPoint_re u y)
    have harg_eq_atan : Real.arctan (y / u) = Complex.arg z :=
      Real.arctan_eq_of_tan_eq htan_arg
        ⟨harg_gt_neg_half, harg_lt_half⟩
    have hatan_neg_norm :
        Real.arctan (y / u) = -Real.arctan (‖y‖ / u) := by
      have hdiv_eq : y / u = -(‖y‖ / u) := by
        calc
          y / u = (-‖y‖) / u := congrArg (fun r : ℝ => r / u) hy_eq_neg_norm
          _ = -(‖y‖ / u) := neg_div u ‖y‖
      exact Eq.trans
        (congrArg Real.arctan hdiv_eq)
        (Real.arctan_neg (‖y‖ / u))
    have hratio_pos : 0 < ‖y‖ / u :=
      div_pos hy_norm_pos hu_pos
    have hinv_eq : (‖y‖ / u)⁻¹ = u / ‖y‖ :=
      inv_div ‖y‖ u
    have hrecip :
        Real.arctan (u / ‖y‖) =
          Real.pi / 2 - Real.arctan (‖y‖ / u) := by
      calc
        Real.arctan (u / ‖y‖) =
            Real.arctan ((‖y‖ / u)⁻¹) :=
          congrArg Real.arctan hinv_eq.symm
        _ = Real.pi / 2 - Real.arctan (‖y‖ / u) :=
          Real.arctan_inv_of_pos hratio_pos
    have hneg_atan_eq :
        -Real.arctan (‖y‖ / u) =
          -(Real.pi / 2) + Real.arctan (u / ‖y‖) := by
      calc
        -Real.arctan (‖y‖ / u) =
            -(Real.pi / 2 - Real.arctan (u / ‖y‖)) := by
          have hswap :
              Real.arctan (‖y‖ / u) =
                Real.pi / 2 - Real.arctan (u / ‖y‖) := by
            have hsum :
                Real.arctan (u / ‖y‖) + Real.arctan (‖y‖ / u) =
                  Real.pi / 2 :=
              eq_sub_iff_add_eq.mp hrecip
            have hsum_comm :
                Real.arctan (‖y‖ / u) + Real.arctan (u / ‖y‖) =
                  Real.pi / 2 := by
              calc
                Real.arctan (‖y‖ / u) + Real.arctan (u / ‖y‖) =
                    Real.arctan (u / ‖y‖) + Real.arctan (‖y‖ / u) :=
                  add_comm (Real.arctan (‖y‖ / u)) (Real.arctan (u / ‖y‖))
                _ = Real.pi / 2 := hsum
            exact eq_sub_iff_add_eq.mpr hsum_comm
          exact congrArg Neg.neg hswap
        _ = -(Real.pi / 2) + Real.arctan (u / ‖y‖) := by
          calc
            -(Real.pi / 2 - Real.arctan (u / ‖y‖)) =
                Real.arctan (u / ‖y‖) - Real.pi / 2 :=
              neg_sub (Real.pi / 2) (Real.arctan (u / ‖y‖))
            _ = Real.arctan (u / ‖y‖) + -(Real.pi / 2) :=
              sub_eq_add_neg (Real.arctan (u / ‖y‖)) (Real.pi / 2)
            _ = -(Real.pi / 2) + Real.arctan (u / ‖y‖) :=
              add_comm (Real.arctan (u / ‖y‖)) (-(Real.pi / 2))
    calc
      Complex.arg (Complex.fixedRealPartVerticalPoint u y) = Complex.arg z := rfl
      _ = Real.arctan (y / u) := harg_eq_atan.symm
      _ = -Real.arctan (‖y‖ / u) := hatan_neg_norm
      _ = -(Real.pi / 2) + Real.arctan (u / ‖y‖) := hneg_atan_eq

/-- Exact arctangent form of the principal-argument defect on the ray `u + i y`
inside the closed right half-plane. -/
theorem Complex.rightHalfPlaneVertical_arg_linear_defect_abs_eq_norm_mul_arctan
    {u y : ℝ}
    (hu : 0 ≤ u) :
    |(Real.pi / 2) * ‖y‖ -
        Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y| =
      ‖y‖ * Real.arctan (u / ‖y‖) := by
  match lt_trichotomy y 0 with
  | Or.inl hy_neg =>
    let n : ℝ := ‖y‖
    let a : ℝ := Real.arctan (u / n)
    let p : ℝ := Real.pi / 2
    have hn_pos : 0 < n :=
      norm_pos_iff.mpr (ne_of_lt hy_neg)
    have hy_eq_neg_n : y = -n := by
      have hnorm : ‖y‖ = -y :=
        Real.norm_of_nonpos (le_of_lt hy_neg)
      have hneg_norm : -n = y := by
        calc
          -n = -‖y‖ := rfl
          _ = -(-y) := congrArg Neg.neg hnorm
          _ = y := neg_neg y
      exact hneg_norm.symm
    have harg :
        Complex.arg (Complex.fixedRealPartVerticalPoint u y) = -p + a :=
      Complex.arg_fixedRealPartVerticalPoint_of_neg_im_eq_neg_pi_div_two_add_arctan
        hu hy_neg
    have ha_nonneg : 0 ≤ a := by
      have hratio_nonneg : 0 ≤ u / n :=
        div_nonneg hu (le_of_lt hn_pos)
      have hzero_le :
          Real.arctan 0 ≤ Real.arctan (u / n) :=
        Real.arctan_strictMono.monotone hratio_nonneg
      calc
        0 = Real.arctan 0 := Real.arctan_zero.symm
        _ ≤ Real.arctan (u / n) := hzero_le
    have hprod_nonneg : 0 ≤ a * n :=
      mul_nonneg ha_nonneg (le_of_lt hn_pos)
    have harg_mul :
        Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y =
          p * n - a * n := by
      calc
        Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y =
            (-p + a) * (-n) := by
          exact congrArg₂
            (fun r s : ℝ => r * s)
            harg
            hy_eq_neg_n
        _ = -((-p + a) * n) := by
          exact mul_neg (-p + a) n
        _ = -((-p) * n + a * n) := by
          exact congrArg Neg.neg (add_mul (-p) a n)
        _ = -((-p) * n) + -(a * n) := by
          exact neg_add ((-p) * n) (a * n)
        _ = p * n + -(a * n) := by
          have hneg_left : -((-p) * n) = p * n := by
            calc
              -((-p) * n) = -(-(p * n)) := by
                exact congrArg Neg.neg (neg_mul p n)
              _ = p * n := neg_neg (p * n)
          exact congrArg (fun r : ℝ => r + -(a * n)) hneg_left
        _ = p * n - a * n := (sub_eq_add_neg (p * n) (a * n)).symm
    have hinside :
        (Real.pi / 2) * ‖y‖ -
            Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y =
          a * n := by
      calc
        (Real.pi / 2) * ‖y‖ -
            Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y =
            p * n - (p * n - a * n) := by
          exact congrArg₂
            (fun r s : ℝ => r - s)
            rfl
            harg_mul
        _ = a * n := sub_sub_self (p * n) (a * n)
    calc
      |(Real.pi / 2) * ‖y‖ -
          Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y| =
          |a * n| := congrArg abs hinside
      _ = a * n := abs_of_nonneg hprod_nonneg
      _ = n * a := mul_comm a n
      _ = ‖y‖ * Real.arctan (u / ‖y‖) := rfl
  | Or.inr (Or.inl hy_zero) =>
    have hnorm_y_zero : ‖y‖ = 0 := by
      calc
        ‖y‖ = ‖(0 : ℝ)‖ := congrArg norm hy_zero
        _ = 0 := norm_zero
    have harg_mul_zero :
        Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y = 0 := by
      calc
        Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y =
            Complex.arg (Complex.fixedRealPartVerticalPoint u y) * 0 :=
          congrArg
            (fun t : ℝ =>
              Complex.arg (Complex.fixedRealPartVerticalPoint u y) * t)
            hy_zero
        _ = 0 := mul_zero (Complex.arg (Complex.fixedRealPartVerticalPoint u y))
    calc
      |(Real.pi / 2) * ‖y‖ -
          Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y| =
          |(Real.pi / 2) * 0 - 0| := by
        exact congrArg₂
          (fun r s : ℝ => |(Real.pi / 2) * r - s|)
          hnorm_y_zero
          harg_mul_zero
      _ = |0 - 0| := by
        have hleft : (Real.pi / 2) * (0 : ℝ) = 0 :=
          mul_zero (Real.pi / 2)
        exact congrArg (fun r : ℝ => |r - 0|) hleft
      _ = 0 := by
        exact Eq.trans (congrArg abs (sub_zero (0 : ℝ))) abs_zero
      _ = ‖y‖ * Real.arctan (u / ‖y‖) := by
        have hright :
            ‖y‖ * Real.arctan (u / ‖y‖) = 0 := by
          calc
            ‖y‖ * Real.arctan (u / ‖y‖) =
                0 * Real.arctan (u / ‖y‖) :=
              congrArg
                (fun r : ℝ => r * Real.arctan (u / ‖y‖))
                hnorm_y_zero
            _ = 0 := zero_mul (Real.arctan (u / ‖y‖))
        exact hright.symm
  | Or.inr (Or.inr hy_pos) =>
    let n : ℝ := ‖y‖
    let a : ℝ := Real.arctan (u / y)
    let p : ℝ := Real.pi / 2
    have hn_eq_y : n = y :=
      Real.norm_of_nonneg (le_of_lt hy_pos)
    have hn_pos : 0 < n :=
      calc
        0 < y := hy_pos
        _ = n := hn_eq_y.symm
    have harg :
        Complex.arg (Complex.fixedRealPartVerticalPoint u y) = p - a :=
      Complex.arg_fixedRealPartVerticalPoint_of_pos_im_eq_pi_div_two_sub_arctan
        hu hy_pos
    have ha_nonneg : 0 ≤ a := by
      have hratio_nonneg : 0 ≤ u / y :=
        div_nonneg hu (le_of_lt hy_pos)
      have hzero_le :
          Real.arctan 0 ≤ Real.arctan (u / y) :=
        Real.arctan_strictMono.monotone hratio_nonneg
      calc
        0 = Real.arctan 0 := Real.arctan_zero.symm
        _ ≤ Real.arctan (u / y) := hzero_le
    have hprod_nonneg : 0 ≤ a * y :=
      mul_nonneg ha_nonneg (le_of_lt hy_pos)
    have harg_mul :
        Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y =
          p * y - a * y := by
      calc
        Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y =
            (p - a) * y := by
          exact congrArg (fun r : ℝ => r * y) harg
        _ = p * y - a * y := sub_mul p a y
    have hinside :
        (Real.pi / 2) * ‖y‖ -
            Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y =
          a * y := by
      calc
        (Real.pi / 2) * ‖y‖ -
            Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y =
            p * y - (p * y - a * y) := by
          have hleft : (Real.pi / 2) * ‖y‖ = p * y := by
            exact congrArg (fun r : ℝ => (Real.pi / 2) * r) hn_eq_y
          exact congrArg₂ (fun r s : ℝ => r - s) hleft harg_mul
        _ = a * y := sub_sub_self (p * y) (a * y)
    calc
      |(Real.pi / 2) * ‖y‖ -
          Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y| =
          |a * y| := congrArg abs hinside
      _ = a * y := abs_of_nonneg hprod_nonneg
      _ = y * a := mul_comm a y
      _ = ‖y‖ * Real.arctan (u / ‖y‖) := by
        have harg_eq : a = Real.arctan (u / ‖y‖) := by
          exact congrArg (fun r : ℝ => Real.arctan (u / r)) hn_eq_y.symm
        exact congrArg₂ (fun r s : ℝ => r * s) hn_eq_y.symm harg_eq

/-- Principal-argument defect on a right-half-plane vertical ray.

For `u ≥ 0`, the angle of `u + i y` differs from `sign(y) · π/2` by at most
`u / |y|`; multiplying by `|y|` gives the displayed scale-free bound.  This is
the canonical `arg` geometry lemma behind the shifted-strip exponential defect. -/
theorem Complex.rightHalfPlaneVertical_arg_linear_defect_abs_le_re
    {u y : ℝ}
    (hu : 0 ≤ u) :
    |(Real.pi / 2) * ‖y‖ -
        Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y| ≤ u := by
  have hdef_eq :
      |(Real.pi / 2) * ‖y‖ -
          Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y| =
        ‖y‖ * Real.arctan (u / ‖y‖) :=
    Complex.rightHalfPlaneVertical_arg_linear_defect_abs_eq_norm_mul_arctan hu
  calc
    |(Real.pi / 2) * ‖y‖ -
        Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y| =
        ‖y‖ * Real.arctan (u / ‖y‖) := hdef_eq
    _ ≤ u := Real.norm_mul_arctan_div_norm_le_self_of_nonneg hu

end
end LFunctions
end Boundary
