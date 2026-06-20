import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.VerticalRecurrence.Sectorial.Owner
import Boundary.LFunctionsRootedTreeFinal.Final.RiemannHypothesisBridge.Bridge.WeilCriterion.ZetaCompletedNormalization.GammaStirlingNormalization.SectorialLog.Owner

/-!
# Vertical recurrence: angular defect and radius power

This file owns arctangent bounds, principal-argument formulas for vertical rays,
angular-defect analysis, and radius-power comparable bounds.
-/

namespace Boundary
namespace LFunctions

noncomputable section

open scoped Filter Topology
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
    (hu : 0 ≤ u) :
    ‖y‖ * Real.arctan (u / ‖y‖) ≤ u := by
  match Decidable.em (‖y‖ = 0) with
  | Or.inl hy_zero =>
    have hleft_eq_zero :
        ‖y‖ * Real.arctan (u / ‖y‖) = 0 := by
      exact Eq.trans
        (congrArg (fun r : ℝ => r * Real.arctan (u / ‖y‖)) hy_zero)
        (zero_mul (Real.arctan (u / ‖y‖)))
    calc
      ‖y‖ * Real.arctan (u / ‖y‖) = 0 := hleft_eq_zero
      _ ≤ u := hu
  | Or.inr hy_ne_zero =>
    have hy_pos : 0 < ‖y‖ :=
      lt_of_le_of_ne (norm_nonneg y) hy_ne_zero.symm
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
    (hy : 0 < y) :
    Complex.arg (Complex.fixedRealPartVerticalPoint u y) =
      Real.pi / 2 - Real.arctan (u / y) := by
  let z : ℂ := Complex.fixedRealPartVerticalPoint u y
  match Decidable.em (u = 0) with
  | Or.inl hu_zero =>
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
  | Or.inr hu_ne_zero =>
    have hu_pos : 0 < u :=
      lt_of_le_of_ne hu hu_ne_zero
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
    (hy : y < 0) :
    Complex.arg (Complex.fixedRealPartVerticalPoint u y) =
      -(Real.pi / 2) + Real.arctan (u / ‖y‖) := by
  let z : ℂ := Complex.fixedRealPartVerticalPoint u y
  match Decidable.em (u = 0) with
  | Or.inl hu_zero =>
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
  | Or.inr hu_ne_zero =>
    have hu_pos : 0 < u :=
      lt_of_le_of_ne hu hu_ne_zero
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
          _ = -(‖y‖ / u) := neg_div ‖y‖ u
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

/-- Additive quantitative argument-defect estimate for shifted right-half-plane
vertical strips.

This is the exact arctangent-defect form behind the exponential comparison:
`-arg(w) y` differs from `-(π/2)|y|` by a bounded amount on every shifted
bounded vertical strip. -/
theorem Complex.shiftedVertical_arg_linear_defect_bounded
    (A B : ℝ) :
    ∃ H : ℝ, ∃ D : ℝ,
      0 < H ∧
      0 ≤ D ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          let w : ℂ :=
            Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y
          -(Complex.arg w * y) ≤ D + (-(Real.pi / 2) * ‖y‖) ∧
          (-(Real.pi / 2) * ‖y‖) - D ≤ -(Complex.arg w * y) := by
  let D : ℝ :=
    max |A + Complex.verticalStripTransportShift A|
      |B + Complex.verticalStripTransportShift A|
  have hD_nonneg : 0 ≤ D :=
    le_trans (abs_nonneg (A + Complex.verticalStripTransportShift A))
      (le_max_left
        |A + Complex.verticalStripTransportShift A|
        |B + Complex.verticalStripTransportShift A|)
  have hpointwise :
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        (1 : ℝ) ≤ ‖y‖ →
          let w : ℂ :=
            Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y
          -(Complex.arg w * y) ≤ D + (-(Real.pi / 2) * ‖y‖) ∧
          (-(Real.pi / 2) * ‖y‖) - D ≤ -(Complex.arg w * y) := by
  intro x y hxA hxB _hy
  let u : ℝ := x + Complex.verticalStripTransportShift A
  let w : ℂ :=
    Complex.fixedRealPartVerticalPoint
      (x + Complex.verticalStripTransportShift A) y
  have hu_nonneg : 0 ≤ u := by
    have hshift : -A ≤ (Complex.verticalStripRightShift A : ℝ) :=
      Complex.neg_lower_le_verticalStripRightShift A
    calc
      0 = A + -A := by
        exact (add_right_neg A).symm
      _ ≤ x + (Complex.verticalStripRightShift A : ℝ) :=
        add_le_add hxA hshift
  have hu_abs_le_D : |u| ≤ D := by
    exact real_abs_le_max_abs_of_mem_Icc
      (add_le_add_right hxA (Complex.verticalStripTransportShift A))
      (add_le_add_right hxB (Complex.verticalStripTransportShift A))
  have hu_le_D : u ≤ D :=
    le_trans (le_abs_self u) hu_abs_le_D
  have hdef_abs :
      |(Real.pi / 2) * ‖y‖ - Complex.arg w * y| ≤ D := by
    have hray :
        |(Real.pi / 2) * ‖y‖ -
            Complex.arg (Complex.fixedRealPartVerticalPoint u y) * y| ≤ u :=
      Complex.rightHalfPlaneVertical_arg_linear_defect_abs_le_re hu_nonneg
    exact le_trans hray hu_le_D
  have hdef_upper :
      (Real.pi / 2) * ‖y‖ - Complex.arg w * y ≤ D :=
    le_trans (le_abs_self ((Real.pi / 2) * ‖y‖ - Complex.arg w * y))
      hdef_abs
  have hdef_lower :
      -D ≤ (Real.pi / 2) * ‖y‖ - Complex.arg w * y := by
    have hneg_abs :
        -|(Real.pi / 2) * ‖y‖ - Complex.arg w * y| ≤
          (Real.pi / 2) * ‖y‖ - Complex.arg w * y :=
      neg_abs_le ((Real.pi / 2) * ‖y‖ - Complex.arg w * y)
    have hneg_bound :
        -D ≤ -|(Real.pi / 2) * ‖y‖ - Complex.arg w * y| :=
      neg_le_neg hdef_abs
    exact le_trans hneg_bound hneg_abs
  constructor
  · have htarget :
        - (Complex.arg w * y) ≤
          D + (-(Real.pi / 2) * ‖y‖) := by
      calc
        -(Complex.arg w * y) =
            ((Real.pi / 2) * ‖y‖ - Complex.arg w * y) +
              (-(Real.pi / 2) * ‖y‖) := by
          exact (add_neg_cancel_left ((Real.pi / 2) * ‖y‖)
            (-(Complex.arg w * y))).symm
        _ ≤ D + (-(Real.pi / 2) * ‖y‖) :=
          add_le_add_right hdef_upper (-(Real.pi / 2) * ‖y‖)
    exact htarget
  · have htarget :
        (-(Real.pi / 2) * ‖y‖) - D ≤
          -(Complex.arg w * y) := by
      calc
        (-(Real.pi / 2) * ‖y‖) - D =
            -D + (-(Real.pi / 2) * ‖y‖) := by
          calc
            (-(Real.pi / 2) * ‖y‖) - D =
                (-(Real.pi / 2) * ‖y‖) + -D :=
              sub_eq_add_neg (-(Real.pi / 2) * ‖y‖) D
            _ = -D + (-(Real.pi / 2) * ‖y‖) :=
              add_comm (-(Real.pi / 2) * ‖y‖) (-D)
        _ ≤ ((Real.pi / 2) * ‖y‖ - Complex.arg w * y) +
              (-(Real.pi / 2) * ‖y‖) :=
          add_le_add_right hdef_lower (-(Real.pi / 2) * ‖y‖)
        _ = -(Complex.arg w * y) := by
          exact add_neg_cancel_left ((Real.pi / 2) * ‖y‖)
            (-(Complex.arg w * y))
    exact htarget
  exact ⟨1, D, zero_lt_one, hD_nonneg, hpointwise⟩

/-- Quantitative arctangent-defect comparison for shifted right-half-plane
vertical strips.

For `w = x + N + i y` with `x` in a fixed bounded strip and `N` the deterministic
right-half-plane shift, the classical estimate
`|arg w - sign(y) · π/2| = O(1 / |y|)` gives a bounded multiplicative loss in
`exp (-arg(w) y)`.  This is the precise geometric input needed by the normalized
Stirling denominator comparison. -/
theorem Complex.shiftedVertical_arg_exponential_defect_comparable_quantitative
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          let w : ℂ :=
            Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y
          Real.exp (-(Complex.arg w * y)) ≤
            C * Real.exp (-(Real.pi / 2) * ‖y‖) ∧
          c * Real.exp (-(Real.pi / 2) * ‖y‖) ≤
            Real.exp (-(Complex.arg w * y)) := by
  match Complex.shiftedVertical_arg_linear_defect_bounded A B with
  | ⟨H, D, hH_pos, hD_nonneg, hdefect⟩ =>
  have hC_pos : 0 < Real.exp D :=
    Real.exp_pos D
  have hc_pos : 0 < Real.exp (-D) :=
    Real.exp_pos (-D)
  have hpointwise :
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          let w : ℂ :=
            Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y
          Real.exp (-(Complex.arg w * y)) ≤
            Real.exp D * Real.exp (-(Real.pi / 2) * ‖y‖) ∧
          Real.exp (-D) * Real.exp (-(Real.pi / 2) * ‖y‖) ≤
            Real.exp (-(Complex.arg w * y)) := by
  intro x y hxA hxB hy
  let w : ℂ :=
    Complex.fixedRealPartVerticalPoint
      (x + Complex.verticalStripTransportShift A) y
  let b : ℝ := -(Real.pi / 2) * ‖y‖
  have hdef := hdefect x y hxA hxB hy
  constructor
  · have hexp_le :
        Real.exp (-(Complex.arg w * y)) ≤ Real.exp (D + b) :=
      Real.exp_le_exp.mpr hdef.1
    have hsplit :
        Real.exp (D + b) =
          Real.exp D * Real.exp b :=
      Real.exp_add D b
    exact le_trans hexp_le
      (le_of_eq
        (Eq.trans hsplit
          (by
            rfl)))
  · have hlower_exp :
        Real.exp (b - D) ≤ Real.exp (-(Complex.arg w * y)) :=
      Real.exp_le_exp.mpr hdef.2
    have hsplit :
        Real.exp (b - D) =
          Real.exp (-D) * Real.exp b := by
      calc
        Real.exp (b - D) =
            Real.exp (b + -D) := by
          exact congrArg Real.exp (sub_eq_add_neg b D)
        _ = Real.exp b * Real.exp (-D) :=
          Real.exp_add b (-D)
        _ = Real.exp (-D) * Real.exp b :=
          mul_comm (Real.exp b) (Real.exp (-D))
    exact le_trans (le_of_eq hsplit.symm) hlower_exp
  exact ⟨H, Real.exp D, Real.exp (-D), hH_pos, hC_pos, hc_pos, hpointwise⟩

/-- Quantitative vertical argument-defect estimate for shifted right-half-plane
strip points.

This is the real geometric core of the denominator comparison.  In a fixed
right-half-plane vertical strip, the principal argument approaches
`sign(y) * π/2`, and the defect contributes only a bounded exponential factor
to `exp (-arg(w) y)`. -/
theorem Complex.shiftedVertical_arg_exponential_defect_comparable
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          let w : ℂ :=
            Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y
          Real.exp (-(Complex.arg w * y)) ≤
            C * Real.exp (-(Real.pi / 2) * ‖y‖) ∧
          c * Real.exp (-(Real.pi / 2) * ‖y‖) ≤
            Real.exp (-(Complex.arg w * y)) := by
  exact
    Complex.shiftedVertical_arg_exponential_defect_comparable_quantitative
      A B

/-- On a deterministically shifted vertical strip, the radius is comparable to
`1 + |y|`.

This is the base geometric input for the radius-power comparison; the remaining
power step only has to transport this through `rpow` with bounded exponent. -/
theorem Complex.shiftedVertical_radius_base_comparable
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          let w : ℂ :=
            Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y
          ‖w‖ ≤ C * (1 + ‖y‖) ∧
          c * (1 + ‖y‖) ≤ ‖w‖ := by
  match
      Complex.gammaRecurrenceProduct_factor_upper_on_verticalStrip
        (A + Complex.verticalStripTransportShift A)
        (B + Complex.verticalStripTransportShift A)
        1 with
  | ⟨C, hC_pos, hupper⟩ =>
  have hc_pos : 0 < (1 / 2 : ℝ) :=
    one_div_pos.mpr two_pos
  exact ⟨1, C, 1 / 2, zero_lt_one, hC_pos, hc_pos, by
  intro x y hxA hxB hy
  let w : ℂ :=
    Complex.fixedRealPartVerticalPoint
      (x + Complex.verticalStripTransportShift A) y
  have hxA_shift :
      A + Complex.verticalStripTransportShift A ≤
        x + Complex.verticalStripTransportShift A :=
    add_le_add_right hxA (Complex.verticalStripTransportShift A)
  have hxB_shift :
      x + Complex.verticalStripTransportShift A ≤
        B + Complex.verticalStripTransportShift A :=
    add_le_add_right hxB (Complex.verticalStripTransportShift A)
  have hzero_lt_one_nat : (0 : ℕ) < 1 :=
    Nat.zero_lt_one
  have hupper_w :
      ‖Complex.fixedRealPartVerticalPoint
          (x + Complex.verticalStripTransportShift A) y + (0 : ℂ)‖ ≤
        C * (1 + ‖y‖) :=
    hupper (x + Complex.verticalStripTransportShift A) y
      hxA_shift hxB_shift 0 hzero_lt_one_nat
  have hzero_add :
      Complex.fixedRealPartVerticalPoint
          (x + Complex.verticalStripTransportShift A) y + (0 : ℂ) =
        w :=
    add_zero w
  have hupper_final :
      ‖w‖ ≤ C * (1 + ‖y‖) :=
    calc
      ‖w‖ =
          ‖Complex.fixedRealPartVerticalPoint
            (x + Complex.verticalStripTransportShift A) y + (0 : ℂ)‖ :=
        congrArg norm hzero_add.symm
      _ ≤ C * (1 + ‖y‖) := hupper_w
  have hlower_final :
      (1 / 2 : ℝ) * (1 + ‖y‖) ≤ ‖w‖ := by
    have hlower_raw :
        (1 / 2 : ℝ) * (1 + ‖y‖) ≤
          ‖Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y + (0 : ℂ)‖ :=
      Complex.gammaRecurrenceProduct_factor_largeHeight_lower 0 hy
    calc
      (1 / 2 : ℝ) * (1 + ‖y‖) ≤
          ‖Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y + (0 : ℂ)‖ :=
        hlower_raw
      _ = ‖w‖ := congrArg norm hzero_add
  exact ⟨hupper_final, hlower_final⟩⟩

/-- Real bounded-exponent transport for radius powers.

If `R` is uniformly comparable to the height scale `Y`, and the exponent `e`
stays in a fixed bounded interval, then `R^e` is uniformly comparable to
`Y^e`.  This is the purely real step needed after the shifted-strip radius
comparison has removed all complex geometry. -/
theorem real_rpow_comparable_of_base_comparable_and_bounded_exponent
    (C c L U : ℝ)
    (hC_pos : 0 < C)
    (hc_pos : 0 < c) :
    ∃ K : ℝ, ∃ k : ℝ,
      0 < K ∧
      0 < k ∧
      ∀ R Y e : ℝ,
        0 < Y →
        c * Y ≤ R →
        R ≤ C * Y →
        L ≤ e →
        e ≤ U →
          R ^ e ≤ K * Y ^ e ∧
          k * Y ^ e ≤ R ^ e := by
  let E : ℝ := max |L| |U|
  let M : ℝ := |Real.log c| + |Real.log C|
  let K : ℝ := Real.exp (E * M)
  let k : ℝ := Real.exp (-(E * M))
  have hE_nonneg : 0 ≤ E :=
    le_trans (abs_nonneg L) (le_max_left |L| |U|)
  have hM_nonneg : 0 ≤ M :=
    add_nonneg (abs_nonneg (Real.log c)) (abs_nonneg (Real.log C))
  have hEM_nonneg : 0 ≤ E * M :=
    mul_nonneg hE_nonneg hM_nonneg
  have hK_pos : 0 < K :=
    Real.exp_pos (E * M)
  have hk_pos : 0 < k :=
    Real.exp_pos (-(E * M))
  exact ⟨K, k, hK_pos, hk_pos, by
  intro R Y e hY_pos hlow hhigh hL hU
  let q : ℝ := R / Y
  have hY_nonneg : 0 ≤ Y :=
    le_of_lt hY_pos
  have hY_ne : Y ≠ 0 :=
    ne_of_gt hY_pos
  have hq_lower : c ≤ q := by
    calc
      c = (c * Y) / Y := by
        exact (mul_div_cancel_right₀ c hY_ne).symm
      _ ≤ R / Y :=
        div_le_div_of_nonneg_right hlow hY_nonneg
  have hq_upper : q ≤ C := by
    calc
      q = R / Y := rfl
      _ ≤ (C * Y) / Y :=
        div_le_div_of_nonneg_right hhigh hY_nonneg
      _ = C := by
        exact mul_div_cancel_right₀ C hY_ne
  have hq_pos : 0 < q :=
    lt_of_lt_of_le hc_pos hq_lower
  have hq_nonneg : 0 ≤ q :=
    le_of_lt hq_pos
  have hR_eq : R = q * Y := by
    calc
      R = (R / Y) * Y := by
        exact (div_mul_cancel₀ R hY_ne).symm
      _ = q * Y := rfl
  have he_abs : |e| ≤ E :=
    real_abs_le_max_abs_of_mem_Icc hL hU
  have hlog_abs : |Real.log q| ≤ M := by
    match Decidable.em (0 ≤ Real.log q) with
    | Or.inl hlog_nonneg =>
      have hlog_le_C : Real.log q ≤ Real.log C :=
        Real.log_le_log hq_pos hq_upper
      have hlog_abs_eq : |Real.log q| = Real.log q :=
        abs_of_nonneg hlog_nonneg
      have hC_le_abs : Real.log C ≤ |Real.log C| :=
        le_abs_self (Real.log C)
      calc
        |Real.log q| = Real.log q := hlog_abs_eq
        _ ≤ Real.log C := hlog_le_C
        _ ≤ |Real.log C| := hC_le_abs
        _ ≤ |Real.log c| + |Real.log C| :=
          le_add_of_nonneg_left (abs_nonneg (Real.log c))
    | Or.inr hlog_not_nonneg =>
      have hlog_nonpos : Real.log q ≤ 0 :=
        le_of_not_ge hlog_not_nonneg
      have hlog_c_le : Real.log c ≤ Real.log q :=
        Real.log_le_log hc_pos hq_lower
      have hneg_le : -Real.log q ≤ -Real.log c :=
        neg_le_neg hlog_c_le
      have hneg_c_le_abs : -Real.log c ≤ |Real.log c| :=
        neg_le_abs (Real.log c)
      have hlog_abs_eq : |Real.log q| = -Real.log q :=
        abs_of_nonpos hlog_nonpos
      calc
        |Real.log q| = -Real.log q := hlog_abs_eq
        _ ≤ -Real.log c := hneg_le
        _ ≤ |Real.log c| := hneg_c_le_abs
        _ ≤ |Real.log c| + |Real.log C| :=
          le_add_of_nonneg_right (abs_nonneg (Real.log C))
  have hmul_abs :
      |e * Real.log q| ≤ E * M := by
    calc
      |e * Real.log q| = |e| * |Real.log q| :=
        abs_mul e (Real.log q)
      _ ≤ E * M :=
        mul_le_mul he_abs hlog_abs hM_nonneg (abs_nonneg e)
  have hupper_exp_arg : e * Real.log q ≤ E * M :=
    le_trans (le_abs_self (e * Real.log q)) hmul_abs
  have hlower_exp_arg : -(E * M) ≤ e * Real.log q := by
    have hneg_abs : -|e * Real.log q| ≤ e * Real.log q :=
      neg_abs_le (e * Real.log q)
    have hneg_bound : -(E * M) ≤ -|e * Real.log q| :=
      neg_le_neg hmul_abs
    exact le_trans hneg_bound hneg_abs
  have hq_pow_upper : q ^ e ≤ K := by
    have hq_pow_eq : q ^ e = Real.exp (Real.log q * e) :=
      Real.rpow_def_of_pos hq_pos e
    have hcomm : Real.log q * e = e * Real.log q :=
      mul_comm (Real.log q) e
    calc
      q ^ e = Real.exp (Real.log q * e) := hq_pow_eq
      _ = Real.exp (e * Real.log q) := congrArg Real.exp hcomm
      _ ≤ K := Real.exp_le_exp.mpr hupper_exp_arg
  have hq_pow_lower : k ≤ q ^ e := by
    have hq_pow_eq : q ^ e = Real.exp (Real.log q * e) :=
      Real.rpow_def_of_pos hq_pos e
    have hcomm : Real.log q * e = e * Real.log q :=
      mul_comm (Real.log q) e
    calc
      k ≤ Real.exp (e * Real.log q) := Real.exp_le_exp.mpr hlower_exp_arg
      _ = Real.exp (Real.log q * e) := (congrArg Real.exp hcomm).symm
      _ = q ^ e := hq_pow_eq.symm
  have hY_pow_nonneg : 0 ≤ Y ^ e :=
    Real.rpow_nonneg hY_nonneg e
  have hR_pow_eq : R ^ e = q ^ e * Y ^ e := by
    calc
      R ^ e = (q * Y) ^ e := by
        exact congrArg (fun t : ℝ => t ^ e) hR_eq
      _ = q ^ e * Y ^ e :=
        Real.mul_rpow hq_nonneg hY_nonneg
  constructor
  · calc
      R ^ e = q ^ e * Y ^ e := hR_pow_eq
      _ ≤ K * Y ^ e :=
        mul_le_mul_of_nonneg_right hq_pow_upper hY_pow_nonneg
  · calc
      k * Y ^ e ≤ q ^ e * Y ^ e :=
        mul_le_mul_of_nonneg_right hq_pow_lower hY_pow_nonneg
      _ = R ^ e := hR_pow_eq.symm⟩

/-- Bounded-exponent radius-power comparison for shifted vertical strips.

On a bounded shifted strip, `‖x + N + i y‖` is comparable to `1 + |y|`, while
the exponent `x + N - 1/2` ranges over a fixed compact real interval.  The
standard logarithmic/rpow comparison therefore gives uniform two-sided
constants for the radius power. -/
theorem Complex.shiftedVertical_radiusPower_comparable_boundedExponent
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          let w : ℂ :=
            Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y
          ‖w‖ ^ (w.re - 1 / 2) ≤
            C * (1 + ‖y‖) ^ (x + Complex.verticalStripTransportShift A - 1 / 2) ∧
          c * (1 + ‖y‖) ^ (x + Complex.verticalStripTransportShift A - 1 / 2) ≤
            ‖w‖ ^ (w.re - 1 / 2) := by
  match Complex.shiftedVertical_radius_base_comparable A B with
  | ⟨Hbase, Cbase, cbase, hHbase_pos, hCbase_pos, hcbase_pos, hbase⟩ =>
  let L : ℝ := A + Complex.verticalStripTransportShift A - 1 / 2
  let U : ℝ := B + Complex.verticalStripTransportShift A - 1 / 2
  match
      real_rpow_comparable_of_base_comparable_and_bounded_exponent
        Cbase cbase L U hCbase_pos hcbase_pos with
  | ⟨K, k, hK_pos, hk_pos, hrpow⟩ =>
  exact ⟨Hbase, K, k, hHbase_pos, hK_pos, hk_pos, by
  intro x y hxA hxB hy
  let w : ℂ :=
    Complex.fixedRealPartVerticalPoint
      (x + Complex.verticalStripTransportShift A) y
  let Y : ℝ := 1 + ‖y‖
  let e : ℝ := x + Complex.verticalStripTransportShift A - 1 / 2
  have hbase_xy := hbase x y hxA hxB hy
  have hY_pos : 0 < Y :=
    add_pos_of_pos_of_nonneg zero_lt_one (norm_nonneg y)
  have hw_re :
      w.re = x + Complex.verticalStripTransportShift A :=
    Complex.fixedRealPartVerticalPoint_re
      (x + Complex.verticalStripTransportShift A) y
  have heq :
      w.re - 1 / 2 = e := by
    exact congrArg (fun t : ℝ => t - 1 / 2) hw_re
  have hL : L ≤ e :=
    add_le_add_right
      (add_le_add_right hxA (Complex.verticalStripTransportShift A))
      (-(1 / 2 : ℝ))
  have hU : e ≤ U :=
    add_le_add_right
      (add_le_add_right hxB (Complex.verticalStripTransportShift A))
      (-(1 / 2 : ℝ))
  have hr :
      ‖w‖ ^ e ≤ K * Y ^ e ∧
        k * Y ^ e ≤ ‖w‖ ^ e :=
    hrpow ‖w‖ Y e hY_pos hbase_xy.2 hbase_xy.1 hL hU
  exact
    ⟨by
      calc
        ‖w‖ ^ (w.re - 1 / 2) = ‖w‖ ^ e :=
          congrArg (fun t : ℝ => ‖w‖ ^ t) heq
        _ ≤ K * Y ^ e := hr.1,
      by
      calc
        k * Y ^ e ≤ ‖w‖ ^ e := hr.2
        _ = ‖w‖ ^ (w.re - 1 / 2) :=
          (congrArg (fun t : ℝ => ‖w‖ ^ t) heq).symm⟩⟩

/-- In a fixed shifted vertical strip, the radial polynomial factor in the
principal-power denominator is comparable to the standard height polynomial. -/
theorem Complex.shiftedVertical_radiusPower_comparable
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          let w : ℂ :=
            Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y
          ‖w‖ ^ (w.re - 1 / 2) ≤
            C * (1 + ‖y‖) ^ (x + Complex.verticalStripTransportShift A - 1 / 2) ∧
          c * (1 + ‖y‖) ^ (x + Complex.verticalStripTransportShift A - 1 / 2) ≤
            ‖w‖ ^ (w.re - 1 / 2) := by
  exact
    Complex.shiftedVertical_radiusPower_comparable_boundedExponent
      A B

/-- On a fixed shifted vertical strip, the real-part exponential factor
`exp (-Re w)` is bounded above and below by positive constants. -/
theorem Complex.shiftedVertical_realPartExp_bounded
    (A B : ℝ) :
    ∃ C : ℝ, ∃ c : ℝ,
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
          let w : ℂ :=
            Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y
          Real.exp (-w.re) ≤ C ∧
          c ≤ Real.exp (-w.re) := by
  let N : ℝ := Complex.verticalStripTransportShift A
  let C : ℝ := max (Real.exp (-(A + N))) (Real.exp (-(B + N)))
  let c : ℝ := min (Real.exp (-(A + N))) (Real.exp (-(B + N)))
  have hEA_pos : 0 < Real.exp (-(A + N)) :=
    Real.exp_pos (-(A + N))
  have hEB_pos : 0 < Real.exp (-(B + N)) :=
    Real.exp_pos (-(B + N))
  have hC_pos : 0 < C :=
    lt_of_lt_of_le hEA_pos (le_max_left (Real.exp (-(A + N))) (Real.exp (-(B + N))))
  have hc_pos : 0 < c :=
    lt_min hEA_pos hEB_pos
  exact ⟨C, c, hC_pos, hc_pos, by
  intro x y hxA hxB
  let w : ℂ :=
    Complex.fixedRealPartVerticalPoint
      (x + Complex.verticalStripTransportShift A) y
  have hw_re :
      w.re = x + N := by
    exact Complex.fixedRealPartVerticalPoint_re
      (x + Complex.verticalStripTransportShift A) y
  have hleft : A + N ≤ x + N :=
    add_le_add_right hxA N
  have hright : x + N ≤ B + N :=
    add_le_add_right hxB N
  have hneg_upper : -(B + N) ≤ -(x + N) :=
    neg_le_neg hright
  have hneg_lower : -(x + N) ≤ -(A + N) :=
    neg_le_neg hleft
  have hexp_upper_A :
      Real.exp (-(x + N)) ≤ Real.exp (-(A + N)) :=
    Real.exp_le_exp.mpr hneg_lower
  have hexp_upper :
      Real.exp (-(x + N)) ≤ C :=
    le_trans hexp_upper_A
      (le_max_left (Real.exp (-(A + N))) (Real.exp (-(B + N))))
  have hexp_lower_B :
      Real.exp (-(B + N)) ≤ Real.exp (-(x + N)) :=
    Real.exp_le_exp.mpr hneg_upper
  have hexp_lower :
      c ≤ Real.exp (-(x + N)) :=
    le_trans
      (min_le_right (Real.exp (-(A + N))) (Real.exp (-(B + N))))
      hexp_lower_B
  exact
    ⟨by
      calc
        Real.exp (-w.re) = Real.exp (-(x + N)) :=
          congrArg (fun t : ℝ => Real.exp (-t)) hw_re
        _ ≤ C := hexp_upper,
      by
      calc
        c ≤ Real.exp (-(x + N)) := hexp_lower
        _ = Real.exp (-w.re) :=
          (congrArg (fun t : ℝ => Real.exp (-t)) hw_re).symm⟩⟩

/-- Real algebra behind the reciprocal denominator after the exponential and
principal-power norm formulas have been substituted. -/
theorem real_stirlingDenominator_reciprocal_shape
    (R x θ y : ℝ)
    (hR_pos : 0 < R) :
    1 / (Real.exp x *
        (R ^ (1 / 2 - x) / Real.exp (θ * (-y)))) =
      Real.exp (-(θ * y)) * R ^ (x - 1 / 2) * Real.exp (-x) := by
  let E : ℝ := Real.exp x
  let Q : ℝ := R ^ (1 / 2 - x)
  let F : ℝ := Real.exp (θ * (-y))
  have hQ_pos : 0 < Q :=
    Real.rpow_pos_of_pos hR_pos (1 / 2 - x)
  have hF_pos : 0 < F :=
    Real.exp_pos (θ * (-y))
  have hE_pos : 0 < E :=
    Real.exp_pos x
  have htheta : θ * (-y) = -(θ * y) := by
    exact mul_neg θ y
  have hF_eq : F = Real.exp (-(θ * y)) := by
    exact congrArg Real.exp htheta
  have hQ_inv :
      Q⁻¹ = R ^ (x - 1 / 2) := by
    have hexp : x - 1 / 2 = -(1 / 2 - x) := by
      calc
        x - 1 / 2 = x + -(1 / 2) := sub_eq_add_neg x (1 / 2)
        _ = -(1 / 2) + x := add_comm x (-(1 / 2))
        _ = -(1 / 2) + -(-x) := by
          exact congrArg (fun t : ℝ => -(1 / 2) + t) (neg_neg x).symm
        _ = -(1 / 2 + -x) := by
          exact (neg_add (1 / 2) (-x)).symm
        _ = -(1 / 2 - x) := by
          exact congrArg Neg.neg (sub_eq_add_neg (1 / 2) x).symm
    have hneg :
        R ^ (-(1 / 2 - x)) = Q⁻¹ :=
      Real.rpow_neg (le_of_lt hR_pos) (1 / 2 - x)
    exact Eq.trans hneg.symm (congrArg (fun t : ℝ => R ^ t) hexp).symm
  have hE_inv : E⁻¹ = Real.exp (-x) := by
    exact (Real.exp_neg x).symm
  calc
    1 / (Real.exp x * (R ^ (1 / 2 - x) / Real.exp (θ * (-y)))) =
        1 / (E * (Q / F)) := rfl
    _ = (E * (Q / F))⁻¹ := by
      exact one_div (E * (Q / F))
    _ = (Q / F)⁻¹ * E⁻¹ := by
      exact mul_inv_rev E (Q / F)
    _ = (F * Q⁻¹) * E⁻¹ := by
      have hdiv_inv : (Q / F)⁻¹ = F * Q⁻¹ := by
        calc
          (Q / F)⁻¹ = F / Q := inv_div Q F
          _ = F * Q⁻¹ := div_eq_mul_inv F Q
      exact congrArg (fun t : ℝ => t * E⁻¹) hdiv_inv
    _ = F * Q⁻¹ * E⁻¹ := by
      rfl
    _ = Real.exp (-(θ * y)) * R ^ (x - 1 / 2) * Real.exp (-x) := by
      exact congrArg₂ HMul.hMul
        (congrArg₂ HMul.hMul hF_eq hQ_inv)
        hE_inv

/-- Exact reciprocal shape of the normalized-Stirling denominator on a fixed
vertical point, after expanding `‖exp w‖` and the principal-branch power norm. -/
theorem Complex.stirlingDenominator_reciprocal_shape_fixedVertical
    {w : ℂ}
    {y : ℝ}
    (hw_ne : w ≠ 0)
    (hw_im : w.im = y) :
    1 / (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) =
      Real.exp (-(Complex.arg w * y)) *
        ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) := by
  have hR_pos : 0 < ‖w‖ :=
    norm_pos_iff.mpr hw_ne
  have hexp_norm :
      ‖Complex.exp w‖ = Real.exp w.re :=
    Complex.norm_exp_eq_exp_re w
  have hre_exp :
      ((1 / 2 : ℂ) - w).re = 1 / 2 - w.re :=
    Complex.half_minus_self_re w
  have him_exp :
      ((1 / 2 : ℂ) - w).im = -y := by
    exact Eq.trans (Complex.half_minus_self_im w) (congrArg Neg.neg hw_im)
  have hcpow_norm :
      ‖w ^ ((1 / 2 : ℂ) - w)‖ =
        ‖w‖ ^ (1 / 2 - w.re) /
          Real.exp (Complex.arg w * (-y)) := by
    have hraw :
        ‖w ^ ((1 / 2 : ℂ) - w)‖ =
          ‖w‖ ^ (((1 / 2 : ℂ) - w).re) /
            Real.exp (Complex.arg w * (((1 / 2 : ℂ) - w).im)) :=
      Complex.norm_cpow_eq_norm_rpow_div_exp_arg_mul_im_of_ne_zero hw_ne
    exact Eq.trans hraw
      (congrArg₂ HDiv.hDiv
        (congrArg (fun t : ℝ => ‖w‖ ^ t) hre_exp)
        (congrArg (fun t : ℝ => Real.exp (Complex.arg w * t)) him_exp))
  calc
    1 / (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) =
        1 / (Real.exp w.re *
          (‖w‖ ^ (1 / 2 - w.re) /
            Real.exp (Complex.arg w * (-y)))) := by
      exact congrArg
        (fun t : ℝ => 1 / t)
        (congrArg₂ HMul.hMul hexp_norm hcpow_norm)
    _ =
        Real.exp (-(Complex.arg w * y)) *
          ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) :=
      real_stirlingDenominator_reciprocal_shape
        ‖w‖ w.re (Complex.arg w) y hR_pos

/-- Reciprocal denominator comparison for the shifted vertical Stirling
normalization.

For `w = x + N + i y` in a fixed shifted right-half-plane strip, the
principal-branch identity
`log ‖w^(1/2-w)‖ = (1/2 - Re w) log ‖w‖ + arg(w) Im w`, together with
`‖exp w‖ = exp (Re w)`, shows that
`1 / (‖exp w‖ ‖w^(1/2-w)‖)` is comparable to
`exp (-π |y| / 2) (1 + |y|)^(Re w - 1/2)`.  This is the sharp vertical-line
branch comparison left after the normalized sectorial Stirling estimate has
been extracted. -/
theorem Complex.shiftedVerticalStirlingDenominator_reciprocal_comparable
    (A B : ℝ) :
    ∃ H : ℝ, ∃ C : ℝ, ∃ c : ℝ,
      0 < H ∧
      0 < C ∧
      0 < c ∧
      ∀ x y : ℝ,
        A ≤ x →
        x ≤ B →
        H ≤ ‖y‖ →
          let w : ℂ :=
            Complex.fixedRealPartVerticalPoint
              (x + Complex.verticalStripTransportShift A) y
          0 < ‖Complex.exp w‖ *
                ‖w ^ ((1 / 2 : ℂ) - w)‖ ∧
          1 / (‖Complex.exp w‖ *
                ‖w ^ ((1 / 2 : ℂ) - w)‖) ≤
            C * Complex.fixedRealPartVerticalStirlingEnvelope
              (x + Complex.verticalStripTransportShift A) y ∧
          c * Complex.fixedRealPartVerticalStirlingEnvelope
              (x + Complex.verticalStripTransportShift A) y ≤
            1 / (‖Complex.exp w‖ *
                ‖w ^ ((1 / 2 : ℂ) - w)‖) := by
  match Complex.shiftedVertical_arg_exponential_defect_comparable A B with
  | ⟨Ha, Ca, ca, hHa_pos, hCa_pos, hca_pos, harg⟩ =>
  match Complex.shiftedVertical_radiusPower_comparable A B with
  | ⟨Hr, Cr, cr, hHr_pos, hCr_pos, hcr_pos, hradius⟩ =>
  match Complex.shiftedVertical_realPartExp_bounded A B with
  | ⟨Ce, ce, hCe_pos, hce_pos, hexpRe⟩ =>
  let H : ℝ := max Ha Hr
  have hH_pos : 0 < H :=
    lt_of_lt_of_le hHa_pos (le_max_left Ha Hr)
  have hC_pos : 0 < (Ca * Cr) * Ce :=
    mul_pos (mul_pos hCa_pos hCr_pos) hCe_pos
  have hc_pos : 0 < (ca * cr) * ce :=
    mul_pos (mul_pos hca_pos hcr_pos) hce_pos
  exact ⟨H, (Ca * Cr) * Ce, (ca * cr) * ce,
    hH_pos, hC_pos, hc_pos, by
  intro x y hxA hxB hy
  have hy_a : Ha ≤ ‖y‖ :=
    le_trans (le_max_left Ha Hr) hy
  have hy_r : Hr ≤ ‖y‖ :=
    le_trans (le_max_right Ha Hr) hy
  let w : ℂ :=
    Complex.fixedRealPartVerticalPoint
      (x + Complex.verticalStripTransportShift A) y
  let Eexp : ℝ := Real.exp (-(Real.pi / 2) * ‖y‖)
  let P : ℝ := (1 + ‖y‖) ^
    (x + Complex.verticalStripTransportShift A - 1 / 2)
  have harg_xy := harg x y hxA hxB hy_a
  have hradius_xy := hradius x y hxA hxB hy_r
  have hexpRe_xy := hexpRe x y hxA hxB
  have hw_re :
      w.re = x + Complex.verticalStripTransportShift A :=
    Complex.fixedRealPartVerticalPoint_re
      (x + Complex.verticalStripTransportShift A) y
  have hw_ne : w ≠ 0 := by
    have hH_pos : 0 < H :=
      lt_of_lt_of_le hHa_pos (le_max_left Ha Hr)
    have hw_norm_pos : 0 < ‖w‖ :=
      lt_of_lt_of_le hH_pos
        (Complex.verticalStripTransportShift_radius_ge_of_height_ge hy)
    exact norm_pos_iff.mp hw_norm_pos
  have hden_pos :
      0 < ‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖ :=
    Complex.stirlingDenominator_pos_of_ne_zero hw_ne
  have hcpow_norm :
      ‖w ^ ((1 / 2 : ℂ) - w)‖ =
        ‖w‖ ^ (((1 / 2 : ℂ) - w).re) /
          Real.exp (Complex.arg w * (((1 / 2 : ℂ) - w).im)) :=
    Complex.norm_cpow_eq_norm_rpow_div_exp_arg_mul_im_of_ne_zero hw_ne
  have hreciprocal_shape :
      1 / (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) =
        Real.exp (-(Complex.arg w * y)) *
          ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) := by
    exact
      Complex.stirlingDenominator_reciprocal_shape_fixedVertical
        hw_ne
        (Complex.fixedRealPartVerticalPoint_im
          (x + Complex.verticalStripTransportShift A) y)
  constructor
  · exact hden_pos
  constructor
  · have hrad_upper :
        ‖w‖ ^ (w.re - 1 / 2) ≤ Cr * P := by
      calc
        ‖w‖ ^ (w.re - 1 / 2) =
            ‖w‖ ^ ((x + Complex.verticalStripTransportShift A) - 1 / 2) :=
          congrArg (fun t : ℝ => ‖w‖ ^ (t - 1 / 2)) hw_re
        _ ≤ Cr * P := hradius_xy.1
    have harg_upper :
        Real.exp (-(Complex.arg w * y)) ≤ Ca * Eexp :=
      harg_xy.1
    have hexpRe_upper :
        Real.exp (-w.re) ≤ Ce :=
      hexpRe_xy.1
    have hshape_bound :
        Real.exp (-(Complex.arg w * y)) *
            ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) ≤
          ((Ca * Cr) * Ce) *
            (Eexp * P) := by
      have harg_nonneg :
          0 ≤ Real.exp (-(Complex.arg w * y)) :=
        le_of_lt (Real.exp_pos (-(Complex.arg w * y)))
      have hrad_nonneg :
          0 ≤ ‖w‖ ^ (w.re - 1 / 2) :=
        Real.rpow_nonneg (norm_nonneg w) (w.re - 1 / 2)
      have hexpRe_nonneg :
          0 ≤ Real.exp (-w.re) :=
        le_of_lt (Real.exp_pos (-w.re))
      have hEexp_nonneg : 0 ≤ Eexp :=
        le_of_lt (Real.exp_pos (-(Real.pi / 2) * ‖y‖))
      have hP_nonneg : 0 ≤ P :=
        Real.rpow_nonneg (add_nonneg zero_le_one (norm_nonneg y))
          (x + Complex.verticalStripTransportShift A - 1 / 2)
      have hCrP_nonneg : 0 ≤ Cr * P :=
        mul_nonneg (le_of_lt hCr_pos) hP_nonneg
      have hCaE_nonneg : 0 ≤ Ca * Eexp :=
        mul_nonneg (le_of_lt hCa_pos) hEexp_nonneg
      have hfirst :
          Real.exp (-(Complex.arg w * y)) *
              ‖w‖ ^ (w.re - 1 / 2) ≤
            (Ca * Eexp) * (Cr * P) :=
        mul_le_mul harg_upper hrad_upper hrad_nonneg hCaE_nonneg
      have htarget_step :
          Real.exp (-(Complex.arg w * y)) *
              ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) ≤
            ((Ca * Eexp) * (Cr * P)) * Ce :=
        mul_le_mul hfirst hexpRe_upper hexpRe_nonneg
          (mul_nonneg hCaE_nonneg hCrP_nonneg)
      have htarget_eq :
          ((Ca * Eexp) * (Cr * P)) * Ce =
            ((Ca * Cr) * Ce) * (Eexp * P) := by
        calc
          ((Ca * Eexp) * (Cr * P)) * Ce =
              (Ca * Eexp) * ((Cr * P) * Ce) :=
            (mul_assoc (Ca * Eexp) (Cr * P) Ce).symm
          _ = (Ca * Eexp) * (Ce * (Cr * P)) := by
            exact congrArg
              (fun t : ℝ => (Ca * Eexp) * t)
              (mul_comm (Cr * P) Ce)
          _ = ((Ca * Eexp) * Ce) * (Cr * P) :=
            mul_assoc (Ca * Eexp) Ce (Cr * P)
          _ = (Ca * (Eexp * Ce)) * (Cr * P) := by
            exact congrArg
              (fun t : ℝ => t * (Cr * P))
              (mul_assoc Ca Eexp Ce)
          _ = (Ca * (Ce * Eexp)) * (Cr * P) := by
            exact congrArg
              (fun t : ℝ => (Ca * t) * (Cr * P))
              (mul_comm Eexp Ce)
          _ = ((Ca * Ce) * Eexp) * (Cr * P) := by
            exact congrArg
              (fun t : ℝ => t * (Cr * P))
              (mul_assoc Ca Ce Eexp).symm
          _ = (Ca * Ce) * (Eexp * (Cr * P)) :=
            (mul_assoc (Ca * Ce) Eexp (Cr * P)).symm
          _ = (Ca * Ce) * ((Cr * P) * Eexp) := by
            exact congrArg
              (fun t : ℝ => (Ca * Ce) * t)
              (mul_comm Eexp (Cr * P))
          _ = ((Ca * Ce) * (Cr * P)) * Eexp :=
            mul_assoc (Ca * Ce) (Cr * P) Eexp
          _ = (Ca * (Ce * (Cr * P))) * Eexp := by
            exact congrArg
              (fun t : ℝ => t * Eexp)
              (mul_assoc Ca Ce (Cr * P))
          _ = (Ca * ((Cr * P) * Ce)) * Eexp := by
            exact congrArg
              (fun t : ℝ => (Ca * t) * Eexp)
              (mul_comm Ce (Cr * P))
          _ = (Ca * (Cr * (P * Ce))) * Eexp := by
            exact congrArg
              (fun t : ℝ => (Ca * t) * Eexp)
              (mul_assoc Cr P Ce)
          _ = (Ca * (Cr * (Ce * P))) * Eexp := by
            exact congrArg
              (fun t : ℝ => (Ca * (Cr * t)) * Eexp)
              (mul_comm P Ce)
          _ = (Ca * ((Cr * Ce) * P)) * Eexp := by
            exact congrArg
              (fun t : ℝ => (Ca * t) * Eexp)
              (mul_assoc Cr Ce P).symm
          _ = ((Ca * (Cr * Ce)) * P) * Eexp :=
            congrArg (fun t : ℝ => t * Eexp)
              (mul_assoc Ca (Cr * Ce) P)
          _ = (((Ca * Cr) * Ce) * P) * Eexp := by
            exact congrArg
              (fun t : ℝ => (t * P) * Eexp)
              (mul_assoc Ca Cr Ce).symm
          _ = ((Ca * Cr) * Ce) * (P * Eexp) :=
            (mul_assoc ((Ca * Cr) * Ce) P Eexp).symm
          _ = ((Ca * Cr) * Ce) * (Eexp * P) := by
            exact congrArg
              (fun t : ℝ => ((Ca * Cr) * Ce) * t)
              (mul_comm P Eexp)
      exact le_trans htarget_step (le_of_eq htarget_eq)
    have henv_eq :
        Eexp * P =
          Complex.fixedRealPartVerticalStirlingEnvelope
            (x + Complex.verticalStripTransportShift A) y := by
      rfl
    calc
      1 / (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) =
          Real.exp (-(Complex.arg w * y)) *
            ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) :=
        hreciprocal_shape
      _ ≤ ((Ca * Cr) * Ce) * (Eexp * P) := hshape_bound
      _ = ((Ca * Cr) * Ce) *
          Complex.fixedRealPartVerticalStirlingEnvelope
            (x + Complex.verticalStripTransportShift A) y :=
        congrArg (fun t : ℝ => ((Ca * Cr) * Ce) * t) henv_eq
  · have hrad_lower :
        cr * P ≤ ‖w‖ ^ (w.re - 1 / 2) := by
      calc
        cr * P ≤
            ‖w‖ ^ ((x + Complex.verticalStripTransportShift A) - 1 / 2) :=
          hradius_xy.2
        _ = ‖w‖ ^ (w.re - 1 / 2) :=
          (congrArg (fun t : ℝ => ‖w‖ ^ (t - 1 / 2)) hw_re).symm
    have harg_lower :
        ca * Eexp ≤ Real.exp (-(Complex.arg w * y)) :=
      harg_xy.2
    have hexpRe_lower :
        ce ≤ Real.exp (-w.re) :=
      hexpRe_xy.2
    have hshape_bound :
        ((ca * cr) * ce) *
            (Eexp * P) ≤
          Real.exp (-(Complex.arg w * y)) *
            ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) := by
      have hEexp_nonneg : 0 ≤ Eexp :=
        le_of_lt (Real.exp_pos (-(Real.pi / 2) * ‖y‖))
      have hP_nonneg : 0 ≤ P :=
        Real.rpow_nonneg (add_nonneg zero_le_one (norm_nonneg y))
          (x + Complex.verticalStripTransportShift A - 1 / 2)
      have hce_nonneg : 0 ≤ ce :=
        le_of_lt hce_pos
      have hcrP_nonneg : 0 ≤ cr * P :=
        mul_nonneg (le_of_lt hcr_pos) hP_nonneg
      have hcaE_nonneg : 0 ≤ ca * Eexp :=
        mul_nonneg (le_of_lt hca_pos) hEexp_nonneg
      have hleft_eq :
          ((ca * cr) * ce) * (Eexp * P) =
            (ca * Eexp) * (cr * P) * ce := by
        calc
          ((ca * cr) * ce) * (Eexp * P) =
              (ca * cr) * (ce * (Eexp * P)) :=
            (mul_assoc (ca * cr) ce (Eexp * P)).symm
          _ = (ca * cr) * ((Eexp * P) * ce) := by
            exact congrArg
              (fun t : ℝ => (ca * cr) * t)
              (mul_comm ce (Eexp * P))
          _ = ((ca * cr) * (Eexp * P)) * ce :=
            mul_assoc (ca * cr) (Eexp * P) ce
          _ = (ca * (cr * (Eexp * P))) * ce := by
            exact congrArg
              (fun t : ℝ => t * ce)
              (mul_assoc ca cr (Eexp * P))
          _ = (ca * ((Eexp * P) * cr)) * ce := by
            exact congrArg
              (fun t : ℝ => (ca * t) * ce)
              (mul_comm cr (Eexp * P))
          _ = (ca * (Eexp * (P * cr))) * ce := by
            exact congrArg
              (fun t : ℝ => (ca * t) * ce)
              (mul_assoc Eexp P cr)
          _ = (ca * (Eexp * (cr * P))) * ce := by
            exact congrArg
              (fun t : ℝ => (ca * (Eexp * t)) * ce)
              (mul_comm P cr)
          _ = (ca * ((Eexp * cr) * P)) * ce := by
            exact congrArg
              (fun t : ℝ => (ca * t) * ce)
              (mul_assoc Eexp cr P).symm
          _ = (ca * ((cr * Eexp) * P)) * ce := by
            exact congrArg
              (fun t : ℝ => (ca * (t * P)) * ce)
              (mul_comm Eexp cr)
          _ = (ca * (cr * (Eexp * P))) * ce := by
            exact congrArg
              (fun t : ℝ => (ca * t) * ce)
              (mul_assoc cr Eexp P)
          _ = ((ca * cr) * (Eexp * P)) * ce := by
            exact congrArg
              (fun t : ℝ => t * ce)
              (mul_assoc ca cr (Eexp * P)).symm
          _ = ((ca * cr) * (P * Eexp)) * ce := by
            exact congrArg
              (fun t : ℝ => ((ca * cr) * t) * ce)
              (mul_comm Eexp P)
          _ = (ca * cr) * (P * Eexp) * ce := rfl
          _ = (ca * (cr * P) * Eexp) * ce := by
            exact congrArg
              (fun t : ℝ => t * ce)
              (by
                calc
                  (ca * cr) * (P * Eexp) =
                      ca * (cr * (P * Eexp)) :=
                    (mul_assoc ca cr (P * Eexp)).symm
                  _ = ca * ((cr * P) * Eexp) := by
                    exact congrArg
                      (fun t : ℝ => ca * t)
                      (mul_assoc cr P Eexp)
                  _ = ca * (cr * P) * Eexp :=
                    mul_assoc ca (cr * P) Eexp)
          _ = (Eexp * (ca * (cr * P))) * ce := by
            exact congrArg
              (fun t : ℝ => t * ce)
              (mul_comm (ca * (cr * P)) Eexp)
          _ = ((ca * (cr * P)) * Eexp) * ce := by
            exact congrArg
              (fun t : ℝ => t * ce)
              (mul_comm Eexp (ca * (cr * P)))
          _ = (ca * ((cr * P) * Eexp)) * ce := by
            exact congrArg
              (fun t : ℝ => t * ce)
              (mul_assoc ca (cr * P) Eexp).symm
          _ = (ca * (Eexp * (cr * P))) * ce := by
            exact congrArg
              (fun t : ℝ => (ca * t) * ce)
              (mul_comm (cr * P) Eexp)
          _ = ((ca * Eexp) * (cr * P)) * ce := by
            exact congrArg
              (fun t : ℝ => t * ce)
              (mul_assoc ca Eexp (cr * P))
          _ = (ca * Eexp) * (cr * P) * ce := rfl
      have hfirst :
          (ca * Eexp) * (cr * P) ≤
            Real.exp (-(Complex.arg w * y)) *
              ‖w‖ ^ (w.re - 1 / 2) :=
        mul_le_mul harg_lower hrad_lower hcrP_nonneg
          (le_of_lt (Real.exp_pos (-(Complex.arg w * y))))
      have hsecond :
          (ca * Eexp) * (cr * P) * ce ≤
            Real.exp (-(Complex.arg w * y)) *
              ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) :=
        mul_le_mul hfirst hexpRe_lower hce_nonneg
          (mul_nonneg
            (le_of_lt (Real.exp_pos (-(Complex.arg w * y))))
            (Real.rpow_nonneg (norm_nonneg w) (w.re - 1 / 2)))
      exact le_trans (le_of_eq hleft_eq) hsecond
    have henv_eq :
        Eexp * P =
          Complex.fixedRealPartVerticalStirlingEnvelope
            (x + Complex.verticalStripTransportShift A) y := by
      rfl
    calc
      ((ca * cr) * ce) *
          Complex.fixedRealPartVerticalStirlingEnvelope
            (x + Complex.verticalStripTransportShift A) y =
          ((ca * cr) * ce) * (Eexp * P) :=
        congrArg (fun t : ℝ => ((ca * cr) * ce) * t) henv_eq.symm
      _ ≤ Real.exp (-(Complex.arg w * y)) *
            ‖w‖ ^ (w.re - 1 / 2) * Real.exp (-w.re) :=
        hshape_bound
      _ = 1 / (‖Complex.exp w‖ * ‖w ^ ((1 / 2 : ℂ) - w)‖) :=
        hreciprocal_shape.symm⟩

/- Sectorial normalized Stirling, on the shifted closed-right-half-plane
points, gives the raw two-sided Gamma envelope with shifted real part.

This is the branch/exponential extraction layer: it converts control of
`Γ(w) e^w w^(1/2-w)` into the classical
`exp (-π |y| / 2) (1 + |y|)^(Re w - 1/2)` profile for
`w = x + N + i y`.  The only analytic input is the sectorial Stirling
hypothesis; the rest is principal-branch norm algebra. -/

end
end LFunctions
